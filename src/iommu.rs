// Copyright (C) 2025 Red Hat. All rights reserved.
//
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Provide an interface for IOMMUs enabling I/O virtual address (IOVA) translation.
//!
//! All IOMMUs consist of an IOTLB ([`Iotlb`]), which is backed by a data source that can deliver
//! all mappings.  For example, for vhost-user, that data source is the vhost-user front-end; i.e.
//! IOTLB misses require sending a notification to the front-end and awaiting a reply that supplies
//! the desired mapping.

use crate::bitmap::{self, Bitmap};
use crate::guest_memory::{
    Error as GuestMemoryError, GuestMemorySliceIterator, IoMemorySliceIterator,
    Result as GuestMemoryResult,
};
use crate::{
    Address, GuestAddress, GuestMemory, GuestMemoryRegion, GuestUsize, IoMemory, Permissions,
    VolatileSlice,
};
use rangemap::RangeMap;
use std::cmp;
use std::fmt::{self, Debug};
use std::iter::FusedIterator;
use std::num::Wrapping;
use std::ops::{Deref, Range};
use std::sync::Arc;

/// Errors associated with IOMMU address translation.
#[derive(Debug, thiserror::Error)]
pub enum Error {
    /// Lookup cannot be resolved.
    #[error(
        "Cannot translate I/O virtual address range {:#x}+{}: {reason}",
        iova_range.base.0,
        iova_range.length,
    )]
    CannotResolve {
        /// IOVA range that could not be resolved
        iova_range: IovaRange,
        /// Some human-readable specifics about the reason
        reason: String,
    },

    /// Wanted to translate an IOVA range into a single slice, but the range is fragmented.
    #[error(
        "Expected {:#x}+{} to be a continuous I/O virtual address range, but only {continuous_length} bytes are",
        iova_range.base.0,
        iova_range.length,
    )]
    Fragmented {
        /// Full IOVA range that was to be translated
        iova_range: IovaRange,
        /// Length of the continuous head (i.e. the first fragment)
        continuous_length: usize,
    },

    /// IOMMU is not configured correctly, and so cannot translate addresses.
    #[error("IOMMU not configured correctly, cannot operate: {reason}")]
    IommuMisconfigured {
        /// Some human-readable specifics about the misconfiguration
        reason: String,
    },
}

/// An IOMMU, allowing translation of I/O virtual addresses (IOVAs).
///
/// Generally, `Iommu` implementaions consist of an [`Iotlb`], which is supposed to be consulted
/// first for lookup requests.  All misses and access failures then should be resolved by looking
/// up the affected ranges in the actual IOMMU (which has all current mappings) and putting the
/// results back into the IOTLB.  A subsequent lookup in the IOTLB should result in a full
/// translation, which can then be returned.
pub trait Iommu: Debug + Send + Sync {
    /// `Deref` type associated with the type that internally wraps the `Iotlb`.
    ///
    /// For example, the `Iommu` may keep the `Iotlb` wrapped in an `RwLock`, making this type
    /// `RwLockReadGuard<'a, Iotlb>`.
    ///
    /// We need this specific type instead of a plain reference so that [`IotlbIterator`] can
    /// actually own the reference and prolong its lifetime.
    type IotlbGuard<'a>: Deref<Target = Iotlb> + 'a
    where
        Self: 'a;

    /// Translate the given range for the given access into the underlying address space.
    ///
    /// Any translation request is supposed to be fully served by an internal [`Iotlb`] instance.
    /// Any misses or access failures should result in a lookup in the full IOMMU structures,
    /// filling the IOTLB with the results, and then repeating the lookup in there.
    fn translate(
        &self,
        iova: GuestAddress,
        length: usize,
        access: Permissions,
    ) -> Result<IotlbIterator<Self::IotlbGuard<'_>>, Error>;
}

/// Mapping target in an IOMMU/IOTLB.
///
/// This is the data to which each entry in an IOMMU/IOTLB maps.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct IommuMapping {
    /// Difference between the mapped and the IOVA address, i.e. what to add to an IOVA address to
    /// get the mapped adrress.
    ///
    /// We cannot store the more obvious mapped base address for this range because that would
    /// allow rangemap to wrongfully merge consecutive map entries if they are a duplicate mapping
    /// (which does happen).  Storing the difference ensures that entries are only merged when they
    /// are indeed consecutive.
    ///
    /// Note that we make no granularity restrictions (i.e. do not operate on a unit like pages),
    /// so the source and target address may have arbitrary alignment.  That is why both fields
    /// here need to be separate and we cannot merge the two bits that are `permissions` with this
    /// base address into a single `u64` field.
    target_source_diff: Wrapping<u64>,
    /// Allowed access for the mapped range
    permissions: Permissions,
}

/// Provides an IOTLB.
///
/// The IOTLB caches IOMMU mappings.  It must be preemptively updated whenever mappings are
/// restricted or removed; in contrast, adding mappings or making them more permissive does not
/// require preemptive updates, as subsequent accesses that violate the previous (more restrictive)
/// permissions will trigger TLB misses or access failures, which is then supposed to result in an
/// update from the outer [`Iommu`] object that performs the translation.
#[derive(Debug, Default)]
pub struct Iotlb {
    /// Mappings of which we know.
    ///
    /// Note that the vhost(-user) specification makes no mention of a specific page size, even
    /// though in practice the IOVA address space will be organized in terms of pages.  However, we
    /// cannot really rely on that (or any specific page size; it could be 4k, the guest page size,
    /// or the host page size), so we need to be able to handle continuous ranges of any
    /// granularity.
    tlb: RangeMap<u64, IommuMapping>,
}

/// Iterates over a range of valid IOTLB mappings that together constitute a continuous range in
/// I/O virtual address space.
///
/// Returned by [`Iotlb::lookup()`] and [`Iommu::translate()`] in case translation was successful
/// (i.e. the whole requested range is mapped and permits the given access).
#[derive(Clone, Debug)]
pub struct IotlbIterator<D: Deref<Target = Iotlb>> {
    /// IOTLB that provides these mapings
    iotlb: D,
    /// I/O virtual address range left to iterate over
    range: Range<u64>,
    /// Requested access permissions
    access: Permissions,
}

/// Representation of an IOVA memory range (i.e. in the I/O virtual address space).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IovaRange {
    /// IOVA base address
    pub base: GuestAddress,
    /// Length (in bytes) of this range
    pub length: usize,
}

/// Representation of a mapped memory range in the underlying address space.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MappedRange {
    /// Base address in the underlying address space
    pub base: GuestAddress,
    /// Length (in bytes) of this mapping
    pub length: usize,
}

/// Lists the subranges in I/O virtual address space that turned out to not be accessible when
/// trying to access an IOVA range.
#[derive(Clone, Debug)]
pub struct IotlbFails {
    /// Subranges not mapped at all
    pub misses: Vec<IovaRange>,
    /// Subranges that are mapped, but do not allow the requested access mode
    pub access_fails: Vec<IovaRange>,
}

/// [`IoMemory`] type that consists of an underlying [`GuestMemory`] object plus an [`Iommu`].
///
/// The underlying [`GuestMemory`] is basically the physical memory, and the [`Iommu`] translates
/// the I/O virtual address space that `IommuMemory` provides into that underlying physical address
/// space.
///
/// Note that this type’s implementation of memory write tracking (“logging”) is specific to what
/// is required by vhost-user:
/// - When the IOMMU is disabled ([`IommuMemory::set_iommu_enabled()`]), writes to memory are
///   tracked by the underlying [`GuestMemory`] in its bitmap(s).
/// - When it is enabled, they are instead tracked in the [`IommuMemory`]’s dirty bitmap; the
///   offset in the bitmap is calculated from the write’s IOVA.
///
/// That is, there are two bitmap levels, one in the underlying [`GuestMemory`], and one in
/// [`IommuMemory`].  The former is used when the IOMMU is disabled, the latter when it is enabled.
///
/// If you need a different model (e.g. always use the [`GuestMemory`] bitmaps), you should not use
/// this type.
pub struct IommuMemory<M: GuestMemory, I: Iommu> {
    /// Physical memory
    backend: M,
    /// IOMMU to translate IOVAs into physical addresses
    iommu: Arc<I>,
    /// Whether the IOMMU is even to be used or not; disabling it makes this a pass-through to
    /// `backend`.
    use_iommu: bool,
    /// Dirty bitmap to use for IOVA accesses
    bitmap: Arc<<M::R as GuestMemoryRegion>::B>,
}

impl IommuMapping {
    /// Create a new mapping.
    fn new(source_base: u64, target_base: u64, permissions: Permissions) -> Self {
        IommuMapping {
            target_source_diff: Wrapping(target_base) - Wrapping(source_base),
            permissions,
        }
    }

    /// Map the given source address (IOVA) to its corresponding target address.
    fn map(&self, iova: u64) -> u64 {
        (Wrapping(iova) + self.target_source_diff).0
    }

    /// Return the permissions for this mapping.
    fn permissions(&self) -> Permissions {
        self.permissions
    }
}

impl Iotlb {
    /// Create a new empty instance.
    pub fn new() -> Self {
        Default::default()
    }

    /// Change the mapping of the given IOVA range.
    pub fn set_mapping(
        &mut self,
        iova: GuestAddress,
        map_to: GuestAddress,
        length: usize,
        perm: Permissions,
    ) -> Result<(), Error> {
        // Soft TODO: We may want to evict old entries here once the TLB grows to a certain size,
        // but that will require LRU book-keeping.  However, this is left for the future, because:
        // - this TLB is not implemented in hardware, so we do not really have strong entry count
        //   constraints, and
        // - it seems like at least Linux guests invalidate mappings often, automatically limiting
        //   our entry count.

        let mapping = IommuMapping::new(iova.0, map_to.0, perm);
        self.tlb.insert(iova.0..(iova.0 + length as u64), mapping);

        Ok(())
    }

    /// Remove any mapping in the given IOVA range.
    pub fn invalidate_mapping(&mut self, iova: GuestAddress, length: usize) {
        self.tlb.remove(iova.0..(iova.0 + length as u64));
    }

    /// Remove all mappings.
    pub fn invalidate_all(&mut self) {
        self.tlb.clear();
    }

    /// Perform a lookup for the given range and the given `access` mode.
    ///
    /// If the whole range is mapped and accessible, return an iterator over all mappings.
    ///
    /// If any part of the range is not mapped or does not permit the given access mode, return an
    /// `Err(_)` that contains a list of all such subranges.
    pub fn lookup<D: Deref<Target = Iotlb>>(
        this: D,
        iova: GuestAddress,
        length: usize,
        access: Permissions,
    ) -> Result<IotlbIterator<D>, IotlbFails> {
        let full_range = iova.0..(iova.0 + length as u64);

        let has_misses = this.tlb.gaps(&full_range).any(|_| true);
        let has_access_fails = this
            .tlb
            .overlapping(full_range.clone())
            .any(|(_, mapping)| !mapping.permissions().allow(access));

        if has_misses || has_access_fails {
            let misses = this
                .tlb
                .gaps(&full_range)
                .map(|range| {
                    // Gaps are always cut down to the range given to `gaps()`
                    debug_assert!(range.start >= full_range.start && range.end <= full_range.end);
                    range.try_into().unwrap()
                })
                .collect::<Vec<_>>();

            let access_fails = this
                .tlb
                .overlapping(full_range.clone())
                .filter(|(_, mapping)| !mapping.permissions().allow(access))
                .map(|(range, _)| {
                    let start = cmp::max(range.start, full_range.start);
                    let end = cmp::min(range.end, full_range.end);
                    (start..end).try_into().unwrap()
                })
                .collect::<Vec<_>>();

            return Err(IotlbFails {
                misses,
                access_fails,
            });
        }

        Ok(IotlbIterator {
            iotlb: this,
            range: full_range,
            access,
        })
    }
}

impl<D: Deref<Target = Iotlb>> Iterator for IotlbIterator<D> {
    /// Addresses in the underlying address space
    type Item = MappedRange;

    fn next(&mut self) -> Option<Self::Item> {
        // Note that we can expect the whole IOVA range to be mapped with the right access flags.
        // The `IotlbIterator` is created by `Iotlb::lookup()` only if the whole range is mapped
        // accessibly; we have a permanent reference to `Iotlb`, so the range cannot be invalidated
        // in the meantime.
        // Another note: It is tempting to have `IotlbIterator` wrap around the
        // `rangemap::Overlapping` iterator, but that just takes a (lifetimed) reference to the
        // map, not an owned reference (like RwLockReadGuard), which we want to use; so using that
        // would probably require self-referential structs.

        if self.range.is_empty() {
            return None;
        }

        let (range, mapping) = self.iotlb.tlb.get_key_value(&self.range.start).unwrap();

        assert!(mapping.permissions().allow(self.access));

        let mapping_iova_start = self.range.start;
        let mapping_iova_end = cmp::min(self.range.end, range.end);
        let mapping_len = mapping_iova_end - mapping_iova_start;

        self.range.start = mapping_iova_end;

        Some(MappedRange {
            base: GuestAddress(mapping.map(mapping_iova_start)),
            length: mapping_len.try_into().unwrap(),
        })
    }
}

impl TryFrom<Range<u64>> for IovaRange {
    type Error = <u64 as TryFrom<usize>>::Error;

    fn try_from(range: Range<u64>) -> Result<Self, Self::Error> {
        Ok(IovaRange {
            base: GuestAddress(range.start),
            length: (range.end - range.start).try_into()?,
        })
    }
}

impl<M: GuestMemory, I: Iommu> IommuMemory<M, I> {
    /// Create a new `IommuMemory` instance.
    pub fn new(backend: M, iommu: I, use_iommu: bool, bitmap: <Self as IoMemory>::Bitmap) -> Self {
        IommuMemory {
            backend,
            iommu: Arc::new(iommu),
            use_iommu,
            bitmap: Arc::new(bitmap),
        }
    }

    /// Create a new version of `self` with the underlying physical memory replaced.
    ///
    /// Note that the inner `Arc` references to the IOMMU and bitmap are cloned, i.e. both the
    /// existing and the new `IommuMemory` object will share the IOMMU and bitmap instances.  (The
    /// `use_iommu` flag however is copied, so is independent between the two instances.)
    pub fn with_replaced_backend(&self, new_backend: M) -> Self {
        IommuMemory {
            backend: new_backend,
            iommu: Arc::clone(&self.iommu),
            use_iommu: self.use_iommu,
            bitmap: Arc::clone(&self.bitmap),
        }
    }

    /// Return a reference to the IOVA address space's dirty bitmap.
    ///
    /// This bitmap tracks write accesses done while the IOMMU is enabled.
    pub fn bitmap(&self) -> &Arc<<Self as IoMemory>::Bitmap> {
        &self.bitmap
    }

    /// Enable or disable the IOMMU.
    ///
    /// Disabling the IOMMU switches to pass-through mode, where every access is done directly on
    /// the underlying physical memory.
    pub fn set_iommu_enabled(&mut self, enabled: bool) {
        self.use_iommu = enabled;
    }

    /// Check whether the IOMMU is enabled.
    ///
    /// If the IOMMU is disabled, we operate in pass-through mode, where every access is done
    /// directly on the underlying physical memory.
    pub fn get_iommu_enabled(&self) -> bool {
        self.use_iommu
    }

    /// Return a reference to the IOMMU.
    pub fn iommu(&self) -> &Arc<I> {
        &self.iommu
    }

    /// Return a reference to the underlying physical memory object.
    pub fn get_backend(&self) -> &M {
        &self.backend
    }
}

impl<M: GuestMemory + Clone, I: Iommu> Clone for IommuMemory<M, I> {
    fn clone(&self) -> Self {
        IommuMemory {
            backend: self.backend.clone(),
            iommu: Arc::clone(&self.iommu),
            use_iommu: self.use_iommu,
            bitmap: Arc::clone(&self.bitmap),
        }
    }
}

impl<M: GuestMemory + Debug, I: Iommu> Debug for IommuMemory<M, I>
where
    <M::R as GuestMemoryRegion>::B: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IommuMemory")
            .field("backend", &self.backend)
            .field("iommu", &self.iommu)
            .field("use_iommu", &self.use_iommu)
            .field("bitmap", &self.bitmap)
            .finish()
    }
}

impl<M: GuestMemory + Default, I: Iommu + Default> Default for IommuMemory<M, I>
where
    <M::R as GuestMemoryRegion>::B: Default,
{
    fn default() -> Self {
        IommuMemory {
            backend: Default::default(),
            iommu: Default::default(),
            use_iommu: Default::default(),
            bitmap: Default::default(),
        }
    }
}

impl<M: GuestMemory, I: Iommu> IoMemory for IommuMemory<M, I> {
    type PhysicalMemory = M;
    type Bitmap = <M::R as GuestMemoryRegion>::B;

    fn check_range(&self, addr: GuestAddress, count: usize, access: Permissions) -> bool {
        if !self.use_iommu {
            return self.backend.check_range(addr, count);
        }

        let Ok(mut translated_iter) = self.iommu.translate(addr, count, access) else {
            return false;
        };

        translated_iter
            .all(|translated| self.backend.check_range(translated.base, translated.length))
    }

    fn get_slices<'a>(
        &'a self,
        addr: GuestAddress,
        count: usize,
        access: Permissions,
    ) -> GuestMemoryResult<impl IoMemorySliceIterator<'a, bitmap::BS<'a, Self::Bitmap>>> {
        if self.use_iommu {
            IommuMemorySliceIterator::virt(self, addr, count, access)
                .map_err(GuestMemoryError::IommuError)
        } else {
            Ok(IommuMemorySliceIterator::phys(self, addr, count))
        }
    }

    fn physical_memory(&self) -> Option<&Self::PhysicalMemory> {
        if self.use_iommu {
            None
        } else {
            Some(&self.backend)
        }
    }
}

/// Iterates over [`VolatileSlice`]s that together form an area in an `IommuMemory`.
///
/// Returned by [`IommuMemory::get_slices()`]
pub struct IommuMemorySliceIterator<'a, M: GuestMemory, I: Iommu + 'a> {
    /// Current IOVA (needed to access the right slice of the IOVA space dirty bitmap)
    iova: GuestAddress,
    /// IOVA space dirty bitmap
    bitmap: Option<&'a <M::R as GuestMemoryRegion>::B>,
    /// Underlying physical memory (i.e. not the `IommuMemory`)
    phys_mem: &'a M,
    /// IOMMU translation result (i.e. remaining physical regions to visit)
    translation: Option<IotlbIterator<I::IotlbGuard<'a>>>,
    /// Iterator in the currently visited physical region
    current_translated_iter: Option<GuestMemorySliceIterator<'a, M>>,
}

impl<'a, M: GuestMemory, I: Iommu> IommuMemorySliceIterator<'a, M, I> {
    /// Create an iterator over the physical region `[addr, addr + count)`.
    ///
    /// “Physical” means that the IOMMU is not used to translate this address range.  The resulting
    /// iterator is effectively the same as would be returned by [`GuestMemory::get_slices()`] on
    /// the underlying physical memory for the given address range.
    fn phys(mem: &'a IommuMemory<M, I>, addr: GuestAddress, count: usize) -> Self {
        IommuMemorySliceIterator {
            iova: addr,
            bitmap: None,
            phys_mem: &mem.backend,
            translation: None,
            current_translated_iter: Some(mem.backend.get_slices(addr, count)),
        }
    }

    /// Create an iterator over the IOVA region `[addr, addr + count)`.
    ///
    /// This address range is translated using the IOMMU, and the resulting mappings are then
    /// separately visited via [`GuestMemory::get_slices()`].
    fn virt(
        mem: &'a IommuMemory<M, I>,
        addr: GuestAddress,
        count: usize,
        access: Permissions,
    ) -> Result<Self, Error> {
        let translation = mem.iommu.translate(addr, count, access)?;
        Ok(IommuMemorySliceIterator {
            iova: addr,
            bitmap: Some(mem.bitmap.as_ref()),
            phys_mem: &mem.backend,
            translation: Some(translation),
            current_translated_iter: None,
        })
    }

    /// Helper function for [`<Self as Iterator>::next()`](IommuMemorySliceIterator::next).
    ///
    /// Get the next slice and update the internal state.  If there is an element left in
    /// `self.current_translated_iter`, return that; otherwise, move to the next mapping left in
    /// `self.translation` until there are no more mappings left.
    ///
    /// If both fields are `None`, always return `None`.
    ///
    /// # Safety
    ///
    /// This function never resets `self.current_translated_iter` or `self.translation` to `None`,
    /// particularly not in case of error; calling this function with these fields not reset after
    /// an error is ill-defined, so the caller must check the return value, and in case of an
    /// error, reset these fields to `None`.
    ///
    /// (This is why this function exists, so this reset can happen in a single central location.)
    unsafe fn do_next(
        &mut self,
    ) -> Option<GuestMemoryResult<VolatileSlice<'a, bitmap::MS<'a, M>>>> {
        loop {
            if let Some(item) = self
                .current_translated_iter
                .as_mut()
                .and_then(|iter| iter.next())
            {
                let mut item = match item {
                    Ok(item) => item,
                    Err(err) => return Some(Err(err)),
                };

                if let Some(bitmap) = self.bitmap.as_ref() {
                    let bitmap_slice = bitmap.slice_at(self.iova.0 as usize);
                    item = item.replace_bitmap(bitmap_slice);
                }

                self.iova = match self.iova.overflowing_add(item.len() as GuestUsize) {
                    (x @ GuestAddress(0), _) | (x, false) => x,
                    (_, true) => return Some(Err(GuestMemoryError::GuestAddressOverflow)),
                };

                return Some(Ok(item));
            }

            let next_mapping = self.translation.as_mut()?.next()?;
            self.current_translated_iter = Some(
                self.phys_mem
                    .get_slices(next_mapping.base, next_mapping.length),
            );
        }
    }
}

impl<'a, M: GuestMemory, I: Iommu> Iterator for IommuMemorySliceIterator<'a, M, I> {
    type Item = GuestMemoryResult<VolatileSlice<'a, bitmap::MS<'a, M>>>;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // We reset `current_translated_iter` and `translation` to `None` in case of error
        match unsafe { self.do_next() } {
            Some(Ok(slice)) => Some(Ok(slice)),
            other => {
                // On error (or end), clear both so iteration remains stopped
                self.current_translated_iter.take();
                self.translation.take();
                other
            }
        }
    }
}

/// This iterator continues to return `None` when exhausted.
///
/// [`<Self as Iterator>::next()`](IommuMemorySliceIterator::next) sets both
/// `self.current_translated_iter` and `self.translation` to `None` when returning anything but
/// `Some(Ok(_))`, ensuring that it will only return `None` from that point on.
impl<M: GuestMemory, I: Iommu> FusedIterator for IommuMemorySliceIterator<'_, M, I> {}

impl<'a, M: GuestMemory, I: Iommu> IoMemorySliceIterator<'a, bitmap::MS<'a, M>>
    for IommuMemorySliceIterator<'a, M, I>
{
}

impl<'a, M: GuestMemory + Debug, I: Iommu> Debug for IommuMemorySliceIterator<'a, M, I>
where
    I::IotlbGuard<'a>: Debug,
    <M::R as GuestMemoryRegion>::B: Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IommuMemorySliceIterator")
            .field("iova", &self.iova)
            .field("bitmap", &self.bitmap)
            .field("phys_mem", &self.phys_mem)
            .field("translation", &self.translation)
            .field("current_translated_iter", &self.current_translated_iter)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{Error, IotlbIterator, IovaRange, MappedRange};
    #[cfg(all(feature = "backend-bitmap", feature = "backend-mmap"))]
    use crate::bitmap::AtomicBitmap;
    #[cfg(feature = "backend-mmap")]
    use crate::bitmap::NewBitmap;
    #[cfg(all(feature = "backend-bitmap", feature = "backend-mmap"))]
    use crate::GuestMemoryRegion;
    #[cfg(feature = "backend-mmap")]
    use crate::{
        Bytes, GuestMemoryError, GuestMemoryMmap, GuestMemoryResult, IoMemory, IommuMemory,
    };
    use crate::{GuestAddress, Iommu, Iotlb, Permissions};
    use std::fmt::Debug;
    #[cfg(all(feature = "backend-bitmap", feature = "backend-mmap"))]
    use std::num::NonZeroUsize;
    use std::ops::Deref;
    use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
    use std::sync::{RwLock, RwLockReadGuard};

    #[derive(Debug)]
    struct SimpleIommu {
        iotlb: RwLock<Iotlb>,
        /// Records the last fail event's base IOVA
        fail_base: AtomicU64,
        /// Records the last fail event's length
        fail_len: AtomicUsize,
        /// Records whether the last fail event was a miss
        fail_was_miss: AtomicBool,
        /// What base physical address to map to on the next fail event (0 means return error)
        next_map_to: AtomicU64,
    }

    impl SimpleIommu {
        #[cfg(feature = "backend-mmap")]
        fn new() -> Self {
            SimpleIommu {
                iotlb: Iotlb::new().into(),
                fail_base: 0.into(),
                fail_len: 0.into(),
                fail_was_miss: false.into(),
                next_map_to: 0.into(),
            }
        }

        #[cfg(feature = "backend-mmap")]
        fn expect_mapping_request(&self, to_phys: GuestAddress) {
            // Clear failed range info so it can be tested after the request
            self.fail_base.store(0, Ordering::Relaxed);
            self.fail_len.store(0, Ordering::Relaxed);
            self.next_map_to.store(to_phys.0, Ordering::Relaxed);
        }

        #[cfg(feature = "backend-mmap")]
        fn verify_mapping_request(&self, virt: GuestAddress, len: usize, was_miss: bool) {
            assert_eq!(self.fail_base.load(Ordering::Relaxed), virt.0);
            assert_eq!(self.fail_len.load(Ordering::Relaxed), len);
            assert_eq!(self.fail_was_miss.load(Ordering::Relaxed), was_miss);
        }
    }

    impl Iommu for SimpleIommu {
        type IotlbGuard<'a> = RwLockReadGuard<'a, Iotlb>;

        fn translate(
            &self,
            iova: GuestAddress,
            length: usize,
            access: Permissions,
        ) -> Result<IotlbIterator<Self::IotlbGuard<'_>>, Error> {
            loop {
                let mut fails =
                    match Iotlb::lookup(self.iotlb.read().unwrap(), iova, length, access) {
                        Ok(success) => return Ok(success),
                        Err(fails) => fails,
                    };
                let miss = !fails.misses.is_empty();
                let fail = fails
                    .misses
                    .pop()
                    .or_else(|| fails.access_fails.pop())
                    .expect("No failure reported, even though a failure happened");
                self.fail_base.store(fail.base.0, Ordering::Relaxed);
                self.fail_len.store(fail.length, Ordering::Relaxed);
                self.fail_was_miss.store(miss, Ordering::Relaxed);

                if !fails.misses.is_empty() || !fails.access_fails.is_empty() {
                    return Err(Error::CannotResolve {
                        iova_range: IovaRange { base: iova, length },
                        reason: "This IOMMU can only handle one failure per access".into(),
                    });
                }

                let map_to = self.next_map_to.swap(0, Ordering::Relaxed);
                if map_to == 0 {
                    return Err(Error::CannotResolve {
                        iova_range: IovaRange {
                            base: fail.base,
                            length: fail.length,
                        },
                        reason: "No mapping provided for failed range".into(),
                    });
                }

                self.iotlb.write().unwrap().set_mapping(
                    fail.base,
                    GuestAddress(map_to),
                    fail.length,
                    access,
                )?;
            }
        }
    }

    /// Verify that `iova`+`length` is mapped to `expected`.
    fn verify_hit(
        iotlb: impl Deref<Target = Iotlb> + Debug,
        iova: GuestAddress,
        length: usize,
        permissions: Permissions,
        expected: impl IntoIterator<Item = MappedRange>,
    ) {
        let mut iter = Iotlb::lookup(iotlb, iova, length, permissions)
            .inspect_err(|err| panic!("Unexpected lookup error {err:?}"))
            .unwrap();

        for e in expected {
            assert_eq!(iter.next(), Some(e));
        }
        assert_eq!(iter.next(), None);
    }

    /// Verify that trying to look up `iova`+`length` results in misses at `expected_misses` and
    /// access failures (permission-related) at `expected_access_fails`.
    fn verify_fail(
        iotlb: impl Deref<Target = Iotlb> + Debug,
        iova: GuestAddress,
        length: usize,
        permissions: Permissions,
        expected_misses: impl IntoIterator<Item = IovaRange>,
        expected_access_fails: impl IntoIterator<Item = IovaRange>,
    ) {
        let fails = Iotlb::lookup(iotlb, iova, length, permissions)
            .inspect(|hits| panic!("Expected error on lookup, found {hits:?}"))
            .unwrap_err();

        let mut miss_iter = fails.misses.into_iter();
        for e in expected_misses {
            assert_eq!(miss_iter.next(), Some(e));
        }
        assert_eq!(miss_iter.next(), None);

        let mut accf_iter = fails.access_fails.into_iter();
        for e in expected_access_fails {
            assert_eq!(accf_iter.next(), Some(e));
        }
        assert_eq!(accf_iter.next(), None);
    }

    /// Enter adjacent IOTLB entries and verify they are merged into a single one.
    #[test]
    fn test_iotlb_merge() -> Result<(), Error> {
        const IOVA: GuestAddress = GuestAddress(42);
        const PHYS: GuestAddress = GuestAddress(87);
        const LEN_1: usize = 123;
        const LEN_2: usize = 234;

        let mut iotlb = Iotlb::new();
        iotlb.set_mapping(IOVA, PHYS, LEN_1, Permissions::ReadWrite)?;
        iotlb.set_mapping(
            GuestAddress(IOVA.0 + LEN_1 as u64),
            GuestAddress(PHYS.0 + LEN_1 as u64),
            LEN_2,
            Permissions::ReadWrite,
        )?;

        verify_hit(
            &iotlb,
            IOVA,
            LEN_1 + LEN_2,
            Permissions::ReadWrite,
            [MappedRange {
                base: PHYS,
                length: LEN_1 + LEN_2,
            }],
        );

        // Also check just a partial range
        verify_hit(
            &iotlb,
            GuestAddress(IOVA.0 + LEN_1 as u64 - 1),
            2,
            Permissions::ReadWrite,
            [MappedRange {
                base: GuestAddress(PHYS.0 + LEN_1 as u64 - 1),
                length: 2,
            }],
        );

        Ok(())
    }

    /// Test that adjacent IOTLB entries that map to the same physical address are not merged into
    /// a single entry.
    #[test]
    fn test_iotlb_nomerge_same_phys() -> Result<(), Error> {
        const IOVA: GuestAddress = GuestAddress(42);
        const PHYS: GuestAddress = GuestAddress(87);
        const LEN_1: usize = 123;
        const LEN_2: usize = 234;

        let mut iotlb = Iotlb::new();
        iotlb.set_mapping(IOVA, PHYS, LEN_1, Permissions::ReadWrite)?;
        iotlb.set_mapping(
            GuestAddress(IOVA.0 + LEN_1 as u64),
            PHYS,
            LEN_2,
            Permissions::ReadWrite,
        )?;

        verify_hit(
            &iotlb,
            IOVA,
            LEN_1 + LEN_2,
            Permissions::ReadWrite,
            [
                MappedRange {
                    base: PHYS,
                    length: LEN_1,
                },
                MappedRange {
                    base: PHYS,
                    length: LEN_2,
                },
            ],
        );

        Ok(())
    }

    /// Test permission handling
    #[test]
    fn test_iotlb_perms() -> Result<(), Error> {
        const IOVA_R: GuestAddress = GuestAddress(42);
        const PHYS_R: GuestAddress = GuestAddress(87);
        const LEN_R: usize = 123;
        const IOVA_W: GuestAddress = GuestAddress(IOVA_R.0 + LEN_R as u64);
        const PHYS_W: GuestAddress = GuestAddress(PHYS_R.0 + LEN_R as u64);
        const LEN_W: usize = 234;
        const IOVA_FULL: GuestAddress = IOVA_R;
        const LEN_FULL: usize = LEN_R + LEN_W;

        let mut iotlb = Iotlb::new();
        iotlb.set_mapping(IOVA_R, PHYS_R, LEN_R, Permissions::Read)?;
        iotlb.set_mapping(IOVA_W, PHYS_W, LEN_W, Permissions::Write)?;

        // Test 1: Access whole range as R+W, should completely fail
        verify_fail(
            &iotlb,
            IOVA_FULL,
            LEN_FULL,
            Permissions::ReadWrite,
            [],
            [
                IovaRange {
                    base: IOVA_R,
                    length: LEN_R,
                },
                IovaRange {
                    base: IOVA_W,
                    length: LEN_W,
                },
            ],
        );

        // Test 2: Access whole range as R-only, should fail on second part
        verify_fail(
            &iotlb,
            IOVA_FULL,
            LEN_FULL,
            Permissions::Read,
            [],
            [IovaRange {
                base: IOVA_W,
                length: LEN_W,
            }],
        );

        // Test 3: Access whole range W-only, should fail on second part
        verify_fail(
            &iotlb,
            IOVA_FULL,
            LEN_FULL,
            Permissions::Write,
            [],
            [IovaRange {
                base: IOVA_R,
                length: LEN_R,
            }],
        );

        // Test 4: Access whole range w/o perms, should succeed
        verify_hit(
            &iotlb,
            IOVA_FULL,
            LEN_FULL,
            Permissions::No,
            [
                MappedRange {
                    base: PHYS_R,
                    length: LEN_R,
                },
                MappedRange {
                    base: PHYS_W,
                    length: LEN_W,
                },
            ],
        );

        // Test 5: Access R range as R, should succeed
        verify_hit(
            &iotlb,
            IOVA_R,
            LEN_R,
            Permissions::Read,
            [MappedRange {
                base: PHYS_R,
                length: LEN_R,
            }],
        );

        // Test 6: Access W range as W, should succeed
        verify_hit(
            &iotlb,
            IOVA_W,
            LEN_W,
            Permissions::Write,
            [MappedRange {
                base: PHYS_W,
                length: LEN_W,
            }],
        );

        Ok(())
    }

    /// Test IOTLB invalidation
    #[test]
    fn test_iotlb_invalidation() -> Result<(), Error> {
        const IOVA: GuestAddress = GuestAddress(42);
        const PHYS: GuestAddress = GuestAddress(87);
        const LEN: usize = 123;
        const INVAL_OFS: usize = LEN / 2;
        const INVAL_LEN: usize = 3;
        const IOVA_AT_INVAL: GuestAddress = GuestAddress(IOVA.0 + INVAL_OFS as u64);
        const PHYS_AT_INVAL: GuestAddress = GuestAddress(PHYS.0 + INVAL_OFS as u64);
        const IOVA_POST_INVAL: GuestAddress = GuestAddress(IOVA_AT_INVAL.0 + INVAL_LEN as u64);
        const PHYS_POST_INVAL: GuestAddress = GuestAddress(PHYS_AT_INVAL.0 + INVAL_LEN as u64);
        const POST_INVAL_LEN: usize = LEN - INVAL_OFS - INVAL_LEN;

        let mut iotlb = Iotlb::new();
        iotlb.set_mapping(IOVA, PHYS, LEN, Permissions::ReadWrite)?;
        verify_hit(
            &iotlb,
            IOVA,
            LEN,
            Permissions::ReadWrite,
            [MappedRange {
                base: PHYS,
                length: LEN,
            }],
        );

        // Invalidate something in the middle; expect mapping at the start, then miss, then further
        // mapping
        iotlb.invalidate_mapping(IOVA_AT_INVAL, INVAL_LEN);
        verify_hit(
            &iotlb,
            IOVA,
            INVAL_OFS,
            Permissions::ReadWrite,
            [MappedRange {
                base: PHYS,
                length: INVAL_OFS,
            }],
        );
        verify_fail(
            &iotlb,
            IOVA,
            LEN,
            Permissions::ReadWrite,
            [IovaRange {
                base: IOVA_AT_INVAL,
                length: INVAL_LEN,
            }],
            [],
        );
        verify_hit(
            &iotlb,
            IOVA_POST_INVAL,
            POST_INVAL_LEN,
            Permissions::ReadWrite,
            [MappedRange {
                base: PHYS_POST_INVAL,
                length: POST_INVAL_LEN,
            }],
        );

        // And invalidate everything; expect full miss
        iotlb.invalidate_all();
        verify_fail(
            &iotlb,
            IOVA,
            LEN,
            Permissions::ReadWrite,
            [IovaRange {
                base: IOVA,
                length: LEN,
            }],
            [],
        );

        Ok(())
    }

    /// Create `IommuMemory` backed by multiple physical regions, all mapped into a single virtual
    /// region (if `virt_start`/`virt_perm` are given).
    ///
    /// Memory is filled with incrementing (overflowing) bytes, starting with value `value_offset`.
    #[cfg(feature = "backend-mmap")]
    fn create_virt_memory<B: NewBitmap>(
        virt_mapping: Option<(GuestAddress, Permissions)>,
        value_offset: u8,
        phys_regions: impl IntoIterator<Item = MappedRange>,
        bitmap: B,
    ) -> IommuMemory<GuestMemoryMmap<B>, SimpleIommu> {
        let phys_ranges = phys_regions
            .into_iter()
            .map(|range| (range.base, range.length))
            .collect::<Vec<(GuestAddress, usize)>>();
        let phys_mem = GuestMemoryMmap::<B>::from_ranges(&phys_ranges).unwrap();

        let mut byte_val = value_offset;
        for (base, len) in &phys_ranges {
            let mut slices = phys_mem
                .get_slices(*base, *len, Permissions::Write)
                .inspect_err(|err| panic!("Failed to access memory: {err}"))
                .unwrap();
            let slice = slices
                .next()
                .unwrap()
                .inspect_err(|err| panic!("Failed to access memory: {err}"))
                .unwrap();
            assert!(slices.next().is_none(), "Expected single slice");

            for i in 0..*len {
                slice.write(&[byte_val], i).unwrap();
                byte_val = byte_val.wrapping_add(1);
            }
        }

        let mem = IommuMemory::new(phys_mem, SimpleIommu::new(), true, bitmap);

        // IOMMU is in use, this will be `None`
        assert!(mem.physical_memory().is_none());

        if let Some((mut virt, perm)) = virt_mapping {
            for (base, len) in phys_ranges {
                let mut iotlb = mem.iommu().iotlb.write().unwrap();
                iotlb.set_mapping(virt, base, len, perm).unwrap();
                virt = GuestAddress(virt.0 + len as u64);
            }
        }

        mem
    }

    /// Verify the byte contents at `start`+`len`.  Assume the initial byte value to be
    /// `value_offset`.
    ///
    /// Each byte is expected to be incremented over the last (as created by
    /// `create_virt_memory()`).
    ///
    /// Return an error if mapping fails, but just panic if there is a content mismatch.
    #[cfg(feature = "backend-mmap")]
    fn check_virt_mem_content(
        mem: &impl IoMemory,
        start: GuestAddress,
        len: usize,
        value_offset: u8,
    ) -> GuestMemoryResult<()> {
        let mut ref_value = value_offset;
        for slice in mem.get_slices(start, len, Permissions::Read)? {
            let slice = slice?;

            let count = slice.len();
            let mut data = vec![0u8; count];
            slice.read(&mut data, 0).unwrap();
            for val in data {
                assert_eq!(val, ref_value);
                ref_value = ref_value.wrapping_add(1);
            }
        }

        Ok(())
    }

    #[cfg(feature = "backend-mmap")]
    fn verify_virt_mem_content(
        m: &impl IoMemory,
        start: GuestAddress,
        len: usize,
        value_offset: u8,
    ) {
        check_virt_mem_content(m, start, len, value_offset).unwrap();
    }

    /// Verify that trying to read from `start`+`len` fails (because of `CannotResolve`).
    ///
    /// The reported failed-to-map range is checked to be `fail_start`+`fail_len`.  `fail_start`
    /// defaults to `start`, `fail_len` defaults to the remaining length of the whole mapping
    /// starting at `fail_start` (i.e. `start + len - fail_start`).
    #[cfg(feature = "backend-mmap")]
    fn verify_virt_mem_error(
        m: &impl IoMemory,
        start: GuestAddress,
        len: usize,
        fail_start: Option<GuestAddress>,
        fail_len: Option<usize>,
    ) {
        let fail_start = fail_start.unwrap_or(start);
        let fail_len = fail_len.unwrap_or(len - (fail_start.0 - start.0) as usize);
        let err = check_virt_mem_content(m, start, len, 0).unwrap_err();
        let GuestMemoryError::IommuError(Error::CannotResolve {
            iova_range: failed_range,
            reason: _,
        }) = err
        else {
            panic!("Unexpected error: {err:?}");
        };
        assert_eq!(
            failed_range,
            IovaRange {
                base: fail_start,
                length: fail_len,
            }
        );
    }

    /// Test `IommuMemory`, with pre-filled mappings.
    #[cfg(feature = "backend-mmap")]
    #[test]
    fn test_iommu_memory_pre_mapped() {
        const PHYS_START_1: GuestAddress = GuestAddress(0x4000);
        const PHYS_START_2: GuestAddress = GuestAddress(0x8000);
        const PHYS_LEN: usize = 128;
        const VIRT_START: GuestAddress = GuestAddress(0x2a000);
        const VIRT_LEN: usize = PHYS_LEN * 2;
        const VIRT_POST_MAP: GuestAddress = GuestAddress(VIRT_START.0 + VIRT_LEN as u64);

        let mem = create_virt_memory(
            Some((VIRT_START, Permissions::Read)),
            0,
            [
                MappedRange {
                    base: PHYS_START_1,
                    length: PHYS_LEN,
                },
                MappedRange {
                    base: PHYS_START_2,
                    length: PHYS_LEN,
                },
            ],
            (),
        );

        assert!(mem.check_range(VIRT_START, VIRT_LEN, Permissions::No));
        assert!(mem.check_range(VIRT_START, VIRT_LEN, Permissions::Read));
        assert!(!mem.check_range(VIRT_START, VIRT_LEN, Permissions::Write));
        assert!(!mem.check_range(VIRT_START, VIRT_LEN, Permissions::ReadWrite));
        assert!(!mem.check_range(GuestAddress(VIRT_START.0 - 1), 1, Permissions::No));
        assert!(!mem.check_range(VIRT_POST_MAP, 1, Permissions::No));

        verify_virt_mem_content(&mem, VIRT_START, VIRT_LEN, 0);
        verify_virt_mem_error(&mem, GuestAddress(VIRT_START.0 - 1), 1, None, None);
        verify_virt_mem_error(&mem, VIRT_POST_MAP, 1, None, None);
        verify_virt_mem_error(&mem, VIRT_START, VIRT_LEN + 1, Some(VIRT_POST_MAP), None);
    }

    /// Test `IommuMemory`, with mappings created through the IOMMU on the fly.
    #[cfg(feature = "backend-mmap")]
    #[test]
    fn test_iommu_memory_live_mapped() {
        const PHYS_START_1: GuestAddress = GuestAddress(0x4000);
        const PHYS_START_2: GuestAddress = GuestAddress(0x8000);
        const PHYS_LEN: usize = 128;
        const VIRT_START: GuestAddress = GuestAddress(0x2a000);
        const VIRT_START_1: GuestAddress = VIRT_START;
        const VIRT_START_2: GuestAddress = GuestAddress(VIRT_START.0 + PHYS_LEN as u64);
        const VIRT_LEN: usize = PHYS_LEN * 2;
        const VIRT_POST_MAP: GuestAddress = GuestAddress(VIRT_START.0 + VIRT_LEN as u64);

        let mem = create_virt_memory(
            None,
            0,
            [
                MappedRange {
                    base: PHYS_START_1,
                    length: PHYS_LEN,
                },
                MappedRange {
                    base: PHYS_START_2,
                    length: PHYS_LEN,
                },
            ],
            (),
        );

        assert!(!mem.check_range(VIRT_START, VIRT_LEN, Permissions::No));
        assert!(!mem.check_range(VIRT_START, VIRT_LEN, Permissions::Read));
        assert!(!mem.check_range(VIRT_START, VIRT_LEN, Permissions::Write));
        assert!(!mem.check_range(VIRT_START, VIRT_LEN, Permissions::ReadWrite));
        assert!(!mem.check_range(GuestAddress(VIRT_START.0 - 1), 1, Permissions::No));
        assert!(!mem.check_range(VIRT_POST_MAP, 1, Permissions::No));

        verify_virt_mem_error(&mem, VIRT_START, VIRT_LEN, None, None);
        verify_virt_mem_error(&mem, GuestAddress(VIRT_START.0 - 1), 1, None, None);
        verify_virt_mem_error(&mem, VIRT_POST_MAP, 1, None, None);
        verify_virt_mem_error(&mem, VIRT_START, VIRT_LEN + 1, None, None);

        let iommu = mem.iommu();

        // Can only map one region at a time (with `SimpleIommu`), so only access `PHYS_LEN` first,
        // not `VIRT_LEN`
        iommu.expect_mapping_request(PHYS_START_1);
        verify_virt_mem_content(&mem, VIRT_START, PHYS_LEN, 0);
        iommu.verify_mapping_request(VIRT_START_1, PHYS_LEN, true);

        iommu.expect_mapping_request(PHYS_START_2);
        verify_virt_mem_content(&mem, VIRT_START, VIRT_LEN, 0);
        iommu.verify_mapping_request(VIRT_START_2, PHYS_LEN, true);

        // Also check invalid access failure
        iommu
            .iotlb
            .write()
            .unwrap()
            .set_mapping(VIRT_START_1, PHYS_START_1, PHYS_LEN, Permissions::Write)
            .unwrap();

        iommu.expect_mapping_request(PHYS_START_1);
        verify_virt_mem_content(&mem, VIRT_START, VIRT_LEN, 0);
        iommu.verify_mapping_request(VIRT_START_1, PHYS_LEN, false);
    }

    /// Test replacing the physical memory of an `IommuMemory`.
    #[cfg(feature = "backend-mmap")]
    #[test]
    fn test_mem_replace() {
        const PHYS_START_1: GuestAddress = GuestAddress(0x4000);
        const PHYS_START_2: GuestAddress = GuestAddress(0x8000);
        const PHYS_LEN: usize = 128;
        const VIRT_START: GuestAddress = GuestAddress(0x2a000);

        // Note only one physical region.  `mem2` will have two, to see that this pattern
        // (`with_replaced_backend()`) can be used to e.g. extend physical memory.
        let mem = create_virt_memory(
            Some((VIRT_START, Permissions::Read)),
            0,
            [MappedRange {
                base: PHYS_START_1,
                length: PHYS_LEN,
            }],
            (),
        );

        verify_virt_mem_content(&mem, VIRT_START, PHYS_LEN, 0);
        verify_virt_mem_error(
            &mem,
            VIRT_START,
            PHYS_LEN * 2,
            Some(GuestAddress(VIRT_START.0 + PHYS_LEN as u64)),
            None,
        );

        let mut mem2 = create_virt_memory(
            Some((VIRT_START, Permissions::Read)),
            42,
            [
                MappedRange {
                    base: PHYS_START_1,
                    length: PHYS_LEN,
                },
                MappedRange {
                    base: PHYS_START_2,
                    length: PHYS_LEN,
                },
            ],
            (),
        );

        verify_virt_mem_content(&mem2, VIRT_START, PHYS_LEN * 2, 42);

        // Clone `mem` before replacing its physical memory, to see that works
        let mem_cloned = mem.clone();

        // Use `mem2`'s physical memory for `mem`
        mem2.set_iommu_enabled(false);
        let pmem2 = mem2.physical_memory().unwrap();
        assert!(std::ptr::eq(pmem2, mem2.get_backend()));
        let mem = mem.with_replaced_backend(pmem2.clone());

        // The physical memory has been replaced, but `mem` still uses its old IOMMU, so the
        // mapping for everything past VIRT_START + PHYS_LEN does not yet exist.
        mem.iommu().expect_mapping_request(PHYS_START_2);
        verify_virt_mem_content(&mem, VIRT_START, PHYS_LEN * 2, 42);
        mem.iommu().verify_mapping_request(
            GuestAddress(VIRT_START.0 + PHYS_LEN as u64),
            PHYS_LEN,
            true,
        );

        // Verify `mem`'s clone still is the same (though it does use the same IOMMU)
        verify_virt_mem_content(&mem_cloned, VIRT_START, PHYS_LEN, 0);
        // See, it's the same IOMMU (i.e. it has a mapping PHYS_START_2):
        verify_hit(
            mem_cloned.iommu().iotlb.read().unwrap(),
            VIRT_START,
            PHYS_LEN * 2,
            Permissions::Read,
            [
                MappedRange {
                    base: PHYS_START_1,
                    length: PHYS_LEN,
                },
                MappedRange {
                    base: PHYS_START_2,
                    length: PHYS_LEN,
                },
            ],
        );
        // (But we cannot access that mapping because `mem_cloned`'s physical memory does not
        // contain that physical range.)
    }

    /// In `mem`'s dirty bitmap, verify that the given `clean` addresses are clean, and the `dirty`
    /// addresses are dirty.  Auto-clear the dirty addresses checked.
    ///
    /// Cannot import `GuestMemory` in this module, as that would interfere with `IoMemory` for
    /// methods that have the same name between the two.
    #[cfg(all(feature = "backend-bitmap", feature = "backend-mmap"))]
    fn verify_mem_bitmap<
        M: crate::GuestMemory<R = R>,
        R: GuestMemoryRegion<B = AtomicBitmap>,
        I: Iommu,
    >(
        mem: &IommuMemory<M, I>,
        clean: impl IntoIterator<Item = usize>,
        dirty: impl IntoIterator<Item = usize>,
    ) {
        let bitmap = mem.bitmap();
        for addr in clean {
            if bitmap.is_addr_set(addr) {
                panic!("Expected addr {addr:#x} to be clean, but is dirty");
            }
        }
        for addr in dirty {
            if !bitmap.is_addr_set(addr) {
                panic!("Expected addr {addr:#x} to be dirty, but is clean");
            }
            bitmap.reset_addr_range(addr, 1);
        }
    }

    #[cfg(all(feature = "backend-bitmap", feature = "backend-mmap"))]
    #[test]
    fn test_dirty_bitmap() {
        const PAGE_SIZE: usize = 4096;
        const PHYS_START: GuestAddress = GuestAddress(0x4000);
        const PHYS_LEN: usize = PAGE_SIZE * 2;
        const PHYS_PAGE_0: usize = PHYS_START.0 as usize;
        const PHYS_PAGE_1: usize = PHYS_START.0 as usize + PAGE_SIZE;
        const VIRT_START: GuestAddress = GuestAddress(0x2a000);
        const VIRT_PAGE_0: usize = VIRT_START.0 as usize;
        const VIRT_PAGE_1: usize = VIRT_START.0 as usize + PAGE_SIZE;

        let bitmap = AtomicBitmap::new(
            VIRT_START.0 as usize + PHYS_LEN,
            NonZeroUsize::new(PAGE_SIZE).unwrap(),
        );

        let mem = create_virt_memory(
            Some((VIRT_START, Permissions::ReadWrite)),
            0,
            [MappedRange {
                base: PHYS_START,
                length: PHYS_LEN,
            }],
            bitmap,
        );

        // Check bitmap is cleared before everything -- through the whole test, the physical ranges
        // should remain clean as the bitmap is only supposed to track IOVAs
        verify_mem_bitmap(
            &mem,
            [PHYS_PAGE_0, PHYS_PAGE_1, VIRT_PAGE_0, VIRT_PAGE_1],
            [],
        );

        // Just to be sure, check that PHYS_PAGE_0 and PHYS_PAGE_1 technically can be dirtied,
        // though, or testing them would not be really useful
        mem.bitmap().set_addr_range(PHYS_PAGE_0, 2 * PAGE_SIZE);
        verify_mem_bitmap(&mem, [VIRT_PAGE_0, VIRT_PAGE_1], [PHYS_PAGE_0, PHYS_PAGE_1]);

        // Just read from memory, should not dirty bitmap
        verify_virt_mem_content(&mem, VIRT_START, PHYS_LEN, 0);
        verify_mem_bitmap(
            &mem,
            [PHYS_PAGE_0, PHYS_PAGE_1, VIRT_PAGE_0, VIRT_PAGE_1],
            [],
        );

        // Verify that writing to a writeable slice causes dirtying, i.e. that the `VolatileSlice`
        // returned here correctly dirties the bitmap when written to
        let mut slices = mem
            .get_slices(VIRT_START, PHYS_LEN, Permissions::Write)
            .inspect_err(|err| panic!("Failed to access memory: {err}"))
            .unwrap();
        let slice = slices
            .next()
            .unwrap()
            .inspect_err(|err| panic!("Failed to access memory: {err}"))
            .unwrap();
        assert!(slices.next().is_none(), "Expected single slice");

        verify_mem_bitmap(
            &mem,
            [PHYS_PAGE_0, PHYS_PAGE_1, VIRT_PAGE_0, VIRT_PAGE_1],
            [],
        );

        slice
            .store(42, 0, Ordering::Relaxed)
            .inspect_err(|err| panic!("Writing to memory failed: {err}"))
            .unwrap();
        verify_mem_bitmap(&mem, [PHYS_PAGE_0, PHYS_PAGE_1, VIRT_PAGE_1], [VIRT_PAGE_0]);

        slice
            .store(23, PAGE_SIZE, Ordering::Relaxed)
            .inspect_err(|err| panic!("Writing to memory failed: {err}"))
            .unwrap();
        verify_mem_bitmap(&mem, [PHYS_PAGE_0, PHYS_PAGE_1, VIRT_PAGE_0], [VIRT_PAGE_1]);
    }
}
