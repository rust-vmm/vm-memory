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

use crate::{GuestAddress, Permissions};
use rangemap::RangeMap;
use std::cmp;
use std::fmt::Debug;
use std::num::Wrapping;
use std::ops::{Deref, Range};

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
