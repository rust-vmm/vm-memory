//! Module containing abstracts for dealing with contiguous regions of guest memory

use crate::bitmap::{Bitmap, BS};
use crate::guest_memory::Error;
use crate::guest_memory::Result;
use crate::{
    Address, Bytes, FileOffset, GuestAddress, GuestMemory, GuestUsize, MemoryRegionAddress,
    VolatileSlice,
};
use std::sync::Arc;

/// Represents a continuous region of guest physical memory.
#[allow(clippy::len_without_is_empty)]
pub trait GuestMemoryRegion: Bytes<MemoryRegionAddress, E = Error> {
    /// Type used for dirty memory tracking.
    type B: Bitmap;

    /// Returns the size of the region.
    fn len(&self) -> GuestUsize;

    /// Returns the minimum (inclusive) address managed by the region.
    fn start_addr(&self) -> GuestAddress;

    /// Returns the maximum (inclusive) address managed by the region.
    fn last_addr(&self) -> GuestAddress {
        // unchecked_add is safe as the region bounds were checked when it was created.
        self.start_addr().unchecked_add(self.len() - 1)
    }

    /// Borrow the associated `Bitmap` object.
    fn bitmap(&self) -> BS<'_, Self::B>;

    /// Returns the given address if it is within this region.
    fn check_address(&self, addr: MemoryRegionAddress) -> Option<MemoryRegionAddress> {
        if self.address_in_range(addr) {
            Some(addr)
        } else {
            None
        }
    }

    /// Returns `true` if the given address is within this region.
    fn address_in_range(&self, addr: MemoryRegionAddress) -> bool {
        addr.raw_value() < self.len()
    }

    /// Returns the address plus the offset if it is in this region.
    fn checked_offset(
        &self,
        base: MemoryRegionAddress,
        offset: usize,
    ) -> Option<MemoryRegionAddress> {
        base.checked_add(offset as u64)
            .and_then(|addr| self.check_address(addr))
    }

    /// Tries to convert an absolute address to a relative address within this region.
    ///
    /// Returns `None` if `addr` is out of the bounds of this region.
    fn to_region_addr(&self, addr: GuestAddress) -> Option<MemoryRegionAddress> {
        addr.checked_offset_from(self.start_addr())
            .and_then(|offset| self.check_address(MemoryRegionAddress(offset)))
    }

    /// Returns the host virtual address corresponding to the region address.
    ///
    /// Some [`GuestMemory`](trait.GuestMemory.html) implementations, like `GuestMemoryMmap`,
    /// have the capability to mmap guest address range into host virtual address space for
    /// direct access, so the corresponding host virtual address may be passed to other subsystems.
    ///
    /// # Note
    /// The underlying guest memory is not protected from memory aliasing, which breaks the
    /// Rust memory safety model. It's the caller's responsibility to ensure that there's no
    /// concurrent accesses to the underlying guest memory.
    fn get_host_address(&self, _addr: MemoryRegionAddress) -> Result<*mut u8> {
        Err(Error::HostAddressNotAvailable)
    }

    /// Returns information regarding the file and offset backing this memory region.
    fn file_offset(&self) -> Option<&FileOffset> {
        None
    }

    /// Returns a [`VolatileSlice`](struct.VolatileSlice.html) of `count` bytes starting at
    /// `offset`.
    #[allow(unused_variables)]
    fn get_slice(
        &self,
        offset: MemoryRegionAddress,
        count: usize,
    ) -> Result<VolatileSlice<BS<Self::B>>> {
        Err(Error::HostAddressNotAvailable)
    }

    /// Gets a slice of memory for the entire region that supports volatile access.
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// # use vm_memory::{GuestAddress, MmapRegion, GuestRegionMmap, GuestMemoryRegion};
    /// # use vm_memory::volatile_memory::{VolatileMemory, VolatileSlice, VolatileRef};
    /// #
    /// let region = GuestRegionMmap::<()>::from_range(GuestAddress(0x0), 0x400, None)
    ///     .expect("Could not create guest memory");
    /// let slice = region
    ///     .as_volatile_slice()
    ///     .expect("Could not get volatile slice");
    ///
    /// let v = 42u32;
    /// let r = slice
    ///     .get_ref::<u32>(0x200)
    ///     .expect("Could not get reference");
    /// r.store(v);
    /// assert_eq!(r.load(), v);
    /// # }
    /// ```
    fn as_volatile_slice(&self) -> Result<VolatileSlice<BS<Self::B>>> {
        self.get_slice(MemoryRegionAddress(0), self.len() as usize)
    }

    /// Show if the region is based on the `HugeTLBFS`.
    /// Returns Some(true) if the region is backed by hugetlbfs.
    /// None represents that no information is available.
    ///
    /// # Examples (uses the `backend-mmap` feature)
    ///
    /// ```
    /// # #[cfg(feature = "backend-mmap")]
    /// # {
    /// #   use vm_memory::{GuestAddress, GuestMemory, GuestMemoryMmap, GuestRegionMmap};
    /// let addr = GuestAddress(0x1000);
    /// let mem = GuestMemoryMmap::<()>::from_ranges(&[(addr, 0x1000)]).unwrap();
    /// let r = mem.find_region(addr).unwrap();
    /// assert_eq!(r.is_hugetlbfs(), None);
    /// # }
    /// ```
    #[cfg(target_os = "linux")]
    fn is_hugetlbfs(&self) -> Option<bool> {
        None
    }
}

/// Errors that can occur when dealing with [`GuestRegion`]s, or collections thereof
#[derive(Debug, thiserror::Error)]
pub enum GuestRegionError {
    /// Adding the guest base address to the length of the underlying mapping resulted
    /// in an overflow.
    #[error("Adding the guest base address to the length of the underlying mapping resulted in an overflow")]
    #[cfg(feature = "backend-mmap")]
    InvalidGuestRegion,
    /// Error creating a `MmapRegion` object.
    #[error("{0}")]
    #[cfg(feature = "backend-mmap")]
    MmapRegion(crate::mmap::MmapRegionError),
    /// No memory region found.
    #[error("No memory region found")]
    NoMemoryRegion,
    /// Some of the memory regions intersect with each other.
    #[error("Some of the memory regions intersect with each other")]
    MemoryRegionOverlap,
    /// The provided memory regions haven't been sorted.
    #[error("The provided memory regions haven't been sorted")]
    UnsortedMemoryRegions,
}

/// [`GuestMemory`](trait.GuestMemory.html) implementation based on a homogeneous collection
/// of [`GuestMemoryRegion`] implementations.
///
/// Represents a sorted set of non-overlapping physical guest memory regions.
#[derive(Debug)]
pub struct GuestRegionCollection<R> {
    regions: Vec<Arc<R>>,
}

impl<R> Default for GuestRegionCollection<R> {
    fn default() -> Self {
        Self {
            regions: Vec::new(),
        }
    }
}

impl<R> Clone for GuestRegionCollection<R> {
    fn clone(&self) -> Self {
        GuestRegionCollection {
            regions: self.regions.iter().map(Arc::clone).collect(),
        }
    }
}

impl<R: GuestMemoryRegion> GuestRegionCollection<R> {
    /// Creates an empty `GuestMemoryMmap` instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a new [`GuestRegionCollection`] from a vector of regions.
    ///
    /// # Arguments
    ///
    /// * `regions` - The vector of regions.
    ///               The regions shouldn't overlap, and they should be sorted
    ///               by the starting address.
    pub fn from_regions(mut regions: Vec<R>) -> std::result::Result<Self, GuestRegionError> {
        Self::from_arc_regions(regions.drain(..).map(Arc::new).collect())
    }

    /// Creates a new [`GuestRegionCollection`] from a vector of Arc regions.
    ///
    /// Similar to the constructor `from_regions()` as it returns a
    /// [`GuestRegionCollection`]. The need for this constructor is to provide a way for
    /// consumer of this API to create a new [`GuestRegionCollection`] based on existing
    /// regions coming from an existing [`GuestRegionCollection`] instance.
    ///
    /// # Arguments
    ///
    /// * `regions` - The vector of `Arc` regions.
    ///               The regions shouldn't overlap and they should be sorted
    ///               by the starting address.
    pub fn from_arc_regions(regions: Vec<Arc<R>>) -> std::result::Result<Self, GuestRegionError> {
        if regions.is_empty() {
            return Err(GuestRegionError::NoMemoryRegion);
        }

        for window in regions.windows(2) {
            let prev = &window[0];
            let next = &window[1];

            if prev.start_addr() > next.start_addr() {
                return Err(GuestRegionError::UnsortedMemoryRegions);
            }

            if prev.last_addr() >= next.start_addr() {
                return Err(GuestRegionError::MemoryRegionOverlap);
            }
        }

        Ok(Self { regions })
    }

    /// Insert a region into the `GuestMemoryMmap` object and return a new `GuestMemoryMmap`.
    ///
    /// # Arguments
    /// * `region`: the memory region to insert into the guest memory object.
    pub fn insert_region(
        &self,
        region: Arc<R>,
    ) -> std::result::Result<GuestRegionCollection<R>, GuestRegionError> {
        let mut regions = self.regions.clone();
        regions.push(region);
        regions.sort_by_key(|x| x.start_addr());

        Self::from_arc_regions(regions)
    }

    /// Remove a region from the [`GuestRegionCollection`] object and return a new `GuestRegionCollection`
    /// on success, together with the removed region.
    ///
    /// # Arguments
    /// * `base`: base address of the region to be removed
    /// * `size`: size of the region to be removed
    pub fn remove_region(
        &self,
        base: GuestAddress,
        size: GuestUsize,
    ) -> std::result::Result<(GuestRegionCollection<R>, Arc<R>), GuestRegionError> {
        if let Ok(region_index) = self.regions.binary_search_by_key(&base, |x| x.start_addr()) {
            if self.regions.get(region_index).unwrap().len() == size {
                let mut regions = self.regions.clone();
                let region = regions.remove(region_index);
                return Ok((Self { regions }, region));
            }
        }

        Err(GuestRegionError::NoMemoryRegion)
    }
}

impl<R: GuestMemoryRegion> GuestMemory for GuestRegionCollection<R> {
    type R = R;

    fn num_regions(&self) -> usize {
        self.regions.len()
    }

    fn find_region(&self, addr: GuestAddress) -> Option<&R> {
        let index = match self.regions.binary_search_by_key(&addr, |x| x.start_addr()) {
            Ok(x) => Some(x),
            // Within the closest region with starting address < addr
            Err(x) if (x > 0 && addr <= self.regions[x - 1].last_addr()) => Some(x - 1),
            _ => None,
        };
        index.map(|x| self.regions[x].as_ref())
    }

    fn iter(&self) -> impl Iterator<Item = &Self::R> {
        self.regions.iter().map(AsRef::as_ref)
    }
}
