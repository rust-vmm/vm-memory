// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! The default implementation for the [`GuestMemory`](trait.GuestMemory.html) trait.
//!
//! This implementation is mmap-ing the memory of the guest into the current process.

use std::borrow::Borrow;
use std::error;
use std::fmt;
use std::io::{Read, Write};
use std::ops::Deref;
use std::result;
use std::sync::Arc;

use crate::address::Address;
use crate::guest_memory::{
    self, FileOffset, GuestAddress, GuestMemory, GuestMemoryOptions, GuestMemoryRegion, GuestUsize, MemoryRegionAddress,
};
use crate::volatile_memory::{VolatileMemory, VolatileSlice};
use crate::Bytes;

#[cfg(unix)]
pub use crate::mmap_unix::{Error as MmapRegionError, MmapRegion};

#[cfg(windows)]
pub use crate::mmap_windows::MmapRegion;
#[cfg(windows)]
pub use std::io::Error as MmapRegionError;

/// Trait implemented by the underlying `MmapRegion`.
pub(crate) trait AsSlice {
    /// Returns a slice corresponding to the data in the underlying `MmapRegion`.
    ///
    /// # Safety
    ///
    /// This is unsafe because of possible aliasing.
    unsafe fn as_slice(&self) -> &[u8];

    /// Returns a mutable slice corresponding to the data in the underlying `MmapRegion`.
    ///
    /// # Safety
    ///
    /// This is unsafe because of possible aliasing.
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut_slice(&self) -> &mut [u8];
}

/// Errors that can occur when creating a memory map.
#[derive(Debug)]
pub enum Error {
    /// Adding the guest base address to the length of the underlying mapping resulted
    /// in an overflow.
    InvalidGuestRegion,
    /// Error creating a `MmapRegion` object.
    MmapRegion(MmapRegionError),
    /// No memory region found.
    NoMemoryRegion,
    /// Some of the memory regions intersect with each other.
    MemoryRegionOverlap,
    /// The provided memory regions haven't been sorted.
    UnsortedMemoryRegions,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::InvalidGuestRegion => write!(
                f,
                "Adding the guest base address to the length of the underlying mapping \
                 resulted in an overflow"
            ),
            Error::MmapRegion(e) => write!(f, "{}", e),
            Error::NoMemoryRegion => write!(f, "No memory region found"),
            Error::MemoryRegionOverlap => {
                write!(f, "Some of the memory regions intersect with each other")
            }
            Error::UnsortedMemoryRegions => {
                write!(f, "The provided memory regions haven't been sorted")
            }
        }
    }
}

impl error::Error for Error {}

// TODO: use this for Windows as well after we redefine the Error type there.
#[cfg(unix)]
/// Checks if a mapping of `size` bytes fits at the provided `file_offset`.
///
/// For a borrowed `FileOffset` and size, this function checks whether the mapping does not
/// extend past EOF, and that adding the size to the file offset does not lead to overflow.
pub fn check_file_offset(
    file_offset: &FileOffset,
    size: usize,
) -> result::Result<(), MmapRegionError> {
    let file = file_offset.file();
    let start = file_offset.start();

    if let Some(end) = start.checked_add(size as u64) {
        if let Ok(metadata) = file.metadata() {
            if metadata.len() < end {
                return Err(MmapRegionError::MappingPastEof);
            }
        }
    } else {
        return Err(MmapRegionError::InvalidOffsetLength);
    }

    Ok(())
}

/// [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) implementation that mmaps the guest's
/// memory region in the current process.
///
/// Represents a continuous region of the guest's physical memory that is backed by a mapping
/// in the virtual address space of the calling process.
#[derive(Debug)]
pub struct GuestRegionMmap {
    mapping: MmapRegion,
    guest_base: GuestAddress,
}

impl GuestRegionMmap {
    /// Create a new memory-mapped memory region for the guest's physical memory.
    pub fn new(mapping: MmapRegion, guest_base: GuestAddress) -> result::Result<Self, Error> {
        if guest_base.0.checked_add(mapping.len() as u64).is_none() {
            return Err(Error::InvalidGuestRegion);
        }
        Ok(GuestRegionMmap {
            mapping,
            guest_base,
        })
    }
}

impl Deref for GuestRegionMmap {
    type Target = MmapRegion;

    fn deref(&self) -> &MmapRegion {
        &self.mapping
    }
}

impl Bytes<MemoryRegionAddress> for GuestRegionMmap {
    type E = guest_memory::Error;

    /// # Examples
    /// * Write a slice at guest address 0x1200.
    ///
    /// ```
    /// # use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};
    /// # let start_addr = GuestAddress(0x1000);
    /// # let mut gm = GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)]).unwrap();
    ///   let res = gm.write(&[1,2,3,4,5], GuestAddress(0x1200)).unwrap();
    ///   assert_eq!(5, res);
    /// ```
    fn write(&self, buf: &[u8], addr: MemoryRegionAddress) -> guest_memory::Result<usize> {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .write(buf, maddr)
            .map_err(Into::into)
    }

    /// # Examples
    /// * Read a slice of length 16 at guestaddress 0x1200.
    ///
    /// ```
    /// # use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};
    /// # let start_addr = GuestAddress(0x1000);
    /// # let mut gm = GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)]).unwrap();
    ///   let buf = &mut [0u8; 16];
    ///   let res = gm.read(buf, GuestAddress(0x1200)).unwrap();
    ///   assert_eq!(16, res);
    /// ```
    fn read(&self, buf: &mut [u8], addr: MemoryRegionAddress) -> guest_memory::Result<usize> {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .read(buf, maddr)
            .map_err(Into::into)
    }

    fn write_slice(&self, buf: &[u8], addr: MemoryRegionAddress) -> guest_memory::Result<()> {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .write_slice(buf, maddr)
            .map_err(Into::into)
    }

    fn read_slice(&self, buf: &mut [u8], addr: MemoryRegionAddress) -> guest_memory::Result<()> {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .read_slice(buf, maddr)
            .map_err(Into::into)
    }

    /// # Examples
    ///
    /// * Read bytes from /dev/urandom
    ///
    /// ```
    /// # use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # let start_addr = GuestAddress(0x1000);
    /// # let gm = GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)]).unwrap();
    ///   let mut file = if cfg!(unix) {
    ///       File::open(Path::new("/dev/urandom")).unwrap()
    ///   } else {
    ///       File::open(Path::new("c:\\Windows\\system32\\ntoskrnl.exe")).unwrap()
    ///   };
    ///   let addr = GuestAddress(0x1010);
    ///   gm.read_from(addr, &mut file, 128).unwrap();
    ///   let read_addr = addr.checked_add(8).unwrap();
    ///   let _: u32 = gm.read_obj(read_addr).unwrap();
    /// ```
    fn read_from<F>(
        &self,
        addr: MemoryRegionAddress,
        src: &mut F,
        count: usize,
    ) -> guest_memory::Result<usize>
    where
        F: Read,
    {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .read_from::<F>(maddr, src, count)
            .map_err(Into::into)
    }

    /// # Examples
    ///
    /// * Read bytes from /dev/urandom
    ///
    /// ```
    /// # use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # let start_addr = GuestAddress(0x1000);
    /// # let gm = GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)]).unwrap();
    ///   let mut file = if cfg!(unix) {
    ///       File::open(Path::new("/dev/urandom")).unwrap()
    ///   } else {
    ///       File::open(Path::new("c:\\Windows\\system32\\ntoskrnl.exe")).unwrap()
    ///   };
    ///   let addr = GuestAddress(0x1010);
    ///   gm.read_exact_from(addr, &mut file, 128).unwrap();
    ///   let read_addr = addr.checked_add(8).unwrap();
    ///   let _: u32 = gm.read_obj(read_addr).unwrap();
    /// ```
    fn read_exact_from<F>(
        &self,
        addr: MemoryRegionAddress,
        src: &mut F,
        count: usize,
    ) -> guest_memory::Result<()>
    where
        F: Read,
    {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .read_exact_from::<F>(maddr, src, count)
            .map_err(Into::into)
    }

    /// Writes data from the region to a writable object.
    ///
    /// # Examples
    ///
    /// * Write 128 bytes to a temp file
    ///
    /// ```
    /// # extern crate vmm_sys_util;
    /// # use vmm_sys_util::tempfile::TempFile;
    /// # use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::OpenOptions;
    /// # let start_addr = GuestAddress(0x1000);
    /// # let gm = GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)]).unwrap();
    ///   let mut file = TempFile::new().unwrap().into_file();
    ///   let mut mem = [0u8; 1024];
    ///   gm.write_to(start_addr, &mut file, 128).unwrap();
    /// ```
    fn write_to<F>(
        &self,
        addr: MemoryRegionAddress,
        dst: &mut F,
        count: usize,
    ) -> guest_memory::Result<usize>
    where
        F: Write,
    {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .write_to::<F>(maddr, dst, count)
            .map_err(Into::into)
    }

    /// Writes data from the region to a writable object.
    ///
    /// # Examples
    ///
    /// * Write 128 bytes to a temp file
    ///
    /// ```
    /// # extern crate vmm_sys_util;
    /// # use vmm_sys_util::tempfile::TempFile;
    /// # use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::OpenOptions;
    /// # let start_addr = GuestAddress(0x1000);
    /// # let gm = GuestMemoryMmap::from_ranges(&vec![(start_addr, 0x400)]).unwrap();
    ///   let mut file = TempFile::new().unwrap().into_file();
    ///   let mut mem = [0u8; 1024];
    ///   gm.write_all_to(start_addr, &mut file, 128).unwrap();
    /// ```
    fn write_all_to<F>(
        &self,
        addr: MemoryRegionAddress,
        dst: &mut F,
        count: usize,
    ) -> guest_memory::Result<()>
    where
        F: Write,
    {
        let maddr = addr.raw_value() as usize;
        self.as_volatile_slice()
            .unwrap()
            .write_all_to::<F>(maddr, dst, count)
            .map_err(Into::into)
    }
}

impl GuestMemoryRegion for GuestRegionMmap {
    fn len(&self) -> GuestUsize {
        self.mapping.len() as GuestUsize
    }

    fn start_addr(&self) -> GuestAddress {
        self.guest_base
    }

    fn file_offset(&self) -> Option<&FileOffset> {
        self.mapping.file_offset()
    }

    unsafe fn as_slice(&self) -> Option<&[u8]> {
        Some(self.mapping.as_slice())
    }

    unsafe fn as_mut_slice(&self) -> Option<&mut [u8]> {
        Some(self.mapping.as_mut_slice())
    }

    fn get_host_address(&self, addr: MemoryRegionAddress) -> guest_memory::Result<*mut u8> {
        // Not sure why wrapping_offset is not unsafe.  Anyway this
        // is safe because we've just range-checked addr using check_address.
        self.check_address(addr)
            .ok_or(guest_memory::Error::InvalidBackendAddress)
            .map(|addr| self.as_ptr().wrapping_offset(addr.raw_value() as isize))
    }

    fn get_slice(
        &self,
        offset: MemoryRegionAddress,
        count: usize,
    ) -> guest_memory::Result<VolatileSlice> {
        let slice = self.mapping.get_slice(offset.raw_value() as usize, count)?;
        Ok(slice)
    }
}

/// [`GuestMemory`](trait.GuestMemory.html) implementation that mmaps the guest's memory
/// in the current process.
///
/// Represents the entire physical memory of the guest by tracking all its memory regions.
/// Each region is an instance of `GuestRegionMmap`, being backed by a mapping in the
/// virtual address space of the calling process.
#[derive(Clone, Debug, Default)]
pub struct GuestMemoryMmap {
    options: GuestMemoryOptions,
    regions: Vec<Arc<GuestRegionMmap>>,
}

impl GuestMemoryMmap {
    /// Creates an empty `GuestMemoryMmap` instance.
    pub fn new() -> Self {
        Self::default()
    }

    /// Creates a container and allocates anonymous memory for guest memory regions.
    ///
    /// Valid memory regions are specified as a slice of (Address, Size) tuples sorted by Address.
    pub fn from_ranges(ranges: &[(GuestAddress, usize)]) -> result::Result<Self, Error> {
        Self::from_ranges_with_files(ranges.iter().map(|r| (r.0, r.1, None)))
    }

    /// Creates a container and allocates anonymous memory for guest memory regions.
    ///
    /// Valid memory regions are specified as a sequence of (Address, Size, Option<FileOffset>)
    /// tuples sorted by Address.
    pub fn from_ranges_with_files<A, T>(ranges: T) -> result::Result<Self, Error>
    where
        A: Borrow<(GuestAddress, usize, Option<FileOffset>)>,
        T: IntoIterator<Item = A>,
    {
        let options = GuestMemoryOptions {huge_page : false, transparent_huge_page : false};
        Self::from_regions(
            ranges
                .into_iter()
                .map(|x| {
                    let guest_base = x.borrow().0;
                    let size = x.borrow().1;

                    if let Some(ref f_off) = x.borrow().2 {
                        MmapRegion::from_file(f_off.clone(), size, options)
                    } else {
                        MmapRegion::new(size, options)
                    }
                    .map_err(Error::MmapRegion)
                    .and_then(|r| GuestRegionMmap::new(r, guest_base))
                })
                .collect::<result::Result<Vec<_>, Error>>()?,
        )
    }

    /// Creates a new `GuestMemoryMmap` from a vector of regions.
    ///
    /// # Arguments
    ///
    /// * `regions` - The vector of regions.
    ///               The regions shouldn't overlap and they should be sorted
    ///               by the starting address.
    pub fn from_regions(mut regions: Vec<GuestRegionMmap>) -> result::Result<Self, Error> {
        Self::from_arc_regions(regions.drain(..).map(Arc::new).collect())
    }

    /// Creates a new `GuestMemoryMmap` from a vector of Arc regions.
    ///
    /// Similar to the constructor from_regions() as it returns a
    /// GuestMemoryMmap. The need for this constructor is to provide a way for
    /// consumer of this API to create a new GuestMemoryMmap based on existing
    /// regions coming from an existing GuestMemoryMmap instance.
    ///
    /// # Arguments
    ///
    /// * `regions` - The vector of Arc regions.
    ///               The regions shouldn't overlap and they should be sorted
    ///               by the starting address.
    pub fn from_arc_regions(regions: Vec<Arc<GuestRegionMmap>>) -> result::Result<Self, Error> {
        if regions.is_empty() {
            return Err(Error::NoMemoryRegion);
        }

        for window in regions.windows(2) {
            let prev = &window[0];
            let next = &window[1];

            if prev.start_addr() > next.start_addr() {
                return Err(Error::UnsortedMemoryRegions);
            }

            if prev.last_addr() >= next.start_addr() {
                return Err(Error::MemoryRegionOverlap);
            }
        }

        Ok(Self { regions, options: GuestMemoryOptions {huge_page : false, transparent_huge_page : false} })
    }

    /// Insert a region into the `GuestMemoryMmap` object and return a new `GuestMemoryMmap`.
    ///
    /// # Arguments
    /// * `region`: the memory region to insert into the guest memory object.
    pub fn insert_region(
        &self,
        region: Arc<GuestRegionMmap>,
    ) -> result::Result<GuestMemoryMmap, Error> {
        let mut regions = self.regions.clone();
        regions.push(region);
        regions.sort_by_key(|x| x.start_addr());

        Self::from_arc_regions(regions)
    }

    /// Remove a region into the `GuestMemoryMmap` object and return a new `GuestMemoryMmap`
    /// on success, together with the removed region.
    ///
    /// # Arguments
    /// * `base`: base address of the region to be removed
    /// * `size`: size of the region to be removed
    pub fn remove_region(
        &self,
        base: GuestAddress,
        size: GuestUsize,
    ) -> result::Result<(GuestMemoryMmap, Arc<GuestRegionMmap>), Error> {
        if let Ok(region_index) = self.regions.binary_search_by_key(&base, |x| x.start_addr()) {
            if self.regions.get(region_index).unwrap().size() as GuestUsize == size {
                let mut regions = self.regions.clone();
                let region = regions.remove(region_index);
                return Ok((Self { regions, options: GuestMemoryOptions {huge_page : false, transparent_huge_page : false} }, region));
            }
        }

        Err(Error::InvalidGuestRegion)
    }
}

impl GuestMemory for GuestMemoryMmap {
    type R = GuestRegionMmap;

    fn num_regions(&self) -> usize {
        self.regions.len()
    }

    fn find_region(&self, addr: GuestAddress) -> Option<&GuestRegionMmap> {
        let index = match self.regions.binary_search_by_key(&addr, |x| x.start_addr()) {
            Ok(x) => Some(x),
            // Within the closest region with starting address < addr
            Err(x) if (x > 0 && addr <= self.regions[x - 1].last_addr()) => Some(x - 1),
            _ => None,
        };
        index.map(|x| self.regions[x].as_ref())
    }

    fn with_regions<F, E>(&self, cb: F) -> result::Result<(), E>
    where
        F: Fn(usize, &Self::R) -> result::Result<(), E>,
    {
        for (index, region) in self.regions.iter().enumerate() {
            cb(index, region)?;
        }
        Ok(())
    }

    fn with_regions_mut<F, E>(&self, mut cb: F) -> result::Result<(), E>
    where
        F: FnMut(usize, &Self::R) -> result::Result<(), E>,
    {
        for (index, region) in self.regions.iter().enumerate() {
            cb(index, region)?;
        }
        Ok(())
    }

    fn map_and_fold<F, G, T>(&self, init: T, mapf: F, foldf: G) -> T
    where
        F: Fn((usize, &Self::R)) -> T,
        G: Fn(T, T) -> T,
    {
        self.regions
            .iter()
            .enumerate()
            .map(|(idx, region)| mapf((idx, region.as_ref())))
            .fold(init, foldf)
    }
}

#[cfg(test)]
mod tests {
    extern crate vmm_sys_util;

    use super::*;
    use crate::GuestAddressSpace;

    use std::fs::File;
    use std::mem;
    use std::path::Path;
    use vmm_sys_util::tempfile::TempFile;

    use Bytes;

    #[test]
    fn basic_map() {
        let m = MmapRegion::new(1024).unwrap();
        assert_eq!(1024, m.len());
    }

    fn check_guest_memory_mmap(
        maybe_guest_mem: Result<GuestMemoryMmap, Error>,
        expected_regions_summary: &[(GuestAddress, usize)],
    ) {
        assert!(maybe_guest_mem.is_ok());

        let guest_mem = maybe_guest_mem.unwrap();
        assert_eq!(guest_mem.num_regions(), expected_regions_summary.len());
        let maybe_last_mem_reg = expected_regions_summary.last();
        if let Some((region_addr, region_size)) = maybe_last_mem_reg {
            let mut last_addr = region_addr.unchecked_add(*region_size as u64);
            if last_addr.raw_value() != 0 {
                last_addr = last_addr.unchecked_sub(1);
            }
            assert_eq!(guest_mem.last_addr(), last_addr);
        }
        for ((region_addr, region_size), mmap) in expected_regions_summary
            .iter()
            .zip(guest_mem.regions.iter())
        {
            assert_eq!(region_addr, &mmap.guest_base);
            assert_eq!(region_size, &mmap.mapping.size());

            assert!(guest_mem.find_region(*region_addr).is_some());
        }
    }

    fn new_guest_memory_mmap(
        regions_summary: &[(GuestAddress, usize)],
    ) -> Result<GuestMemoryMmap, Error> {
        GuestMemoryMmap::from_ranges(regions_summary)
    }

    fn new_guest_memory_mmap_from_regions(
        regions_summary: &[(GuestAddress, usize)],
    ) -> Result<GuestMemoryMmap, Error> {
        GuestMemoryMmap::from_regions(
            regions_summary
                .iter()
                .map(|(region_addr, region_size)| {
                    GuestRegionMmap::new(MmapRegion::new(*region_size).unwrap(), *region_addr)
                        .unwrap()
                })
                .collect(),
        )
    }

    fn new_guest_memory_mmap_from_arc_regions(
        regions_summary: &[(GuestAddress, usize)],
    ) -> Result<GuestMemoryMmap, Error> {
        GuestMemoryMmap::from_arc_regions(
            regions_summary
                .iter()
                .map(|(region_addr, region_size)| {
                    Arc::new(
                        GuestRegionMmap::new(MmapRegion::new(*region_size).unwrap(), *region_addr)
                            .unwrap(),
                    )
                })
                .collect(),
        )
    }

    fn new_guest_memory_mmap_with_files(
        regions_summary: &[(GuestAddress, usize)],
    ) -> Result<GuestMemoryMmap, Error> {
        let regions: Vec<(GuestAddress, usize, Option<FileOffset>)> = regions_summary
            .iter()
            .map(|(region_addr, region_size)| {
                let f = TempFile::new().unwrap().into_file();
                f.set_len(*region_size as u64).unwrap();

                (*region_addr, *region_size, Some(FileOffset::new(f, 0)))
            })
            .collect();

        GuestMemoryMmap::from_ranges_with_files(&regions)
    }

    #[test]
    fn test_no_memory_region() {
        let regions_summary = [];

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap(&regions_summary).err().unwrap()
            ),
            format!("{:?}", Error::NoMemoryRegion)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_with_files(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::NoMemoryRegion)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_from_regions(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::NoMemoryRegion)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_from_arc_regions(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::NoMemoryRegion)
        );
    }

    #[test]
    fn test_overlapping_memory_regions() {
        let regions_summary = [
            (GuestAddress(0), 100 as usize),
            (GuestAddress(99), 100 as usize),
        ];

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap(&regions_summary).err().unwrap()
            ),
            format!("{:?}", Error::MemoryRegionOverlap)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_with_files(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::MemoryRegionOverlap)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_from_regions(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::MemoryRegionOverlap)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_from_arc_regions(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::MemoryRegionOverlap)
        );
    }

    #[test]
    fn test_unsorted_memory_regions() {
        let regions_summary = [
            (GuestAddress(100), 100 as usize),
            (GuestAddress(0), 100 as usize),
        ];

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap(&regions_summary).err().unwrap()
            ),
            format!("{:?}", Error::UnsortedMemoryRegions)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_with_files(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::UnsortedMemoryRegions)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_from_regions(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::UnsortedMemoryRegions)
        );

        assert_eq!(
            format!(
                "{:?}",
                new_guest_memory_mmap_from_arc_regions(&regions_summary)
                    .err()
                    .unwrap()
            ),
            format!("{:?}", Error::UnsortedMemoryRegions)
        );
    }

    #[test]
    fn test_valid_memory_regions() {
        let regions_summary = [
            (GuestAddress(0), 100 as usize),
            (GuestAddress(100), 100 as usize),
        ];

        let guest_mem = GuestMemoryMmap::new();
        assert_eq!(guest_mem.regions.len(), 0);

        check_guest_memory_mmap(new_guest_memory_mmap(&regions_summary), &regions_summary);

        check_guest_memory_mmap(
            new_guest_memory_mmap_with_files(&regions_summary),
            &regions_summary,
        );

        check_guest_memory_mmap(
            new_guest_memory_mmap_from_regions(&regions_summary),
            &regions_summary,
        );

        check_guest_memory_mmap(
            new_guest_memory_mmap_from_arc_regions(&regions_summary),
            &regions_summary,
        );
    }

    #[test]
    fn slice_addr() {
        let m = MmapRegion::new(5).unwrap();
        let s = m.get_slice(2, 3).unwrap();
        assert_eq!(s.as_ptr(), unsafe { m.as_ptr().offset(2) });
    }

    #[test]
    fn mapped_file_read() {
        let mut f = TempFile::new().unwrap().into_file();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert!(f.write_all(sample_buf).is_ok());

        let mem_map = MmapRegion::from_file(FileOffset::new(f, 0), sample_buf.len()).unwrap();
        let buf = &mut [0u8; 16];
        assert_eq!(
            mem_map.as_volatile_slice().read(buf, 0).unwrap(),
            sample_buf.len()
        );
        assert_eq!(buf[0..sample_buf.len()], sample_buf[..]);
    }

    #[test]
    fn test_address_in_range() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x400).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x400).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        let guest_mem =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x400), (start_addr2, 0x400)]).unwrap();
        let guest_mem_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ])
        .unwrap();

        let guest_mem_list = vec![guest_mem, guest_mem_backed_by_file];
        for guest_mem in guest_mem_list.iter() {
            assert!(guest_mem.address_in_range(GuestAddress(0x200)));
            assert!(!guest_mem.address_in_range(GuestAddress(0x600)));
            assert!(guest_mem.address_in_range(GuestAddress(0xa00)));
            assert!(!guest_mem.address_in_range(GuestAddress(0xc00)));
        }
    }

    #[test]
    fn test_check_address() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x400).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x400).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        let guest_mem =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x400), (start_addr2, 0x400)]).unwrap();
        let guest_mem_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ])
        .unwrap();

        let guest_mem_list = vec![guest_mem, guest_mem_backed_by_file];
        for guest_mem in guest_mem_list.iter() {
            assert_eq!(
                guest_mem.check_address(GuestAddress(0x200)),
                Some(GuestAddress(0x200))
            );
            assert_eq!(guest_mem.check_address(GuestAddress(0x600)), None);
            assert_eq!(
                guest_mem.check_address(GuestAddress(0xa00)),
                Some(GuestAddress(0xa00))
            );
            assert_eq!(guest_mem.check_address(GuestAddress(0xc00)), None);
        }
    }

    #[test]
    fn test_to_region_addr() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x400).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x400).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        let guest_mem =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x400), (start_addr2, 0x400)]).unwrap();
        let guest_mem_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ])
        .unwrap();

        let guest_mem_list = vec![guest_mem, guest_mem_backed_by_file];
        for guest_mem in guest_mem_list.iter() {
            assert!(guest_mem.to_region_addr(GuestAddress(0x600)).is_none());
            let (r0, addr0) = guest_mem.to_region_addr(GuestAddress(0x800)).unwrap();
            let (r1, addr1) = guest_mem.to_region_addr(GuestAddress(0xa00)).unwrap();
            assert!(r0.as_ptr() == r1.as_ptr());
            assert_eq!(addr0, MemoryRegionAddress(0));
            assert_eq!(addr1, MemoryRegionAddress(0x200));
        }
    }

    #[test]
    fn test_get_host_address() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x400).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x400).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        let guest_mem =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x400), (start_addr2, 0x400)]).unwrap();
        let guest_mem_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ])
        .unwrap();

        let guest_mem_list = vec![guest_mem, guest_mem_backed_by_file];
        for guest_mem in guest_mem_list.iter() {
            assert!(guest_mem.get_host_address(GuestAddress(0x600)).is_err());
            let ptr0 = guest_mem.get_host_address(GuestAddress(0x800)).unwrap();
            let ptr1 = guest_mem.get_host_address(GuestAddress(0xa00)).unwrap();
            assert_eq!(
                ptr0,
                guest_mem.find_region(GuestAddress(0x800)).unwrap().as_ptr()
            );
            assert_eq!(unsafe { ptr0.offset(0x200) }, ptr1);
        }
    }

    #[test]
    fn test_deref() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let start_addr = GuestAddress(0x0);
        let guest_mem = GuestMemoryMmap::from_ranges(&[(start_addr, 0x400)]).unwrap();
        let guest_mem_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[(
            start_addr,
            0x400,
            Some(FileOffset::new(f, 0)),
        )])
        .unwrap();

        let guest_mem_list = vec![guest_mem, guest_mem_backed_by_file];
        for guest_mem in guest_mem_list.iter() {
            let sample_buf = &[1, 2, 3, 4, 5];

            assert_eq!(guest_mem.write(sample_buf, start_addr).unwrap(), 5);
            let slice = guest_mem
                .find_region(GuestAddress(0))
                .unwrap()
                .as_volatile_slice()
                .unwrap();

            let buf = &mut [0, 0, 0, 0, 0];
            assert_eq!(slice.read(buf, 0).unwrap(), 5);
            assert_eq!(buf, sample_buf);
        }
    }

    #[test]
    fn test_read_u64() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x1000).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x1000).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        let bad_addr = GuestAddress(0x2001);
        let bad_addr2 = GuestAddress(0x1ffc);
        let max_addr = GuestAddress(0x2000);

        let gm =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x1000), (start_addr2, 0x1000)]).unwrap();
        let gm_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[
            (start_addr1, 0x1000, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x1000, Some(FileOffset::new(f2, 0))),
        ])
        .unwrap();

        let gm_list = vec![gm, gm_backed_by_file];
        for gm in gm_list.iter() {
            let val1: u64 = 0xaa55_aa55_aa55_aa55;
            let val2: u64 = 0x55aa_55aa_55aa_55aa;
            assert_eq!(
                format!("{:?}", gm.write_obj(val1, bad_addr).err().unwrap()),
                format!("InvalidGuestAddress({:?})", bad_addr,)
            );
            assert_eq!(
                format!("{:?}", gm.write_obj(val1, bad_addr2).err().unwrap()),
                format!(
                    "PartialBuffer {{ expected: {:?}, completed: {:?} }}",
                    mem::size_of::<u64>(),
                    max_addr.checked_offset_from(bad_addr2).unwrap()
                )
            );

            gm.write_obj(val1, GuestAddress(0x500)).unwrap();
            gm.write_obj(val2, GuestAddress(0x1000 + 32)).unwrap();
            let num1: u64 = gm.read_obj(GuestAddress(0x500)).unwrap();
            let num2: u64 = gm.read_obj(GuestAddress(0x1000 + 32)).unwrap();
            assert_eq!(val1, num1);
            assert_eq!(val2, num2);
        }
    }

    #[test]
    fn write_and_read() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let mut start_addr = GuestAddress(0x1000);
        let gm = GuestMemoryMmap::from_ranges(&[(start_addr, 0x400)]).unwrap();
        let gm_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[(
            start_addr,
            0x400,
            Some(FileOffset::new(f, 0)),
        )])
        .unwrap();

        let gm_list = vec![gm, gm_backed_by_file];
        for gm in gm_list.iter() {
            let sample_buf = &[1, 2, 3, 4, 5];

            assert_eq!(gm.write(sample_buf, start_addr).unwrap(), 5);

            let buf = &mut [0u8; 5];
            assert_eq!(gm.read(buf, start_addr).unwrap(), 5);
            assert_eq!(buf, sample_buf);

            start_addr = GuestAddress(0x13ff);
            assert_eq!(gm.write(sample_buf, start_addr).unwrap(), 1);
            assert_eq!(gm.read(buf, start_addr).unwrap(), 1);
            assert_eq!(buf[0], sample_buf[0]);
            start_addr = GuestAddress(0x1000);
        }
    }

    #[test]
    fn read_to_and_write_from_mem() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let gm = GuestMemoryMmap::from_ranges(&[(GuestAddress(0x1000), 0x400)]).unwrap();
        let gm_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[(
            GuestAddress(0x1000),
            0x400,
            Some(FileOffset::new(f, 0)),
        )])
        .unwrap();

        let gm_list = vec![gm, gm_backed_by_file];
        for gm in gm_list.iter() {
            let addr = GuestAddress(0x1010);
            let mut file = if cfg!(unix) {
                File::open(Path::new("/dev/zero")).unwrap()
            } else {
                File::open(Path::new("c:\\Windows\\system32\\ntoskrnl.exe")).unwrap()
            };
            gm.write_obj(!0u32, addr).unwrap();
            gm.read_exact_from(addr, &mut file, mem::size_of::<u32>())
                .unwrap();
            let value: u32 = gm.read_obj(addr).unwrap();
            if cfg!(unix) {
                assert_eq!(value, 0);
            } else {
                assert_eq!(value, 0x0090_5a4d);
            }

            let mut sink = Vec::new();
            gm.write_all_to(addr, &mut sink, mem::size_of::<u32>())
                .unwrap();
            if cfg!(unix) {
                assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
            } else {
                assert_eq!(sink, vec![0x4d, 0x5a, 0x90, 0x00]);
            };
        }
    }

    #[test]
    fn create_vec_with_regions() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let mut iterated_regions = Vec::new();
        let gm = GuestMemoryMmap::from_ranges(&regions).unwrap();
        let res: guest_memory::Result<()> = gm.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestUsize);
            Ok(())
        });
        assert!(res.is_ok());
        let res: guest_memory::Result<()> = gm.with_regions_mut(|_, region| {
            iterated_regions.push((region.start_addr(), region.len() as usize));
            Ok(())
        });
        assert!(res.is_ok());
        assert_eq!(regions, iterated_regions);

        assert!(regions
            .iter()
            .map(|x| (x.0, x.1))
            .eq(iterated_regions.iter().map(|x| *x)));

        assert_eq!(gm.clone().regions[0].guest_base, regions[0].0);
        assert_eq!(gm.clone().regions[1].guest_base, regions[1].0);
    }

    #[test]
    fn test_memory() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let mut iterated_regions = Vec::new();
        let gm = Arc::new(GuestMemoryMmap::from_ranges(&regions).unwrap());
        let mem = gm.memory();

        let res: guest_memory::Result<()> = mem.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestUsize);
            Ok(())
        });
        assert!(res.is_ok());
        let res: guest_memory::Result<()> = mem.with_regions_mut(|_, region| {
            iterated_regions.push((region.start_addr(), region.len() as usize));
            Ok(())
        });
        assert!(res.is_ok());
        assert_eq!(regions, iterated_regions);

        assert!(regions
            .iter()
            .map(|x| (x.0, x.1))
            .eq(iterated_regions.iter().map(|x| *x)));

        assert_eq!(gm.clone().regions[0].guest_base, regions[0].0);
        assert_eq!(gm.clone().regions[1].guest_base, regions[1].0);
    }

    #[test]
    fn test_access_cross_boundary() {
        let f1 = TempFile::new().unwrap().into_file();
        f1.set_len(0x1000).unwrap();
        let f2 = TempFile::new().unwrap().into_file();
        f2.set_len(0x1000).unwrap();

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        let gm =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x1000), (start_addr2, 0x1000)]).unwrap();
        let gm_backed_by_file = GuestMemoryMmap::from_ranges_with_files(&[
            (start_addr1, 0x1000, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x1000, Some(FileOffset::new(f2, 0))),
        ])
        .unwrap();

        let gm_list = vec![gm, gm_backed_by_file];
        for gm in gm_list.iter() {
            let sample_buf = &[1, 2, 3, 4, 5];
            assert_eq!(gm.write(sample_buf, GuestAddress(0xffc)).unwrap(), 5);
            let buf = &mut [0u8; 5];
            assert_eq!(gm.read(buf, GuestAddress(0xffc)).unwrap(), 5);
            assert_eq!(buf, sample_buf);
        }
    }

    #[test]
    fn test_retrieve_fd_backing_memory_region() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x400).unwrap();

        let start_addr = GuestAddress(0x0);
        let gm = GuestMemoryMmap::from_ranges(&[(start_addr, 0x400)]).unwrap();
        assert!(gm.find_region(start_addr).is_some());
        let region = gm.find_region(start_addr).unwrap();
        assert!(region.file_offset().is_none());

        let gm = GuestMemoryMmap::from_ranges_with_files(&[(
            start_addr,
            0x400,
            Some(FileOffset::new(f, 0)),
        )])
        .unwrap();
        assert!(gm.find_region(start_addr).is_some());
        let region = gm.find_region(start_addr).unwrap();
        assert!(region.file_offset().is_some());
    }

    // Windows needs a dedicated test where it will retrieve the allocation
    // granularity to determine a proper offset (other than 0) that can be
    // used for the backing file. Refer to Microsoft docs here:
    // https://docs.microsoft.com/en-us/windows/desktop/api/memoryapi/nf-memoryapi-mapviewoffile
    #[test]
    #[cfg(unix)]
    fn test_retrieve_offset_from_fd_backing_memory_region() {
        let f = TempFile::new().unwrap().into_file();
        f.set_len(0x1400).unwrap();
        // Needs to be aligned on 4k, otherwise mmap will fail.
        let offset = 0x1000;

        let start_addr = GuestAddress(0x0);
        let gm = GuestMemoryMmap::from_ranges(&[(start_addr, 0x400)]).unwrap();
        assert!(gm.find_region(start_addr).is_some());
        let region = gm.find_region(start_addr).unwrap();
        assert!(region.file_offset().is_none());

        let gm = GuestMemoryMmap::from_ranges_with_files(&[(
            start_addr,
            0x400,
            Some(FileOffset::new(f, offset)),
        )])
        .unwrap();
        assert!(gm.find_region(start_addr).is_some());
        let region = gm.find_region(start_addr).unwrap();
        assert!(region.file_offset().is_some());
        assert_eq!(region.file_offset().unwrap().start(), offset);
    }

    #[test]
    fn test_mmap_insert_region() {
        let region_size = 0x1000;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x10_0000), region_size),
        ];
        let gm = Arc::new(GuestMemoryMmap::from_ranges(&regions).unwrap());
        let mem_orig = gm.memory();
        assert_eq!(mem_orig.num_regions(), 2);

        let mmap = Arc::new(
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0x8000)).unwrap(),
        );
        let gm = gm.insert_region(mmap).unwrap();
        let mmap = Arc::new(
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0x4000)).unwrap(),
        );
        let gm = gm.insert_region(mmap).unwrap();
        let mmap = Arc::new(
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0xc000)).unwrap(),
        );
        let gm = gm.insert_region(mmap).unwrap();
        let mmap = Arc::new(
            GuestRegionMmap::new(MmapRegion::new(0x1000).unwrap(), GuestAddress(0xc000)).unwrap(),
        );
        gm.insert_region(mmap).unwrap_err();

        assert_eq!(mem_orig.num_regions(), 2);
        assert_eq!(gm.num_regions(), 5);

        assert_eq!(gm.regions[0].start_addr(), GuestAddress(0x0000));
        assert_eq!(gm.regions[1].start_addr(), GuestAddress(0x4000));
        assert_eq!(gm.regions[2].start_addr(), GuestAddress(0x8000));
        assert_eq!(gm.regions[3].start_addr(), GuestAddress(0xc000));
        assert_eq!(gm.regions[4].start_addr(), GuestAddress(0x10_0000));
    }

    #[test]
    fn test_mmap_remove_region() {
        let region_size = 0x1000;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x10_0000), region_size),
        ];
        let gm = Arc::new(GuestMemoryMmap::from_ranges(&regions).unwrap());
        let mem_orig = gm.memory();
        assert_eq!(mem_orig.num_regions(), 2);

        gm.remove_region(GuestAddress(0), 128).unwrap_err();
        gm.remove_region(GuestAddress(0x4000), 128).unwrap_err();
        let (gm, region) = gm.remove_region(GuestAddress(0x10_0000), 0x1000).unwrap();

        assert_eq!(mem_orig.num_regions(), 2);
        assert_eq!(gm.num_regions(), 1);

        assert_eq!(gm.regions[0].start_addr(), GuestAddress(0x0000));
        assert_eq!(region.start_addr(), GuestAddress(0x10_0000));
    }

    #[test]
    fn test_guest_memory_mmap_get_slice() {
        let region_addr = GuestAddress(0);
        let region_size = 0x400;
        let region =
            GuestRegionMmap::new(MmapRegion::new(region_size).unwrap(), region_addr).unwrap();

        // Normal case.
        let slice_addr = MemoryRegionAddress(0x100);
        let slice_size = 0x200;
        let slice = region.get_slice(slice_addr, slice_size).unwrap();
        assert_eq!(slice.len(), slice_size);

        // Empty slice.
        let slice_addr = MemoryRegionAddress(0x200);
        let slice_size = 0x0;
        let slice = region.get_slice(slice_addr, slice_size).unwrap();
        assert!(slice.is_empty());

        // Error case when slice_size is beyond the boundary.
        let slice_addr = MemoryRegionAddress(0x300);
        let slice_size = 0x200;
        assert!(region.get_slice(slice_addr, slice_size).is_err());
    }

    #[test]
    fn test_guest_memory_mmap_as_volatile_slice() {
        let region_addr = GuestAddress(0);
        let region_size = 0x400;
        let region =
            GuestRegionMmap::new(MmapRegion::new(region_size).unwrap(), region_addr).unwrap();

        // Test slice length.
        let slice = region.as_volatile_slice().unwrap();
        assert_eq!(slice.len(), region_size);

        // Test slice data.
        let v = 0x1234_5678u32;
        let r = slice.get_ref::<u32>(0x200).unwrap();
        r.store(v);
        assert_eq!(r.load(), v);
    }

    #[test]
    fn test_guest_memory_get_slice() {
        let start_addr1 = GuestAddress(0);
        let start_addr2 = GuestAddress(0x800);
        let guest_mem =
            GuestMemoryMmap::from_ranges(&[(start_addr1, 0x400), (start_addr2, 0x400)]).unwrap();

        // Normal cases.
        let slice_size = 0x200;
        let slice = guest_mem
            .get_slice(GuestAddress(0x100), slice_size)
            .unwrap();
        assert_eq!(slice.len(), slice_size);

        let slice_size = 0x400;
        let slice = guest_mem
            .get_slice(GuestAddress(0x800), slice_size)
            .unwrap();
        assert_eq!(slice.len(), slice_size);

        // Empty slice.
        assert!(guest_mem
            .get_slice(GuestAddress(0x900), 0)
            .unwrap()
            .is_empty());

        // Error cases, wrong size or base address.
        assert!(guest_mem.get_slice(GuestAddress(0), 0x500).is_err());
        assert!(guest_mem.get_slice(GuestAddress(0x600), 0x100).is_err());
        assert!(guest_mem.get_slice(GuestAddress(0xc00), 0x100).is_err());
    }
}
