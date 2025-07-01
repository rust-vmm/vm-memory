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
use std::ops::Deref;
use std::result;

use crate::address::Address;
use crate::bitmap::{Bitmap, BS};
use crate::guest_memory::{self, FileOffset, GuestAddress, GuestUsize, MemoryRegionAddress};
use crate::region::{GuestMemoryRegion, GuestMemoryRegionBytes};
use crate::volatile_memory::{VolatileMemory, VolatileSlice};
use crate::{Error, GuestRegionCollection};

// re-export for backward compat, as the trait used to be defined in mmap.rs
pub use crate::bitmap::NewBitmap;

#[cfg(all(not(feature = "xen"), target_family = "unix"))]
mod unix;

#[cfg(all(feature = "xen", target_family = "unix"))]
pub(crate) mod xen;

#[cfg(target_family = "windows")]
mod windows;

#[cfg(all(not(feature = "xen"), target_family = "unix"))]
pub use unix::{Error as MmapRegionError, MmapRegion, MmapRegionBuilder};

#[cfg(all(feature = "xen", target_family = "unix"))]
pub use xen::{Error as MmapRegionError, MmapRange, MmapRegion, MmapXenFlags};

#[cfg(target_family = "windows")]
pub use std::io::Error as MmapRegionError;
#[cfg(target_family = "windows")]
pub use windows::MmapRegion;

/// [`GuestMemoryRegion`](trait.GuestMemoryRegion.html) implementation that mmaps the guest's
/// memory region in the current process.
///
/// Represents a continuous region of the guest's physical memory that is backed by a mapping
/// in the virtual address space of the calling process.
#[derive(Debug)]
pub struct GuestRegionMmap<B = ()> {
    mapping: MmapRegion<B>,
    guest_base: GuestAddress,
}

impl<B> Deref for GuestRegionMmap<B> {
    type Target = MmapRegion<B>;

    fn deref(&self) -> &MmapRegion<B> {
        &self.mapping
    }
}

impl<B: Bitmap> GuestRegionMmap<B> {
    /// Create a new memory-mapped memory region for the guest's physical memory.
    ///
    /// Returns `None` if `guest_base` + `mapping.len()` would overflow.
    pub fn new(mapping: MmapRegion<B>, guest_base: GuestAddress) -> Option<Self> {
        guest_base
            .0
            .checked_add(mapping.size() as u64)
            .map(|_| Self {
                mapping,
                guest_base,
            })
    }
}

#[cfg(not(feature = "xen"))]
impl<B: NewBitmap> GuestRegionMmap<B> {
    /// Create a new memory-mapped memory region from guest's physical memory, size and file.
    pub fn from_range(
        addr: GuestAddress,
        size: usize,
        file: Option<FileOffset>,
    ) -> result::Result<Self, Error> {
        let region = if let Some(ref f_off) = file {
            MmapRegion::from_file(f_off.clone(), size)
        } else {
            MmapRegion::new(size)
        }
        .map_err(Error::MmapRegion)?;

        Self::new(region, addr).ok_or(Error::InvalidGuestRegion)
    }
}

#[cfg(feature = "xen")]
impl<B: NewBitmap> GuestRegionMmap<B> {
    /// Create a new Unix memory-mapped memory region from guest's physical memory, size and file.
    /// This must only be used for tests, doctests, benches and is not designed for end consumers.
    pub fn from_range(
        addr: GuestAddress,
        size: usize,
        file: Option<FileOffset>,
    ) -> result::Result<Self, Error> {
        let range = MmapRange::new_unix(size, file, addr);

        let region = MmapRegion::from_range(range).map_err(Error::MmapRegion)?;
        Self::new(region, addr).ok_or(Error::InvalidGuestRegion)
    }
}

impl<B: Bitmap> GuestMemoryRegion for GuestRegionMmap<B> {
    type B = B;

    fn len(&self) -> GuestUsize {
        self.mapping.size() as GuestUsize
    }

    fn start_addr(&self) -> GuestAddress {
        self.guest_base
    }

    fn bitmap(&self) -> BS<'_, Self::B> {
        self.mapping.bitmap().slice_at(0)
    }

    fn get_host_address(&self, addr: MemoryRegionAddress) -> guest_memory::Result<*mut u8> {
        // Not sure why wrapping_offset is not unsafe.  Anyway this
        // is safe because we've just range-checked addr using check_address.
        self.check_address(addr)
            .ok_or(guest_memory::Error::InvalidBackendAddress)
            .map(|addr| {
                self.mapping
                    .as_ptr()
                    .wrapping_offset(addr.raw_value() as isize)
            })
    }

    fn file_offset(&self) -> Option<&FileOffset> {
        self.mapping.file_offset()
    }

    fn get_slice(
        &self,
        offset: MemoryRegionAddress,
        count: usize,
    ) -> guest_memory::Result<VolatileSlice<BS<B>>> {
        let slice = self.mapping.get_slice(offset.raw_value() as usize, count)?;
        Ok(slice)
    }

    #[cfg(target_os = "linux")]
    fn is_hugetlbfs(&self) -> Option<bool> {
        self.mapping.is_hugetlbfs()
    }
}

impl<B: Bitmap> GuestMemoryRegionBytes for GuestRegionMmap<B> {}

/// [`GuestMemory`](trait.GuestMemory.html) implementation that mmaps the guest's memory
/// in the current process.
///
/// Represents the entire physical memory of the guest by tracking all its memory regions.
/// Each region is an instance of `GuestRegionMmap`, being backed by a mapping in the
/// virtual address space of the calling process.
pub type GuestMemoryMmap<B = ()> = GuestRegionCollection<GuestRegionMmap<B>>;

impl<B: NewBitmap> GuestMemoryMmap<B> {
    /// Creates a container and allocates anonymous memory for guest memory regions.
    ///
    /// Valid memory regions are specified as a slice of (Address, Size) tuples sorted by Address.
    pub fn from_ranges(ranges: &[(GuestAddress, usize)]) -> result::Result<Self, Error> {
        Self::from_ranges_with_files(ranges.iter().map(|r| (r.0, r.1, None)))
    }

    /// Creates a container and allocates anonymous memory for guest memory regions.
    ///
    /// Valid memory regions are specified as a sequence of (Address, Size, [`Option<FileOffset>`])
    /// tuples sorted by Address.
    pub fn from_ranges_with_files<A, T>(ranges: T) -> result::Result<Self, Error>
    where
        A: Borrow<(GuestAddress, usize, Option<FileOffset>)>,
        T: IntoIterator<Item = A>,
    {
        Self::from_regions(
            ranges
                .into_iter()
                .map(|x| {
                    GuestRegionMmap::from_range(x.borrow().0, x.borrow().1, x.borrow().2.clone())
                })
                .collect::<result::Result<Vec<_>, Error>>()?,
        )
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]
    extern crate vmm_sys_util;

    use super::*;

    use crate::bitmap::tests::test_guest_memory_and_region;
    use crate::bitmap::AtomicBitmap;
    use crate::{Bytes, GuestMemory, GuestMemoryError};

    use std::io::Write;
    use std::mem;
    #[cfg(feature = "rawfd")]
    use std::{fs::File, path::Path};
    use vmm_sys_util::tempfile::TempFile;

    type GuestRegionMmap = super::GuestRegionMmap<()>;
    type GuestMemoryMmap = super::GuestRegionCollection<GuestRegionMmap>;
    type MmapRegion = super::MmapRegion<()>;

    #[test]
    fn basic_map() {
        let m = MmapRegion::new(1024).unwrap();
        assert_eq!(1024, m.size());
    }

    #[test]
    fn slice_addr() {
        let m = GuestRegionMmap::from_range(GuestAddress(0), 5, None).unwrap();
        let s = m.get_slice(MemoryRegionAddress(2), 3).unwrap();
        let guard = s.ptr_guard();
        assert_eq!(guard.as_ptr(), unsafe { m.as_ptr().offset(2) });
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn mapped_file_read() {
        let mut f = TempFile::new().unwrap().into_file();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert!(f.write_all(sample_buf).is_ok());

        let file = Some(FileOffset::new(f, 0));
        let mem_map = GuestRegionMmap::from_range(GuestAddress(0), sample_buf.len(), file).unwrap();
        let buf = &mut [0u8; 16];
        assert_eq!(
            mem_map.as_volatile_slice().unwrap().read(buf, 0).unwrap(),
            sample_buf.len()
        );
        assert_eq!(buf[0..sample_buf.len()], sample_buf[..]);
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

        let guest_mem_list = [guest_mem, guest_mem_backed_by_file];
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

        let guest_mem_list = [guest_mem, guest_mem_backed_by_file];
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

        let guest_mem_list = [guest_mem, guest_mem_backed_by_file];
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

        let gm_list = [gm, gm_backed_by_file];
        for gm in gm_list.iter() {
            let val1: u64 = 0xaa55_aa55_aa55_aa55;
            let val2: u64 = 0x55aa_55aa_55aa_55aa;
            assert!(matches!(
                gm.write_obj(val1, bad_addr).unwrap_err(),
                GuestMemoryError::InvalidGuestAddress(addr) if addr == bad_addr
            ));
            assert!(matches!(
                gm.write_obj(val1, bad_addr2).unwrap_err(),
                GuestMemoryError::PartialBuffer { expected, completed} if expected == size_of::<u64>() && completed == max_addr.checked_offset_from(bad_addr2).unwrap() as usize));

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

        let gm_list = [gm, gm_backed_by_file];
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
    #[cfg(feature = "rawfd")]
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

        let gm_list = [gm, gm_backed_by_file];
        for gm in gm_list.iter() {
            let addr = GuestAddress(0x1010);
            let mut file = if cfg!(target_family = "unix") {
                File::open(Path::new("/dev/zero")).unwrap()
            } else {
                File::open(Path::new("c:\\Windows\\system32\\ntoskrnl.exe")).unwrap()
            };
            gm.write_obj(!0u32, addr).unwrap();
            gm.read_exact_volatile_from(addr, &mut file, mem::size_of::<u32>())
                .unwrap();
            let value: u32 = gm.read_obj(addr).unwrap();
            if cfg!(target_family = "unix") {
                assert_eq!(value, 0);
            } else {
                assert_eq!(value, 0x0090_5a4d);
            }

            let mut sink = vec![0; mem::size_of::<u32>()];
            gm.write_all_volatile_to(addr, &mut sink.as_mut_slice(), mem::size_of::<u32>())
                .unwrap();
            if cfg!(target_family = "unix") {
                assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
            } else {
                assert_eq!(sink, vec![0x4d, 0x5a, 0x90, 0x00]);
            };
        }
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

        let gm_list = [gm, gm_backed_by_file];
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
    #[cfg(target_family = "unix")]
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
    fn test_guest_memory_mmap_get_slice() {
        let region = GuestRegionMmap::from_range(GuestAddress(0), 0x400, None).unwrap();

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
        let region_size = 0x400;
        let region = GuestRegionMmap::from_range(GuestAddress(0), region_size, None).unwrap();

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

    #[test]
    fn test_atomic_accesses() {
        let region = GuestRegionMmap::from_range(GuestAddress(0), 0x1000, None).unwrap();

        crate::bytes::tests::check_atomic_accesses(
            region,
            MemoryRegionAddress(0),
            MemoryRegionAddress(0x1000),
        );
    }

    #[test]
    fn test_dirty_tracking() {
        test_guest_memory_and_region(|| {
            crate::GuestMemoryMmap::<AtomicBitmap>::from_ranges(&[(GuestAddress(0), 0x1_0000)])
                .unwrap()
        });
    }
}
