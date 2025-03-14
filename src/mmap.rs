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

#[cfg(unix)]
use std::io::{Seek, SeekFrom};
use std::result;

use crate::bitmap::Bitmap;
use crate::guest_memory::FileOffset;

#[cfg(all(not(feature = "xen"), unix))]
pub use crate::mmap_unix::{Error as MmapRegionError, MmapRegion, MmapRegionBuilder};

#[cfg(all(feature = "xen", unix))]
pub use crate::mmap_xen::{Error as MmapRegionError, MmapRange, MmapRegion, MmapXenFlags};

/// A `Bitmap` that can be created starting from an initial size.
pub trait NewBitmap: Bitmap + Default {
    /// Create a new object based on the specified length in bytes.
    fn with_len(len: usize) -> Self;
}

impl NewBitmap for () {
    fn with_len(_len: usize) -> Self {}
}

/// Errors that can occur during [`check_file_offset`]
#[derive(Debug, thiserror::Error)]
pub enum CheckFileOffsetError {
    /// Seeking the end of the file returned an error.
    #[error("Error seeking the end of the file: {0}")]
    SeekEnd(std::io::Error),
    /// Seeking the start of the file returned an error.
    #[error("Error seeking the start of the file: {0}")]
    SeekStart(std::io::Error),
    /// A mapping with offset + length > EOF was attempted.
    #[error("The specified file offset and length is greater then file length")]
    MappingPastEof,
    /// The specified file offset and length cause overflow when added.
    #[error("The specified file offset and length cause overflow when added")]
    InvalidOffsetLength,
}

// TODO: use this for Windows as well after we redefine the Error type there.
#[cfg(unix)]
/// Checks if a mapping of `size` bytes fits at the provided `file_offset`.
///
/// For a borrowed `FileOffset` and size, this function checks whether the mapping does not
/// extend past EOF, and that adding the size to the file offset does not lead to overflow.
pub fn check_file_offset(
    file_offset: &FileOffset,
    size: usize,
) -> result::Result<(), CheckFileOffsetError> {
    let mut file = file_offset.file();
    let start = file_offset.start();

    if let Some(end) = start.checked_add(size as u64) {
        let filesize = file
            .seek(SeekFrom::End(0))
            .map_err(CheckFileOffsetError::SeekEnd)?;
        file.rewind().map_err(CheckFileOffsetError::SeekStart)?;
        if filesize < end {
            return Err(CheckFileOffsetError::MappingPastEof);
        }
    } else {
        return Err(CheckFileOffsetError::InvalidOffsetLength);
    }

    Ok(())
}

#[cfg(test)]
pub(crate) mod tests {
    #![allow(clippy::undocumented_unsafe_blocks)]
    extern crate vmm_sys_util;

    use super::*;

    use crate::bitmap::BS;
    use crate::{
        guest_memory, Address, Bytes, GuestAddress, GuestMemory, GuestMemoryError,
        GuestMemoryRegion, GuestUsize, MemoryRegionAddress, VolatileMemory, VolatileSlice,
    };

    use std::io::Write;
    use std::mem;
    use std::sync::Arc;
    #[cfg(feature = "rawfd")]
    use std::{fs::File, path::Path};
    use vmm_sys_util::tempfile::TempFile;

    macro_rules! any_backend {
        ($($(#[$attr:meta])* $backend: ident[$region: path]), *) => {
            #[derive(Debug)]
            pub enum AnyRegion {
                $(
                    $(#[$attr])* $backend($region)
                ),*
            }

            pub type AnyBackend = $crate::GuestRegionCollection<AnyRegion>;

            impl $crate::GuestMemoryRegion for AnyRegion {
                type B = ();

                fn len(&self) -> GuestUsize {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => $crate::GuestMemoryRegion::len(inner)),*
                    }
                }

                fn start_addr(&self) -> GuestAddress {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => inner.start_addr()),*
                    }
                }

                fn bitmap(&self) -> &Self::B {
                    &()
                }

                fn get_host_address(&self, addr: MemoryRegionAddress) -> guest_memory::Result<*mut u8> {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => inner.get_host_address(addr)),*
                    }
                }

                fn file_offset(&self) -> Option<&FileOffset> {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => inner.file_offset()),*
                    }
                }

                fn get_slice(&self, offset: MemoryRegionAddress, count: usize) -> guest_memory::Result<VolatileSlice<BS<Self::B>>> {
                    match self {
                        $($(#[$attr])* AnyRegion::$backend(inner) => $crate::GuestMemoryRegion::get_slice(inner, offset, count)),*
                    }
                }
            }
        };
    }

    any_backend! {
        #[cfg(all(windows, feature = "backend-mmap"))]
        Windows[crate::mmap_windows::GuestRegionWindows<()>],
        #[cfg(all(unix, feature = "backend-mmap", not(feature = "xen")))]
        Mmap[crate::mmap_unix::GuestRegionMmap<()>],
        #[cfg(all(unix, feature = "backend-mmap", feature = "xen"))]
        Xen[crate::mmap_xen::MmapRegion]
    }

    // The cfgs make using vec![...] instead more unreadable, so suppress the lint here.
    #[allow(clippy::vec_init_then_push)]
    impl AnyRegion {
        fn all_with_file(addr: GuestAddress, size: usize, f_off: &FileOffset) -> Vec<AnyRegion> {
            let mut regions = Vec::new();
            #[cfg(all(windows, feature = "backend-mmap"))]
            regions.push(AnyRegion::Windows(
                crate::mmap_windows::GuestRegionWindows::new(
                    crate::mmap_windows::MmapRegion::from_file(f_off.clone(), size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap", not(feature = "xen")))]
            regions.push(AnyRegion::Mmap(
                crate::mmap_unix::GuestRegionMmap::new(
                    MmapRegion::from_file(f_off.clone(), size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap", feature = "xen"))]
            regions.push(AnyRegion::Xen(
                MmapRegion::from_range(MmapRange::new_unix(size, Some(f_off.clone()), addr))
                    .unwrap(),
            ));
            regions
        }

        fn all(addr: GuestAddress, size: usize, file: &Option<FileOffset>) -> Vec<AnyRegion> {
            let mut regions = if let Some(file) = file {
                Self::all_with_file(addr, size, file)
            } else {
                Vec::new()
            };
            #[cfg(all(windows, feature = "backend-mmap"))]
            regions.push(AnyRegion::Windows(
                crate::mmap_windows::GuestRegionWindows::new(
                    crate::mmap_windows::MmapRegion::new(size).unwrap(),
                    addr,
                )
                .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap", not(feature = "xen")))]
            regions.push(AnyRegion::Mmap(
                crate::mmap_unix::GuestRegionMmap::new(MmapRegion::new(size).unwrap(), addr)
                    .unwrap(),
            ));
            #[cfg(all(unix, feature = "backend-mmap", feature = "xen"))]
            regions.push(AnyRegion::Xen(
                MmapRegion::from_range(MmapRange::new_unix(size, None, addr)).unwrap(),
            ));
            regions
        }

        fn as_ptr(&self) -> *mut u8 {
            self.get_host_address(MemoryRegionAddress(0)).unwrap()
        }
    }

    fn transpose(striped: Vec<Vec<AnyRegion>>) -> Vec<AnyBackend> {
        assert!(!striped.is_empty(), "No test cases found!");

        let mut backends = (0..striped[0].len())
            .map(|_| AnyBackend::default())
            .collect::<Vec<_>>();
        for stripe in striped {
            backends
                .iter_mut()
                .zip(stripe)
                .for_each(|(backend, region)| {
                    *backend = backend.insert_region(Arc::new(region)).unwrap();
                });
        }
        backends
    }

    impl AnyBackend {
        fn all_with_file(regions: &[(GuestAddress, usize, FileOffset)]) -> Vec<AnyBackend> {
            let striped = regions
                .iter()
                .map(|(addr, size, file)| AnyRegion::all_with_file(*addr, *size, file))
                .collect::<Vec<_>>();

            transpose(striped)
        }

        pub(crate) fn all(
            regions: &[(GuestAddress, usize, Option<FileOffset>)],
        ) -> Vec<AnyBackend> {
            let striped = regions
                .iter()
                .map(|(addr, size, file)| AnyRegion::all(*addr, *size, file))
                .collect::<Vec<_>>();

            transpose(striped)
        }
    }

    #[test]
    fn basic_map() {
        for m in AnyRegion::all(GuestAddress(0), 1024, &None) {
            assert_eq!(1024, m.len());
        }
    }

    #[test]
    fn slice_addr() {
        for m in AnyRegion::all(GuestAddress(0), 5, &None) {
            let s = m.get_slice(MemoryRegionAddress(2), 3).unwrap();
            let guard = s.ptr_guard();
            assert_eq!(guard.as_ptr(), unsafe { m.as_ptr().offset(2) });
        }
    }

    #[test]
    #[cfg(not(miri))] // Miri cannot mmap files
    fn mapped_file_read() {
        let mut f = TempFile::new().unwrap().into_file();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert!(f.write_all(sample_buf).is_ok());

        let file = FileOffset::new(f, 0);
        for mem_map in AnyRegion::all_with_file(GuestAddress(0), sample_buf.len(), &file) {
            let buf = &mut [0u8; 16];
            assert_eq!(
                mem_map.as_volatile_slice().unwrap().read(buf, 0).unwrap(),
                sample_buf.len()
            );
            assert_eq!(buf[0..sample_buf.len()], sample_buf[..]);
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
        for guest_mem in AnyBackend::all(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ]) {
            assert!(guest_mem.to_region_addr(GuestAddress(0x600)).is_none());
            let (r0, addr0) = guest_mem.to_region_addr(GuestAddress(0x800)).unwrap();
            let (r1, addr1) = guest_mem.to_region_addr(GuestAddress(0xa00)).unwrap();
            assert_eq!(r0.as_ptr(), r1.as_ptr());
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
        for guest_mem in AnyBackend::all(&[
            (start_addr1, 0x400, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x400, Some(FileOffset::new(f2, 0))),
        ]) {
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
        for guest_mem in AnyBackend::all(&[(start_addr, 0x400, Some(FileOffset::new(f, 0)))]) {
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

        for gm in AnyBackend::all(&[
            (start_addr1, 0x1000, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x1000, Some(FileOffset::new(f2, 0))),
        ]) {
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
        for gm in AnyBackend::all(&[(start_addr, 0x400, Some(FileOffset::new(f, 0)))]) {
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

        for gm in AnyBackend::all(&[(GuestAddress(0x1000), 0x400, Some(FileOffset::new(f, 0)))]) {
            let addr = GuestAddress(0x1010);
            let mut file = File::open(Path::new("/dev/zero")).unwrap();
            gm.write_obj(!0u32, addr).unwrap();
            gm.read_exact_volatile_from(addr, &mut file, mem::size_of::<u32>())
                .unwrap();
            let value: u32 = gm.read_obj(addr).unwrap();
            if cfg!(unix) {
                assert_eq!(value, 0);
            } else {
                assert_eq!(value, 0x0090_5a4d);
            }

            let mut sink = vec![0; mem::size_of::<u32>()];
            gm.write_all_volatile_to(addr, &mut sink.as_mut_slice(), mem::size_of::<u32>())
                .unwrap();
            assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
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
        for gm in AnyBackend::all(&[
            (start_addr1, 0x1000, Some(FileOffset::new(f1, 0))),
            (start_addr2, 0x1000, Some(FileOffset::new(f2, 0))),
        ]) {
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
        for gm in AnyBackend::all_with_file(&[(start_addr, 0x400, FileOffset::new(f, 0))]) {
            assert!(gm.find_region(start_addr).is_some());
            let region = gm.find_region(start_addr).unwrap();
            assert!(region.file_offset().is_some());
        }
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

        for gm in AnyBackend::all_with_file(&[(start_addr, 0x400, FileOffset::new(f, offset))]) {
            assert!(gm.find_region(start_addr).is_some());
            let region = gm.find_region(start_addr).unwrap();
            assert!(region.file_offset().is_some());
            assert_eq!(region.file_offset().unwrap().start(), offset);
        }
    }

    #[test]
    fn test_guest_memory_mmap_get_slice() {
        for region in AnyRegion::all(GuestAddress(0), 0x400, &None) {
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
    }

    #[test]
    fn test_guest_memory_mmap_as_volatile_slice() {
        let region_size = 0x400;

        for region in AnyRegion::all(GuestAddress(0), region_size, &None) {
            // Test slice length.
            let slice = region.as_volatile_slice().unwrap();
            assert_eq!(slice.len(), region_size);

            // Test slice data.
            let v = 0x1234_5678u32;
            let r = slice.get_ref::<u32>(0x200).unwrap();
            r.store(v);
            assert_eq!(r.load(), v);
        }
    }

    #[test]
    fn test_guest_memory_get_slice() {
        let start_addr1 = GuestAddress(0);
        let start_addr2 = GuestAddress(0x800);
        for guest_mem in AnyBackend::all(&[(start_addr1, 0x400, None), (start_addr2, 0x400, None)])
        {
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

    #[test]
    fn test_atomic_accesses() {
        for region in AnyRegion::all(GuestAddress(0), 0x1000, &None) {
            crate::bytes::tests::check_atomic_accesses(
                region,
                MemoryRegionAddress(0),
                MemoryRegionAddress(0x1000),
            );
        }
    }
}
