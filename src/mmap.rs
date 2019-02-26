// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! A default implementation of GuestMemory by mmap()-ing guest's memory into current process.
//!
//! The main structs to access guest's memory are:
//! - MmapRegion: mmap a continuous region of guest's memory into current process
//! - GuestRegionMmap: map from guest physical address into mmapped offset
//! - GuestMemoryMmap: manage a collection of GuestRegionMmap objects

use libc;
use std::io::{self, Read, Write};
use std::ops::{BitAnd, BitOr};
use std::os::unix::io::AsRawFd;
use std::ptr::null_mut;
use std::sync::Arc;

use address_space::{Address, AddressRegion, AddressSpace, AddressValue};
use guest_memory::*;
use volatile_memory::*;
use Bytes;

type MmapAddressValue = <MmapAddress as AddressValue>::V;
type Result<T> = std::result::Result<T, Error>;

/// Represents an offset into a memory mapped area.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct MmapAddress(pub usize);

impl_address_ops!(MmapAddress, usize);

/// A backend driver to access guest's physical memory by mmapping guest's memory into current
/// process.
/// For a combination of 32-bit hypervisor and 64-bit virtual machine, only partial of guest's
/// physical memory may be mapped into current process due to limited process virtual address
/// space size.
#[derive(Debug)]
pub struct MmapRegion {
    addr: *mut u8,
    size: usize,
}

/// Errors that can happen when creating a memory map
#[derive(Debug)]
pub enum MmapError {
    /// Syscall returned the given error.
    SystemCallFailed(io::Error),
    /// No memory region found.
    NoMemoryRegion,
    /// Some of the memory regions intersect with each other.
    MemoryRegionOverlap,
}

// Send and Sync aren't automatically inherited for the raw address pointer.
// Accessing that pointer is only done through the stateless interface which
// allows the object to be shared by multiple threads without a decrease in
// safety.
unsafe impl Send for MmapRegion {}
unsafe impl Sync for MmapRegion {}

impl MmapRegion {
    /// Creates an anonymous shared mapping of `size` bytes.
    ///
    /// # Arguments
    /// * `size` - Size of memory region in bytes.
    pub fn new(size: usize) -> io::Result<Self> {
        // This is safe because we are creating an anonymous mapping in a place not already used by
        // any other area in this process.
        let addr = unsafe {
            libc::mmap(
                null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_ANONYMOUS | libc::MAP_SHARED | libc::MAP_NORESERVE,
                -1,
                0,
            )
        };
        if addr == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        Ok(Self {
            addr: addr as *mut u8,
            size,
        })
    }

    /// Maps the `size` bytes starting at `offset` bytes of the given `fd`.
    ///
    /// # Arguments
    /// * `fd` - File descriptor to mmap from.
    /// * `size` - Size of memory region in bytes.
    /// * `offset` - Offset in bytes from the beginning of `fd` to start the mmap.
    pub fn from_fd(fd: &AsRawFd, size: usize, offset: libc::off_t) -> io::Result<Self> {
        // This is safe because we are creating a mapping in a place not already used by any other
        // area in this process.
        let addr = unsafe {
            libc::mmap(
                null_mut(),
                size,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                fd.as_raw_fd(),
                offset as libc::off_t,
            )
        };
        if addr == libc::MAP_FAILED {
            return Err(io::Error::last_os_error());
        }
        Ok(Self {
            addr: addr as *mut u8,
            size,
        })
    }

    /// Returns a pointer to the beginning of the memory region.  Should only be
    /// used for passing this region to ioctls for setting guest memory.
    pub fn as_ptr(&self) -> *mut u8 {
        self.addr
    }

    unsafe fn as_slice(&self) -> &[u8] {
        // This is safe because we mapped the area at addr ourselves, so this slice will not
        // overflow. However, it is possible to alias.
        std::slice::from_raw_parts(self.addr, self.size)
    }

    // safe because it's expected interior mutability
    #[allow(clippy::mut_from_ref)]
    unsafe fn as_mut_slice(&self) -> &mut [u8] {
        // This is safe because we mapped the area at addr ourselves, so this slice will not
        // overflow. However, it is possible to alias.
        std::slice::from_raw_parts_mut(self.addr, self.size)
    }

    // Check that addr + count is valid and return the sum.
    fn region_end(&self, addr: usize, count: usize) -> Result<usize> {
        let end = addr
            .checked_add(count)
            .ok_or_else(|| Error::InvalidBackendAddress)?;
        if end > self.size {
            return Err(Error::InvalidBackendAddress);
        }
        Ok(end)
    }
}

impl AddressRegion for MmapRegion {
    type A = MmapAddress;
    type E = Error;

    fn len(&self) -> MmapAddressValue {
        self.size
    }

    fn max_addr(&self) -> MmapAddress {
        MmapAddress(self.size)
    }

    fn is_valid(&self) -> bool {
        !self.addr.is_null() && self.addr != libc::MAP_FAILED as *mut u8
    }
}

impl Bytes<MmapAddress> for MmapRegion {
    type E = Error;

    /// Writes a slice to the region at the specified address.
    /// Returns the number of bytes written. The number of bytes written can
    /// be less than the length of the slice if there isn't enough room in the
    /// region.
    ///
    /// # Examples
    /// * Write a slice at offset 256.
    ///
    /// ```
    /// #   use vm_memory::{AddressRegion, Bytes, MmapAddress, MmapRegion};
    /// #   let mut mem_map = MmapRegion::new(1024).unwrap();
    ///     let res = mem_map.write(&[1,2,3,4,5], MmapAddress(1020));
    ///     assert!(res.is_ok());
    ///     assert_eq!(res.unwrap(), 4);
    /// ```
    fn write(&self, buf: &[u8], addr: MmapAddress) -> Result<usize> {
        if addr.raw_value() >= self.size {
            return Err(Error::InvalidBackendAddress);
        }
        unsafe {
            // Guest memory can't strictly be modeled as a slice because it is
            // volatile.  Writing to it with what compiles down to a memcpy
            // won't hurt anything as long as we get the bounds checks right.
            let mut slice: &mut [u8] = &mut self.as_mut_slice()[addr.raw_value()..];
            Ok(slice.write(buf).map_err(Error::IOError)?)
        }
    }

    /// Reads to a slice from the region at the specified address.
    /// Returns the number of bytes read. The number of bytes read can be less than the length
    /// of the slice if there isn't enough room in the region.
    ///
    /// # Examples
    /// * Read a slice of size 16 at offset 256.
    ///
    /// ```
    /// #   use vm_memory::{AddressRegion, Bytes, MmapAddress, MmapRegion};
    /// #   let mut mem_map = MmapRegion::new(1024).unwrap();
    ///     let buf = &mut [0u8; 16];
    ///     let res = mem_map.read(buf, MmapAddress(1010));
    ///     assert!(res.is_ok());
    ///     assert_eq!(res.unwrap(), 14);
    /// ```
    fn read(&self, mut buf: &mut [u8], addr: MmapAddress) -> Result<usize> {
        if addr.raw_value() >= self.size {
            return Err(Error::InvalidBackendAddress);
        }
        unsafe {
            // Guest memory can't strictly be modeled as a slice because it is
            // volatile.  Writing to it with what compiles down to a memcpy
            // won't hurt anything as long as we get the bounds checks right.
            let slice: &[u8] = &self.as_slice()[addr.raw_value()..];
            Ok(buf.write(slice).map_err(Error::IOError)?)
        }
    }

    /// Writes a slice to the region at the specified address.
    ///
    /// # Examples
    /// * Write a slice at offset 256.
    ///
    /// ```
    /// #   use vm_memory::{AddressRegion, Bytes, MmapAddress, MmapRegion};
    /// #   let mut mem_map = MmapRegion::new(1024).unwrap();
    ///     let res = mem_map.write_slice(&[1,2,3,4,5], MmapAddress(256));
    ///     assert!(res.is_ok());
    ///     assert_eq!(res.unwrap(), ());
    /// ```
    fn write_slice(&self, buf: &[u8], addr: MmapAddress) -> Result<()> {
        let len = self.write(buf, addr)?;
        if len != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len() as u64,
                completed: len as u64,
            });
        }
        Ok(())
    }

    /// Reads to a slice from the region at the specified address.
    ///
    /// # Examples
    /// * Read a slice of size 16 at offset 256.
    ///
    /// ```
    /// #   use vm_memory::{AddressRegion, Bytes, MmapAddress, MmapRegion};
    /// #   let mut mem_map = MmapRegion::new(1024).unwrap();
    ///     let buf = &mut [0u8; 16];
    ///     let res = mem_map.read_slice(buf, MmapAddress(256));
    ///     assert!(res.is_ok());
    ///     assert_eq!(res.unwrap(), ());
    /// ```
    fn read_slice(&self, buf: &mut [u8], addr: MmapAddress) -> Result<()> {
        let len = self.read(buf, addr)?;
        if len != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len() as u64,
                completed: len as u64,
            });
        }
        Ok(())
    }

    /// Writes data from a readable object like a File and writes it to the region.
    ///
    /// # Examples
    ///
    /// * Read bytes from /dev/urandom
    ///
    /// ```
    /// # use vm_memory::{Bytes, MmapAddress, MmapRegion};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # fn test_read_random() -> Result<u32, ()> {
    /// #     let mut mem_map = MmapRegion::new(1024).unwrap();
    ///       let mut file = File::open(Path::new("/dev/urandom")).map_err(|_| ())?;
    ///       mem_map.write_from_stream(MmapAddress(32), &mut file, 128).map_err(|_| ())?;
    ///       let rand_val: u32 =  mem_map.read_obj(MmapAddress(40)).map_err(|_| ())?;
    /// #     Ok(rand_val)
    /// # }
    /// ```
    fn write_from_stream<F>(&self, addr: MmapAddress, src: &mut F, count: usize) -> Result<()>
    where
        F: Read,
    {
        let end = self.region_end(addr.raw_value(), count)?;
        unsafe {
            // It is safe to overwrite the volatile memory. Accessing the guest
            // memory as a mutable slice is OK because nothing assumes another
            // thread won't change what is loaded.
            let dst = &mut self.as_mut_slice()[addr.raw_value()..end];
            src.read_exact(dst).map_err(Error::IOError)?;
        }
        Ok(())
    }

    /// Reads data from the region to a writable object.
    ///
    /// # Examples
    ///
    /// * Write 128 bytes to /dev/null
    ///
    /// ```
    /// # use vm_memory::{Bytes, MmapAddress, MmapRegion};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # fn test_write_null() -> Result<(), ()> {
    /// #     let mut mem_map = MmapRegion::new(1024).unwrap();
    ///       let mut file = File::open(Path::new("/dev/null")).map_err(|_| ())?;
    ///       mem_map.read_into_stream(MmapAddress(32), &mut file, 128).map_err(|_| ())?;
    /// #     Ok(())
    /// # }
    /// ```
    fn read_into_stream<F>(&self, addr: MmapAddress, dst: &mut F, count: usize) -> Result<()>
    where
        F: Write,
    {
        let end = self.region_end(addr.raw_value(), count)?;
        unsafe {
            // It is safe to read from volatile memory. Accessing the guest
            // memory as a slice is OK because nothing assumes another thread
            // won't change what is loaded.
            let src = &self.as_mut_slice()[addr.raw_value()..end];
            dst.write_all(src).map_err(Error::IOError)?;
        }
        Ok(())
    }
}

impl VolatileMemory for MmapRegion {
    fn get_slice(&self, offset: usize, count: usize) -> VolatileMemoryResult<VolatileSlice> {
        let end = calc_offset(offset, count)?;
        if end > self.size {
            return Err(VolatileMemoryError::OutOfBounds { addr: end });
        }

        // Safe because we checked that offset + count was within our range and we only ever hand
        // out volatile accessors.
        Ok(unsafe { VolatileSlice::new((self.addr as usize + offset) as *mut _, count) })
    }
}

impl Drop for MmapRegion {
    fn drop(&mut self) {
        // This is safe because we mmap the area at addr ourselves, and nobody
        // else is holding a reference to it.
        unsafe {
            libc::munmap(self.addr as *mut libc::c_void, self.size);
        }
    }
}

/// Tracks a mapping of memory in the current process and the corresponding base address
/// in the guest's memory space.
pub struct GuestRegionMmap {
    mapping: MmapRegion,
    guest_base: GuestAddress,
}

impl GuestRegionMmap {
    /// Create a new memory-mapped memory region for guest's physical memory.
    /// Note: caller needs to ensure that (mapping.len() + guest_base) doesn't wrapping around.
    pub fn new(mapping: MmapRegion, guest_base: GuestAddress) -> Self {
        GuestRegionMmap {
            mapping,
            guest_base,
        }
    }

    fn to_mmap_addr(&self, addr: GuestAddress) -> Result<MmapAddress> {
        let offset = addr
            .checked_offset_from(self.guest_base)
            .ok_or_else(|| Error::InvalidGuestAddress(addr))?;
        if offset >= self.len() {
            return Err(Error::InvalidGuestAddress(addr));
        }
        Ok(MmapAddress(offset as usize))
    }

    unsafe fn as_slice(&self) -> &[u8] {
        self.mapping.as_slice()
    }

    unsafe fn as_mut_slice(&self) -> &mut [u8] {
        self.mapping.as_mut_slice()
    }
}

impl AddressRegion for GuestRegionMmap {
    type A = GuestAddress;
    type E = Error;

    fn len(&self) -> GuestAddressValue {
        self.mapping.len() as GuestAddressValue
    }

    fn min_addr(&self) -> GuestAddress {
        self.guest_base
    }

    fn max_addr(&self) -> GuestAddress {
        // unchecked_add is safe as the region bounds were checked when it was created.
        self.guest_base
            .unchecked_add(self.mapping.len() as GuestAddressValue)
    }
}

impl Bytes<GuestAddress> for GuestRegionMmap {
    type E = Error;

    fn write(&self, buf: &[u8], addr: GuestAddress) -> Result<usize> {
        let maddr = self.to_mmap_addr(addr)?;
        self.mapping.write(buf, maddr)
    }

    fn read(&self, buf: &mut [u8], addr: GuestAddress) -> Result<usize> {
        let maddr = self.to_mmap_addr(addr)?;
        self.mapping.read(buf, maddr)
    }

    fn write_slice(&self, buf: &[u8], addr: GuestAddress) -> Result<()> {
        let maddr = self.to_mmap_addr(addr)?;
        self.mapping.write_slice(buf, maddr)
    }

    fn read_slice(&self, buf: &mut [u8], addr: GuestAddress) -> Result<()> {
        let maddr = self.to_mmap_addr(addr)?;
        self.mapping.read_slice(buf, maddr)
    }

    fn write_from_stream<F>(&self, addr: GuestAddress, src: &mut F, count: usize) -> Result<()>
    where
        F: Read,
    {
        let maddr = self.to_mmap_addr(addr)?;
        self.mapping.write_from_stream::<F>(maddr, src, count)
    }

    fn read_into_stream<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<()>
    where
        F: Write,
    {
        let maddr = self.to_mmap_addr(addr)?;
        self.mapping.read_into_stream::<F>(maddr, dst, count)
    }
}

impl GuestMemoryRegion for GuestRegionMmap {}

/// Tracks memory regions allocated/mapped for the guest in the current process.
#[derive(Clone)]
pub struct GuestMemoryMmap {
    regions: Arc<Vec<GuestRegionMmap>>,
}

impl GuestMemoryMmap {
    /// Creates a container and allocates anonymous memory for guest memory regions.
    /// Valid memory regions are specified as a Vec of (Address, Size) tuples sorted by Address.
    pub fn new(ranges: &[(GuestAddress, usize)]) -> std::result::Result<Self, MmapError> {
        if ranges.is_empty() {
            return Err(MmapError::NoMemoryRegion);
        }

        let mut regions = Vec::<GuestRegionMmap>::new();
        for range in ranges.iter() {
            if let Some(last) = regions.last() {
                if last
                    .guest_base
                    .checked_add(last.mapping.len() as GuestAddressValue)
                    .map_or(true, |a| a > range.0)
                {
                    return Err(MmapError::MemoryRegionOverlap);
                }
            }

            let mapping = MmapRegion::new(range.1).map_err(MmapError::SystemCallFailed)?;
            regions.push(GuestRegionMmap {
                mapping,
                guest_base: range.0,
            });
        }

        Ok(Self {
            regions: Arc::new(regions),
        })
    }
}

impl AddressRegion for GuestMemoryMmap {
    type A = GuestAddress;
    type E = Error;

    fn len(&self) -> GuestAddressValue {
        self.regions
            .iter()
            .map(|region| region.mapping.len() as GuestAddressValue)
            .sum()
    }

    fn min_addr(&self) -> GuestAddress {
        self.regions
            .iter()
            .min_by_key(|region| region.min_addr())
            .map_or(GuestAddress(0), |region| region.min_addr())
    }

    /// # Examples
    ///
    /// ```
    /// # use vm_memory::{Address, AddressRegion, GuestAddress, GuestMemoryMmap};
    /// # fn test_end_addr() -> Result<(), ()> {
    ///     let start_addr = GuestAddress(0x1000);
    ///     let mut gm = GuestMemoryMmap::new(&vec![(start_addr, 0x400)]).map_err(|_| ())?;
    ///     assert_eq!(start_addr.checked_add(0x400), Some(gm.max_addr()));
    ///     Ok(())
    /// # }
    /// ```
    fn max_addr(&self) -> GuestAddress {
        self.regions
            .iter()
            .max_by_key(|region| region.max_addr())
            .map_or(GuestAddress(0), |region| region.max_addr())
    }

    fn is_valid(&self) -> bool {
        // TODO: verify there's no intersection among regions
        true
    }

    fn address_in_range(&self, addr: GuestAddress) -> bool {
        for region in self.regions.iter() {
            if addr >= region.min_addr() && addr < region.max_addr() {
                return true;
            }
        }
        false
    }
}

impl Bytes<GuestAddress> for GuestMemoryMmap {
    type E = Error;

    /// # Examples
    /// * Write a slice at guestaddress 0x200.
    ///
    /// ```
    /// # use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};
    /// # fn test_write_u64() -> Result<(), ()> {
    /// #   let start_addr = GuestAddress(0x1000);
    /// #   let mut gm = GuestMemoryMmap::new(&vec![(start_addr, 0x400)]).map_err(|_| ())?;
    ///     let res = gm.write(&[1,2,3,4,5], GuestAddress(0x200)).map_err(|_| ())?;
    ///     assert_eq!(5, res);
    ///     Ok(())
    /// # }
    /// ```
    fn write(&self, buf: &[u8], addr: GuestAddress) -> Result<usize> {
        self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() as GuestAddressValue {
                    return Err(Error::InvalidBackendOffset);
                }
                region.write(&buf[offset as usize..], caddr)
            },
        )
    }

    /// # Examples
    /// * Read a slice of length 16 at guestaddress 0x200.
    ///
    /// ```
    /// # use vm_memory::{Bytes, GuestAddress, GuestMemoryMmap};
    /// # fn test_write_u64() -> Result<(), ()> {
    /// #   let start_addr = GuestAddress(0x1000);
    /// #   let mut gm = GuestMemoryMmap::new(&vec![(start_addr, 0x400)]).map_err(|_| ())?;
    ///     let buf = &mut [0u8; 16];
    ///     let res = gm.read(buf, GuestAddress(0x200)).map_err(|_| ())?;
    ///     assert_eq!(16, res);
    ///     Ok(())
    /// # }
    /// ```
    fn read(&self, buf: &mut [u8], addr: GuestAddress) -> Result<usize> {
        self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() as GuestAddressValue {
                    return Err(Error::InvalidBackendOffset);
                }
                region.read(&mut buf[offset as usize..], caddr)
            },
        )
    }

    fn write_slice(&self, buf: &[u8], addr: GuestAddress) -> Result<()> {
        let res = self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() as GuestAddressValue {
                    return Err(Error::InvalidBackendOffset);
                }
                region.write(&buf[offset as usize..], caddr)
            },
        )?;
        if res != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len() as GuestAddressValue,
                completed: res as GuestAddressValue,
            });
        }
        Ok(())
    }

    fn read_slice(&self, buf: &mut [u8], addr: GuestAddress) -> Result<()> {
        let res = self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() as GuestAddressValue {
                    return Err(Error::InvalidBackendOffset);
                }
                region.read(&mut buf[offset as usize..], caddr)
            },
        )?;
        if res != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len() as GuestAddressValue,
                completed: res as GuestAddressValue,
            });
        }
        Ok(())
    }

    /// # Examples
    ///
    /// * Read bytes from /dev/urandom
    ///
    /// ```
    /// # use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # fn test_read_random() -> Result<u32, ()> {
    /// #     let start_addr = GuestAddress(0x1000);
    /// #     let gm = GuestMemoryMmap::new(&vec![(start_addr, 0x400)]).map_err(|_| ())?;
    ///       let mut file = File::open(Path::new("/dev/urandom")).map_err(|_| ())?;
    ///       let addr = GuestAddress(0x1010);
    ///       gm.write_from_stream(addr, &mut file, 128).map_err(|_| ())?;
    ///       let read_addr = addr.checked_add(8).ok_or(())?;
    ///       let rand_val: u32 = gm.read_obj(read_addr).map_err(|_| ())?;
    /// #     Ok(rand_val)
    /// # }
    /// ```
    fn write_from_stream<F>(&self, addr: GuestAddress, src: &mut F, count: usize) -> Result<()>
    where
        F: Read,
    {
        let res = self.try_access(count, addr, |offset, cnt, caddr, region| -> Result<usize> {
            // Something bad happened...
            if offset >= count as GuestAddressValue {
                return Err(Error::InvalidBackendOffset);
            }
            // This is safe cauase the `caddr` is within the `region`.
            let start = caddr.unchecked_offset_from(region.min_addr()) as usize;
            let cap = region.max_addr().unchecked_offset_from(caddr) as usize;
            let len = std::cmp::min(cap, cnt);
            let end = start + len;
            let dst = unsafe { &mut region.as_mut_slice()[start..end] };
            src.read_exact(dst).map_err(Error::IOError)?;
            Ok(len)
        })?;
        if res != count {
            return Err(Error::PartialBuffer {
                expected: count as GuestAddressValue,
                completed: res as GuestAddressValue,
            });
        }
        Ok(())
    }

    /// Reads data from the region to a writable object.
    ///
    /// # Examples
    ///
    /// * Write 128 bytes to /dev/null
    ///
    /// ```
    /// # use vm_memory::{Address, Bytes, GuestAddress, GuestMemoryMmap};
    /// # use std::fs::File;
    /// # use std::path::Path;
    /// # fn test_write_null() -> Result<(), ()> {
    /// #     let start_addr = GuestAddress(0x1000);
    /// #     let gm = GuestMemoryMmap::new(&vec![(start_addr, 0x400)]).map_err(|_| ())?;
    ///       let mut file = File::open(Path::new("/dev/null")).map_err(|_| ())?;
    ///       gm.read_into_stream(start_addr, &mut file, 128).map_err(|_| ())?;
    /// #     Ok(())
    /// # }
    /// ```
    fn read_into_stream<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<()>
    where
        F: Write,
    {
        let res = self.try_access(count, addr, |offset, cnt, caddr, region| -> Result<usize> {
            // Something bad happened...
            if offset >= count as GuestAddressValue {
                return Err(Error::InvalidBackendOffset);
            }
            // This is safe cauase the `caddr` is within the `region`.
            let start = caddr.unchecked_offset_from(region.min_addr()) as usize;
            let cap = region.max_addr().unchecked_offset_from(caddr) as usize;
            let len = std::cmp::min(cap, cnt);
            let end = start + len;
            let src = unsafe { &region.as_slice()[start..end] };
            // It is safe to read from volatile memory. Accessing the guest
            // memory as a slice is OK because nothing assumes another thread
            // won't change what is loaded.
            dst.write_all(src).map_err(Error::IOError)?;
            Ok(len)
        })?;
        if res != count {
            return Err(Error::PartialBuffer {
                expected: count as GuestAddressValue,
                completed: res as GuestAddressValue,
            });
        }
        Ok(())
    }
}

impl AddressSpace<GuestAddress, Error> for GuestMemoryMmap {
    type T = GuestRegionMmap;

    fn num_regions(&self) -> usize {
        self.regions.len()
    }

    fn find_region(&self, addr: GuestAddress) -> Option<&Self::T> {
        for region in self.regions.iter() {
            if addr >= region.min_addr() && addr < region.max_addr() {
                return Some(region);
            }
        }
        None
    }

    fn with_regions<F>(&self, cb: F) -> Result<()>
    where
        F: Fn(usize, &Self::T) -> Result<()>,
    {
        for (index, region) in self.regions.iter().enumerate() {
            cb(index, region)?;
        }
        Ok(())
    }

    fn with_regions_mut<F>(&self, mut cb: F) -> Result<()>
    where
        F: FnMut(usize, &Self::T) -> Result<()>,
    {
        for (index, region) in self.regions.iter().enumerate() {
            cb(index, region)?;
        }
        Ok(())
    }
}

impl GuestMemory for GuestMemoryMmap {}

#[cfg(test)]
mod tests {
    extern crate tempfile;

    use self::tempfile::tempfile;
    use super::*;
    use std::fs::File;
    use std::mem;
    use std::os::unix::io::FromRawFd;
    use std::path::Path;

    use Bytes;

    #[test]
    fn basic_map() {
        let m = MmapRegion::new(1024).unwrap();
        assert_eq!(1024, m.len());
    }

    #[test]
    fn map_invalid_size() {
        let e = MmapRegion::new(0).unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::EINVAL));
    }

    #[test]
    fn map_invalid_fd() {
        let fd = unsafe { std::fs::File::from_raw_fd(-1) };
        let e = MmapRegion::from_fd(&fd, 1024, 0).unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::EBADF));
    }

    #[test]
    fn slice_len() {
        let m = MmapRegion::new(5).unwrap();
        let s = m.get_slice(2, 3).unwrap();
        assert_eq!(s.len(), 3);
    }

    #[test]
    fn slice_addr() {
        let m = MmapRegion::new(5).unwrap();
        let s = m.get_slice(2, 3).unwrap();
        assert_eq!(s.as_ptr(), unsafe { m.as_ptr().offset(2) });
    }

    #[test]
    fn slice_store() {
        let m = MmapRegion::new(5).unwrap();
        let r = m.get_ref(2).unwrap();
        r.store(9u16);
        assert_eq!(m.read_obj::<u16>(MmapAddress(2)).unwrap(), 9);
    }

    #[test]
    fn slice_overflow_error() {
        let m = MmapRegion::new(5).unwrap();
        let res = m.get_slice(std::usize::MAX, 3).unwrap_err();
        assert_eq!(
            res,
            VolatileMemoryError::Overflow {
                base: std::usize::MAX,
                offset: 3,
            }
        );
    }

    #[test]
    fn slice_oob_error() {
        let m = MmapRegion::new(5).unwrap();
        let res = m.get_slice(3, 3).unwrap_err();
        assert_eq!(res, VolatileMemoryError::OutOfBounds { addr: 6 });
    }

    #[test]
    fn test_write_past_end() {
        let m = MmapRegion::new(5).unwrap();
        let res = m.write(&[1, 2, 3, 4, 5, 6], MmapAddress(0));
        assert!(res.is_ok());
        assert_eq!(res.unwrap(), 5);
    }

    #[test]
    fn slice_read_and_write() {
        let mem_map = MmapRegion::new(5).unwrap();
        let sample_buf = [1, 2, 3];
        assert!(mem_map.write(&sample_buf, MmapAddress(5)).is_err());
        assert!(mem_map.write(&sample_buf, MmapAddress(2)).is_ok());
        let mut buf = [0u8; 3];
        assert!(mem_map.read(&mut buf, MmapAddress(5)).is_err());
        assert!(mem_map.read_slice(&mut buf, MmapAddress(2)).is_ok());
        assert_eq!(buf, sample_buf);
    }

    #[test]
    fn obj_read_and_write() {
        let mem_map = MmapRegion::new(5).unwrap();
        assert!(mem_map.write_obj(55u16, MmapAddress(4)).is_err());
        assert!(mem_map
            .write_obj(55u16, MmapAddress(core::usize::MAX))
            .is_err());
        assert!(mem_map.write_obj(55u16, MmapAddress(2)).is_ok());
        assert_eq!(mem_map.read_obj::<u16>(MmapAddress(2)).unwrap(), 55u16);
        assert!(mem_map.read_obj::<u16>(MmapAddress(4)).is_err());
        assert!(mem_map
            .read_obj::<u16>(MmapAddress(core::usize::MAX))
            .is_err());
    }

    #[test]
    fn mem_read_and_write() {
        let mem_map = MmapRegion::new(5).unwrap();
        assert!(mem_map.write_obj(!0u32, MmapAddress(1)).is_ok());
        let mut file = File::open(Path::new("/dev/zero")).unwrap();
        assert!(mem_map
            .write_from_stream(MmapAddress(2), &mut file, mem::size_of::<u32>())
            .is_err());
        assert!(mem_map
            .write_from_stream(
                MmapAddress(core::usize::MAX),
                &mut file,
                mem::size_of::<u32>()
            )
            .is_err());

        assert!(mem_map
            .write_from_stream(MmapAddress(1), &mut file, mem::size_of::<u32>())
            .is_ok());

        let mut f = tempfile().unwrap();
        assert!(mem_map
            .write_from_stream(MmapAddress(1), &mut f, mem::size_of::<u32>())
            .is_err());
        format!(
            "{:?}",
            mem_map.write_from_stream(MmapAddress(1), &mut f, mem::size_of::<u32>())
        );

        assert_eq!(mem_map.read_obj::<u32>(MmapAddress(1)).unwrap(), 0);

        let mut sink = Vec::new();
        assert!(mem_map
            .read_into_stream(MmapAddress(1), &mut sink, mem::size_of::<u32>())
            .is_ok());
        assert!(mem_map
            .read_into_stream(MmapAddress(2), &mut sink, mem::size_of::<u32>())
            .is_err());
        assert!(mem_map
            .read_into_stream(
                MmapAddress(core::usize::MAX),
                &mut sink,
                mem::size_of::<u32>()
            )
            .is_err());
        format!(
            "{:?}",
            mem_map.read_into_stream(MmapAddress(2), &mut sink, mem::size_of::<u32>())
        );
        assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
    }

    #[test]
    fn mapped_file_read() {
        let mut f = tempfile().unwrap();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert!(f.write_all(sample_buf).is_ok());

        let mem_map = MmapRegion::from_fd(&f, sample_buf.len(), 0).unwrap();
        let buf = &mut [0u8; 16];
        assert_eq!(mem_map.read(buf, MmapAddress(0)).unwrap(), sample_buf.len());
        assert_eq!(buf[0..sample_buf.len()], sample_buf[..]);
    }

    #[test]
    fn test_regions() {
        // No regions provided should return error.
        assert_eq!(
            format!("{:?}", GuestMemoryMmap::new(&vec![]).err().unwrap()),
            format!("{:?}", MmapError::NoMemoryRegion)
        );

        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x800);
        let guest_mem =
            GuestMemoryMmap::new(&vec![(start_addr1, 0x400), (start_addr2, 0x400)]).unwrap();
        assert_eq!(guest_mem.num_regions(), 2);
        assert!(guest_mem.address_in_range(GuestAddress(0x200)));
        assert!(!guest_mem.address_in_range(GuestAddress(0x600)));
        assert!(guest_mem.address_in_range(GuestAddress(0xa00)));
        let end_addr = GuestAddress(0xc00);
        assert!(!guest_mem.address_in_range(end_addr));
        assert_eq!(guest_mem.max_addr(), end_addr);
        assert!(guest_mem.checked_offset(start_addr1, 0x900).is_some());
        assert!(guest_mem.checked_offset(start_addr1, 0x700).is_none());
        assert!(guest_mem.checked_offset(start_addr2, 0xc00).is_none());
    }

    #[test]
    fn overlap_memory() {
        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        let res = GuestMemoryMmap::new(&vec![(start_addr1, 0x2000), (start_addr2, 0x2000)]);
        assert_eq!(
            format!("{:?}", res.err().unwrap()),
            format!("{:?}", MmapError::MemoryRegionOverlap)
        );
    }

    #[test]
    fn test_read_u64() {
        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        let bad_addr = GuestAddress(0x2001);
        let bad_addr2 = GuestAddress(0x1ffc);
        let max_addr = GuestAddress(0x2000);

        let gm = GuestMemoryMmap::new(&vec![(start_addr1, 0x1000), (start_addr2, 0x1000)]).unwrap();

        let val1: u64 = 0xaa55aa55aa55aa55;
        let val2: u64 = 0x55aa55aa55aa55aa;
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

    #[test]
    fn write_and_read() {
        let mut start_addr = GuestAddress(0x1000);
        let gm = GuestMemoryMmap::new(&vec![(start_addr, 0x400)]).unwrap();
        let sample_buf = &[1, 2, 3, 4, 5];

        assert_eq!(gm.write(sample_buf, start_addr).unwrap(), 5);

        let buf = &mut [0u8; 5];
        assert_eq!(gm.read(buf, start_addr).unwrap(), 5);
        assert_eq!(buf, sample_buf);

        start_addr = GuestAddress(0x13ff);
        assert_eq!(gm.write(sample_buf, start_addr).unwrap(), 1);
        assert_eq!(gm.read(buf, start_addr).unwrap(), 1);
        assert_eq!(buf[0], sample_buf[0]);
    }

    #[test]
    fn read_to_and_write_from_mem() {
        let gm = GuestMemoryMmap::new(&vec![(GuestAddress(0x1000), 0x400)]).unwrap();
        let addr = GuestAddress(0x1010);
        gm.write_obj(!0u32, addr).unwrap();
        gm.write_from_stream(
            addr,
            &mut File::open(Path::new("/dev/zero")).unwrap(),
            mem::size_of::<u32>(),
        )
        .unwrap();
        let value: u32 = gm.read_obj(addr).unwrap();
        assert_eq!(value, 0);

        let mut sink = Vec::new();
        gm.read_into_stream(addr, &mut sink, mem::size_of::<u32>())
            .unwrap();
        assert_eq!(sink, vec![0; mem::size_of::<u32>()]);
    }

    #[test]
    fn create_vec_with_regions() {
        let region_size = 0x400;
        let regions = vec![
            (GuestAddress(0x0), region_size),
            (GuestAddress(0x1000), region_size),
        ];
        let mut iterated_regions = Vec::new();
        let gm = GuestMemoryMmap::new(&regions).unwrap();

        let res: Result<()> = gm.with_regions(|_, region| {
            assert_eq!(region.len(), region_size as GuestAddressValue);
            Ok(())
        });
        assert!(res.is_ok());

        let res: Result<()> = gm.with_regions_mut(|_, region| {
            iterated_regions.push((region.min_addr(), region.len() as usize));
            Ok(())
        });
        assert!(res.is_ok());
        assert_eq!(regions, iterated_regions);
        assert_eq!(gm.clone().regions[0].guest_base, regions[0].0);
        assert_eq!(gm.clone().regions[1].guest_base, regions[1].0);
    }

    #[test]
    fn test_access_cross_boundary() {
        let start_addr1 = GuestAddress(0x0);
        let start_addr2 = GuestAddress(0x1000);
        let gm = GuestMemoryMmap::new(&vec![(start_addr1, 0x1000), (start_addr2, 0x1000)]).unwrap();
        let sample_buf = &[1, 2, 3, 4, 5];
        assert_eq!(gm.write(sample_buf, GuestAddress(0xffc)).unwrap(), 5);
        let buf = &mut [0u8; 5];
        assert_eq!(gm.read(buf, GuestAddress(0xffc)).unwrap(), 5);
        assert_eq!(buf, sample_buf);
    }
}
