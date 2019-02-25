// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! Traits to track and access guest's physical memory.
//!
//! To make the abstraction as generic as possible, all the core traits defined here only
//! define methods to access the address space are defined here, and they never define
//! methods to manage (create, delete, insert, remove etc) address spaces. By this way,
//! the address space consumers (virtio device drivers, vhost drivers and boot loaders
//! etc) may be decoupled from the address space provider (typically a hypervisor).
//!
//! Traits and Structs
//! - GuestAddress: represents a guest physical address (GPA).
//! - MemoryRegionAddress: represents an offset inside a region.
//! - GuestMemoryRegion: represent a continuous region of guest's physical memory.
//! - GuestMemory:  represent a collection of GuestMemoryRegion objects. The main responsibilities
//!   of the GuestMemory trait are:
//!     - hide the detail of accessing guest's physical address.
//!     - map a request address to a GuestMemoryRegion object and relay the request to it.
//!     - handle cases where an access request spanning two or more GuestMemoryRegion objects.

use std::convert::From;
use std::fmt::{self, Display};
use std::io::{self, Read, Write};
use std::ops::{BitAnd, BitOr};

use super::{Address, AddressValue, Bytes};
use volatile_memory;

static MAX_ACCESS_CHUNK: usize = 4096;

/// Errors associated with handling guest memory accesses.
#[allow(missing_docs)]
#[derive(Debug)]
pub enum Error {
    /// Failure in finding a guest address in any memory regions mapped by this guest.
    InvalidGuestAddress(GuestAddress),
    /// Couldn't read/write from the given source.
    IOError(io::Error),
    /// Incomplete read or write
    PartialBuffer { expected: usize, completed: usize },
    /// Requested backend address is out of range.
    InvalidBackendAddress,
    /// Requested offset is out of range.
    InvalidBackendOffset,
}

impl From<volatile_memory::Error> for Error {
    fn from(e: volatile_memory::Error) -> Self {
        match e {
            volatile_memory::Error::OutOfBounds { .. } => Error::InvalidBackendAddress,
            volatile_memory::Error::Overflow { .. } => Error::InvalidBackendAddress,
            volatile_memory::Error::IOError(e) => Error::IOError(e),
            volatile_memory::Error::PartialBuffer {
                expected,
                completed,
            } => Error::PartialBuffer {
                expected,
                completed,
            },
        }
    }
}

/// Result of guest memory operations
pub type Result<T> = std::result::Result<T, Error>;

impl std::error::Error for Error {}

impl Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Guest memory error: ")?;
        match self {
            Error::InvalidGuestAddress(addr) => {
                write!(f, "invalid guest address {}", addr.raw_value())
            }
            Error::IOError(error) => write!(f, "{}", error),
            Error::PartialBuffer {
                expected,
                completed,
            } => write!(
                f,
                "only used {} bytes in {} long buffer",
                completed, expected,
            ),
            Error::InvalidBackendAddress => write!(f, "invalid backend address"),
            Error::InvalidBackendOffset => write!(f, "invalid backend offset"),
        }
    }
}

/// Represents a guest physical address (GPA).
///
/// Notes:
/// - On ARM64, a 32-bit hypervisor may be used to support a 64-bit guest. For simplicity,
/// u64 is used to store the the raw value no matter if the guest a 32-bit or 64-bit virtual
/// machine.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct GuestAddress(pub u64);
impl_address_ops!(GuestAddress, u64);

/// Represents an offset inside a region.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub struct MemoryRegionAddress(pub u64);
impl_address_ops!(MemoryRegionAddress, u64);

/// Type of the raw value stored in a GuestAddress object.
pub type GuestAddressValue = <GuestAddress as AddressValue>::V;

/// Type to encode offset in the guest physical address space.
pub type GuestAddressOffset = <GuestAddress as AddressValue>::V;

/// Represents a continuous region of guest physical memory.
#[allow(clippy::len_without_is_empty)]
pub trait GuestMemoryRegion: Bytes<MemoryRegionAddress, E = Error> {
    /// Get the size of the region.
    fn len(&self) -> GuestAddressValue;

    /// Get minimum (inclusive) address managed by the region.
    fn min_addr(&self) -> GuestAddress;

    /// Get maximum (exclusive) address managed by the region.
    fn max_addr(&self) -> GuestAddress {
        // unchecked_add is safe as the region bounds were checked when it was created.
        self.min_addr().unchecked_add(self.len())
    }

    /// Convert an absolute address into an address space (GuestMemory)
    /// to a relative address within this region, or return an error if
    /// it is out of bounds.
    fn to_region_addr(&self, addr: GuestAddress) -> Result<MemoryRegionAddress> {
        let offset = addr
            .checked_offset_from(self.min_addr())
            .ok_or_else(|| Error::InvalidGuestAddress(addr))?;
        if offset >= self.len() {
            return Err(Error::InvalidGuestAddress(addr));
        }
        Ok(MemoryRegionAddress(offset))
    }

    /// Return a slice corresponding to the data in the region; unsafe because of
    /// possible aliasing.  Return None if the region does not support slice-based
    /// access.
    unsafe fn as_slice(&self) -> Option<&[u8]> {
        None
    }

    /// Return a mutable slice corresponding to the data in the region; unsafe because of
    /// possible aliasing.  Return None if the region does not support slice-based
    /// access.
    unsafe fn as_mut_slice(&self) -> Option<&mut [u8]> {
        None
    }
}

/// Represents a container for a collection of GuestMemoryRegion objects.
///
/// The main responsibilities of the GuestMemory trait are:
/// - hide the detail of accessing guest's physical address.
/// - map a request address to a GuestMemoryRegion object and relay the request to it.
/// - handle cases where an access request spanning two or more GuestMemoryRegion objects.
///
/// Note: all regions in a GuestMemory object must not intersect with each other.
pub trait GuestMemory {
    /// Type of objects hosted by the address space.
    type R: GuestMemoryRegion;

    /// Returns the number of regions in the collection.
    fn num_regions(&self) -> usize;

    /// Return the region containing the specified address or None.
    fn find_region(&self, GuestAddress) -> Option<&Self::R>;

    /// Perform the specified action on each region.
    /// It only walks children of current region and do not step into sub regions.
    fn with_regions<F>(&self, cb: F) -> Result<()>
    where
        F: Fn(usize, &Self::R) -> Result<()>;

    /// Perform the specified action on each region mutably.
    /// It only walks children of current region and do not step into sub regions.
    fn with_regions_mut<F>(&self, cb: F) -> Result<()>
    where
        F: FnMut(usize, &Self::R) -> Result<()>;

    /// Invoke callback `f` to handle data in the address range [addr, addr + count).
    ///
    /// The address range [addr, addr + count) may span more than one GuestMemoryRegion objects, or
    /// even has holes within it. So try_access() invokes the callback 'f' for each GuestMemoryRegion
    /// object involved and returns:
    /// - error code returned by the callback 'f'
    /// - size of data already handled when encountering the first hole
    /// - size of data already handled when the whole range has been handled
    fn try_access<F>(&self, count: usize, addr: GuestAddress, mut f: F) -> Result<usize>
    where
        F: FnMut(usize, usize, MemoryRegionAddress, &Self::R) -> Result<usize>,
    {
        let mut cur = addr;
        let mut total = 0;
        while let Some(region) = self.find_region(cur) {
            let start = region.to_region_addr(cur).unwrap();
            let cap = region.len() as usize;
            let len = std::cmp::min(cap, count - total);
            match f(total, len, start, region) {
                // no more data
                Ok(0) => break,
                // made some progress
                Ok(len) => {
                    total += len;
                    if total == count {
                        break;
                    }
                    cur = match cur.overflowing_add(len as GuestAddressValue) {
                        (GuestAddress(0), _) => GuestAddress(0),
                        (result, false) => result,
                        (_, true) => panic!("guest address overflow"),
                    }
                }
                // error happened
                e => return e,
            }
        }
        if total == 0 {
            Err(Error::InvalidGuestAddress(addr))
        } else {
            Ok(total)
        }
    }
}

impl<T: GuestMemory> Bytes<GuestAddress> for T {
    type E = Error;

    fn write(&self, buf: &[u8], addr: GuestAddress) -> Result<usize> {
        self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() {
                    return Err(Error::InvalidBackendOffset);
                }
                region.write(&buf[offset as usize..], caddr)
            },
        )
    }

    fn read(&self, buf: &mut [u8], addr: GuestAddress) -> Result<usize> {
        self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() {
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
                if offset >= buf.len() {
                    return Err(Error::InvalidBackendOffset);
                }
                region.write(&buf[offset as usize..], caddr)
            },
        )?;
        if res != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len(),
                completed: res,
            });
        }
        Ok(())
    }

    fn read_slice(&self, buf: &mut [u8], addr: GuestAddress) -> Result<()> {
        let res = self.try_access(
            buf.len(),
            addr,
            |offset, _count, caddr, region| -> Result<usize> {
                if offset >= buf.len() {
                    return Err(Error::InvalidBackendOffset);
                }
                region.read(&mut buf[offset as usize..], caddr)
            },
        )?;
        if res != buf.len() {
            return Err(Error::PartialBuffer {
                expected: buf.len(),
                completed: res,
            });
        }
        Ok(())
    }

    fn write_from_stream<F>(&self, addr: GuestAddress, src: &mut F, count: usize) -> Result<()>
    where
        F: Read,
    {
        let res = self.try_access(count, addr, |offset, len, caddr, region| -> Result<usize> {
            // Something bad happened...
            if offset >= count {
                return Err(Error::InvalidBackendOffset);
            }
            if let Some(dst) = unsafe { region.as_mut_slice() } {
                // This is safe cause `start` and `len` are within the `region`.
                let start = caddr.raw_value() as usize;
                let end = start + len;
                src.read_exact(&mut dst[start..end])
                    .map_err(Error::IOError)?;
                Ok(len)
            } else {
                let len = std::cmp::min(len, MAX_ACCESS_CHUNK);
                let mut buf = vec![0u8; len].into_boxed_slice();
                src.read_exact(&mut buf[..]).map_err(Error::IOError)?;
                let bytes_written = region.write(&buf, caddr)?;
                assert_eq!(bytes_written, len);
                Ok(len)
            }
        })?;
        if res != count {
            return Err(Error::PartialBuffer {
                expected: count,
                completed: res,
            });
        }
        Ok(())
    }

    fn read_into_stream<F>(&self, addr: GuestAddress, dst: &mut F, count: usize) -> Result<()>
    where
        F: Write,
    {
        let res = self.try_access(count, addr, |offset, len, caddr, region| -> Result<usize> {
            // Something bad happened...
            if offset >= count {
                return Err(Error::InvalidBackendOffset);
            }
            if let Some(src) = unsafe { region.as_slice() } {
                // This is safe cause `start` and `len` are within the `region`.
                let start = caddr.raw_value() as usize;
                let end = start + len;
                // It is safe to read from volatile memory. Accessing the guest
                // memory as a slice is OK because nothing assumes another thread
                // won't change what is loaded.
                dst.write_all(&src[start as usize..end])
                    .map_err(Error::IOError)?;
                Ok(len)
            } else {
                let len = std::cmp::min(len, MAX_ACCESS_CHUNK);
                let mut buf = vec![0u8; len].into_boxed_slice();
                let bytes_read = region.read(&mut buf, caddr)?;
                assert_eq!(bytes_read, len);
                dst.write_all(&buf).map_err(Error::IOError)?;
                Ok(len)
            }
        })?;
        if res != count {
            return Err(Error::PartialBuffer {
                expected: count,
                completed: res,
            });
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offset_from() {
        let base = GuestAddress(0x100);
        let addr = GuestAddress(0x150);
        assert_eq!(addr.unchecked_offset_from(base), 0x50u64);
        assert_eq!(addr.checked_offset_from(base), Some(0x50u64));
        assert_eq!(base.checked_offset_from(addr), None);
    }

    #[test]
    fn equals() {
        let a = GuestAddress(0x300);
        let b = GuestAddress(0x300);
        let c = GuestAddress(0x301);
        assert_eq!(a, GuestAddress(a.raw_value()));
        assert_eq!(a, b);
        assert_eq!(b, a);
        assert_ne!(a, c);
        assert_ne!(c, a);
    }

    #[test]
    fn cmp() {
        let a = GuestAddress(0x300);
        let b = GuestAddress(0x301);
        assert!(a < b);
        assert!(b > a);
        assert!(!(a < a));
    }

    #[test]
    fn mask() {
        let a = GuestAddress(0x5050);
        assert_eq!(GuestAddress(0x5000), a & 0xff00u64);
        assert_eq!(GuestAddress(0x5000), a.mask(0xff00u64));
        assert_eq!(GuestAddress(0x5055), a | 0x0005u64);
    }

    #[test]
    fn add_sub() {
        let a = GuestAddress(0x50);
        let b = GuestAddress(0x60);
        assert_eq!(Some(GuestAddress(0xb0)), a.checked_add(0x60));
        assert_eq!(0x10, b.unchecked_offset_from(a));
    }

    #[test]
    fn checked_add_overflow() {
        let a = GuestAddress(0xffffffffffffff55);
        assert_eq!(Some(GuestAddress(0xffffffffffffff57)), a.checked_add(2));
        assert!(a.checked_add(0xf0).is_none());
    }

    #[test]
    fn checked_sub_underflow() {
        let a = GuestAddress(0xff);
        assert_eq!(Some(GuestAddress(0x0f)), a.checked_sub(0xf0));
        assert!(a.checked_sub(0xffff).is_none());
    }
}
