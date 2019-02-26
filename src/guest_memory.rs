// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! Traits to track and access memory regions that are mapped to a virtual machine.
//!
//! The GuestMemoryRegion trait is used to represent a continuous region of guest's physical memory.
//! And the GuestMemory trait is used to represent a collection of GuestMemoryRegion objects.
//! The main responsibilities of the GuestMemory trait are:
//! - hide the detail of accessing guest's physical address.
//! - map a request address to a GuestMemoryRegion object and relay the request to it.
//! - handle cases where an access request spanning two or more GuestMemoryRegion objects.

use address::{Address, AddressValue};
use std::fmt::{self, Display};
use std::io;
use std::ops::{BitAnd, BitOr};
use Bytes;

/// Errors associated with handling guest memory accesses.
#[allow(missing_docs)]
#[derive(Debug)]
pub enum Error {
    /// Failure in finding a guest address in any memory regions mapped by this guest.
    InvalidGuestAddress(GuestAddress),
    /// Couldn't read/write from the given source.
    IOError(io::Error),
    /// Incomplete read or write
    PartialBuffer {
        expected: GuestAddressValue,
        completed: GuestAddressValue,
    },
    /// Requested backend address is out of range.
    InvalidBackendAddress,
    /// Requested offset is out of range.
    InvalidBackendOffset,
}

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

/// Type of the raw value stored in a GuestAddress object.
pub type GuestAddressValue = <GuestAddress as AddressValue>::V;

/// Type to encode offset in the guest physical address space.
pub type GuestAddressOffset = <GuestAddress as AddressValue>::V;

/// Represents a continuous region of guest physical memory.
pub trait GuestMemoryRegion: Bytes<GuestAddress, E = Error> {}

/// Represents a collection of GuestMemoryRegion objects.
///
/// Container for a set of GuestMemoryRegion objects and methods to access those objects.
///
/// The main responsibilities of the GuestMemory trait are:
/// - hide the detail of accessing guest's physical address.
/// - map a request address to a GuestMemoryRegion object and relay the request to it.
/// - handle cases where an access request spanning two or more GuestMemoryRegion objects.
///
/// Note: all regions in a GuestMemory object must not intersect with each other.
pub trait GuestMemory {
    /// Type of objects hosted by the address space.
    type R: Bytes<GuestAddress, E = Error>;

    /// Returns the number of regions in the collection.
    fn num_regions(&self) -> usize;

    /// Return the region containing the specified address or None.
    fn find_region(&self, GuestAddress) -> Option<&Self::R>;

    /// Perform the specified action on each region.
    /// It only walks children of current region and do not step into sub regions.
    fn with_regions<F>(&self, cb: F) -> Result<(), Error>
    where
        F: Fn(usize, &Self::R) -> Result<(), Error>;

    /// Perform the specified action on each region mutably.
    /// It only walks children of current region and do not step into sub regions.
    fn with_regions_mut<F>(&self, cb: F) -> Result<(), Error>
    where
        F: FnMut(usize, &Self::R) -> Result<(), Error>;

    /// Invoke callback `f` to handle data in the address range [addr, addr + count).
    ///
    /// The address range [addr, addr + count) may span more than one GuestMemoryRegion objects, or
    /// even has holes within it. So try_access() invokes the callback 'f' for each GuestMemoryRegion
    /// object involved and returns:
    /// - error code returned by the callback 'f'
    /// - size of data already handled when encountering the first hole
    /// - size of data already handled when the whole range has been handled
    fn try_access<F>(&self, count: usize, addr: GuestAddress, mut f: F) -> Result<usize, Error>
    where
        F: FnMut(GuestAddressOffset, usize, GuestAddress, &Self::R) -> Result<usize, Error>,
    {
        let mut cur = addr;
        let mut total = 0;
        while total < count {
            if let Some(region) = self.find_region(cur) {
                match f(total as GuestAddressOffset, count - total, cur, region) {
                    // no more data
                    Ok(0) => break,
                    // made some progress
                    Ok(len) => {
                        cur = cur
                            .checked_add(len as GuestAddressValue)
                            .ok_or_else(|| Error::InvalidGuestAddress(cur))?;
                        total += len;
                    }
                    // error happened
                    e => return e,
                }
            } else {
                // no region for address found
                break;
            }
        }
        if total == 0 {
            Err(Error::InvalidGuestAddress(addr))
        } else {
            Ok(total)
        }
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
