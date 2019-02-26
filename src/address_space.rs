// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! Traits to access content in memory-alike byte-addressable address spaces.
//!
//! Four abstractions are defined to access content within an address space, which are:
//! - AddressValue: stores the raw value of an address. Typically u32, u64 or usize is used to
//! store the raw value. But pointers, such as *u8, can't be used because it doesn't implement
//! the Add and Sub traits.
//! - Address: encapsulates an AddressValue object and defines methods to access it.
//! - AddressRegion: defines methods to access content within an address region. An address region
//! may be continuous or it may have holes within the range [min_addr, max_addr) managed by it.
//! - AddressSpace: extends AddressRegion to build hierarchy architecture. An AnddressSpace object
//! contains a group of non-intersected AddressRegion objects, and the contained AddressRegion
//! object may be another AddressSpace object. By this way, a hierarchy tree may be built to
//! describe an complex address space structure.
//!
//! To make the abstraction as generic as possible, all the core traits only define methods to
//! access the address space are defined here, and they never define methods to manage (create,
//! delete, insert, remove etc) address spaces.  By this way, the address space consumers
//! (virtio device drivers, vhost drivers and boot loaders etc) may be decoupled from the address
//! space provider (typically a hypervisor).

use std::cmp::{Eq, Ord, PartialEq, PartialOrd};
use std::ops::{Add, BitAnd, BitOr, Sub};

/// Simple helper trait to store a raw address value.
pub trait AddressValue {
    /// Type of the address raw value.
    type V: Copy
        + PartialEq
        + Eq
        + Ord
        + Add<Output = Self::V>
        + Sub<Output = Self::V>
        + BitAnd<Output = Self::V>
        + BitOr<Output = Self::V>;
}

/// Trait for address objects, define methods to access and manipulate it.
///
/// To simplify the design and implementation, assume the same raw data type could be used to store
/// address, size and offset for an address space. So the Address trait will be used for address,
/// size and offset. To ease code review, aliases may be defined though.
pub trait Address:
    AddressValue
    + Sized
    + Default
    + Clone
    + Copy
    + Eq
    + PartialEq
    + Ord
    + PartialOrd
    + BitAnd<<Self as AddressValue>::V, Output = Self>
    + BitOr<<Self as AddressValue>::V, Output = Self>
{
    /// Create an address from the raw value.
    fn new(Self::V) -> Self;

    /// Get the raw value of an address.
    fn raw_value(&self) -> Self::V;

    /// Returns the bitwise and of the address with the given mask.
    fn mask(&self, mask: Self::V) -> Self {
        Self::new(self.raw_value() & mask)
    }

    /// Returns the offset from this address to the given base address and None if there is
    /// underflow.
    fn checked_offset_from(&self, base: Self) -> Option<Self::V>;

    /// Returns the offset from this address to the given base address.
    /// Only use this when `base` is guaranteed not to overflow.
    fn unchecked_offset_from(&self, base: Self) -> Self::V {
        self.raw_value() - base.raw_value()
    }

    /// Returns the result of the add or None if there is overflow.
    fn checked_add(&self, other: Self::V) -> Option<Self>;

    /// Returns the result of the base address + the size.
    /// Only use this when `offset` is guaranteed not to overflow.
    fn unchecked_add(&self, offset: Self::V) -> Self;

    /// Returns the result of the subtraction or None if there is underflow.
    fn checked_sub(&self, other: Self::V) -> Option<Self>;

    /// Returns the result of the subtraction.
    /// Only use this when `other` is guaranteed not to underflow.
    fn unchecked_sub(&self, other: Self::V) -> Self;
}

#[macro_export]
macro_rules! impl_address_ops {
    ($T:ident, $V:ty) => {
        impl AddressValue for $T {
            type V = $V;
        }

        impl Address for $T {
            fn new(value: $V) -> $T {
                $T(value)
            }

            fn raw_value(&self) -> $V {
                self.0
            }

            fn checked_offset_from(&self, base: $T) -> Option<$V> {
                self.0.checked_sub(base.0)
            }

            fn checked_add(&self, other: $V) -> Option<$T> {
                self.0.checked_add(other).map($T)
            }

            fn unchecked_add(&self, offset: $V) -> $T {
                $T(self.0 + offset)
            }

            fn checked_sub(&self, other: $V) -> Option<$T> {
                self.0.checked_sub(other).map($T)
            }

            fn unchecked_sub(&self, other: $V) -> $T {
                $T(self.0 - other)
            }
        }

        impl Default for $T {
            fn default() -> $T {
                Self::new(0 as $V)
            }
        }

        impl BitAnd<$V> for $T {
            type Output = $T;

            fn bitand(self, other: $V) -> $T {
                $T(self.0 & other)
            }
        }

        impl BitOr<$V> for $T {
            type Output = $T;

            fn bitor(self, other: $V) -> $T {
                $T(self.0 | other)
            }
        }
    };
}

/// A container to host content for an address range and methods to access the content.
///
/// An address region may be continuous or may contain holes within the range
/// [min_addr(), max_addr()).
///
/// The trait provides two categories of methods to access the object:
/// - get attribute of the region: len(), min_addr(), max_addr(), is_valid(), address_in_range()
///   and checked_offset().
/// - access content: read(), write(), read_slice(), write_slice(), read_obj(), write_obj(),
/// read_from_stream(), write_to_stream().
///
/// Candidates implement this trait include:
/// - anonymous memory areas
/// - mmapped memory areas
/// - data files
/// - a proxy to access memory on remote
pub trait AddressRegion {
    /// Associated address type
    type A: Address;

    /// Associated error codes
    type E;

    /// Get size of the region, excluding possible holes.
    fn len(&self) -> <Self::A as AddressValue>::V;

    /// Get minimum (inclusive) address managed by the region.
    fn min_addr(&self) -> Self::A {
        Self::A::default()
    }

    /// Get maxixum (exclusive) address managed by the region.
    fn max_addr(&self) -> Self::A {
        Self::A::default()
    }

    /// Check whether the region is valid.
    fn is_valid(&self) -> bool {
        true
    }

    /// Check whether the address is managed by the region.
    /// The default implementation assumes the address is continuous.
    /// Address regions with holes need to provide its own implementation.
    fn address_in_range(&self, addr: Self::A) -> bool {
        addr >= self.min_addr() && addr < self.max_addr()
    }

    /// Returns the address plus the offset or None if it is out of range.
    fn checked_offset(
        &self,
        addr: Self::A,
        offset: <Self::A as AddressValue>::V,
    ) -> Option<Self::A> {
        let pos = addr.checked_add(offset)?;
        if self.address_in_range(pos) {
            return Some(pos);
        }
        None
    }
}

/// Container for a set of AddressRegion objects and methods to access those objects.
///
/// The AddressSpace trait is a subtrait of the AddressRegion trait. So an AddressSpace object
/// is itself an AddressRegion object too. That means a AddressSpace object may contain sub
/// AddressSpace objects, and thus composes a tree hierarchy to describe a complex address space.
///
/// Note: all objects in an AddressSpace object must not intersect with each other.
pub trait AddressSpace<A: Address, E>: AddressRegion<A = A, E = E> {
    /// Type of objects hosted by the address space.
    type T: AddressRegion<A = A, E = E>;

    /// Returns the number of regions in the collection.
    fn num_regions(&self) -> usize;

    /// Return the region containing the specified address or None.
    fn find_region(&self, A) -> Option<&Self::T>;

    /// Perform the specified action on each region.
    /// It only walks children of current region and do not step into sub regions.
    fn with_regions<F>(&self, cb: F) -> Result<(), E>
    where
        F: Fn(usize, &Self::T) -> Result<(), E>;

    /// Perform the specified action on each region mutably.
    /// It only walks children of current region and do not step into sub regions.
    fn with_regions_mut<F>(&self, cb: F) -> Result<(), E>
    where
        F: FnMut(usize, &Self::T) -> Result<(), E>;
}
