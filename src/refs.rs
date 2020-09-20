//! This module provides two abstractions that allow borrowing a `GuestMemory` locations, instead
//! of looking them up each time. `Ref` does that for a single `T: ByteValued` object, whereas
//! `ArrayRef` is essentially (as the name suggests) an array of `Ref`s. All accesses done
//! through these objects are inherently aligned.

use std::marker::PhantomData;
use std::mem::size_of;
use std::ptr;

use crate::access::{AutoBytes, HostRegion};
use crate::ByteValued;
use crate::GuestMemoryError;

/// Alias for the result of operations defined in this module.
pub type Result<T> = std::result::Result<T, GuestMemoryError>;

/// Represents a `T: ByteValued` located in guest memory.
#[derive(Debug)]
pub struct Ref<'a, T: ByteValued> {
    addr: *mut u8,
    phantom: PhantomData<&'a T>,
}

impl<T: ByteValued> Ref<'_, T> {
    /// Create a new `Ref` object.
    ///
    /// # Safety
    ///
    /// `addr` must be properly aligned with respect to `T` and valid for reads/writes.
    pub unsafe fn new(addr: *mut u8) -> Self {
        Ref {
            addr,
            phantom: PhantomData,
        }
    }

    /// Return the inner pointer to host memory.
    pub fn as_ptr(&self) -> *mut T {
        self.addr as *mut T
    }

    /// Read the value of the associated object.
    pub fn read(&self) -> T {
        // Safe because `addr` is valid for reads and properly aligned.
        unsafe { ptr::read_volatile(self.as_ptr()) }
    }

    /// Write a new value to the associated object.
    pub fn write(&self, value: T) {
        // Safe because `addr` is valid for writes and properly aligned.
        unsafe { ptr::write_volatile(self.as_ptr(), value) }
    }
}

/// Represents an array of `T: ByteValued` located in guest memory.
#[derive(Debug)]
pub struct ArrayRef<'a, T: ByteValued> {
    addr: *mut u8,
    len: usize,
    phantom: PhantomData<&'a T>,
}

impl<'a, T: ByteValued> ArrayRef<'a, T> {
    /// Create a new `ArrayRef` object.
    ///
    /// # Safety
    ///
    /// `addr` must be properly aligned with respect to `T` and valid for reads/writes for the
    /// entire length of the array.
    pub unsafe fn new(addr: *mut u8, len: usize) -> Self {
        ArrayRef {
            addr,
            len,
            phantom: PhantomData,
        }
    }

    /// Return the inner pointer to host memory.
    pub fn as_ptr(&self) -> *mut T {
        self.addr as *mut T
    }

    /// Return the number of elements in the array.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Return the `Ref` object for the specified `index`.
    pub fn at(&self, index: usize) -> Result<Ref<'a, T>> {
        if index >= self.len {
            return Err(GuestMemoryError::InvalidAccess);
        }

        // We don't have to check for overflow because the index is within bounds.
        let ref_addr = self.addr as usize + (index * size_of::<T>());

        // Safe because `T` is `ByteValued`, and the address is properly aligned and
        // within array bounds.
        unsafe { Ok(Ref::new(ref_addr as *mut u8)) }
    }
}

// `ArrayRef<u8>` can be seen as an opaque region of host process memory.
impl HostRegion for ArrayRef<'_, u8> {
    fn as_ptr(&self) -> *mut u8 {
        ArrayRef::as_ptr(self)
    }
    fn len(&self) -> usize {
        ArrayRef::len(self)
    }
}

// This provides an automatic `Bytes` implementation for `ArrayRef<u8>` based on
// `CheckAccess<usize>` (itself automatically implemented because `ArrayRef<u8>: HostRegion`.
impl AutoBytes<usize> for ArrayRef<'_, u8> {}
