//! This module provides two abstractions that allow borrowing a `GuestMemory` locations, instead
//! of looking them up each time. `Ref` does that for a single `T: ByteValued` object, whereas
//! `ArrayRef` is essentially (as the name suggests) an array of `Ref`s. All accesses done
//! through these objects are inherently aligned.

use std::marker::PhantomData;
use std::mem::{align_of, size_of};
use std::ptr;
use std::slice;
use std::sync::atomic::{AtomicU16, AtomicU32, AtomicU64, AtomicU8, Ordering};

use crate::access::{AutoBytes, HostRegion};
use crate::bytes::{AtomicAccess, AtomicInteger};
use crate::{ByteValued, GuestMemoryError};

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

// Adds methods for atomic access to the inner value.
impl<T: AtomicAccess> Ref<'_, T> {
    // This is just a helper method for now. The current public facing a atomic functionality
    // is exposed via  `store` and `load`. It's TBD what the best way of exposing other atomic
    // operations  (fetch+arithmetic, swap, etc).
    fn atomic_ref<I: AtomicInteger>(&self) -> &I {
        assert_eq!(size_of::<T>(), align_of::<T>());
        assert_eq!(size_of::<T>(), size_of::<I>());
        // Safe because ...
        unsafe { slice::from_raw_parts(self.addr as *const I, 1) }
            .first()
            .unwrap()
    }

    /// Perform an atomic load from the inner memory location.
    pub fn load(&self, order: Ordering) -> T {
        // This invariant must hold for every type that implements `AtomicAccess`.
        assert_eq!(size_of::<T>(), align_of::<T>());

        // The unwrap cannot fail because the types have the same size.
        match size_of::<T>() {
            1 => self.atomic_ref::<AtomicU8>().load(order).transmute(),
            2 => self.atomic_ref::<AtomicU16>().load(order).transmute(),
            4 => self.atomic_ref::<AtomicU32>().load(order).transmute(),
            #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
            8 => self.atomic_ref::<AtomicU64>().load(order).transmute(),
            _ => unreachable!(),
        }
        .unwrap()
    }

    /// Perform an atomic store at the inner memory location.
    pub fn store(&self, value: T, order: Ordering) {
        // This invariant must hold for every type that implements `AtomicAccess`.
        assert_eq!(size_of::<T>(), align_of::<T>());

        // The unwraps cannot fail because the types have the same size.
        match size_of::<T>() {
            1 => self
                .atomic_ref::<AtomicU8>()
                .store(value.transmute().unwrap(), order),
            2 => self
                .atomic_ref::<AtomicU16>()
                .store(value.transmute().unwrap(), order),
            4 => self
                .atomic_ref::<AtomicU32>()
                .store(value.transmute().unwrap(), order),
            #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
            8 => self
                .atomic_ref::<AtomicU64>()
                .store(value.transmute().unwrap(), order),
            _ => unreachable!(),
        }
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
