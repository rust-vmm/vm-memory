//! Provides abstractions (often effectively zero-cost) for modeling the alignment
//! of addresses by leveraging the type system.

use std::convert::TryFrom;
use std::marker::PhantomData;
use std::mem::align_of;
use std::result;

use crate::Address;

/// Errors related to operations which involve aligned addresses.
#[derive(Debug, PartialEq)]
pub enum AlignmentError {
    /// Misalignment was detected during a conversion.
    Misaligned,
    /// An overflow occurred while computing address values.
    Overflow,
}

// Check whether `addr` is aligned with respect to `T`.
fn check_addr_aligned<Addr: Address, T>(addr: Addr) -> result::Result<(), AlignmentError> {
    // The value returned from `align_of` should fit within an `u8`
    // for the foreseeable future.
    let align = u8::try_from(align_of::<T>()).expect("Unexpected align_of value.");
    let aligned_addr = addr
        .checked_align_up(Addr::V::from(align))
        .ok_or(AlignmentError::Overflow)?;
    if addr == aligned_addr {
        Ok(())
    } else {
        Err(AlignmentError::Misaligned)
    }
}

/// An address that's aligned with respect to `T`.
#[derive(Clone, Copy)]
pub struct Aligned<Addr, T> {
    addr: Addr,
    phantom: PhantomData<*const T>,
}

impl<Addr, T> Aligned<Addr, T> {
    /// Instantiate a new `Aligned` value without checking the alignment.
    ///
    /// # Safety
    ///
    /// The value of `addr` must be aligned with respect to `T`.
    pub unsafe fn new(addr: Addr) -> Self {
        Aligned {
            addr,
            phantom: PhantomData,
        }
    }

    /// Return the inner address value.
    pub fn into(self) -> Addr {
        self.addr
    }

    /// Convert `self` into an `Aligned` value with the specified alignment without
    /// performing any checks.
    ///
    /// # Safety
    ///
    /// The inner address value must be aligned with respect to `U`.
    pub unsafe fn reinterpret<U>(self) -> Aligned<Addr, U> {
        Aligned {
            addr: self.addr,
            phantom: PhantomData,
        }
    }
}

impl<Addr: Address, T> Aligned<Addr, T> {
    /// Attempt to create an `Aligned` value based on `addr`.
    pub fn from_addr(addr: Addr) -> result::Result<Self, AlignmentError> {
        check_addr_aligned::<Addr, T>(addr)?;
        // Safe because we checked the alignment.
        Ok(unsafe { Self::new(addr) })
    }

    /// Attempt to convert `self` into an `Aligned` value with the specified alignment.
    pub fn cast<U>(self) -> result::Result<Aligned<Addr, U>, AlignmentError> {
        // Fast (compile time) conversion path.
        if align_of::<T>() >= align_of::<U>() {
            // Safe because the above inequality holds.
            Ok(unsafe { self.reinterpret::<U>() })
        } else {
            Aligned::from_addr(self.addr)
        }
    }

    /// Attempt to obtain an `Aligned<Addr, U>` after offsetting the current address by `value`.
    pub fn offset<U>(self, value: Addr::V) -> result::Result<Aligned<Addr, U>, AlignmentError> {
        let addr = self
            .addr
            .checked_add(value)
            .ok_or(AlignmentError::Overflow)?;

        // Fast path.
        if align_of::<T>() >= align_of::<U>() {
            // We only need to check if the offset value is aligned here w.r.t. `U`, because we
            // know the  base is aligned based on the condition above. This check can be optimized
            // away in certain conditions (i.e. when `value` is known at compile time).
            check_addr_aligned::<Addr, U>(Addr::new(value))?;

            // Safe because the above checks/conditions ensure `addr` is properly aligned.
            Ok(unsafe { Aligned::new(addr) })
        } else {
            Aligned::from_addr(addr)
        }
    }
}
