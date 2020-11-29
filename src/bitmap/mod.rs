// Copyright 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! This module holds abstractions that enable tracking the areas dirtied by writes of a specified
//! length to a given offset. In particular, this is used to track write accesses within a
//! `GuestMemoryRegion` object, and the resulting bitmaps can then be aggregated to build the
//! global view for an entire `GuestMemory` object.

use std::fmt::Debug;

use crate::{GuestMemory, GuestMemoryRegion};

/// Trait implemented by types that support creating `BitmapSlice` objects.
pub trait WithBitmapSlice<'a> {
    /// Type of the bitmap slice.
    type S: BitmapSlice;
}

/// Trait used to represent that a `BitmapSlice` is a `Bitmap` itself, but also satisfies the
/// restriction that slices created from it have the same type as `Self`.
pub trait BitmapSlice:
    Bitmap + Clone + Copy + Debug + for<'a> WithBitmapSlice<'a, S = Self>
{
}

/// Common bitmap operations. Using Higher-Rank Trait Bounds (HRTBs) to effectively define
/// an associated type that has a lifetime parameter, without tagging the `Bitmap` trait with
/// a lifetime as well.
///
/// Using an associated type allows implementing the `Bitmap` and `BitmapSlice` functionality
/// as a zero-cost abstraction when providing trivial implementations such as the one
/// defined for `()`.
// These methods represent the core functionality that's required by `vm-memory` abstractions
// to implement generic tracking logic, as well as tests that can be reused by different backends.
pub trait Bitmap: for<'a> WithBitmapSlice<'a> {
    /// Mark the memory range specified by the given `offset` and `len` as dirtied.
    fn mark_dirty(&self, offset: usize, len: usize);

    /// Check whether the specified `offset` is marked as dirty.
    fn dirty_at(&self, offset: usize) -> bool;

    /// Return a `<Self as WithBitmapSlice>::S` slice of the current bitmap, starting at
    /// the specified `offset`.
    fn slice_at(&self, offset: usize) -> <Self as WithBitmapSlice>::S;
}

/// A no-op `Bitmap` implementation that can be provided for backends that do not actually
/// require the tracking functionality.

impl<'a> WithBitmapSlice<'a> for () {
    type S = Self;
}

impl BitmapSlice for () {}

impl Bitmap for () {
    fn mark_dirty(&self, _offset: usize, _len: usize) {}

    fn dirty_at(&self, _offset: usize) -> bool {
        false
    }

    fn slice_at(&self, _offset: usize) -> Self {}
}

/// A `Bitmap` and `BitmapSlice` implementation for `Option<B>`.

impl<'a, B> WithBitmapSlice<'a> for Option<B>
where
    B: WithBitmapSlice<'a>,
{
    type S = Option<B::S>;
}

impl<B: BitmapSlice> BitmapSlice for Option<B> {}

impl<B: Bitmap> Bitmap for Option<B> {
    fn mark_dirty(&self, offset: usize, len: usize) {
        if let Some(inner) = self {
            inner.mark_dirty(offset, len)
        }
    }

    fn dirty_at(&self, offset: usize) -> bool {
        if let Some(inner) = self {
            return inner.dirty_at(offset);
        }
        false
    }

    fn slice_at(&self, offset: usize) -> Option<<B as WithBitmapSlice>::S> {
        if let Some(inner) = self {
            return Some(inner.slice_at(offset));
        }
        None
    }
}

/// Helper type alias for referring to the `BitmapSlice` concrete type associated with
/// an object `B: WithBitmapSlice<'a>`.
pub type BS<'a, B> = <B as WithBitmapSlice<'a>>::S;

/// Helper type alias for referring to the `BitmapSlice` concrete type associated with
/// the memory regions of an object `M: GuestMemory`.
pub type MS<'a, M> = BS<'a, <<M as GuestMemory>::R as GuestMemoryRegion>::B>;
