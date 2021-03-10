// Copyright 2021 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Contains a generic implementation of `BitmapSlice`.

use std::fmt::{self, Debug};

use crate::bitmap::{Bitmap, BitmapSlice, WithBitmapSlice};

/// Represents a slice into a `Bitmap` object, starting at `base_offset`.
pub struct RefSlice<'a, B> {
    inner: &'a B,
    base_offset: usize,
}

impl<'a, B: Bitmap + 'a> RefSlice<'a, B> {
    /// Create a new `BitmapSlice`, starting at the specified `offset`.
    pub fn new(bitmap: &'a B, offset: usize) -> Self {
        RefSlice {
            inner: bitmap,
            base_offset: offset,
        }
    }
}

impl<'a, B: Bitmap> WithBitmapSlice<'a> for RefSlice<'_, B> {
    type S = Self;
}

impl<B: Bitmap> BitmapSlice for RefSlice<'_, B> {}

impl<'a, B: Bitmap> Bitmap for RefSlice<'a, B> {
    /// Mark the memory range specified by the given `offset` (relative to the base offset of
    /// the slice) and `len` as dirtied.
    fn mark_dirty(&self, offset: usize, len: usize) {
        // The `Bitmap` operations are supposed to accompany guest memory accesses defined by the
        // same parameters (i.e. offset & length), so we use simple wrapping arithmetic instead of
        // performing additional checks. If an overflow would occur, we simply end up marking some
        // other region as dirty (which is just a false positive) instead of a region that could
        // not have been accessed to begin with.
        self.inner
            .mark_dirty(self.base_offset.wrapping_add(offset), len)
    }

    fn dirty_at(&self, offset: usize) -> bool {
        self.inner.dirty_at(self.base_offset.wrapping_add(offset))
    }

    /// Create a new `BitmapSlice` starting from the specified `offset` into the current slice.
    fn slice_at(&self, offset: usize) -> Self {
        RefSlice {
            inner: self.inner,
            base_offset: self.base_offset.wrapping_add(offset),
        }
    }
}

impl<'a, B> Clone for RefSlice<'a, B> {
    fn clone(&self) -> Self {
        RefSlice {
            inner: self.inner,
            base_offset: self.base_offset,
        }
    }
}

impl<'a, B> Copy for RefSlice<'a, B> {}

impl<'a, B> Debug for RefSlice<'a, B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Dummy impl for now.
        write!(f, "(bitmap slice)")
    }
}
