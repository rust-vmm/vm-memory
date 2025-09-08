// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
//
// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! Traits to represent an address within an address space.
//!
//! Two traits are defined to represent an address within an address space:
//! - [`AddressValue`](trait.AddressValue.html): stores the raw value of an address. Typically
//!   `u32`,`u64` or `usize` is used to store the raw value. But pointers, such as `*u8`, can't be used
//!   because they don't implement the [`Add`](https://doc.rust-lang.org/std/ops/trait.Add.html) and
//!   [`Sub`](https://doc.rust-lang.org/std/ops/trait.Sub.html) traits.
//! - [Address](trait.Address.html): encapsulates an [`AddressValue`](trait.AddressValue.html)
//!   object and defines methods to access and manipulate it.

/// Simple helper trait used to store a raw address value.
pub use vm_memory_new::address::{Address, AddressValue};
