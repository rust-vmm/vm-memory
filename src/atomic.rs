// Copyright (C) 2019 Alibaba Cloud Computing. All rights reserved.
// Copyright (C) 2020 Red Hat, Inc. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! A wrapper over an `ArcSwap<GuestMemory>` struct to support RCU-style mutability.
//!
//! With the `backend-atomic` feature enabled, simply replacing `GuestMemoryMmap`
//! with `GuestMemoryAtomic<GuestMemoryMmap>` will enable support for mutable memory maps.
//! To support mutable memory maps, devices will also need to use
//! `GuestAddressSpace::memory()` to gain temporary access to guest memory.

pub use vm_memory_new::atomic::{
    GuestMemoryAtomic, GuestMemoryExclusiveGuard, GuestMemoryLoadGuard,
};
