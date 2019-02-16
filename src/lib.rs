// Portions Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Portions Copyright 2017 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the THIRD-PARTY file.

//! Traits for allocating, handling and interacting with the VM's physical memory.
//!
//! For a typical hypervisor, there are seveval components, such as boot loader, virtual device
//! drivers, virtio backend drivers and vhost drivers etc, that need to access VM's physical memory.
//! This crate aims to provide a set of stable traits to decouple VM memory consumers from VM
//! memory providers. Based on these traits, VM memory consumers could access VM's physical memory
//! without knowing the implementation details of the VM memory provider. Thus hypervisor
//! components, such as boot loader, virtual device drivers, virtio backend drivers and vhost
//! drivers etc, could be shared and reused by multiple hypervisors.

#![deny(missing_docs)]

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
