#![deny(rustdoc::broken_intra_doc_links, rust_2018_idioms)]
#![allow(clippy::default_constructed_unit_structs, unused)]
#![warn(
    clippy::clone_on_ref_ptr,
    clippy::dbg_macro,
    clippy::explicit_iter_loop,
    clippy::future_not_send,
    clippy::todo,
    clippy::use_self,
    missing_copy_implementations,
    missing_debug_implementations,
    unused_crate_dependencies,
    unreachable_pub
)]

//   Copyright 2023 Dominic Dwyer (dom@itsallbroken.com)
//
//   Licensed under the Apache License, Version 2.0 (the "License"); you may not
//   use this file except in compliance with the License. You may obtain a copy
//   of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in writing, software
//   distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
//   WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
//   License for the specific language governing permissions and limitations
//   under the License.

mod dot;
mod interval;
mod node;
mod tree;

#[cfg(test)]
mod test_utils;
