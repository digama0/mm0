//! A utility for recursively measuring the size of an object
//!
//! This is an adaptation of the [`deepsize`](https://docs.rs/deepsize) crate.
#![allow(clippy::redundant_pub_crate)]

#[cfg(feature = "memory")]
mod main;

#[cfg(feature = "memory")]
pub(crate) use main::*;

/// A macro to generate an impl for types with no inner allocation.
#[cfg(not(feature = "memory"))]
#[macro_export]
macro_rules! deep_size_0 {($($_:tt)*) => {}}
