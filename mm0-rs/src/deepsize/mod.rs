//! A utility for recursively measuring the size of an object
//!
//! This is an adaptation of the [`deepsize`](https://docs.rs/deepsize) crate.

#[cfg(feature = "memory")]
mod deepsize;

#[cfg(feature = "memory")]
pub(crate) use deepsize::*;

/// A macro to generate an impl for types with no inner allocation.
#[cfg(not(feature = "memory"))]
#[macro_export]
macro_rules! deep_size_0 {($($_:tt)*) => {}}
