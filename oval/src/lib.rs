//! Oval lang

#![no_std]
extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

// #![deny(missing_docs)]

pub mod symbol;
pub mod compile;
pub mod mir;
pub mod miri;