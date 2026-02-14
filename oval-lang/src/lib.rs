//! Oval lang

#![no_std]
#![forbid(unsafe_op_in_unsafe_fn)]

extern crate alloc;

pub(crate) mod abort;
pub(crate) mod hashed;
pub(crate) mod alloc_helper;
pub(crate) mod bitset;
pub(crate) mod arena;
pub(crate) mod mutex;
pub(crate) mod gc;

pub mod ast;
pub mod compile;
pub mod interner;
pub mod parser;
pub mod spanned;
pub mod tokens;

#[inline(always)]
pub(crate) fn recurse<R, F: FnOnce() -> R>(callback: F) -> R {
    cfg_if::cfg_if! {
        if #[cfg(feature = "stacker")] {
            // we want at least 128 kib
            // and if not available grow by 2 mib
            stacker::maybe_grow(128 * 1024, 2024 * 1024, callback)
        } else {
            callback()
        }
    }
}
