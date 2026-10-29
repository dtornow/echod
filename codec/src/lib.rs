//! Versioned canonical persistence bytes for echod.
//!
//! The verified layer deliberately models text as validated UTF-8 bytes.  The
//! only unverified boundary is the ordinary-Rust conversion between those
//! bytes and `String`; it lives in `bridge` and is omitted from Verus builds.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

pub mod frame;
pub mod laws;
pub mod primitives;
pub mod record;
pub mod text;
pub mod types;

#[cfg(not(verus_keep_ghost))]
pub mod bridge;
