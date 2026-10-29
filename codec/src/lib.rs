//! Versioned canonical persistence bytes for echod.
//!
//! Text is canonical UTF-8 and the kernel `String` correspondence is verified
//! against vstd's UTF-8 model.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

pub mod bridge;
pub mod frame;
pub mod laws;
pub mod primitives;
pub mod record;
pub mod text;
pub mod types;

mod runtime;
