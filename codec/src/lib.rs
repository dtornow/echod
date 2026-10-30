//! Versioned canonical persistence bytes for echod.
//!
//! Text is canonical UTF-8 and the kernel `String` correspondence is verified
//! against vstd's UTF-8 model.

#![cfg_attr(
    not(verus_keep_ghost),
    allow(unused_imports, dead_code, unused_variables)
)]

pub mod bridge;
pub mod document;
pub mod frame;
pub mod laws;
pub mod primitives;
pub mod record;
pub mod store_key_text;
pub mod text;
pub mod types;

mod runtime;

pub use runtime::{
    decode_announcement, decode_header, decode_membership, decode_promise,
    decode_promise_model, decode_schedule, decode_schedule_model,
    decode_store_key, encode_announcement, encode_header, encode_membership,
    encode_promise, encode_promise_model, encode_schedule,
    encode_schedule_model, encode_store_key, CodecResult,
};
