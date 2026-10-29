# echod-codec

`echod-codec` is an independent executable persistence codec. Nothing in
`echod-logic` or the runtime uses it yet.

## Format

Every top-level value is:

```text
"ECHO" | version:u8 | kind:u8 | payload-length:u64be | payload
```

Version 1 payloads are records. A record is an element count (`u64be`) followed
by length-prefixed byte fields. Integers are fixed-width big endian; booleans
and options use only tags 0 and 1; sequences carry an element count and frame
every element; text fields are canonical UTF-8 and reject overlong encodings,
surrogates, truncation, and values above U+10FFFF. Decoders require exact
lengths, so trailing bytes are invalid.

Kinds are assigned for Header, Promise, Schedule, node Announcement,
Membership, and StoreKey. Store keys have variants for document, schedule,
origin timer, schedule timer, node, and membership objects.

## Verification boundary

`./verify.sh` verifies the byte/model implementation and 71 obligations without
trusted stubs or proof escape hatches. It proves executable/spec agreement for
primitive decoders, UTF-8 validation, blobs, options, sequences, envelopes, and
records; their canonical round trips; kind separation; and model-level typed
round trips for Header, Announcement, Membership, Value, Task, Promise,
Schedule, and every StoreKey variant.

The isolated proof boundary is `bridge.rs`: current Verus `String` has a
`Seq<char>` view but no proved UTF-8 relation for `str::as_bytes` or
`String::from_utf8`. The module is ordinary Rust and is excluded from Verus.
It contains the kernel Promise/Schedule conversion and typed runtime assembly.
The typed model laws are proved, while the ordinary-Rust implementation of
that bridge is covered by executable round-trip and rejection tests rather
than a false theorem about `String`. No axiom is used to hide that gap.

Run:

```bash
./verify.sh
RUSTUP_TOOLCHAIN=1.99.1-x86_64-unknown-linux-gnu cargo test --locked
```
