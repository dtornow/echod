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

## Verification

`./verify.sh` verifies the byte/model implementation and 131 obligations without
trusted stubs or proof escape hatches. It proves executable/spec agreement for
primitive decoders, UTF-8 validation, blobs, options, sequences, envelopes, and
records; their canonical round trips; kind separation; and model-level typed
round trips for Header, Announcement, Membership, Value, Task, Promise,
Schedule, and every StoreKey variant.

`bridge.rs` is part of the verified build. It proves the custom canonical UTF-8
validator equivalent to `vstd::utf8::valid_utf8`, uses vstd's specified
`str`/`String` operations, and verifies both directions of every nested
Promise/Schedule field conversion. Executable bridge-composition functions
prove kernel→model→kernel and model→kernel→model round trips.

`runtime.rs` only assembles the already specified primitive codecs into the
public `Result`-returning API and is exercised by rejection and round-trip
tests. It is not claimed as an additional end-to-end Verus refinement theorem;
the typed format and bridge theorems on either side of it are proved.

Run:

```bash
./verify.sh
RUSTUP_TOOLCHAIN=1.99.1-x86_64-unknown-linux-gnu cargo test --locked
```
