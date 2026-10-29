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

Promise and Schedule documents use appendable segment kinds 7 and 8. Each
write is one complete envelope whose record contains a Header followed by the
ordered changed rows. A stored document is the direct concatenation of these
self-framed segments; no outer length is rewritten when another write is
appended. Reading rejects an invalid or truncated segment, takes the last
Header, and folds rows by ID in commit order with the last row winning while
retaining each ID's first-seen position. Compaction writes one segment
containing a new Header and the folded rows.

Textual object-store keys are independently available through
`store_key_text.rs` and match `logic::keys::KeySpace` output:

```text
<prefix>wf/<percent-encoded origin>
<prefix>sched/<percent-encoded id>
<prefix>nodes/<percent-encoded id>
<prefix>members
<prefix>t/<bucket:020>/<deadline:020>_<target>@<token:016x>~<percent-encoded by>
```

The optional prefix is normalized with one trailing slash and a zero timer
bucket width behaves as one millisecond. Timer targets are either a
percent-encoded origin or `sched:<percent-encoded id>`. The canonical parser
requires uppercase percent escapes, exact decimal/token widths, lowercase
token hex, valid decoded UTF-8, and the configured deadline-derived bucket.

## Verification

`./verify.sh` verifies 391 obligations across the byte/model implementation without
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

`runtime.rs` is part of the verified build. Every public typed encoder refines
its canonical byte model and, on a successful encoding satisfying the model's
explicit size/well-formedness predicate, establishes the corresponding decoder
round trip. Every public typed decoder establishes an exact two-way result:
`Ok(value)` means the format model decodes to that value, while `Err` means the
format model rejects the input. These contracts cover Header, Announcement,
Membership, Promise, Schedule, every StoreKey variant, and the kernel
Promise/Schedule APIs. The kernel decoder contracts additionally prove that the
decoded model is the verified UTF-8 bridge image of the returned kernel row.

`document.rs` additionally verifies frame splitting, Promise and Schedule
segment refinement, whole-document decoding, literal-concatenation append
laws, last-row-wins folding, fold idempotence, and compaction/rewrite
preservation. Its public segment and document APIs use kernel Promise/Schedule
rows and the typed Header; malformed and truncated non-empty documents are
rejected. The empty byte string represents an empty document.

`store_key_text.rs` verifies percent framing, fixed-width decimal and hex
formatting/parsing, numeric/lexicographic bucket ordering, prefix and class
parsing, every textual StoreKey variant, canonical malformed-input rejection,
UTF-8 validity of emitted S3 keys, byte-model round trips, and the executable
`StringStoreKey`/`String` bridge.

Run:

```bash
./verify.sh
RUSTUP_TOOLCHAIN=1.99.1-x86_64-unknown-linux-gnu cargo test --locked
```
