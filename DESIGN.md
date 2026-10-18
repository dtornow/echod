# echod

A Resonate server on S3 plus a worker that runs JavaScript and TypeScript
durable executions in V8. Built inside out, from the stored data up.

## Crates

| crate | holds |
|---|---|
| `echod-kernel` | the state machine: one object store, one transition per request, verified with Verus against the specification's catalogue |
| `echod-server` | the `ResonateServer`: the kernel over documents in an S3 bucket, committed with conditional writes |
| `echod-worker` | the `ResonateWorker`: a V8 isolate (`deno_core`) whose durable ops are promises on the server |

The server and the worker depend on `resonate-core` for the traits and
protocol types. Origin: `resonate-server-blob` and `resonate-plugin-echod`.

## echod-kernel

The specification is `resonatehq/resonate`, `spec/02-abstract`: a state of
objects, schedules and an outbox; 18 request handlers and 6 internal steps
(`debug.*` and `*.search` left out); a catalogue of 92 properties. The kernel
is that machine as Rust, and every step's `ensures` is the catalogue: `inv`
on the state it leaves, `legal` on the pair, and for an internal step the two
sweeper entries.

```text
types.rs        rows, records, requests, responses; abstract twins and views
ident.rs        ids; the three trusted string primitives
tags.rs         tags: first match wins; otype, timer, target
store.rs        State: row vectors whose view is three maps, via the fold
object.rs       projection, the per-object edits, birth
properties.rs   the catalogue, entry for entry, same names
frame.rs        the frame: what a step owes for the ids it touched
external*.rs    the 18 request handlers
internal.rs     the 6 internal steps
```

The state is `Vec<Promise>`, `Vec<Schedule>`, `Vec<OutboxEntry>`: the rows.
Its abstract view is three maps, the fold of the rows by key, so the
catalogue is stated over maps and the compaction lemma is the view. Each
handler takes the state, the request, `now`, and a `Config`.

Proved: every catalogue entry, at every step, over the whole store. A step
proves the entries at the ids it wrote; the frame lemma proves the rest. One
entry is proved in an amended form, and one internal step departs from the
Lean text, both because the text is wrong:

- `consistent_suspension_registers_callback` demands that a task suspending
  gains a callback it did not have. A task that suspended on `P1` and `P2`,
  was woken by `P1` settling, ran again and suspended on `P2` alone, gains
  nothing: `P2` still held it. Seven steps; the sweep goes to three. Proved
  without the freshness conjunct.
- `processSchedule` creates a promise as of its occurrence `t`. For
  `t + promiseTimeout <= now` that is a pending task on a promise dead at
  `now`, which `preserved_no_dead_dispatch` forbids. The kernel births such a
  promise dead, the state Lean reaches on the next touch.

Trusted, not proved: `same_origin`, `str_eq`, `parse_nat` in `ident.rs`
(bodies are plain Rust, their `ensures` assumed), and the cron arithmetic,
which the caller supplies as a request's occurrences and next run. Doors the
kernel adds: instants and durations at most `MAX_TIME` (2^62 ms), versions
below it, so that no `u64` sum overflows.

`cargo build` compiles the kernel with the ghost code erased; `verify.sh`
runs Verus. Verus pins its own rustc, so the two are separate toolchains.

## echod-server

### The document

One origin is one object at `wf/<origin>`, JSON lines: one `Promise` per
row, in commit order. A task is a field of its promise, since a task's id is
its promise's id. There is no enclosing document and no header.

The document is the fold of the rows: each row replaces the entry for its id,
so the last row for an id wins. Reading an origin replays its object.

```rust
#[derive(Serialize, Deserialize)]
pub struct Promise {
    pub id:         String,
    pub state:      PromiseState,
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub tags:       BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "Value::is_empty")]
    pub param:      Value,
    #[serde(default, skip_serializing_if = "Value::is_empty")]
    pub value:      Value,
    pub timeout_at: i64,
    pub created_at: i64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub settled_at: Option<i64>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub callbacks:  Vec<String>,                // awaiter ids, registration order
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub listeners:  Vec<String>,                // listener addresses, registration order, unique
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub task:       Option<Task>,
}

#[derive(Serialize, Deserialize)]
pub struct Task {
    pub state:   TaskState,
    pub version: i64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub pid:     Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub ttl:     Option<i64>,
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub resumes: BTreeSet<String>,              // awaited ids not yet observed settled
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout: Option<Timeout>,
}

/// At most one deadline is armed on a task, so it is one field.
#[derive(Serialize, Deserialize)]
#[serde(tag = "kind", content = "at", rename_all = "lowercase")]
pub enum Timeout {
    Retry(i64),                                 // re-dispatch deadline while pending
    Lease(i64),                                 // lease expiry while acquired
}

/// `resonate_core::types::PromiseValue` with ordered headers.
#[derive(Serialize, Deserialize, Default)]
pub struct Value {
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub headers: BTreeMap<String, String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub data:    Option<String>,
}
```

`PromiseState` and `TaskState` come from `resonate_core::types`.

### Encoding

`serde_json`, one object per row, joined by `\n`. Encoding is canonical
because every collection is a `BTree*`, field order is declaration order, and
empty fields are omitted.

### Writing

A request reads the object, replays it, decides, and appends one row per
promise it changed. Nothing changed, nothing appended.

Every write carries `If-Match` on the ETag the read returned; the ETag is
the commit. On S3 Express One Zone the write is an append, `PutObject` with
`x-amz-write-offset-bytes` at the current size. On general-purpose S3 there
is no append; the whole object is rewritten.

### Compaction

Appends are capped per object and the log grows, so an object is periodically
rewritten as one row per id. Any one-row-per-id rendering of the document
replays to the same document, in any row order; `proofs/compaction.rs` proves
this in Verus. A rewrite is a write like any other: its new ETag refuses
every append still in flight against the old object.

Removing a promise from an origin needs a tombstone row; a log cannot express
removal by omission.
