# echod

A Resonate server on S3 plus a worker that runs JavaScript and TypeScript
durable executions in V8. Built inside out, from the stored data up.

## Crates

| crate | holds |
|---|---|
| `echod-server` | the `ResonateServer`: one document per origin in an S3 bucket, committed with conditional writes |
| `echod-worker` | the `ResonateWorker`: a V8 isolate (`deno_core`) whose durable ops are promises on the server |

Both depend on `resonate-core` for the traits and protocol types.
Origin: `resonate-server-blob` and `resonate-plugin-echod`.

## echod-server

### The document

One origin is one object at `wf/<origin>`. The object holds the origin's
entire state, so one conditional write commits any transition.

```rust
/// One origin's entire state.
pub struct OriginDoc {
    pub promises: BTreeMap<String, PromiseDoc>, // by full promise id
    pub tasks:    BTreeMap<String, TaskDoc>,    // by full promise id; a task's id is its promise's id
    pub clock:    i64,                          // latest `now` observed
    pub gen:      u64,                          // bumped once per committed write
    pub timer_at: Option<i64>,                  // deadline of the timer object armed for this origin
}

/// A promise plus its registrations.
pub struct PromiseDoc {
    pub state:      PromiseState,
    pub param:      PromiseValue,
    pub value:      PromiseValue,
    pub tags:       BTreeMap<String, String>,
    pub timeout_at: i64,
    pub created_at: i64,
    pub settled_at: Option<i64>,
    pub callbacks:  Vec<String>,                // awaiter ids, registration order
    pub listeners:  Vec<String>,                // listener addresses, registration order, unique
}

/// A task; at most one of `retry_at` / `lease_at` is armed.
pub struct TaskDoc {
    pub state:    TaskState,
    pub version:  i64,
    pub pid:      Option<String>,
    pub ttl:      Option<i64>,
    pub resumes:  BTreeSet<String>,             // awaited ids not yet observed settled
    pub retry_at: Option<i64>,                  // re-dispatch deadline while pending
    pub lease_at: Option<i64>,                  // lease expiry while acquired
}
```

`PromiseState`, `TaskState` and `PromiseValue` come from `resonate_core::types`.
Collections are `BTree*` so encoding is a function of state alone.

### Encoding

One line of canonical JSON per entity, joined by `\n`: a header (`t:"h"`,
format version, clock, gen, origin hash, timer), then promises (`t:"p"`),
tasks (`t:"k"`), armed promise deadlines (`t:"pt"`), armed task deadlines
(`t:"kt"`). Ids are stored relative to the origin. Empty fields are omitted,
never written as `null`. Canonical bytes let the applier skip a write when
nothing changed and recognise its own landed write after a lost response.
