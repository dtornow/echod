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

One origin is one object at `wf/<origin>`, JSON lines: one `Promise` per
line, sorted by id. A task is a field of its promise, since a task's id is its
promise's id. There is no enclosing document and no header.

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

`serde_json`, one object per line, joined by `\n`. Encoding is canonical
because every collection is a `BTree*`, field order is declaration order, and
empty fields are omitted. Canonical bytes let the applier skip a write when
nothing changed and recognise its own landed write after a lost response.
