# echod

A Resonate server on S3 plus a worker that runs JavaScript and TypeScript
durable executions in V8. Built inside out, from the stored data up.

## Crates

| crate | holds |
|---|---|
| `echod-kernel` | the state machine: one object store, one transition per request, verified with Verus against the specification's catalogue |
| `echod-server` | the `ResonateServer`: the kernel over documents in an S3 bucket, committed with conditional writes |
| `echod-dst` | the server under deterministic simulation: one seed, no wall clock, no sockets; checked for linearizability against the kernel |
| `echod-fleet` | the fleet as a TLA-style state machine in Verus over the kernel's own states, Anvil's shape: nodes, bucket, clocks, crashes, the commit protocol; proved: ownership is exclusive, trusted caches are current, every document satisfies the catalogue, every deadline has a timer |
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

```text
config.rs     the dials
keys.rs       where everything lives under the bucket
store.rs      the object store port: object_store behind it, S3 Express on the SDK for appends, an in-memory model
doc.rs        an origin's document: rows in, rows out, the fold between
wire.rs       the kernel's vocabulary to the protocol's and back
nodes.rs      the nodes: announce, heartbeat, list, and who owns what
applier.rs    one request against one origin, serialised and committed
timers.rs     deadlines as objects, fired by the owner
schedules.rs  schedules as objects, fired by the owner
push.rs       messages out: HTTP push, and the router in front of it
server.rs     the ResonateServer: dispatch, forwarding, lifecycle
gateway.rs    POST /, GET /ready and GET /metrics
metrics.rs    what an operator sees: OpenMetrics, with labels from closed sets only
```

### The bucket

```text
wf/<origin>                              an origin's document: rows
sched/<id>                               a schedule: one row
t/<bucket>/<deadline>_<origin>@<token>   a deadline for an origin, empty
t/<bucket>/<deadline>_sched:<id>@<token> a schedule's next run, empty
nodes/<id>                               a node's announcement: id, url, at
```

### The document

One origin is one object, JSON lines: one kernel `Promise` per row, in
commit order, serialised by serde as the kernel declares it. A task is a
field of its promise. There is no enclosing document and no header.

The document is the fold of the rows by id, last row wins — the kernel's
`fold_by`, whose lemmas (and `proofs/compaction.rs`) prove any one-row-per-id
rendering replays to the same document. Reading an origin
replays its object.

### Writing

A request loads the document, runs the kernel handler, drains what the step
left owed (callbacks and listeners of settled promises, retries now due),
and writes the rows that changed. The step is decided at the later of the
node's clock and the document's stamp — the instant of the last write,
carried in the object's header — so every step on a document is decided no
earlier than the one before, which is what the kernel is proved for. Every
write carries `If-Match` on the ETag the read returned, and a header with a
fresh nonce, so every write is a new version even when the rows are the
same; the ETag is the commit, so a stale read cannot win whatever happened
in between. A lost race re-reads and runs the handler again. On a directory
bucket (S3 Express One Zone) the write is an append at the current size;
once the object carries `compact` stale rows, or on a general-purpose
bucket, the whole object is rewritten as one row per id. The outbox is
handed to the router after the commit; delivery is at most once, and a lost
`execute` is re-offered by the task's retry deadline.

A deadline is an empty object whose key says what is due, when, a token
drawn per arm, and the node that armed it, filed under the time bucket (an
hour by default) its deadline falls in. The commit is the protocol
`echod-fleet` proves (`node/txn.rs`, run by `applier.rs`): the key for the
document's nearest deadline is put before the document, unless the node
remembers a key for that instant armed with the very version it loaded;
the document is written; the key replaced is deleted; the key kept is
remembered with the version written. A key that fires sweeps its origin;
the sweep's own write, or, if nothing was due, a rewrite of the document
at a new version, fences every commit in flight that armed the key, and
then the key is deleted, whoever armed it. So a deadline a document owes
always has a key in the bucket, which the fleet proof states and proves. A schedule
is its own object; firing it creates the occurrence's promise and advances
the schedule in one turn on the promise's origin.

### Nodes

A node announces itself at `nodes/<id>` (its URL, when it last did) and
refreshes the announcement every heartbeat. The member list is one object,
`members`, holding the members and the epoch it was written in: whoever
sees the announced set differ from it writes the next epoch with a
conditional put, so epochs are totally ordered and every node reads the
same sequence. A node keeps the epoch and members it read, when it read
them, and when it first read the epoch it holds. Nothing depends on
membership for the state's correctness, which the conditional writes carry;
membership steers three things:

- **Ownership.** `hash(origin) mod n` over the members in order (FNV-1a). A
  load balancer that applies the same function over `members` sends every
  request for an origin to the node that caches it and fires its deadlines.
  A node *acts* as owner of an origin only when its view is fresh (read
  within a TTL), its members make it the owner, and it has held its epoch
  for the grace, `ttl + 4 skew`. Only the acting owner writes an origin. A
  node that is not the owner forwards; if it is the owner but not acting
  yet, or its view is stale, it answers 503.
- **Cache.** Each node caches the documents it read or wrote, with their
  ETags, least recently used out, bounded by entries and by bytes. The
  acting owner uses an entry without asking the store only if it is a
  version the node itself wrote while acting: a version merely read may be
  replaced by a write an earlier owner still had in flight, which lands on
  the version it loaded and no later one. Any other entry is revalidated
  with `If-None-Match`. The cache is a port (`cache.rs`); the one
  implementation is in memory.
- **Timers.** The acting owner fires an origin's deadlines from its wheel.

The state behind these rules and the decisions taken from it are not in
`nodes.rs`: they are `echod_fleet::node::core::NodeCore`, executable Rust
verified to compute the fleet model's specification functions step for
step. `nodes.rs` is the trusted shim around it: it announces, lists, reads
the configuration object and hands it to `read_config`; it asks `acts` and
`trusts`; and `applier.rs` reports every version read or written with
`filled` and every entry dropped, evicted or forgotten with `forget`, so
what the core decides on is what the cache holds. `echod-fleet` proves the
rules exclusive and sound under the one hypothesis every lease carries:
every live clock within `skew` of true time (`--clock-skew-ms`).
Membership is decided on the fleet's time, the later of a node's clock and
the latest announcement it listed, which absorbs a clock that steps back or
runs slow. The simulation found the earlier rules — an owner trusts its
cache; a member counts a TTL after it joins — unsound across membership
changes; the proof gave the rules that are.

A step is decided at an instant never earlier than any instant the origin's
rows record (`step::clamp_now`): the kernel is proved for `now` at or after
every `created_at` and `settled_at`, and a node behind another node's clock
would otherwise step outside that.

### Transport

HTTP push only: a message is POSTed to the worker's URL as the protocol's
JSON `Message`. The router maps `http` and `https` to it.

### The store

The port is `Store`: get, conditional get, conditional put (create, or
update on a version), plain put, delete, list, list prefixes, and, where
the bucket has it, append. Behind it, `ObjectStoreStore` is the
`object_store` crate — the library SlateDB builds on — which gives S3, GCS,
Azure and memory with each service's own conditional writes, named by a
URL (`--store s3://bucket/prefix`, `gs://`, `az://`, `memory:///`). Two
others remain: `MemoryStore`, the model the simulation runs on, with
content-addressed versions as S3 has them; and `S3Store` on the AWS SDK,
only for `--express`, since appending at an offset is an S3 Express One
Zone call `object_store` does not have. `object_store`'s local filesystem
backend is not a store: it has no conditional update.

`tests/store.rs` runs the port's contract on every backend it can reach:
a conditional create of an existing key and a conditional write on a
stale version are refused, a conditional read of the current version says
so, listings page past a thousand keys and come back in order, keys with
the characters ours use round-trip, and, on S3, a version is a function
of the content — the same bytes are the same version, which is why every
write of ours carries a nonce. The end-to-end tests run on the same store
under a prefix of their own when `ECHOD_STORE` is set. `scripts/s3-tests.sh`
runs both against `s3s-fs`, a Rust S3 emulator, against RustFS, the other
Rust S3 server, or against a bucket you name; the SDK examples run
unchanged against a server on either. Both servers refuse conditional
writes as S3 does. RustFS also honours conditional reads and makes
versions from content, as S3 does; `s3s-fs` 0.17 ignores `If-None-Match`
on reads and sends the body where S3 sends 304, which the store treats as
a revalidation that found the version current.

### Observability

`GET /metrics` is OpenMetrics text (`prometheus-client`), one registry per
server. The rule for every label: its values are a closed set the server
decides. No origin, promise id, key, address, node id or error text is ever
a label; a request kind is a label only if the protocol defines it, anything
else is `other`. So the number of series is a small constant however many
promises, origins or workers there are, and a client cannot mint one.

What is counted, and why:

| metric | labels | tells an operator |
|---|---|---|
| `echod_requests_total`, `echod_request_duration_seconds` | `kind`, `route` (`local`, `relayed`: run here for another node, `forwarded`: sent to the owner), `status` | the protocol's traffic, where it ran, how it ended, how long it took |
| `echod_forwards_total`, `echod_forward_duration_seconds` | `outcome` (`answered`, `unavailable`) | the node-to-node hop |
| `echod_messages_total`, `echod_message_duration_seconds` | `kind` (`execute`, `unblock`), `outcome` (`delivered`, `unroutable`, `failed`) | pushes to workers |
| `echod_store_operations_total`, `echod_store_operation_duration_seconds` | `op` (the port's nine calls), `object` (`document`, `schedule`, `timer`, `node`, `members`), `outcome` (`ok`, `not_modified`, `absent`, `conflict`, `failed`) | every call on the bucket: how many, of what, on what, and how it ended. `conflict` is a conditional write the store refused: CAS'ed out. `failed` on a write is the third outcome of the fleet model: the write may or may not have landed |
| `echod_document_writes_total`, `echod_document_bytes` | `mode` (`create`, `rewrite`, `append`) | how documents are written and how big they are |
| `echod_commits_total` | `outcome` (`committed`, `raced`: lost the race on the document and re-decided, `failed`, `exhausted`) | the commit protocol's fate |
| `echod_cache_lookups_total` | `result` (`trusted`: served from memory, `revalidated`: a conditional read said not modified, `refreshed`: it brought a newer version, `absent`, `miss`) | what a load cost; `trusted` is the hit, the rest are round trips |
| `echod_cache_entries`, `echod_cache_bytes`, `echod_cache_evictions_total` | | the cache against its bounds |
| `echod_membership_refreshes_total`, `echod_configuration_writes_total` | `outcome` | the heartbeat, and who wrote the next epoch |
| `echod_configuration_changes_total` | | ownership moved: this node took on a new epoch |
| `echod_membership_epoch`, `echod_members`, `echod_node_fresh`, `echod_node_acting` | | what the node holds of the fleet, and whether it is serving and acting |
| `echod_timer_fires_total`, `echod_timer_lag_seconds` | `kind` (`origin`, `schedule`), `outcome` (`deleted`, `kept`: the delete failed and it fires again, `failed`, `deferred`: not this node's to fire now) | deadlines firing, and how late |
| `echod_timer_listings_total`, `echod_timers_armed` | `outcome` | the three occasions a bucket is listed, and the wheel |
| `echod_sweeps_total` | `outcome` (`fired`, `idle`, `failed`) | what a fired key found |
| `echod_build_info` | `version` | |

The store is observed by a decorator over the port (`MeteredStore`), so
every backend is measured the same way and the object's kind comes from
the key's place in the bucket, not from the caller. The gauges are read
when scraped, from the node's state as it is then. Logs carry the names
the metrics leave out: an origin, a key, an address, an error.

### Simulation

`echod-dst` runs several servers over one in-memory store on one thread
under tokio's paused clock, so time moves only between tasks and the same
seed replays the same run. The simulation owns every port: a reference
clock the clients stamp requests with, and per node a clock with its own
skew, drift and the jumps the run inflicts, backwards included; a store that
answers nothing, loses acks or refuses conditional writes by seeded
percentages and waits a seeded latency, and per node a store that can be cut
off entirely; the peers (a forwarded request is a call), with partitions
between chosen pairs; a bus that checks every message against the bucket.
A chaos task crashes nodes, stops them cleanly, starts new ones, partitions
pairs, cuts nodes off the store and jumps their clocks, within the skew the
servers are told to expect, so the proof's hypothesis holds; set
`--expected-skew` below what the run inflicts to leave it. Clients issue every
request kind over a few origins; every attempt is a history entry, since an
attempt that got no answer may have taken effect. Sweeps enter the history
through an observer port.

The check is linearizability per origin against the kernel: an order of the
entries, each within its span, that yields every answer seen and ends in the
rows the bucket holds, each step decided at the later of its instant and the
document's stamp as the server does; an entry without an answer may be
placed or skipped.
Besides that: every deadline a document owes has a key, every `execute`
names a task that exists and every `unblock` a settled promise, every kind
answered 200 at least once, and the history overlapped.

## echod-fleet

The multi-node system as a state machine, in the shape Anvil gives a
Kubernetes cluster: a state, actions with preconditions and transitions,
`init` and `next`, and Anvil's TLA embedding (`verus-tla`, vendored) to
state the theorem as `always(inv)`. The fleet imports the kernel under
Verus (`verify.sh` exports the kernel's metadata and imports it), so the
bucket's documents are the kernel's own states and the kernel's steps enter
the model with the contracts the kernel proves of them.

```text
tla/            the temporal logic, vendored from Anvil's verus-tla
node/core.rs    the node core: executable Rust, each step ensures its spec function
node/txn.rs     the commit's decisions, the same way
node/step.rs    sweep, drain, next_deadline, clamp_now: verified over the kernel
spec/cluster.rs the state and the seventeen actions
proof/safety.rs the invariant, one lemma per action, the four theorems
```

The node core and the commit are what Anvil calls the reconciler: sans-I/O
step functions. `NodeCore` holds what a node keeps of the configuration
(epoch, members, the clock at the last read and at the first read of the
epoch held), of its cache (each origin's version, when it was filled, and
whether this node wrote it) and of its deadline keys (the key kept for each
origin, with the version written with it). `Txn` is one commit's decisions:
the previous key, whether to arm, what to delete, what to keep. Each
function `ensures` it equals the specification function of the same name
on the state's view. The step module verifies the loops the server runs
around the kernel: `sweep` leaves nothing due at its instant and leaves the
document as it was if nothing fired; `drain` is kernel steps; `next_deadline`
is the least deadline; `clamp_now` the later of clock and stamp. Three
primitives are trusted with their meaning stated: FNV-1a is a function of
the string, `str == str` is equality of views, `String::clone` copies.

The fleet state: real time (ghost), the nodes, the bucket. A node is its
core's view, its body cache, whether it is alive, its clock, the commits it
has in flight, and, ghost, real time at its last read and at its first
read of the epoch held. The bucket has every document as a kernel state
with its version and stamp, the deadline keys, the configuration (members,
epoch) and, ghost, when each version was written, by which key each
document is covered, who armed each key, and when each epoch was written.
The actions: real time advances; a clock advances, within `skew` of real
time; a node joins or crashes; a node reads the configuration or writes the
next epoch; a node drops a cache entry; and the commit, one store operation
per action — the acting owner loads a document and decides a step on it (a
request: any sequence of kernel steps at one instant; a sweep: the step
module's contract), arms a key, writes the document conditionally or is
refused, deletes the key replaced, remembers the key kept and deletes the
key fired, or, having found nothing due, rewrites the document and
collects the key. Every write has three outcomes: applied, refused by its
condition — both decided by the bucket's contents — or unknown, where the
bucket applied it or did not, nondeterministically, and the node, told
only that it failed, trusts nothing cached and gives the commit up; what
landed stays. Deletes may fail silently. Clocks are never read by the model except
through the core's decisions; real time only states the hypothesis and
orders events.

Proved, 233 items, no admits:

- **Exclusion.** Two live nodes never both act as owner of one origin, with
  `grace > ttl + 4 skew` and every live clock within `skew` of real time.
- **Currency.** A node that answers from its cache holds the bucket's
  current version.
- **Catalogue.** Every document in the bucket satisfies the kernel's
  catalogue at its stamp.
- **Timers.** Every deadline in every document — a pending promise's, a
  lease's, a retry's — has a deadline key in the bucket for its origin at
  or before it, at all times.

All four as corollaries of one invariant that `init` establishes and every
action preserves, assembled into `spec ⊨ □inv` by the embedding's induction
rule. A witness shows the invariant is not vacuous. The last two rest on
the commit protocol alone and need no clocks.

The proof changed the design twice. A writer is checked for ownership
when a request is dispatched, but its conditional write lands later; an
earlier owner's write in flight can land after the new owner read and
cached the document, so a node trusts only versions it wrote itself while
acting. And a node that fires a key could delete it while a commit that
armed it was still between its key and its document; so a fired key is
deleted only after a write of the document — the sweep's own, or a rewrite
when nothing was due — which fences such commits. That the write suffices,
whoever armed the key, rests on a ghost order of the bucket's events: a
later writer's cover was armed, or kept from a version written, after the
version the fired key's commit loaded, so it is never that key.

How the proof reaches the running code: the theorems are about the fleet
model; the model's node actions are the core's, the commit's and the step
module's specification functions; their executable functions are verified
to compute those functions; `echod-server` keeps its membership, cache and
deadline-key state in the core and takes its decisions from it, and runs
the step module's loops. That is Anvil's shape of refinement: functional,
per step, with a trusted shim. The shim here is `nodes.rs`, `applier.rs`
and `timers.rs`: that the configuration handed to `read_config` is the
object read, that every version read or written is reported, that the
store operations are issued in the protocol's order with the decisions
the core made, that the clock passed is the fleet's time, that the
document decoded is the one written, and that the bucket behaves as the
model's: conditional writes on versions, one version per content. The S3
model's fidelity, the schedule objects and liveness are not proved.

### The SDKs

`examples/ts` runs the TypeScript SDK against the server. The SDK's default
message source long-polls; `examples/ts/push.ts` is the push side, an HTTP
listener plugged into the SDK's `HttpNetwork` as its adapter, so the worker's
address is a URL. One concession in `wire.rs`: the SDK creates a sleep as a
timer with a target, which the specification refuses; the server drops the
target, and the timer is armed on its own as the specification arms it.
