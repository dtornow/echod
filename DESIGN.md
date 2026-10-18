# echod

A Resonate server on S3 plus a worker that runs JavaScript and TypeScript
durable executions in V8. Built inside out, from the stored data up.

## Crates

| crate | holds |
|---|---|
| `echod-kernel` | the state machine: one object store, one transition per request, verified with Verus against the specification's catalogue |
| `echod-server` | the `ResonateServer`: the kernel over documents in an S3 bucket, committed with conditional writes |
| `echod-dst` | the server under deterministic simulation: one seed, no wall clock, no sockets; checked for linearizability against the kernel |
| `echod-fleet` | the fleet as a TLA-style state machine in Verus, Anvil's shape: nodes, bucket, clocks, crashes; proved: ownership is exclusive and trusted caches are current |
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
store.rs      the object store port: S3, and an in-memory stand-in
doc.rs        an origin's document: rows in, rows out, the fold between
wire.rs       the kernel's vocabulary to the protocol's and back
nodes.rs      the nodes: announce, heartbeat, list, and who owns what
applier.rs    one request against one origin, serialised and committed
timers.rs     deadlines as objects, fired by the owner
schedules.rs  schedules as objects, fired by the owner
push.rs       messages out: HTTP push, and the router in front of it
server.rs     the ResonateServer: dispatch, forwarding, lifecycle
gateway.rs    POST / and GET /ready
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
and writes the rows that changed. Every write carries `If-Match` on the ETag
the read returned; the ETag is the commit, so a stale read cannot win
whatever happened in between. A lost race re-reads and runs the handler
again. On a directory bucket (S3 Express One Zone) the write is an append at
the current size; once the object carries `compact` stale rows, or on a
general-purpose bucket, the whole object is rewritten as one row per id. The
outbox is handed to the router after the commit; delivery is at most once,
and a lost `execute` is re-offered by the task's retry deadline.

A deadline is an empty object whose key says what is due and when, filed
under the time bucket (an hour by default) its deadline falls in. It is
written before the document that arms it and deleted after the document that
disarms it, so a deadline the document owes is always in the bucket. The
token names the arm that wrote the key: a writer removes exactly the key its
own predecessor wrote, never another arm's key for the same instant. A
schedule is its own object; firing it creates the occurrence's promise and
advances the schedule in one turn on the promise's origin.

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
  acting owner uses an entry without asking the store only if the entry was
  filled while it was acting; any other entry is revalidated with
  `If-None-Match`. The cache is a port (`cache.rs`); the one implementation
  is in memory.
- **Timers.** The acting owner fires an origin's deadlines from its wheel.

These are the rules `echod-fleet` proves exclusive and sound, under the one
hypothesis every lease carries: every live clock within `skew` of true
time (`--clock-skew-ms`). Membership is decided on the fleet's time, the
later of a node's clock and the latest announcement it listed, which
absorbs a clock that steps back or runs slow. The simulation found the
earlier rules — an owner trusts its cache; a member counts a TTL after it
joins — unsound across membership changes; the proof gave the rules that
are.

A step is decided at an instant never earlier than any instant the origin's
rows record (`step::clamp_now`): the kernel is proved for `now` at or after
every `created_at` and `settled_at`, and a node behind another node's clock
would otherwise step outside that.

### Transport

HTTP push only: a message is POSTed to the worker's URL as the protocol's
JSON `Message`. The router maps `http` and `https` to it.

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
rows the bucket holds; an entry without an answer may be placed or skipped.
Besides that: every deadline a document owes has a key, every `execute`
names a task that exists and every `unblock` a settled promise, every kind
answered 200 at least once, and the history overlapped.

## echod-fleet

The multi-node system as a state machine, in the shape Anvil gives a
Kubernetes cluster: a state, actions with preconditions and transitions,
`init` and `next`, and Anvil's TLA embedding (`verus-tla`, vendored) to
state the theorem as `always(inv)`.

```text
tla/            the temporal logic, vendored from Anvil's verus-tla
spec/cluster.rs the state and the ten actions
proof/safety.rs the invariant, one lemma per action, the theorem
```

The state: real time (ghost), the nodes, the bucket. A node has a clock, the
epoch and members it read, when it read them (its clock, and ghost real
time), when it first read the epoch it holds, and a cache of document
versions with the clock at which each was filled. The bucket has every
document's version, the configuration (members, epoch) and, ghost, when
each epoch was written. The actions: real time advances; a clock advances,
within `skew` of real time; a node joins or crashes; a node reads the
configuration; a node writes the next epoch, with any members; a node reads
a document; a conditional write lands, or is refused; a node answers from
its cache. Clocks are never read by the model except through the node's
own decisions; real time only states the hypothesis and orders events.

Proved, with `grace > ttl + 4 skew`: two live nodes never both act as owner
of one origin (`exclusion`), and a node that answers from its cache holds
the bucket's current version (`currency`); both as corollaries of an
invariant that `init` establishes and every action preserves, assembled
into `spec ⊨ □inv` by the embedding's induction rule. A witness shows the
invariant is not vacuous. 157 items, no admits.

What the proof covers: the membership and cache rules of `nodes.rs` and
`applier.rs`, as stated in the model. What it does not yet: the refinement
of the running node to the model (the node is async Rust; Anvil's answer is
a sans-I/O step function under a trusted shim), the S3 model's fidelity,
and liveness. Those are the next layers, in that order.

### The SDKs

`examples/ts` runs the TypeScript SDK against the server. The SDK's default
message source long-polls; `examples/ts/push.ts` is the push side, an HTTP
listener plugged into the SDK's `HttpNetwork` as its adapter, so the worker's
address is a URL. One concession in `wire.rs`: the SDK creates a sleep as a
timer with a target, which the specification refuses; the server drops the
target, and the timer is armed on its own as the specification arms it.
