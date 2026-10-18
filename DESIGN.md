# echod

A Resonate server on S3 plus a worker that runs JavaScript and TypeScript
durable executions in V8. Built inside out, from the stored data up.

## Crates

| crate | holds |
|---|---|
| `echod-kernel` | the state machine: one object store, one transition per request, verified with Verus against the specification's catalogue |
| `echod-server` | the `ResonateServer`: the kernel over documents in an S3 bucket, committed with conditional writes |
| `echod-dst` | the server under deterministic simulation: one seed, no wall clock, no sockets; checked for linearizability against the kernel |
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

A node announces itself at `nodes/<id>` (its URL, when it first announced,
when it last did) and refreshes the announcement every heartbeat; every
heartbeat it also lists `nodes/`. The members are the nodes announced within
a TTL whose first announcement is at least a TTL old. Nothing is agreed on
and nothing depends on membership for the state's correctness, which the
conditional writes carry; membership steers three things:

- **Ownership.** `hash(origin) mod n` over the members in id order (FNV-1a).
  A load balancer that applies the same function sends every request for an
  origin to the node that caches it and fires its deadlines. A node that is
  not the owner forwards; if the owner cannot be reached it answers 503
  rather than serve, and a node whose last listing is a TTL old serves
  nothing, since it may be fenced out without knowing.
- **Cache.** Each node caches the documents it read or wrote, with their
  ETags, least recently used out, bounded by entries and by bytes. The owner
  of an origin uses its cache without asking the store, but only for entries
  filled a TTL and a heartbeat after the member set last changed: by then
  every node has seen the change and stopped writing what it no longer owns.
  Any other entry is revalidated with `If-None-Match`. The cache is a port
  (`cache.rs`); the one implementation is in memory.

The three rules — a member counts a TTL after it joins, a change suspends
trust, a stale view serves nothing — are what the simulation demanded: with
"the owner trusts its cache" alone, two nodes mid-change both believed they
owned an origin and one served a stale read.

All of it is decided on the fleet's time: the later of a node's own clock and
the latest announcement it has listed. A clock that steps back or runs slow
is absorbed; the fleet runs on its fastest clock. A clock that steps forward
by about a TTL is not: the node sees every peer expire and, for a heartbeat,
writes as owner of origins whose owners still trust their caches. The rules
hold while any node's skew plus its largest step, plus a heartbeat, stays
under the TTL — the bound every lease carries. Beyond it, exclusive
ownership needs a record the store arbitrates, which is celld's design and
not this one.

A step is decided at an instant never earlier than any instant the origin's
rows record (`step::clamp_now`): the kernel is proved for `now` at or after
every `created_at` and `settled_at`, and a node behind another node's clock
would otherwise step outside that.
- **Timers.** Each node holds its share of the deadlines in an in-memory
  wheel and fires from it. It lists the timer prefix only at startup, when
  the set of live nodes changes (every node's share moved), and when the
  clock reaches a bucket it has not loaded; each listing takes the keys of
  the origins it owns and nothing else. Firing is a sweep of the origin,
  idempotent, so a key fired twice costs nothing; the key is deleted once
  the sweep has committed.

A request names an origin. A node that does not own it forwards the request
to the owner over HTTP (`x-echod-forwarded` stops a second hop) and relays
the answer; if the owner cannot be reached the node serves the request
itself. Every answer carries `x-echod-node`, the node that produced it.

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
pairs, cuts nodes off the store and jumps their clocks. Clients issue every
request kind over a few origins; every attempt is a history entry, since an
attempt that got no answer may have taken effect. Sweeps enter the history
through an observer port.

The check is linearizability per origin against the kernel: an order of the
entries, each within its span, that yields every answer seen and ends in the
rows the bucket holds; an entry without an answer may be placed or skipped.
Besides that: every deadline a document owes has a key, every `execute`
names a task that exists and every `unblock` a settled promise, every kind
answered 200 at least once, and the history overlapped.

### The SDKs

`examples/ts` runs the TypeScript SDK against the server. The SDK's default
message source long-polls; `examples/ts/push.ts` is the push side, an HTTP
listener plugged into the SDK's `HttpNetwork` as its adapter, so the worker's
address is a URL. One concession in `wire.rs`: the SDK creates a sleep as a
timer with a target, which the specification refuses; the server drops the
target, and the timer is armed on its own as the specification arms it.
