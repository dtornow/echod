# echod

A Resonate server on S3 plus a worker that runs JavaScript and TypeScript
durable executions in V8. Built inside out, from the stored data up.

## Layout

| | |
|---|---|
| `rust/impl/process` | `echod-process` (library `echod_logic`): the executable concrete document machine and the decision core, a pure state machine: `State`, `Event` in, `Effect`s out, `on_event` the one step; every store call a submission under an op id, every answer a completion under the same. The whole crate is proved: `State::on_event` computes `spec_on_event`; `src/verified` holds the node's bookkeeping, membership, cache versions, deadline keys, the commit, and the list of what is assumed. No I/O, no clock, no runtime |
| `rust/impl/runtime` | `echod-runtime` (library `echod`): the node, the core's effects performed against a real store, a real clock and HTTP |
| `rust/impl/cli` | `echod`: the binary |
| `rust/spec/rover/spec` | `rover-spec` (library `rover_spec`): mathematical Rover processes, state, steps, and refinement |
| `rust/spec/rover/exec` | `rover-exec` (library `rover_exec`): deterministic execution, bounded search, and verified certificate replay |
| `rust/spec/echod/abstract/spec` | `echod-abstract-spec` (library `echod_abstract_spec`): the mathematical Resonate protocol model |
| `rust/spec/echod/abstract/exec` | `echod-abstract-exec` (library `echod_abstract_exec`): executable realization of the mathematical model |
| `rust/spec/echod/concrete/spec` | `echod-concrete-spec` (library `echod_concrete_spec`): the mathematical catalogue and Echod concrete model |
| `rust/spec/echod/refinement` | `echod-refinement` (library `echod_refinement`): the verified interpretation, relation, and concrete-to-abstract simulation |
| `rust/test/model` | `echod-model-test` (library `echod_model_test`): abstract-model trace translation and workload generation |
| `rust/test/runtime` | `echod-test-runtime` (library `echod_sim`): the synchronous deterministic effect interpreter |
| `rust/test/cli` | the simulator (`echod-sim`), the differential (`echod-diff`), the model driver (`echod-model`), and the store tests |
| `lean/` | the same three layers, for experiment |

The process is proved equal to its specification, `State::on_event` to `spec_on_event`, the commit sequence included: `flight_spec::lemma_sequence` is the order of store calls around each step. The text of keys and the bytes of documents are assumed, stated as specifications (`src/verified/mod.rs`). The runtime performs what the
process asks. The simulator is the evidence. The core and the node depend
on `resonate-core` for the traits and protocol types. Origin:
`resonate-server-blob` and `resonate-plugin-echod`.

The Anvil cluster model and the earlier refinement of the store machine
against the previous-generation `Model` are not in this tree. Catalogue,
deadline keys, cache revalidation, and fired occurrences
are to be restated as Echod concrete theorems. The document machine lives
under `rust/impl/process/src/concrete`, where it is proved equal to
`rust/spec/echod/concrete/spec`'s mathematical transitions.
The sections below that name `echod-system` or `refine/` describe that
earlier proof.

## The document machine

`echod_logic::concrete::document` (`rust/impl/process/src/concrete/document.rs`). A document is
`Doc`: an origin's objects, sorted by id, or a schedule. `handle` runs one
request on it; `run_due` one due step — a promise's timeout, a lease or a
retry timeout, one callback resumed, one listener told, or a schedule's
occurrence; `sweep` runs `run_due` until a step changes nothing or a step
limit is reached; `create_occurrence` births an occurrence in its origin.
Each ensures it computes its specification — `spec_handle`, `spec_run_due`,
`spec_sweep`, `spec_occurrence` — and those are the steps of the
Echod concrete model. `echod_refinement::concrete_refines_abstract` states that this
model refines the abstract one, and
`echod_refinement::refinement_proof` proves it; the private machinery is
consolidated in `rust/spec/echod/refinement/src/refinement_proof.rs`.

The specification is `resonatehq/resonate`, `spec/02-abstract`, as the Lean
models under `lean/` state it: 18 request handlers, the fence's check with
no action for the detached create, and the due steps. Trusted there: the
JSON codec (`assume_specification`), the key hash, `copy`, `expand`, and
`next_cron`. Their contracts refer to the abstract crate's mathematical
specifications; their executable bodies do not live in the spec crate.

The process (`rust/impl/process`) runs that machine. `doc.rs` folds an
object's rows into the model's `Doc` (`Objects::from_entries`) and writes
the `Doc` a step leaves as rows again (`into_entries`); `handler_docs`
decides a request by `handle` and a fired key by `sweep`; `handler_sched`
runs a schedule by `run_due` and `create_occurrence`. Once the write lands,
an `Execute` note goes to the address of the task's `resonate:target` tag,
an `Unblock` to its listener. Every module of the process is inside
`verus!`: each exec function ensures it computes its `spec_*` twin over the
state's view, up to `State::on_event == spec_on_event`. `src/verified` is
the node's own bookkeeping: membership, cache versions, the deadline keys it
armed, and which key a commit arms, removes and remembers (`node.rs`,
`commit.rs`, each ensuring its `spec_*` in `node_spec.rs`, `commit_spec.rs`).
What is assumed is listed in `src/verified/mod.rs`: the text of keys, the
bytes of documents, announcements and configurations, `fnv1a`, `str_eq`,
`clone_string`, `strip_prefix`, `u64_text`, and the store itself.

`cargo build` compiles both with the ghost code erased; `cargo verus verify
-p echod-concrete-spec -p echod-refinement` and
`-p echod-process` run Verus. Verus pins its own
rustc, so the two are separate toolchains.

## echod-logic and echod

The node is two crates, in the shape `celld` gives a node: a decision core
that does no I/O, and an executor that does nothing else.

```text
rust/impl/process/src/
  handler.rs         on_event. A network request above the line; below it a store answer, the heartbeat, or the wheel
  handler_node.rs    the announcement, the membership, who owns a target
  handler_docs.rs    one origin: its promises, the task inside each, a sweep of it
  handler_sched.rs   one schedule: create, read, delete, a run coming due
  handler_timers.rs  which keys are due; an origin goes to docs, a schedule to sched
  state.rs           the node, the timers, the cache, and the steps in progress
  state_node.rs      the members and the epoch, the version last seen of each origin
  state_timers.rs    deadline keys ordered by when they fall due
  types.rs           events, store calls and outcomes, effects, notes
  config.rs          the dials
  keys.rs            where everything lives under the bucket
  doc.rs             a document: rows in, the model's Doc, rows out
  target.rs          an origin's document, or a schedule's
  reason.rs          the words a refusal carries
  cache.rs           documents this node remembers, by LRU under a byte budget
  debug.rs           debug.reset, debug.snap, debug.tick, once the runtime has accepted them
  verified/          the node's bookkeeping: membership, cache, keys, the commit sequence, the trust list
rust/impl/runtime/src/
  config.rs     the dials, as flags and environment
  store.rs      the object store port: object_store behind it, S3 Express on the SDK for appends, an in-memory model
  env.rs        the clock and the listener, as ports
  admit.rs      a protocol envelope to a call the core already accepts, or the refusal
  codec.rs      an answer or a message back to the protocol's bytes
  node.rs       the executor: the core's effects, performed; the ResonateServer
  push.rs       messages out: HTTP push, and the router in front of it
  gateway.rs    POST /, GET /ready and GET /metrics
  metrics.rs    what an operator sees: OpenMetrics, with labels from closed sets only
```

### The core

`State` is everything a node holds: the node (`state_node`: the members,
the epoch, the version last seen of each origin), the timers (`state_timers`:
the wheel), the cache, and the steps in progress, one per document. `on_event`
(`handler.rs`) is the only step. It is told one thing at a time, `Event`:
the node starts; a request came in; a store call it issued has its answer;
a wake it armed has come, named for the heartbeat or the wheel; the
node stops. It answers with `Effect`s: make this call on the store and tell
me under this op id; answer this request; push this message; wake me after
this long for the heartbeat or the wheel; note this. Every event carries the
node's clock as the executor read it; the core never reads one. Nothing in
it waits, sleeps, locks or spawns, so the same events in the same order give
the same effects, which is what `rust/impl/runtime/tests/logic.rs` checks
with a bucket that is a map and a clock that is a number: a promise created,
timed out by its sweep, its listener told, its key collected, and a schedule
fired into its origin, with no runtime under it.

A store call leaves as a submission under an op id and comes back as a
completion under the same id; the core keeps, per id, which machine waits
for it, and an answer nobody waits for is dropped. Three machines wait:
a step on one document (`handler_docs`, and `handler_sched` when the
document is a schedule); the membership refresh (`handler_node`); a timer
listing (`handler_timers`). Each is an explicit phase with the data it
carries, advanced by the answer it waited on until it issues the next call
or ends. Per document one step runs at a time and the rest queue behind it;
a fire holds the schedule's slot and takes the origin's for its first
commit, and since no step on an origin ever waits for a schedule's slot,
none of this waits in a circle.

The executor (`node.rs`) is one `State` behind one lock. `apply` takes
the lock, runs the step, drops the lock, and performs what came out: a
store call is spawned and its answer applied as a completion; a reply
wakes the request waiting on it; a message is pushed; a wake resets the
one timer; a note goes to the metrics, the log, and whoever listens. The
simulation supplies the clock and the listener; everything else it
supplies is the store.

### The bucket

```text
wf/<origin>                              an origin's document: promise rows
sched/<id>                               a schedule's document: its row, or none
t/<bucket>/<deadline>_<origin>@<token>   a deadline for an origin, empty
t/<bucket>/<deadline>_sched:<id>@<token> a schedule's next run, empty
nodes/<id>                               a node's announcement: id, url, at
```

### The document

One origin is one object, JSON lines: one kernel `Promise` per row, in
commit order, serialised by serde as the kernel declares it. A task is a
field of its promise. There is no enclosing document; each write puts a
header line first, carrying the instant the step was decided at (the
stamp), a nonce, and the write's number in the object's history.

The document is the fold of the rows by id, last row wins — the kernel's
`fold_by`, whose lemmas prove any one-row-per-id rendering replays to the
same document (`compaction_replays_to_the_same_document`). Reading an origin
replays its object.

### Writing

A request loads the document, sweeps it at the request's instant and runs
the kernel handler on the swept document, drains what the step left owed
(callbacks and listeners of settled promises, retries now due), and writes
the rows that changed. The Lean specification projects a promise past its
deadline and a lease past its end on every read (`Object.project`): a
client never sees either as still ahead. The kernel keeps the promise's
projection in the document and leaves the lease to the sweep, and `decide`
sweeps before it handles (`handler_docs`), so the handler sees what a
projecting read would. A task's offers run on a grid anchored where it came
to be pending, `due + n·retryTimeout` (the kernel's `next_offer`, Lean's
`nextOffer`): a retry the sweep gets to late is rearmed where an exact
timer would have put it, a lease reclaimed is retried from its end, a task
resumed from the awaited promise's settlement. What a step writes does not
depend on when the node ran it. The step is decided at the later of the
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
the kernel's `commit.rs` decides, run by `handler_docs`: the key for the
document's nearest deadline is put before the document, unless the node
remembers a key for that instant armed with the very version it loaded;
the document is written; the key replaced is deleted; the key kept is
remembered with the version written. A key that fires sweeps its origin;
the sweep's own write, or, if nothing was due, a rewrite of the document
at a new version, fences every commit in flight that armed the key, and
then the key is deleted, whoever armed it. So a deadline a document owes
always has a key in the bucket, which the system's theorems state and prove.

A schedule's document goes through the same commit, with its next run as
the deadline it owes. Its key fires on two documents: the row decides the
occurrence's promise and its origin; the kernel's `processSchedule` runs
on the row beside the origin's objects; the origin is committed first,
then the schedule with the key fired, each under the protocol, the
schedule's conditional on the version loaded with the origin. A crash
between the two refires the occurrence, which the kernel makes a no-op
on the promise and an advance on the schedule. A key whose schedule is
not due, or gone, is collected like an origin's: behind a rewrite. An
earlier design deleted such a key outright, which the model refused: a
node ahead on its clock could delete the key another node had armed for
a schedule it had not yet written.

### Nodes

A node announces itself at `nodes/<id>` (its URL, when it last did) and
refreshes the announcement every heartbeat. The member list is one object,
`members`, holding the members and the epoch it was written in: whoever
sees the announced set differ from it writes the next epoch with a
conditional put, so epochs are totally ordered and every node reads the
same sequence. A node keeps the epoch and members it read and when it read
them. Nothing depends on membership for the state's correctness, which the
conditional writes carry; membership steers three things:

- **Routing.** `hash(origin) mod n` over the members in order (FNV-1a). A
  load balancer that applies the same function over `members` sends every
  request for an origin to the node that caches it and fires its deadlines.
  A node *acts* as owner of an origin when its view is fresh (read within a
  TTL, by its own clock) and its members make it the owner. Nodes do not
  talk to each other: a request that reaches a node that is not the owner
  is served there, revalidating the cache first. Two nodes acting on one
  origin at once waste work: one of them loses the conditional write and
  re-reads. An earlier design forwarded such a request to the owner over
  HTTP; that was the one channel between nodes besides the bucket, and it
  went with the split of the core from the executor: everything a node
  does, it does through the store.
- **Cache.** Each node caches the documents it read or wrote, with their
  ETags, least recently used out, bounded by entries and by bytes. An
  entry is never used without asking the store: every load is a conditional
  read with `If-None-Match`, and the body in memory is used only when the
  store answers not modified. The cache is a port (`cache.rs`); the one
  implementation is in memory.
- **Timers.** The acting owner fires an origin's deadlines from its wheel.

The state behind these rules and the decisions taken from it are not in
`handler_node`: they are `verified::node::NodeCore`, executable Rust
verified to compute the system model's specification functions step for
step. `handler_node` is the trusted shim around it: it announces, lists,
reads the configuration object and hands it to `read_config`; it asks
`acts`; and `handler_docs` reports every version read or written with
`filled` and every entry dropped, evicted or forgotten with `forget`, so
what the core decides on is what the cache holds. Membership is decided on the fleet's
time, the later of a node's clock and the latest announcement it listed,
which absorbs a clock that steps back or runs slow.

Clocks are a node's own. No node's clock is assumed to bear any relation to
another's or to true time, and no safety property rests on one. A clock is
read for one thing: the instant a step is decided at, where the kernel
judges what has expired. An earlier design leased ownership on clocks and
let the owner answer from its cache without asking the store; the system
proof needed a bound on skew for that, and the simulation showed stale
reads the moment the bound was exceeded. The design now asks the store
on every load, one conditional round trip, and needs no bound.

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
write of ours carries a nonce; and, on a store that appends, an append
lands only at the current size under the current version. The end-to-end
tests run on the same store under a prefix of their own when `ECHOD_STORE`
is set, and once more through `S3Store` when `ECHOD_EXPRESS_BUCKET` names
a directory bucket.

No emulator serves S3 Express appends (RustFS answers 501, MinIO's open
build has none), so `rust/test/cli/fakes3` is one of our own: the S3
surface echod uses and nothing else, in memory — conditional reads and
writes, `ListObjectsV2`, `DeleteObjects`, and `PutObject` with
`x-amz-write-offset-bytes`, refused with `InvalidWriteOffset` anywhere but
the current size, as S3 Express refuses it. ETags are the MD5, conditions
are decided atomically against the object as it is, keys round-trip byte
for byte, and the SDK's `aws-chunked` bodies are unframed. `scripts/s3-tests.sh`
runs both suites against it by default, with both clients; against RustFS
or `s3s-fs`, a second implementation's reading of the conditional writes,
without appends; or against a bucket you name. RustFS honours conditional
reads and makes versions from content, as S3 does; `s3s-fs` 0.17 ignores
`If-None-Match` on reads and sends the body where S3 sends 304, which the
store treats as a revalidation that found the version current.

### Observability

`GET /metrics` is OpenMetrics text (`prometheus-client`), one registry per
node. The rule for every label: its values are a closed set the node
decides. No origin, promise id, key, address, node id or error text is ever
a label; a request kind is a label only if the protocol defines it, anything
else is `other`. So the number of series is a small constant however many
promises, origins or workers there are, and a client cannot mint one.

What is counted, and why:

| metric | labels | tells an operator |
|---|---|---|
| `echod_requests_total`, `echod_request_duration_seconds` | `kind`, `status` | the protocol's traffic, how it ended, how long it took |
| `echod_messages_total`, `echod_message_duration_seconds` | `kind` (`execute`, `unblock`), `outcome` (`delivered`, `unroutable`, `failed`) | pushes to workers |
| `echod_store_operations_total`, `echod_store_operation_duration_seconds` | `op` (the port's nine calls), `object` (`document`, `schedule`, `timer`, `node`, `members`), `outcome` (`ok`, `not_modified`, `absent`, `conflict`, `failed`) | every call on the bucket: how many, of what, on what, and how it ended. `conflict` is a conditional write the store refused: CAS'ed out. `failed` on a write is the third outcome of the fleet model: the write may or may not have landed |
| `echod_document_writes_total`, `echod_document_bytes` | `mode` (`create`, `rewrite`, `append`) | how documents are written and how big they are |
| `echod_commits_total` | `outcome` (`committed`, `raced`: lost the race on the document and re-decided, `failed`, `exhausted`) | the commit protocol's fate |
| `echod_cache_lookups_total` | `result` (`revalidated`: a conditional read said not modified and the body in memory was used, `refreshed`: it brought a newer version, `absent`, `miss`) | what a load cost: every load is a round trip, `revalidated` the cheapest |
| `echod_cache_entries`, `echod_cache_bytes`, `echod_cache_evictions_total` | | the cache against its bounds |
| `echod_membership_refreshes_total`, `echod_configuration_writes_total` | `outcome` | the heartbeat, and who wrote the next epoch |
| `echod_configuration_changes_total` | | ownership moved: this node took on a new epoch |
| `echod_membership_epoch`, `echod_members`, `echod_node_fresh`, `echod_node_acting` | | what the node holds of the fleet, and whether it routes as the members intend |
| `echod_timer_fires_total`, `echod_timer_lag_seconds` | `kind` (`origin`, `schedule`), `outcome` (`deleted`, `kept`: the delete failed and it fires again, `failed`, `deferred`: not this node's to fire now) | deadlines firing, and how late |
| `echod_timer_listings_total`, `echod_timers_armed` | `outcome` | the three occasions a bucket is listed, and the wheel |
| `echod_sweeps_total` | `outcome` (`fired`, `idle`, `failed`) | what a fired key found |
| `echod_build_info` | `version` | |

The store is observed by a decorator over the port (`MeteredStore`), so
every backend is measured the same way and the object's kind comes from
the key's place in the bucket, not from the caller. What the core counts
it says as a `Note`, carrying a value from one of its closed sets; the
executor turns the note into the metric. The gauges are read when
scraped, from the node's state as it is then. Logs carry the names the
metrics leave out: an origin, a key, an address, an error; they too are
notes. So are the steps themselves, each as decided and then as committed
or not, with the instant, the document's version, the write's nonce and
the objects: what the simulator checks against the model (below).

### Simulation

`echod-sim` runs several production decision cores over one in-memory store
in a synchronous deterministic event loop. Virtual time advances directly
to the next queued event, so the same seed replays the same run. The
simulation owns every port: one clock the
clients stamp requests with and the nodes read (a node can be given skew,
drift and jumps, backwards included, but the run leaves them off: the
model it is checked against keeps one clock, and a node on a clock of its
own would be reported, not tested); a store that
answers nothing, loses acks or refuses conditional writes by seeded
percentages and waits a seeded latency, and per node a store that can be cut
off entirely; sent effects are recorded as model dispatches and checked
against the bucket. Scheduled chaos events crash nodes, stop them
cleanly, starts new ones and cuts nodes off the store. Clients issue every
request kind over a few origins, as the model types them; every attempt is
a history entry, since an attempt that got no answer may have taken effect.
Clients create, read and delete a few schedules firing every few seconds
into the origins the clients work on, so fires collide with requests. The
run ends with a read of every id, so what the bucket holds is what the
model holds.

The check is the Resonate model, the whole protocol
as the Lean specification has it, through Rover execution
(`rust/spec/rover/exec`): some
execution of the model must show exactly what the clients saw and the bus
carried, the model's internal work (a deadline, a lease's end, a resume, a
retry, an occurrence) placed where the checker likes. The trace is what a
client could record: every request as an invoke at the instant it was sent
(its `head.debug_time`, which is the instant the node decides it at) and a
return where its answer came, every message the bus carried as a receive,
and the clock moving to the instants the nodes stamp at, the requests'
and, through the notes port, the nodes' own sweeps and fires; a return or
a receive moves the clock nowhere, since every instant the clock visits
while a call is open is one more place the model may land its effect.
Nothing else of the nodes' account enters. What makes the check hold is
the protocol: a lease past its end reads as lost and a task's offers are
on a grid (above), so the model's exact timers and the node's sweeps agree
on every state a client can see. The one step that is not a projection, a
schedule's occurrence, the model fires anywhere from its instant to
`fire_within` later, two timer buckets here (`Options::fire_within`), the
bound within which a node gets to a key. Clients are routed to an origin's
owner, as a load balancer over the members would route them, which
serialises an origin's requests behind one flight; `--misroute` sends a
share elsewhere, where a read may miss a write the owner decided and has
not landed, whose stamp precedes the read, which one clock cannot show.
Besides that: every deadline a document owes has a key, every `execute`
names a task that exists and every `unblock` a settled promise, every kind
answered 200 at least once, and the history overlapped.

`test/runtime/src/rover_sim.rs` is an isolated experiment using generic
`RoverExec::exec` to generate a production-backed concrete trace before the
same abstract check. It does not replace the primary DST.

### Differential

`echod-diff` runs echod against the Resonate reference server, both as
processes answering HTTP, on one seeded request stream: the reference's
own differential's (its `diff/port.rs`), the same operation mix over the
same small pools of ids, steered towards the operations not yet covered.
Time is `head.debug_time` and moves only through `debug.tick`, which both
servers honour in debug mode; echod answers `debug.tick`, `debug.snap` and
`debug.reset` from `rust/impl/process/src/debug.rs`, as machines over store calls like
everything else: a tick sweeps every origin at the instant and fires every
schedule due, again and again until none is, as the timers would have had
the clock passed through every instant on the way.

Every step sends one request to each server in turn and compares the
response, the messages pushed to the harness's worker while it was
answered (the sink is given a quiet moment, since echod pushes after it
answers), and the `debug.snap` of the whole state afterwards. A run stops
at its coverage plateau or at a step cap, over several seeds, and reports
every divergence by class with the first example; a snapshot divergence
ends the episode, since the states have parted.

What is compared modulo known differences: `preload` (echod answers an
empty one), `head.serverUrl` in execute messages, and an internal promise
past its deadline (projected as expired in both, as the reference's
harness does). Error reasons are compared word for word: the kernel
proves the status, and `wire::reason_for` says why in the reference's
words, by kind and status, and where one status has several causes (a
callback's awaiter missing, or not a task, or the awaited not awaitable)
by the state the step left, which the refusing checks did not change.
The simulator's model renders its answers through the same function, so
the checker compares like with like. One more is a
deviation of the reference from the specification: on fulfilling a task
it deletes that task from every promise's callbacks, pending ones
included, which the catalogue's `monotone_promise_callbacks_grow_while_pending`
forbids. echod removes a callback only when it is consumed, as the
specification's `processCallback` does, so such callbacks are dropped
from both snapshots before the comparison (`--strict-callbacks` keeps
them). A second one: on a callback registered on a promise already
settled, the reference resumes the awaiter at once, where the
specification's `promiseRegisterCallback` answers the record and changes
nothing; it shows in a task's `resumes` count, dropped likewise
(`--strict-resumes` keeps it). The search operations are not in the
stream: echod does not serve them. Nor is a fence creating a promise in
another origin, where the two part by design ("The detached create"
below); the simulator's workload has none either, its model being one
origin at a time.

Run over four seeds to their coverage plateaus, 164,800 steps in all,
every response, message and snapshot agreed modulo the above; the two
reference deviations were the only divergence classes found. Rerun after
the detached create (two seeds, 63,200 steps), the same.

### The model driver

`rust/test/cli/model` drives echod with the Resonate model, an
executable specification in Verus of the whole protocol as the Lean
specification has it (promises, callbacks, listeners,
tasks with leases, resumes and redispatch, halt and continue, schedules),
and checks every recorded trace against it: an execution of the model must
produce exactly the observations, with the model's internal work (a
deadline, a lease, a resume, a retry, an occurrence) placed where the
checker likes. A run resets echod and takes the model's own actions, the
ones it suggests from the state it reads back through `debug.snap` (fences
at the held and a stale version, the clock to just before and at each
deadline, a settle while a task awaits, a schedule's run) or random ones; a
request is sent with the run's clock as `head.debug_time`, a clock move is
handed to echod as `debug.tick`, and every `execute` and `unblock` the sink
receives is a dispatch, with the address it came to. Then the model's
finishing reads. The marks of the execution that explains an accepted trace
are the coverage. echod runs with the model's retry timeout.

Nothing is translated: a detached create is sent as any other fence, and
`task.create` in every state. One request is not sent: a timer created with
a target, which echod accepts with the target dropped (a concession to the
SDKs' sleep, `wire::create_tags`) and the model refuses, as the Lean
specification does.

### The detached create

A fence whose create names a promise in another origin starts a detached
workflow. The two live on different documents, so they cannot commit as
one write: the create goes first, as a request of its own on its origin's
document, and the fence's check (`task_fence_check`, the kernel's fence
with no action) follows on the task's. A stale fence still leaves the
promise created, and answers its 409; the fence's answer is the check's
status with the create's record inside when it held. `dispatch::decode`
splits the request in two (`Decoded::then`), `flight::Stage` carries the
request through its two commits. A settle in another origin is refused,
as the reference server refuses it. The reference allows a cross-origin
create of a root id alone (an id with no `:`), and checks the fence first;
echod allows any id, and creates first.

## echod-system

This model is not in the tree. What follows is the proof it held, kept
here so the concrete theorems have a statement to be restated from.

The whole system as a state machine, in the shape Anvil gives a
Kubernetes cluster: a state, a `Step` for every action, each action an
`Action` value — a precondition and a transition over the step's input —
`init`, `next` as the step's action forward on its input, and Anvil's TLA
embedding (`verus-tla`, vendored) to state the theorem as `always(inv)`.
The `Action` values are what the embedding's fairness rules take, for the
liveness to come. Nothing in the crate runs: it imports the kernel under
Verus (`verify.sh` exports the kernel's metadata and imports it), so the
bucket's documents are the kernel's own states and a node's actions are
the kernel's `node`, `commit` and `steps` functions, with the contracts
the kernel proves of them.

```text
model.rs      the state and the nine actions
theorems.rs   the invariant, one lemma per action, the four theorems
tla/          the temporal logic, vendored from Anvil's verus-tla
```

The node and the commit, in the kernel, are what Anvil calls the
reconciler: sans-I/O step functions. `NodeCore` (`node.rs`) holds what a
node keeps of the configuration (epoch, members, the clock at the last
read), of its cache (each origin's version and when it was filled) and of
its deadline keys (the key kept for each origin, with the version written
with it). `Commit` (`commit.rs`) is one commit's decisions: the previous
key, whether to arm, what to delete, what to keep. Each function `ensures`
it equals the specification function of the same name on the state's
view. `steps.rs` verifies the loops the node runs around the kernel:
`sweep` leaves nothing due at its instant and leaves the document as it
was if nothing fired; `drain` is kernel steps; `next_deadline` is the
least deadline; `clamp_now` the later of clock and stamp. One primitive
is trusted with its meaning stated: FNV-1a is a function of the string,
as `str == str` and `String::clone` are.

The system state: the nodes and the bucket, and beside them a ghost
history. A node is its core's view, its body cache, whether it is alive,
its clock, and the commits it has in flight. The bucket has every document
— an origin's objects or a schedule's row, the kernel's own types — with
its version and stamp, and the deadline keys: four fields, what S3 holds.
A document is named for what it holds, and the shape is an invariant: an
origin's has no schedule, a schedule's no object. The history is what the proof remembers and no
node reads: every version written and by whom, every key armed and by
whom, which key covers each document, and one order of arms and writes.
There is no real time. A clock is a node's own, advances by any amount,
and is read for one purpose: the instant a step is decided at.

The actions: a clock advances; a node joins or crashes; a node drops a
cache entry; and the commit, five actions, one store round trip each.
`Prepare` loads the bucket's document and decides a step on it, and
touches nothing: for a request, the document after is the kernel's
`spec_handle` of the one loaded followed by any sequence of internal
steps at the same instant, what `drain` ensures; for a sweep, what `sweep`
then `drain` ensure. `AddTimer`
puts the key for the document's nearest deadline. `Process` puts the
document conditionally on the version loaded: the commit of a changed
document, or the rewrite that collects a fired key behind an unchanged
one. `DelTimer` deletes the key replaced and the key fired, and the node
remembers the key kept. `Done` closes a request that changed nothing,
with no round trip. A request's response joins a ghost log at `Process`
or at `Done`, when the client is answered. Each put carries the store's
answer: applied, refused by its condition — both decided by the bucket's
contents — or unknown, where the bucket applied it or did not,
nondeterministically, and the node, told only that it failed, forgets
what it cached and gives the commit up; what landed stays. Deletes may
fail silently. Any live node may act on any origin: which does is the
node's routing, and the theorems hold whoever does.

A schedule's key fires on two documents. `Prepare` on the promise's
origin, with the work `Fire`, loads the schedule's document too, decides
the kernel's `spec_fire` on the pair, and keeps the schedule's half
pending in the flight: what it loaded and at which version, what it
writes, its deadline, the key fired. When the origin's commit is done, by
`DelTimer` or `Done`, the pending half becomes a commit on the schedule's
document, conditional on the version loaded with the origin, and runs the
same five actions. That is the node's order, origin then schedule, and
why a crash between the two loses nothing.

Proved, 251 items, no admits:

- **Catalogue.** Every document in the bucket satisfies the kernel's
  catalogue at its stamp.
- **Timers.** Every deadline in every document — a pending promise's, a
  lease's, a retry's — has a deadline key in the bucket for its origin at
  or before it, at all times.
- **Revalidation.** A cached body whose version the bucket still holds is
  the bucket's document: a conditional read answered not modified may be
  served from the cache.

- **Occurrences.** Every occurrence a schedule has fired has its promise:
  a row whose last run is `t` has the promise its template expands to at
  `t` in the bucket, in its origin's document. The expansion is a function
  of template, schedule and instant, trusted to be the node's.

The Catalogue and Timers theorems cover both kinds of document; in
particular every schedule has a key at or before its next run. That a
key is also fired is the node's liveness, not proved: a node lists each
bucket once ahead of the clock and fires what it owns from its wheel, so a
key another node arms into a bucket already listed, for a target this node
owns, would wait for the next membership change; the node lists a bucket
once more when the clock leaves it, which bounds the wait by a bucket or
two (`handler_timers`, `Listing::Relist`). The simulator found the gap through
a schedule created on one node and owned by another, never fired. The
Occurrences theorem is why a fire commits the origin before the schedule.

What the model asks of a node's step is exactly what the node's verified
functions ensure, and nothing else. A request's document is the handler's
function then `drain`; a sweep's is `sweep` then `drain`; a fire's two are
`spec_fire` then `drain`, and a schedule's key with nothing due is what
`schedule_due` answers. `drain` and `sweep` are proved to keep every
object's key and the schedules; every handler is proved to drop no object
and to keep the other kind's rows (`lemma_spec_handle_keeps`). From these
the proof derives what it needs of a step — that a document keeps its
kind, that no object is lost, that a schedule's rows are the handler's —
rather than assuming it. The catalogue alone would not give the first two:
written from the Lean, it allows a step to drop a promise.

All four as corollaries of one invariant that `init` establishes and every
action preserves, assembled into `spec ⊨ □inv` by the embedding's induction
rule. A witness shows the invariant is not vacuous. Nothing is assumed of
any clock.

The proof changed the design twice. A node that fires a key could delete
it while a commit that armed it was still between its key and its
document; so a fired key is deleted only after a write of the document —
the sweep's own, or a rewrite when nothing was due — which fences such
commits. That the write suffices, whoever armed the key, rests on a ghost
order of the bucket's events: a later writer's cover was armed, or kept
from a version written, after the version the fired key's commit loaded,
so it is never that key. And an earlier model leased ownership on clocks
within a bound of real time, so that the owner could answer from its cache
without a round trip; the bound was the one hypothesis the proof carried,
and the design dropped it: every load asks the store, and the model has
no real time.

How the proof reaches the running code: the theorems are about the system
model; the model's node actions are the kernel's node, commit and steps
specification functions; their executable functions are verified
to compute those functions; `echod-logic` keeps its membership, cache and
deadline-key state in the core and takes its decisions from it, runs
the step module's loops, and serves every request through the kernel's
`handle`: the runtime turns the envelope into a `Request`, the core makes one
call, and the runtime renders the `Response`, so the request the model's `Prepare`
carries is the request the node runs. That is Anvil's shape of refinement: functional,
per step, with a trusted shim. The shim here is `handler_docs`,
`handler_sched`, `handler_node` and `handler_timers`, and it is now a pure
function of its events: that the
configuration handed to `read_config` is the object read, that every
version read or written is reported, that the store calls are issued in
the protocol's order with the decisions the core made, that the document
decoded is the one written. What stays outside it, in `echod`, is that
the executor performs every effect and feeds back every answer, and that
the bucket behaves as the model's: conditional writes on versions, one
version per content. The S3 model's fidelity and liveness are not proved.

### The SDKs

`examples/ts` runs the TypeScript SDK against the node. The SDK's default
message source long-polls; `examples/ts/push.ts` is the push side, an HTTP
listener plugged into the SDK's `HttpNetwork` as its adapter, so the worker's
address is a URL. One concession in the runtime's codec: the SDK creates a sleep as a
timer with a target, which the specification refuses; the node drops the
target, and the timer is armed on its own as the specification arms it.
