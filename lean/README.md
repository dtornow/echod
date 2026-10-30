# Rover

Rover is an append-only message-passing model of the full public Resonate
abstract protocol pinned in `lakefile.toml`.

## Full abstract machine

- `src/Protocol.lean` defines the shared public aliases, transport envelopes,
  and boundary event types.
- `src/abstract/Machine.lean` defines a dependent `DocumentKey`/`Document`
  store.
  `OriginDocument origin` contains fused promise/task rows whose ids can only
  reconstruct that origin. Every schedule has its own distinct
  `schedule id` key and an id-indexed schedule document.
- `Handler key α` is fixed-key Reader+State+Writer. Its state is only
  `Document key`; the global store is not available inside a handler, and bind
  can compose only handlers at the same key. Writes are immediately visible
  inside that document and Writer emissions preserve order.
- `Store.read_write_other`, `Direct.runWith_frame`, and
  `Direct.runWith_changedOnly` prove that committing a handler frames every
  differently indexed document. Origin and schedule keys are disjoint by
  constructor.
- `src/abstract/External.lean` implements the 21 external operations as indexed
  handlers or, for unsupported searches, pure 501 responses. Multi-id
  operations validate one origin before receiving one origin document.
- `src/abstract/Internal.lean` implements promise, callback, listener, lease,
  retry, schedule, and occurrence work as one-document handlers.
- `src/abstract/System.lean` provides dispatch, run, internal work, and timeout
  semantics. `Resonate.run` executes external calls at
  `Call.requestedAt`; `runTimeout` advances at most one document transaction.
- `src/abstract/Model.lean` has one service process. Only external calls are
  injectable. A timeout carries no internal request and nondeterministically
  stutters, executes one pending schedule occurrence, or executes one currently
  eligible document item at a logical firing instant no later than the Rover
  step time. The item's own due predicate holds at that logical instant. The
  finite executable relation enumerates all such instants. Schedule work
  updates only its schedule document and queues occurrences; every occurrence
  updates its origin document on a separate later timeout at the occurrence
  instant. Work newly enabled by a handler waits for a later timeout.
- The service sends Writer emissions directly into the Rover network alongside
  boundary responses. Internal work is never represented as a wire message.
- `src/TraceChecker.lean` searches the full request/response/message
  boundary protocol. A successful certificate is replayed against Rover and
  `check_valid_sound` proves that every `valid` verdict is a real abstract
  behavior. Its timeout action enumerates every finite abstract timeout choice.
  Exhaustion is conservatively `unknown`.
- `src/Examples.lean` contains executable promise, task,
  read-your-own-writes, schedule, ordered and non-deduplicated message,
  timeout-sweep, deferred-work, retry, and trace-checking tests.

The public protocol types under `01-protocol` are authoritative. The local
model reuses the public `PromiseObject`, `TaskObject`, `Object`, and
`Schedule` types and their pure projection/record helpers.

## Full concrete model

`src/concrete/Model.lean` models `Resonate.Concrete`: any duplicate-free list
of server nodes and one
physical store over the same dependent `DocumentKey`/`Document` family.
Store payloads are exactly `get key` and
`put key document expectedVersion`; operation ids are in separate
`RpcRequest`/`RpcReply` envelopes. Calls, loaded snapshots, selected responses
and emissions, workflow continuations, phase, and retry count remain in
node-local flights.

Each document has an optional independent version. Conditional PUT has
acknowledged-written, landed-but-failed, and candidate-not-landed failed
outcomes. The latter consumes the expected version while retaining the old
logical document, so a raw duplicate cannot land after its continuation was
discarded. Flights consume an operation reply at most once. Node timeouts
start a private key/time scan, then execute only work selected from the
validated GET snapshot using that retained logical time. This machinery is
absent from abstract state. Schedule occurrence continuations are separate
later origin-document transactions.

`src/concrete/Refinement.lean` defines `Resonate.Refinement`, including ghost
raw-PUT provenance, per-document store
representation, duplicate reply/PUT lemmas, the reachable one-step simulation
interface, and a proved execution fold preserving the complete boundary
trace. `boundary_refinement` proves
`Concrete.ValidBoundaryTrace → Abstract.ValidBoundaryTrace` for arbitrary
duplicate-free node lists when conditional writes are enabled.

With abstract `Config.unreliable`, the Rover process admits normal service,
landed-but-lost service, and pre-transaction shedding. The trace checker
searches and replays all three branches.

Build with:

```sh
lake build
```
