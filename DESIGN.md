# Accordant in Rust: the model

This covers only the spec/model layer: what a spec is, what the checker keeps, and
how it decides whether an observed history is allowed. Test generation, drivers
and wire clients are left out.

## What Microsoft Accordant's model is

Read from `Accordant/` and `Accordant.Operations/`:

| Accordant | Meaning |
|---|---|
| `[State]` class | The abstract state. A source generator adds clone, freeze and a 64-bit hash. |
| `Operation(req, state) → Expect.OneOf(...)` | Each outcome is a response predicate, a next-state function and optional `.Triggers(step functions)`. |
| `IStepFunction.Apply(state) → [(state', new step functions)]` | Background work. Consumed when it fires. `TerminatingStepFunction` adds `IsTerminalState`. |
| `StateGraphNode` | `(state, set of pending step functions)`, fingerprinted by state hash plus step-function ids. |
| `StateProfile` | The set of nodes still consistent with the observations. |
| `SystemChecker.Validate` | For each batch of concurrent calls, explores every interleaving of the calls (as `ContractStepFunction`s) and the pending background steps, and keeps the nodes where every call has been consumed. |
| `Choose.Each` | Enumerates nondeterministic choices by re-running the lambda over a choice coordinate. |

Three properties of that model matter for the Rust version:

1. **A call is one atomic step.** Request and response are checked together. A
   timeout is modeled as `OneOf(no effect, effect)` *at the moment of the
   timeout*; the effect can never land later. Resonate's `ServerOperation`
   duplicates every outcome to get this (`Spec/Harness.cs`).
2. **"Eventually" exists only at test time.** `TerminatingStepFunction` says when
   work is done; the runner polls up to `MaxRetryCount` times
   (`TraceRunner.PollLiveness`). The spec has no notion of a deadline, so the
   profile carries every not-yet-fired step indefinitely.
3. **Step functions are closures with GUID ids.** `AsyncOperation.Create` gets a
   fresh GUID, and the node fingerprint includes it
   (`StateGraph.GetNodeFingerprint`). Two branches that trigger the same
   `resume:A->B` never converge. The fingerprint is a hash with no equality
   fallback.

## The Rust model

```rust
pub trait Spec {
    type State: Clone + Eq + Hash + Debug;
    type Op: Data;    // requests, usually one enum variant per operation
    type Resp: Data;  // abstract response the spec predicts
    type Step: Data;  // background work as a value, not a closure
    type Key: Data;   // footprint keys

    fn apply(&self, op: &Self::Op, s: &Self::State, now: Time) -> Vec<Outcome<Self>>;  // linearization point
    fn step(&self, st: &Self::Step, s: &Self::State, now: Time) -> StepResult<Self>;   // Disabled | Discharged | Next(..)
    fn fairness(&self, st: &Self::Step) -> Fairness;                                   // May | Eventually { within }
    fn admits(&self, expected: &Self::Resp, observed: &Self::Resp) -> bool;            // default: ==
    fn op_keys(&self, op: &Self::Op) -> Keys<Self::Key>;                               // default: All
    fn step_keys(&self, st: &Self::Step) -> Keys<Self::Key>;                           // default: All
}
```

Mapping from Accordant:

- `[State]` + source generator → `#[derive(Clone, PartialEq, Eq, Hash)]`. Ownership
  replaces freezing: `apply` gets `&State` and returns new states. States are
  immutable once the checker has them; see [State representation](#state-representation).
- `Expect.That(pred).ThenState(f).Triggers(t)` → `Outcome::new(resp, next).spawn(t)`.
  The response is a value, not a predicate, so it can be stored in a node and
  hashed. Wildcards (server ids, timestamps) go in `admits`.
- `Expect.OneOf` → returning several outcomes.
- `IStepFunction` / `AsyncOperation` → a `Step` enum value. `IsTerminalState` → `StepResult::Discharged`.
- `StateProfile` → `Checker::profile()`, a `Vec<Node>`.
- `spec.Allows(op, req, resp, profile)` → `checker.call(id, op, resp)`.
- `AllowsConcurrent` with happens-before edges → overlapping `invoke`/`ret`; real-time order *is* the happens-before relation.

A node is `(Interned<State>, BTreeSet<Pending>)`:

```rust
enum Pending<Op, Resp, Step> {
    InFlight  { call, op, since, must },   // invoked at `since`, not linearized
    Responded { call, resp },              // linearized, awaiting Return
    Step      { step, after, by, must },   // background work, due from `after`, owed by `by`
}
```

## Separating request from response

The history is a sequence of events, each at the checker's current time:

```rust
enum Event<Op, Resp> { Invoke(CallId, Op), Return(CallId, Resp), Tick(Time), Quiesce }
```

- `Invoke` adds `InFlight`. It changes no state and observes nothing, so it never
  triggers exploration.
- The checker places each call's linearization point: firing `InFlight` runs
  `apply` and leaves `Responded { resp }`.
- `Return` must match a `Responded` via `admits`.
- **A call that never returns is not an event.** The client can't distinguish a
  lost request from a lost reply from a slow server, so the model doesn't either.
  The call stays `InFlight`: it may take effect at any later point, including
  after reads that missed it, or never. Accordant's `OneOf(no effect, effect)` at
  the moment of the timeout is a special case that is too strict, because it
  forbids the late effect.
- What bounds that uncertainty is a time assumption about the server:
  `Config::request_lifetime = Some(d)` means a request takes effect within `d` of
  its invoke or never. When the clock passes `since + d`, each branch commits
  once: either it took effect by then (it must linearize at that instant at the
  latest) or it never will (the `InFlight` is dropped, and a later `Return` is a
  violation). A response that arrives late is still fine if the effect happened in
  time.
- `call(id, op, resp)` is `Invoke` + `Return`, so Accordant-style coupled checking
  is the special case.

This is linearizability checking in the style of Wing & Gong / Lowe's
just-in-time linearization, with time, background steps and request lifetimes added.

## Time

The checker owns the clock. Every event happens at `now`. `tick(t)` advances it,
and the spec reads it in `apply` and `step`.

- **Timers.** An outcome or step successor can install one:
  `Outcome::new(resp, next).timer(at, Step::Timeout(id))`. A timer is a step that
  is not enabled before `at`.
- **Deadlines.** `Fairness::Eventually { within: Some(d) }` means the step must
  fire within `d` of becoming due. `Some(0)` is an exact timer: it fires at `at`,
  unless something disables it first (a job that completed before its timeout
  discharges the timer).
- **Stepping through time.** `tick(t)` doesn't jump. It stops at every instant in
  `(now, t]` where some candidate's timer becomes due, a deadline passes, or a
  request lifetime ends. At each instant, work that is overdue fires *at its
  deadline*, so a step that reads `now` (for example to set `settled_at`) sees the
  right time. Work that is merely due is still lazy: it fires when an
  observation needs it, or when its deadline passes.
- **Weak fairness.** An overdue obligation that is disabled owes nothing. It
  fires as soon as it is enabled again, before time moves on.
- **`Quiesce`** asserts the system is idle at `now`: every obligation that is
  already due must have fired. Future timers are untouched, and so are calls
  still waiting for a response. It replaces the poll-until-terminal loop as the
  liveness check.
- `Fairness::May` is work that is allowed but not owed: daemons, optional retries.

The clock is logical and test-driven. That matches a server with a controllable
clock, like Resonate's `AdvanceClock`/debug time: test time *is* server time, so
timeouts are exact. A wall-clock system needs one more thing, and it isn't built
yet: events with timestamp intervals, and linearization points chosen among the
timer instants inside a call's interval.

## Non-determinism

The checker is angelic: a history conforms if *some* resolution of every choice
explains it. There are five sources of choice.

| Source | How it's written | Who resolves it |
|---|---|---|
| **Outcome**: the server may answer or act in several ways | `apply` / `step` return several outcomes or successors (Accordant's `OneOf`) | the observations that follow |
| **Interleaving**: the order of concurrent calls and background work | implicit: every pending item is a possible next move | the search, pruned by footprints |
| **Timing**: when due work fires inside its window | `after` / `by` windows from timers and `Fairness` | the search, bounded by deadlines |
| **Unknown fate**: whether an unanswered request took effect | implicit for every call without a `Return` | later reads; `request_lifetime` bounds it |
| **Unknown values**: server-chosen ids, timestamps | `admits` with a pattern; see below | the `Return` |

Every choice is lazy. A branch exists only when something forces the move:
- An outcome splits when its call linearizes, which happens when its response,
  an overlapping response, or a deadline needs it.
- A background step with two outcomes, like a job that completes or fails, stays
  one pending item until a read needs it.
- Only then does it become two nodes, and the next read usually deletes one of them.

Value non-determinism is the open item. Enumerating a finite domain in `apply`
works, but large domains (UUIDs) need late binding: the outcome stores a
placeholder, and a `refine(op, observed, state)` hook substitutes the observed
value at `Return`. Reads that touch the placeholder before then have to treat it
as unknown, as Accordant's `HasUnknownJob` does.

## Pruning the cone

The profile grows from work that might or might not have happened yet. Six
mechanisms keep it small, and all six are in the prototype.

1. **Lazy, observation-driven firing.** Nothing fires unless a response or a
   deadline needs it. For a `Return(c)`, the search fires only until nothing owed
   remains, and then stops. Any later moves commute past the event and are left
   for the next observation. `Invoke` never searches. Accordant's `SystemChecker`
   instead keeps the whole interleaving closure, including moves after the last call.
2. **Footprints (P-compositionality).** Each request and step declares the keys it
   touches. To explain a response, the checker only tries work whose keys
   intersect what is owed, closed transitively over pending work. Work on other
   keys commutes and stays pending. `Keys::All` is the sound default.
   *Measured (`tests/bank.rs`): 8 concurrent deposits on 8 accounts → profile width
   1 and 32 nodes explored with footprints, versus width 128 and 2,458 nodes without.*
3. **Deadlines.** Obligations have a `by`, and unanswered requests have a lifetime.
   When the clock passes a deadline, the uncertainty is resolved once and then
   gone. Nothing stays pending forever unless the spec says so.
4. **Subsumption (antichains).** `May` work can always be skipped. So a node
   simulates any node with the same state and the same owed work but a subset of
   its `May` work, and the subset node is discarded.
5. **Structural step identity.** Steps are values, so identical work spawned on
   different branches converges to the same node. Accordant's GUIDs prevent this.
6. **Hard limits.** `max_width` and `max_explore` turn a blowup into an error that
   names the event. Exceeding them usually means the spec is missing a footprint
   or has unbounded non-determinism.

Not in the prototype yet, and worth adding in this order:

- **Wall-clock time**: interval timestamps on events (see [Time](#time)).
- **Late binding for unknown values** (see [Non-determinism](#non-determinism)).
- **Sleep sets / dynamic POR** inside a single explanation. Today the visited set
  already merges commuting diamonds into one node; sleep sets would also skip
  the redundant edges.
- **Symmetry reduction**: canonicalize interchangeable ids (`rd:A` vs `rd:B`).
- **Model checking the spec itself**: BFS over the same nodes with ops drawn from
  an input set. This gives test generation and Büchi-style lasso detection for
  unbounded `Eventually` obligations that a cycle can postpone forever.

## State representation

States are immutable and shared. Two pieces make that cheap:

- **`HashedMap<K, V>`** (`src/hashed_map.rs`): an `imbl::OrdMap` that also keeps a
  wrapping sum of per-entry hashes. A clone is O(1) and an update copies one path,
  so states that differ in one account share everything else. Its `Hash` writes
  only the length and the sum, so hashing a state is O(1) per map instead of a
  walk over every entry. Equality still compares contents, but `imbl`'s diff skips
  shared subtrees. A sum collision costs one comparison and is never unsound.
- **Interner** (`src/intern.rs`): each new state is hashed once and stored once.
  Nodes hold an `Interned<State>`, a pointer plus the cached hash, so node hashing
  and equality inside the search are a `u64` and a pointer comparison. States no
  node holds are dropped after every event.

Use `HashedMap` for every map-shaped part of the state. A field outside a map
still hashes in full, which is fine when it is small, like `now`.

`examples/bank_bench.rs` runs rounds of 8 concurrent deposits with footprints
off, so the profile fans out to 128 nodes. 48,840 nodes are explored either way.
These times are with the interner on.

| accounts | state | time | nodes/s | peak memory |
|---:|---|---:|---:|---:|
| 10,000 | `BTreeMap` (copied) | 14.6 s | 3,340 | 64.2 MiB |
| 10,000 | `imbl::OrdMap` | 5.8 s | 8,379 | 0.6 MiB |
| 10,000 | `HashedMap` | 0.20 s | 248,948 | 0.6 MiB |
| 100,000 | `BTreeMap` (copied) | 171.4 s | 285 | 640.2 MiB |
| 100,000 | `imbl::OrdMap` | 58.5 s | 835 | 1.3 MiB |
| 100,000 | `HashedMap` | 0.27 s | 183,530 | 1.3 MiB |

Before the interner, the 10,000-account runs took 27.6 s with `BTreeMap` and
21.3 s with `OrdMap`. A persistent map alone fixes memory but not time: hashing
still walks every entry. The incremental hash is what fixes time.

## Resonate on this model

| Resonate (C#) | Rust |
|---|---|
| `ServerState { Promises, Tasks, Now }` | `State` with `HashedMap<Id, PromiseState>` and `HashedMap<Id, TaskState>`; `Now` moves to the checker's clock |
| `AdvanceClock` request | `checker.tick(t)` alongside the call that advances the server's debug clock |
| `Handler<CreatePromise>(PromiseCreate)` | an `Op::CreatePromise { .. }` arm in `apply` |
| promise `TimeoutAt` + `Project(now)` | `.timer(timeout_at, Step::Timeout(id))` with `within: Some(0)`; the projection becomes a real transition at the deadline |
| `ResumeTriggers` → `AsyncOperation.Create(isTerminal: !Fireable, ...)` | `Step::Resume { awaited, awaiter }`; `step` returns `Discharged` when it's no longer fireable |
| `LeaseTriggers`, `RetryTriggers` | timers: `.timer(acquired_at + ttl, Step::LeaseTimeout(id))`, `.timer(due, Step::Retry(id))` |
| `ServerOperation` + `IndefiniteFailures` duplicating outcomes | nothing: an unanswered call is already "maybe", bounded by `request_lifetime` |
| `PollLiveness(terminal)` | `checker.all(terminal)` while polling; `Quiesce` as the bound |
| `debug.messages` (execute/unblock) | outbound messages as their own `Invoke`/`Return` pairs, or an `Op::Drain` whose response is the message multiset |
| footprint | promise id plus awaiter ids for callbacks; ticks touch only what has a timer due |

## Files

- `src/lib.rs`: the `Spec` trait, `Outcome`, `Succ`, `StepResult`, `Fairness`, `Keys`, `Time`.
- `src/checker.rs`: profile, events, clock, deadlines, footprint-pruned search, subsumption.
- `src/hashed_map.rs`: persistent map with an incrementally maintained hash.
- `src/intern.rs`: hash-consing of states.
- `examples/bank_bench.rs`: the large-bank benchmark (`cargo run --release --example bank_bench -- [accounts] [rounds] [concurrency]`).
- `tests/bank.rs`: overlapping calls, double-spend, real-time order, unanswered requests, request lifetime, pruning measurement.
- `tests/jobs.rs`: background completion, run deadlines, timeout timers, `Quiesce`, deferred independent jobs.
