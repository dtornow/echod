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

    fn apply(&self, op: &Self::Op, s: &Self::State) -> Vec<Outcome<Self>>;      // linearization point
    fn step(&self, st: &Self::Step, s: &Self::State) -> StepResult<Self>;       // Disabled | Discharged | Next(..)
    fn fairness(&self, st: &Self::Step) -> Fairness;                            // May | Eventually { within }
    fn admits(&self, expected: &Self::Resp, observed: &Self::Resp) -> bool;     // default: ==
    fn op_keys(&self, op: &Self::Op) -> Keys<Self::Key>;                        // default: All
    fn step_keys(&self, st: &Self::Step) -> Keys<Self::Key>;                    // default: All
}
```

Mapping from Accordant:

- `[State]` + source generator → `#[derive(Clone, PartialEq, Eq, Hash)]`. Ownership
  replaces freezing: `apply` gets `&State` and returns new states. Nodes hold
  `Arc<State>` and are deduplicated with full equality, not just a hash.
- `Expect.That(pred).ThenState(f).Triggers(t)` → `Outcome { resp, next, spawn }`.
  The response is a value, not a predicate, so it can be stored in a node and
  hashed. Wildcards (server ids, timestamps) go in `admits`.
- `Expect.OneOf` → returning several outcomes.
- `IStepFunction` / `AsyncOperation` → a `Step` enum value. `IsTerminalState` → `StepResult::Discharged`.
- `StateProfile` → `Checker::profile()`, a `Vec<Node>`.
- `spec.Allows(op, req, resp, profile)` → `checker.call(id, op, resp)`.
- `AllowsConcurrent` with happens-before edges → overlapping `invoke`/`ret`; real-time order *is* the happens-before relation.

A node is `(Arc<State>, BTreeSet<Pending>)`:

```rust
enum Pending<Op, Resp, Step> {
    InFlight  { call, op },          // invoked, not linearized
    Responded { call, resp },        // linearized, awaiting Return
    Ghost     { call, op, ttl },     // client gave up; may still take effect
    Forced    { call, op },          // a ghost this branch commits to applying now
    Step      { step, must, ttl },   // background work
    Due       { step },              // obligation past its deadline
}
```

## Separating request from response

The history is a sequence of events:

```rust
enum Event<Op, Resp> { Invoke(CallId, Op), Return(CallId, Resp), Lost(CallId), Quiesce }
```

- `Invoke` adds `InFlight`. It changes no state and observes nothing, so it never
  triggers exploration.
- The checker places each call's linearization point: firing `InFlight` runs
  `apply` and leaves `Responded { resp }`.
- `Return` must match a `Responded` via `admits`.
- `Lost` turns `InFlight` into `Ghost` (it may still take effect, for a bounded
  window, or never) or drops `Responded` (it took effect; only the reply was lost).
  This replaces Accordant's duplicated `OneOf` outcomes and is strictly more
  precise: the effect may land after a read that missed it.
- `call(id, op, resp)` is `Invoke` + `Return`, so Accordant-style coupled checking
  is the special case.

This is linearizability checking in the style of Wing & Gong / Lowe's
just-in-time linearization, with background steps and bounded ghosts added.

## "Eventually", with a budget

`Fairness::Eventually { within: Some(k) }`: the step must have fired by the time
the k-th later response completes. A call that linearized just before may still
miss it. After the deadline it becomes `Due` and fires before every response
while it is enabled. If it is disabled, nothing is owed: weak fairness.
`within: None` defers the obligation to the next `Quiesce`.

`Quiesce` says the system is idle: every enabled obligation has fired and every
ghost has landed or never will. It replaces the poll-until-terminal loop as the
liveness check. You poll the real system until it says it's idle, then assert
`Quiesce`, and any later read that shows unfinished work is a violation.

`Fairness::May` is work that is allowed but not owed: daemons, optional retries.

Budgets count **responses**, not events. Invokes observe nothing, so deferring
work past them costs nothing.

## Pruning the cone

The profile grows from work that might or might not have happened yet. Six
mechanisms keep it small. The first four are in the prototype.

1. **Lazy, observation-driven firing.** Nothing fires unless a response needs it.
   For a `Return(c)`, the search fires only until nothing owed before that event
   remains (`InFlight c`, `Forced`, enabled `Due`), and then stops. Any later moves
   commute past the event and are left for the next observation. Accordant's
   `SystemChecker` instead keeps the whole interleaving closure, including moves
   after the last call.
2. **Footprints (P-compositionality).** Each request and step declares the keys it
   touches. To explain a response, the checker only tries work whose keys
   intersect what is owed, closed transitively over pending work. Work on other
   keys commutes and stays pending. `Keys::All` is the sound default.
   *Measured (`tests/bank.rs`): 8 concurrent deposits on 8 accounts → profile width
   1 and 32 nodes explored with footprints, versus width 128 and 2,458 nodes without.*
3. **Bounded lag.** Ghosts expire after `ghost_ttl` responses, branching once into
   "landed" or "never". Obligations expire after `within`. Nothing waits forever,
   so the number of optional items in a node is bounded by the rate of
   observations.
4. **Subsumption (antichains).** Optional work (ghosts, `May` steps) can always be
   dropped. So a node simulates any node with the same state and the same owed
   work but a subset of its optional work, and the subset node is discarded.
5. **Structural step identity.** Steps are values, so identical work spawned on
   different branches converges to the same node. Accordant's GUIDs prevent this.
6. **Hard limits.** `max_width` and `max_explore` turn a blowup into an error that
   names the event. Exceeding them usually means the spec is missing a footprint
   or has unbounded nondeterminism.

Not in the prototype yet, and worth adding in this order:

- **Sleep sets / dynamic POR** inside a single explanation. Today the visited set
  already merges commuting diamonds into one node; sleep sets would also skip
  the redundant edges.
- **Hash-consing** of states (`Arc` interner plus a cached 128-bit hash), so
  equality is a pointer comparison and hashing isn't repeated per node.
- **Symmetry reduction**: canonicalize interchangeable ids (`rd:A` vs `rd:B`).
- **Response-dependent state** (server-chosen ids): a `refine(op, observed, s)`
  hook applied at `Return`, or a finite id domain enumerated in `apply`.
- **Model checking the spec itself**: BFS over the same nodes with ops drawn from
  an input set. This gives test generation and Büchi-style lasso detection for
  unbounded `Eventually` obligations that a cycle can postpone forever.

## Resonate on this model

| Resonate (C#) | Rust |
|---|---|
| `ServerState { Promises, Tasks, Now }` | `State` with `BTreeMap`s (deterministic `Hash`) |
| `Handler<CreatePromise>(PromiseCreate)` | an `Op::CreatePromise { .. }` arm in `apply` |
| `ResumeTriggers` → `AsyncOperation.Create(isTerminal: !Fireable, ...)` | `Step::Resume { awaited, awaiter }`; `step` returns `Discharged` when it's no longer fireable |
| `LeaseTriggers`, `RetryTriggers` | `Step::LeaseTimeout(id)`, `Step::Retry(id)`; `Fairness::Eventually { within: Some(k) }` |
| `ServerOperation` + `IndefiniteFailures` duplicating outcomes | `Event::Lost`: nothing to duplicate |
| `PollLiveness(terminal)` | `checker.all(terminal)` while polling; `Quiesce` as the bound |
| `debug.messages` (execute/unblock) | outbound messages as their own `Invoke`/`Return` pairs, or an `Op::Drain` whose response is the message multiset |
| footprint | promise id plus awaiter ids for callbacks; `AdvanceClock` is `Keys::All` |

## Files

- `src/lib.rs`: the `Spec` trait, `Outcome`, `StepResult`, `Fairness`, `Keys`.
- `src/checker.rs`: profile, events, budgets, footprint-pruned search, subsumption.
- `tests/bank.rs`: overlapping calls, double-spend, real-time order, late and lost effects, pruning measurement.
- `tests/jobs.rs`: background completion, bounded eventually, `Quiesce`, deferred independent jobs.
