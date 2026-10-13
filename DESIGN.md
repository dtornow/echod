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
pub trait Model {
    type State: Clone + Eq + Hash + Debug;
    type External: Data;   // a request a client sends
    type Response: Data;   // what the system answers to a request
    type Internal: Data;   // work the system does on its own (a timeout, a resume)
    type Dispatch: Data;    // what the system sends to clients on its own (`()` if nothing)

    // Each defaults to "nothing": a model writes only what it has.
    fn external(&self, req: &Self::External, s: &Self::State) -> Vec<ExternalOutcome<Self>>;  // [] = can't take effect
    fn internal(&self, req: &Self::Internal, s: &Self::State) -> Vec<InternalOutcome<Self>>;  // [] = can't run yet; [InternalOutcome::same(s)] = done
    fn now(&self, s: &Self::State) -> Time;                                                    // default: 0
}

pub struct ExternalOutcome<M> { next: M::State, resp: M::Response, work: Vec<Sched<M::Internal>>, send: Vec<M::Dispatch> }
pub struct InternalOutcome<M> { next: M::State,                     work: Vec<Sched<M::Internal>>, send: Vec<M::Dispatch> }

/// Optional, for speed: which keys a step touches.
pub trait Footprint: Model {
    type Key: Data;     // a promise id, an account name
    fn external_touches(&self, req: &Self::External) -> Touches<Self::Key>;  // Everything | Only(vec![..])
    fn internal_touches(&self, step: &Self::Internal) -> Touches<Self::Key>;
}

/// Optional, for speed: keys fall into independent groups.
pub trait Partitioned: Footprint {
    type Group: Data;      // Resonate: the id's origin
    fn group(&self, key: &Self::Key) -> Self::Group;
    fn restrict(&self, s: &Self::State, keep: &dyn Fn(&Self::Group) -> bool) -> Self::State;
    fn join(&self, a: &Self::State, b: &Self::State) -> Self::State;
}
```

**Server-sent messages.** Requests and internal work can send dispatches to
clients: `.send(msg)` on either outcome, with messages of the model's own
`Dispatch` type (`()` for a model that sends nothing).
The client's side is `Event::Receive(msg)` (`checker.receive(msg)`). A sent
message is delivered at most once, in any order, at any time after it was sent,
or never; an unreceived message is optional, so it never forces a split.
Receiving a message no explanation has sent yet forces the internal work that
could send it, searched on the message's keys (`Footprint::dispatch_touches`).
Resonate uses this for `Dispatch::Execute { id, version }`, sent by the step that
makes a task pending: created with a target, resumed, reclaimed after its lease,
or released. Sending from that step, rather than from a separate "dispatch
later" step, matters: a separate step may or may not have run before any later
request, which doubles the explanations per task.

`ExternalOutcome` is one thing the system may do when a request takes effect: the
response, the next state, and the internal work it starts. `external` returns
several when the system may do several things. Rust can't tell whether a model
implements an optional trait, so the constructor says how much to use:
`Checker::new`, `Checker::with_footprints` or `Checker::with_partitions`.

Mapping from Accordant:

- `[State]` + source generator → `#[derive(Clone, PartialEq, Eq, Hash)]`. Ownership
  replaces freezing: `apply` gets `&State` and returns new states. States are
  immutable once the checker has them; see [State representation](#state-representation).
- `Operation(req, state)` → `Model::external`; `Expect.That(pred).ThenState(f).Triggers(t)` → `ExternalOutcome::new(resp, next).later(t)`.
  The response is a value, not a predicate, so it can be stored in a node and
  hashed, and a client must see exactly it. Wildcards (server ids, timestamps)
  are not supported yet.
- `Expect.OneOf` → returning several outcomes.
- `IStepFunction` / `AsyncOperation` → a `Model::Internal` value, run by `Model::internal`. `IsTerminalState` → returning `vec![InternalOutcome::same(state)]`.
- `StateProfile` → `Checker::profile()`, a `Vec<Node>`.
- `spec.Allows(op, req, resp, profile)` → `checker.call(id, op, resp)`.
- `AllowsConcurrent` with happens-before edges → overlapping `invoke`/`ret`; real-time order *is* the happens-before relation.

A node is `(Interned<State>, BTreeSet<Pending>)`:

```rust
enum Pending<Req, Resp, Internal, Dispatch> {
    External { call, req, early },   // invoked, not yet settled
    Settled  { call, resp },         // settled, awaiting Return
    Internal { sched, count },       // an internal op scheduled: later, or at a time
    Sent     { msg, count },         // a dispatch sent, not yet received
}
```

## Checking a trace

A trace is a sequence of observations. It can be a `Vec`, or any iterator,
including one that generates observations lazily: the checker consumes them one
at a time and never holds the whole trace.

```rust
let mut c = Checker::with_partitions(Resonate, Server::default(), Config::default());

c.check(events)?;        // Event::Invoke / Return / Receive, in the order observed
c.check_calls(calls)?;   // (External, Response): sequential calls, each answered before the next
```

Each returns `Ok(&Stats)` if some run of the model produces exactly these
observations, or the first `Violation`, whose `index` is that observation's
position in the trace. The checker keeps its state afterwards, so a long trace can be fed in pieces.
`check_calls` is the shape of a request/response log, like
resonate-specification's NDJSON traces.

### Three answers: OK, KO, UNKNOWN

A rejection is not always a refutation. The checker gives up when a search
exceeds `max_explore`, when the profile exceeds `max_width`, when the spec breaks
a rule the checker relies on (work escaping its partitions), or when a
certificate can't be produced. Those `Violation`s carry `unknown: true` and a
reason starting with "gave up". `Verdict::from(result)` sorts a result into
three:

- `Ok(_)`: an execution of the model produces the trace (with certificates:
  one is in hand, and `certify` replays it).
- `Ko(v)`: no execution does. Every search was exhaustive.
- `Unknown(v)`: the checker gave up; `v.reason` says why.

`tests/verdict.rs` shows all three on one model.

## Testing with the model: driving it, and coverage

The model that checks a trace can also produce one.

- **`drive(model, init, &Drive, choices)`** (`src/drive.rs`) runs the model as a
  server (`Sim`) and records what happens. Each step it either sends a request
  or lets the system move (a call takes effect with one of its outcomes, work
  runs, a response or dispatch is delivered); at the end it sends the model's
  closing requests. It returns a `Run`: the trace, and the choices that made it.
  Every move goes through the replay behind `certify`, so a driven trace is
  valid by construction. Nothing in it knows about a particular model.
- **`Choices`**: every decision of a run is a choice among `n` alternatives, and
  every choice is recorded (`Choice { n, k }`). `Choices::random(seed)` draws
  them; `Choices::replay(&recorded)` serves recorded ones back, so a run is
  reproduced from its choices alone (an edited recording still drives a valid
  run: a choice that no longer fits, and every choice past the end, becomes the
  first alternative). This is what a shrinker would edit.
- **`Explore`** (on the model): which requests to send. `suggest(state)`:
  requests that reach the edges of what the state allows, each with why;
  `arbitrary(state, pick)`: any request; `finish(state)`: requests for the end
  of a run. The driver knows the model's exact state, so it asks directly.
- **Guidance**: with `Drive { guided: true }`, three in four requests are
  suggestions. With `Choices::random(seed).learning(&tried)`, a suggestion is
  picked among the reasons taken least so far, across the runs that share
  `tried`. Only the index picked is recorded, so a replay needs no memory.
- **Marks**: names for what an outcome does, set by the model where it decides
  it (`.mark("lease expired")`; `marks` is a field of both outcome types, empty
  by default). They change nothing. `accordant::marks(m, init, &trace, &cert)`
  collects the marks on the outcomes a certificate takes: coverage of the spec,
  which behaviors a trace is explained by. The Resonate spec marks every branch
  (`mk("...")`, 65 in all); `resonate::MARKS` lists them so a report can show
  the ones nothing reached, and a test keeps the list in step with the spec.

`examples/resonate/examples/fuzz/` uses it: drive a server (the spec, or the
spec with a bug planted), check each recorded trace against the spec, and
collect marks from accepted ones. Resonate's `finish` reads every object, moves
the clock past every deadline, and reads everything again, so every timer must
have fired.

```text
cargo run --release -p resonate --example fuzz -- 300 [--requests 30] [--bug stale-fence|lease-forever]
```

300 runs of 30 requests:

| server | mode | runs KO | marks reached |
|---|---|---|---|
| spec | random | 0 | 45/65 |
| spec | guided | 0 | 53/65 |
| fence ignores the version | random | 43 | |
| fence ignores the version | guided | 91 | |
| a lease never expires | random | 0 | |
| a lease never expires | guided | 29 | |

"Lease expired" is reached in no random run and 44 guided ones. It takes a
chain (a task released, re-acquired with a short lease, the clock past its end
before the promise's deadline) that random requests rarely assemble. Without
the memory across runs, guided runs reach it once in 300.

Not done yet: shrinking. A KO trace is reported as found (30–60 events); a
shrinker would edit a failing run's recorded choices (delete, lower) and drive
again, keeping any change the checker still rejects. (We tried Hegel,
Antithesis's Rust port of Hypothesis, for this: it shrank the stale fence to
the minimal 4 events, but its replay rules rule out memory across runs.)

**The fuzzer tests the checker too.** With no bug, every trace is valid, so a KO
is a checker bug. `CROSS=1` also checks every trace with the partitioned and depth-first
checkers. The first runs found three false KOs, all fixed and
covered by `examples/resonate/tests/sim.rs`:

1. A call in flight reads the clock (`created_at`), so it doesn't commute with a
   clock move. The clock's footprint was only the work falling due. Now it also
   includes every call in flight and runnable step that comes out differently
   when the clock moves first (checked directly: fire then tick versus tick
   then fire).
2. Settling a promise starts the resume of the task that awaits it, and the
   resume sends the dispatch observed. A static footprint (`{promise}`) can't
   name the awaiter, which is in the state. Footprints now include the keys of
   the work an item's outcomes start, followed transitively, and of the
   dispatches they send.
3. A clock move is broadcast to every factor, but partitions no factor held yet
   never saw its invoke. It is now held until the next event. If that event is
   its return, it is explained per partition; otherwise, in one factor, with the
   invoke replayed first.

The price of the first two: a footprint now runs the model. On
`resonate_bench length 400`, where about 400 stale lease checks stay pending,
the check takes 3.1 s instead of 1.1 s. The Porcupine benchmarks are unchanged.

## Soundness and certificates

What the checker promises, in one sentence: if it accepts a trace, then some
execution of the system, projected onto what clients observe, is exactly that
trace. `src/semantics.rs` says this formally, in Verus (`valid` is "some legal
execution projects to the trace"), and `src/certificate.rs` proves it about
the code that runs.

The search is not what is proved. It is large and clever (lazy firing,
footprints, early answers, subsumption, partitions), and it had a real bug: work
spawned while the clock moved could run after its deadline. Instead, the checker
shows its work:

```rust
let mut c = Checker::new(model, init, Config::default());
let cert = c.check_certified(trace)?;   // or Config { certify: true, .. } and c.certified()
```

A certificate is the execution the search found, minus what the trace already
says. The trace has the observed steps; the certificate has the silent ones,
for each event the steps just before it:

```rust
pub enum Silent {
    Effect { call: CallId, j: usize },   // the call took effect with its outcome j
    Run { i: usize, j: usize },          // pending work i ran with its outcome j
}
pub type Certificate = Vec<Vec<Silent>>; // cert[k]: the silent steps just before trace[k]
```

`certify(model, init, &trace, &cert)` (`src/certificate.rs`) walks the trace:
for each event it takes the silent steps, then the event, and refuses the first
step the system can't make. So the guarantee rests on those 150 lines, not on
the search, and they are verified.

### What is proved, where, and what is trusted

The statement, in `src/semantics.rs` (specification only; nothing in it runs):

- `Config`: the system at one point, seen or not: the model's state, and what
  the model doesn't know about: `externals`, the external ops outstanding
  (`{req, res}` by call id, `res` set once settled); `internals`, the internal
  ops scheduled, each a `Sched` (`Later`, or `Timer` at a time) stamped on the
  clock it started on; `sent`, the dispatches not yet received; `now`, the
  clock.
- `step(m, c, label, d)`: the transition relation. Observed: `invoke`, `ret`,
  `receive`, `tick`, each labeled with its event and allowed only when no
  timer is overdue. Silent: `effect` (a pending external op settles with one
  of `m.spec_external`'s outcomes) and `run` (an internal op whose time has
  come runs with one of `m.spec_internal`'s outcomes; while some timer is
  overdue, only an overdue one with the earliest time).
- `legal(m, first, steps)`: every step follows from the configuration before it.
  `project(steps)`: the observed events, in order.
- `valid(m, init, trace) := exists steps. legal(m, initial(init), steps) &&
  project(steps) == trace`.
- `check`: the checker's contract, `Ok ==> valid` and `Ko ==> !valid`, taken
  on trust (`external_body`) around `Checker::check_certified`.

The theorem, as the contract of the function that runs (`src/certificate.rs`):

```text
fn certify(m, init, trace, cert) -> (r: Result<(), usize>)
    ensures r is Ok ==> valid(m, init, trace@)
```

`certify` keeps a ghost execution and extends it at each step; each exec step
of the replay (`Config::silent`, `Config::observe`) ensures it is a `step` from
the view of the configuration before to the view after. The lemmas
(`src/certificate/proof.rs`): the computed silent steps are `effect` and `run`
steps; a legal execution extended by a step stays legal; a silent step shows
nothing and an observed step shows its event; a legal execution that shows the
trace is the witness `valid` asks for. `cargo verus verify -p accordant`
checks all of it: 30 verified, 0 errors, no `assume` or `admit`.

The `Model` trait (`src/lib.rs`, in `verus!`) gives each method a `spec` twin
(`spec_external`, `spec_internal`) and the method's `ensures` ties
the two: `external` returns the vector whose sequence `spec_external` says. The
semantics are stated over the twins.

Trusted, besides Verus and vstd (the specifications of `HashMap` and `Vec`):

- `src/certificate/trusted.rs`: `copy<T: Clone>(t) ensures r == *t` and
  `same<T: PartialEq>(a, b) ensures r == (*a == *b)`, for a model's own types.
  Both `external_body`.
- A model written outside `verus!` (every model so far, Resonate's glue
  included) keeps the default twins, which stand for whatever its methods
  compute. The theorem then says: `certify` accepts only traces valid for the
  functions the model's methods compute, provided they are pure. Nothing
  checks the purity. A model written in Verus overrides the twins and has its
  methods verified against them.
- `check`'s KO line: not proved anywhere; it rests on the search being
  exhaustive.

With the deadline bug put back, `check` accepted a trace in which the work ran
late. `check_certified` refused it, because time can't skip a deadline whose
work could run.

Limits:

- **One factor.** Certificates need `Checker::new` or `Checker::with_footprints`.
  With partitions, candidates in different factors would have to be merged into
  one execution, and that isn't built yet. The Resonate tests check every trace a
  second time in one factor, with certificates.
- **Soundness only, in Rust.** A certificate shows an accepted trace is valid.
  Nothing in Rust shows that a rejected trace is invalid. For example, the
  checker only stops the clock where something is due or observed, so it never
  tries work at the moments in between. A model whose outcome depends on the
  exact `now` between stops can see valid traces rejected (`tests/time.rs`).
  Lean has the other direction, for the plain search: `lean/Search.lean`
  defines `search m init k trace`, one frontier, every interleaving of at most
  `k` silent steps between events, and proves `search_sound` (what it returns
  replays to the trace, so is valid), `search_complete` (every execution within
  the bound is found) and `search_iff` (`Valid ↔ ∃ k, search finds it`). It
  runs (`#guard` lines at the bottom) and is the reference the Rust engines
  refine: footprints and partitions prune its frontier, and proving them is
  proving the pruned frontier represents the full one. The first half of that
  is done: `lean/Footprint.lean` says what a footprint claims (a read set and
  a write set per op; `complete`: the keys cover the state; `r_only`: an op
  reads only its read set; `w_only`: it writes only its write set) and proves
  that independent ops, neither writing what the other reads or writes,
  commute. The reduced search and its completeness are not written yet.
- **Cost.** About 5% time and twice the memory on the Resonate workload:
  every candidate keeps its history, shared with its parent's.

## Separating request from response

The history is a sequence of events, in the order one observer saw them:

```rust
enum Event<X, R, D> {
    Invoke { call: CallId, req: X },   // a client sent a request
    Return { call: CallId, res: R },   // the client got the response to that call
    Receive { msg: D },                // a client got a dispatch the server sent on its own
}
```

- `Invoke` adds a pending `External`. It changes no state and observes nothing,
  so it never triggers exploration.
- The checker places each call's linearization point: settling an `External`
  runs `external` and leaves `Settled { resp }`.
- `Return` must equal a `Settled`.
- **A call that never returns is not an event.** The client can't distinguish a
  lost request from a lost reply from a slow server, so the model doesn't either.
  The call stays pending: it may settle at any later point, including
  after reads that missed it, or never. Accordant's `OneOf(no effect, effect)` at
  the moment of the timeout is a special case that is too strict, because it
  forbids the late effect.
- Nothing bounds that uncertainty but later observations: a read that saw the
  effect, or one that missed it. (An earlier version had a request lifetime on
  the checker's clock; it went with the checker's clock.)
- `call(id, op, resp)` is `Invoke` + `Return`, so Accordant-style coupled checking
  is the special case.

This is linearizability checking in the style of Wing & Gong / Lowe's
just-in-time linearization, with background steps, deadlines on the system's
clock, and server-sent messages added.

## Time

Observations carry no timestamps. A trace is a sequence of `Invoke`, `Return`,
`Receive` and `Clock`, and its order is the real-time order, as one observer
saw it. A client's clock says nothing about the server's, so it isn't part of
the input.

Time is the system's clock, and the trace says when it moved: `Event::Clock {
at }`. The checker keeps it in the configuration, the same for every candidate,
since only an observation moves it. The model reads it, as the `now` argument
of `external` and `internal`, and never moves it: a model is a state machine,
and managing a clock is not part of modeling a system. (An earlier version kept
the clock in the model's state, moved by a request like Resonate's
`AdvanceClock`; every model with timers then had to model a clock, and the
checker had to treat that request specially.) Deadlines are on this clock, and
the checker enforces them.

- **When internal work runs is part of starting it**, not part of the work:

  ```rust
  pub enum Sched<T> {
      Later(T),         // from now on, when an observation needs it, or never
      Timer(Time, T),   // at the given time
  }
  ```

  "Now" is the clock as it reads when the starting step is taken. Each has a builder
  of the same name on both outcomes (`.later(..)`, `.timer(..)`). Work that must
  run by a deadline but may run earlier is both: `.later(w).timer(deadline, w)`,
  with `w` doing nothing once it has run. (There used to be `After`, `Within`
  and `Maybe` as well; they are gone for now.)
- **Overdue work goes first.** Work whose deadline has come on the clock,
  and that can run, runs before anything else: no call takes effect and nothing
  is observed until it has. Work that can't run owes nothing until it can.
- **Time moves in jumps.** When a clock move passes several deadlines, their
  work runs right after it, earliest deadline first, all reading the new time.
  The clock never reads the times in between, so a timer due at 5 that fires
  after a jump from 0 to 10 sees 10. Use the deadline itself (`timeout_at`) for
  anything that should record when it was due.
- **A clock move does nothing else.** Requests that also carry the time
  (Resonate's `resonate:debug_time` header) are recorded as a clock move
  followed by the request. Moving the clock and acting in one step would let
  the action run before the timers due at the new time.
- **Deadlines are inclusive.** At clock `t`, work due by `t` has run. This
  matches servers that test `now >= deadline`, like Resonate.
- **Requests in flight** may take effect before or after a clock move, like
  any other concurrent call. That's how a read that spans a timeout may still
  see the promise pending. A clock move is the one observation that doesn't
  commute with pending work: work that runs before it is timed differently,
  and the move makes timers overdue, so the checker explores the work the move
  changes before consuming it (`clock_seed`).
- **Only safety.** The checker asks whether some execution explains what was
  observed. `Later` work happens when an observation needs it, or never; there
  is no "the system is idle now" assertion. Work that must happen by some time
  gets a timer, and the tester moves the clock past it.
- **Partitions and the clock.** A clock step touches every partition. A request
  that `Partitioned::broadcast` marks (it acts on every partition alike, starts
  nothing, sends nothing) is explained in each partition on its own when it is
  answered before anything else is observed, which is how a driver moves the
  clock. Otherwise the partitions merge for it and split again afterwards.

## Non-determinism

The checker is angelic: a history conforms if *some* resolution of every choice
explains it. There are five sources of choice.

| Source | How it's written | Who resolves it |
|---|---|---|
| **ExternalOutcome**: the server may answer or act in several ways | `apply` / `step` return several outcomes or successors (Accordant's `OneOf`) | the observations that follow |
| **Interleaving**: the order of concurrent calls and background work | implicit: every pending item is a possible next move | the search, pruned by footprints |
| **Timing**: when due work fires inside its window | the `Sched` each piece of work was started with | the search, bounded by deadlines |
| **Unknown fate**: whether an unanswered request took effect | implicit for every call without a `Return` | later reads |
| **Unknown values**: server-chosen ids, timestamps | not supported yet; see below | the `Return` |

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

The profile grows from work that might or might not have happened yet. Eight
mechanisms keep it small, and all eight are in the prototype.

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
3. **Deadlines.** Obligations have a `by` on the clock. When the clock
   passes it, the uncertainty is resolved once and then gone. Nothing stays pending forever unless the spec says so.
4. **Subsumption (antichains).** Optional work (a call the history says never
   returns) can always be skipped, so a node simulates any node with the same
   state and owed work but a subset of its optional work. Likewise for early answers (next item). The weaker node is discarded.
5. **Reads don't branch.** Linearizing a call whose outcomes leave the state
   unchanged only decides its answer. So instead of splitting the profile into
   "answered early" and "not yet", the call keeps the set of answers it could
   already have gotten, and `Return` accepts any of them or a later
   linearization. Without this, the profile is the *product* of independent
   per-key choices: footprints keep each search small, but 50 reads in flight
   across 50 promise deadlines made 2^50 candidates. With it, width stays 1
   (`examples/resonate/tests/traces.rs`, `independent_promises_keep_the_profile_narrow`: failed
   after 47 s before, 400 nodes and 0.02 s after). Writes in flight across
   independent keys still multiply; partitions (next item) handle that.
6. **Partitioned profiles.** A spec that defines `part(key)`, `restrict` and
   `join` gets its profile stored as independent *factors*, one per group of
   partitions. The full profile is their product, but it is never built. An
   event goes to the factor owning its footprint. A request spanning factors
   merges them (their product, built then), and `Keys::All` merges everything.
   After each event a merged factor splits back apart if no pending work links
   its partitions and its candidates are exactly the product of their
   projections, so a merge lasts only as long as the request that caused it.
   Partitions not touched yet are pulled out of the initial state on first use.
   Spawned work must stay inside its spawner's partitions; the checker reports
   a spec error if it doesn't. Resonate partitions by origin. Measured
   (`partitions_keep_independent_origins_apart`): 20 origins, each with an
   unanswered settle across its promise's deadline, means 2^20 candidates. As
   factors that is 20 factors of 2, built in 0.8 ms from 160 nodes. Unpartitioned,
   the same history is still exploring after 246 s.
   `partitioning_never_changes_a_verdict` runs 40 random histories over three
   origins through both modes and asserts identical verdicts.
7. **Structural step identity.** Steps are values, so identical work spawned on
   different branches converges to the same node. Accordant's GUIDs prevent this.
   Pending work is still a multiset: identical work started twice is one item
   with a count of 2, and runs twice (`tests/work.rs`). An earlier version kept a
   set, which merged two identical lease timers into one; the fuzzer caught it
   as certificates that did not replay.
8. **Hard limits.** `max_width` and `max_explore` turn a blowup into an error that
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
  unbounded `Later` obligations that a cycle can postpone forever.

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

`examples/bank/` runs rounds of 8 concurrent deposits with footprints
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
| `ServerState { Promises, Tasks, Now }` | `Server { promises, tasks }`; the clock is the checker's, passed in as `now` |
| `AdvanceClock` request | `Event::Clock { at }` in the trace; no request |
| `Handler<CreatePromise>(PromiseCreate)` | an `Op::CreatePromise { .. }` arm in `apply` |
| internal steps | `type Internal = BTreeSet<Id>`: "process these objects". `internal` does whatever is due on them, read from the state and the clock |
| promise `TimeoutAt` + `Project(now)` | `.timer(timeout_at, on(&[id]))`; the projection becomes a real transition at the deadline |
| `ResumeTriggers` → `AsyncOperation.Create(isTerminal: !Fireable, ...)` | `.later(on(&[awaited, awaiter]))` when the awaited promise settles |
| `LeaseTriggers`, `RetryTriggers` | `.timer(expires, on(&[id]))` when the lease starts or is extended; retries not ported |
| `ServerOperation` + `IndefiniteFailures` duplicating outcomes | nothing: an unanswered call is already "maybe" |
| `PollLiveness(terminal)` | the poll that sees the terminal state is a read like any other; no idle bound |
| `debug.messages` (execute/unblock) | `execute` is a server-sent `Dispatch::Execute { id, version }`, checked with `receive`; `unblock` for listeners is not modeled yet |
| footprint | promise id plus awaiter ids for callbacks |

Origins: the only request that may cross origins is a fence that creates a
promise in another origin, which starts a detached workflow. A cross-origin
fence-settle, `register_callback` or `suspend` is 400. Those refusals are made on
the ids alone, so their footprint stays in one origin and doesn't merge
anything. The C# spec and the server allow cross-origin fence-settles. The Lean
spec refuses every cross-origin fence, the detached create included.

The port is the `resonate` crate (`examples/resonate/src/spec.rs`, written in Verus; traces in `examples/resonate/tests/traces.rs`, from
`ExampleTraces.cs` and `LeaseAndTimeoutTests.cs`). Not ported: the
`egress` capability (retry timeouts) and `debug.messages`.

## Resonate in Verus

The spec is written in Verus, so the code the checker runs is the code the
proofs are about: there is no second copy. `cargo build` compiles `verus!{}`
blocks as ordinary Rust with the proofs erased; `cargo verus verify -p resonate`
verifies them (vstd from crates.io, matching the Verus release).

Verus checks every function for panics, overflow and out-of-bounds indexing,
and checks the properties stated as `ensures`. So far: every promise
`promise_create` creates has `created_at <= settled_at <= timeout_at`, every
promise record it answers with has it, and every promise that had it keeps it.
Planting a bug (an expired promise created at `now`) fails verification.

What it trusts is in `collections.rs`: persistent maps and sets seen as Verus
maps and sets (wrappers over the checker's own `HashedMap` and a `BTreeSet`, so
the checker is as fast as before), a derived `Clone` being a copy, and three
string helpers (an id's origin, URL validation, settle-state names). The glue to
the checker (`model.rs`) is plain Rust; it converts outcomes and computes
footprints and partitions, and decides nothing about what the server does.

What writing it in Verus changed: closures and iterator chains became loops;
internal work is a `Vec` of ids inside the spec (a set at the checker); clock and
version arithmetic saturates instead of overflowing; where the old code indexed
a map it knew had the key, the new code matches and handles the impossible case.

## Porting Resonate: developer experience

Ranked by how much each one hurt.

1. **Violations are unreadable.** A rejected response prints the whole state
   of every candidate on one line. It doesn't show what the spec expected, how
   that differs from what was observed, or which rule applied. The C# spec
   labels each outcome (`"T-03: pending v0 → acquired v1"`), and Accordant
   prints that label. Needed: an outcome label (`.because("T-03 ...")`), "expected
   one of … / observed …" per candidate, and state printed only for the keys in
   the event's footprint.
2. **Clone-then-mutate on every transition.** Nearly every write is
   `let mut n = s.clone(); n.tasks.update(id, |t| …); vec![ExternalOutcome::new(resp, n)]`,
   often followed by re-reading `n.tasks[id]` to build the response. C#'s
   `.ThenState(s => …)` hides the clone. `HashedMap` has no `get_mut`, only an
   `update` closure. Needed: `ExternalOutcome::then(resp, s, |n| …)`, a one-outcome
   return that isn't `vec![…]`, and `get_mut` on `HashedMap` that rehashes on drop.
3. **Unchanged state must still be passed in.** Every error branch is
   `status(409, s)`, which clones the state only to say it didn't change, and
   the checker then hashes and compares it. An outcome that means "state
   unchanged" without a state would be shorter and cheaper.
4. **One step was written in four places**: the enum variant, its `step` arm,
   its `fairness` arm and its `step_keys` arm. *Since fixed:* timing moved into
   `Sched` at the spawn site, and Resonate's internal step is now just the set
   of ids it processes, so there is one `internal` function and no per-kind arms.
5a. **Checking enabledness is expensive.** The checker asks whether a step is
   enabled by calling `step()`, which builds full successor states only for them
   to be discarded. In a wide search that dominates the run time. A separate,
   cheap `enabled(step, state)` on the spec, defaulting to calling `step()`,
   would fix it.
5. **Footprints can be wrong silently.** They are a function of the request
   alone, which fits Resonate. A missing key doesn't fail; it hides
   interleavings. Needed: a debug mode that
   re-checks events with footprints off and reports any difference.
6. **Panics in the spec lose context.** `s.promises[id]` on a missing key panics
   with a bare index error. Accordant wraps spec exceptions with the event and
   the path that led there. The checker should catch the panic and turn it into
   a violation that names the event and candidate.
7. **String ids are noisy.** `.clone()`, `.to_string()` and `.into()` everywhere, and
   footprints need owned keys. An interned, `Copy` id type would remove most of it.
8. **Choices have to be enumerated by hand.** A request that may pick any k of
   n items needs its own subset helper. Accordant has `Choose.Each`; a small set
   of choice helpers belongs in the crate.
9. **Builder chaining in loops.** `ExternalOutcome::spawn`/`timer` take `self`, so a loop
   needs `o = o.timer(…)`. `spawn_all` and `timers` that take iterators fix it.

What got better:

- **Timers removed the read-time projection.** C# calls `Project(now)` wherever
  a promise is read, because a timed-out promise stays stored as pending. Here
  the deadline is a timer that settles it, so "pending" means pending.
- **Indefinite failures cost nothing.** `ServerOperation` duplicated every
  outcome; here an unanswered call is already "maybe".
- **Responses are values.** No mock generators, and `allowed(op)` lists what the
  spec permits, which is how the traces state their expectations without a server.
- **Exhaustive matching.** Adding an op or step without handling it doesn't compile.
- **Smaller.** 711 lines including docs, against 1,062 for `Spec/*.cs`.

Porting also found three checker bugs, all fixed:
- **Exclusive deadlines:** a read at the exact deadline could miss the timer.
- **Reads spanning a tick:** an in-flight read couldn't have linearized before
  a timeout the tick passed. (Now the clock step is a call, and a read in flight
  takes effect before or after it like any concurrent call.)
- **Product blowup:** independent reads multiplied the profile (pruning item 5).

## Files

- `src/lib.rs`: the `Model`, `Footprint` and `Partitioned` traits, `Event`, `ExternalOutcome`, `InternalOutcome`, `Sched`, `Touches`, `Time`. `Model` and the types the proofs mention are inside `verus!`.
- `src/checker.rs`: profile, events, clock, deadlines, footprint-pruned search, subsumption, `allowed`, recording certificates.
- `src/certificate.rs`: `certify`, the replay that backs every certified verdict, verified: `Ok(()) ==> valid`. Below it, outside Verus: legal-move enumeration and `marks`. `src/certificate/proof.rs`: the lemmas; `src/certificate/trusted.rs`: `copy` and `same`, trusted.
- `src/semantics.rs`: what the checker promises (`valid`), as Verus specifications: configurations, the step relation, executions and their projection, and the checker's contract `check`.
- `src/sim.rs`: `Sim`, the model run as a server, on the same replay.
- `src/drive.rs`: `drive`, `Choices` (recorded, replayable decisions), `Drive`, `Tried`.
- `verus/README.md`: where the Verus statement and proof live, and how to run them.
- `lean/Accordant.lean`: the semantics in Lean (`Model`, `Step`, `Valid`), the certificate replay and its soundness proof. `lean/Search.lean`: the plain search, proved sound and complete. `lean/Footprint.lean`: what a footprint means (a view per key; a read set and a write set per op; an op reads only its read set and writes only its write set) and the theorem that independent ops then commute, with the bank as an instance. `cd lean && lake build` checks all of it and the TigerBeetle model.
- `src/hashed_map.rs`: persistent map with an incrementally maintained hash.
- `src/intern.rs`: hash-consing of states.
- `examples/bank/`: the large-bank benchmark (`cargo run --release --example bank -- [accounts] [rounds] [concurrency]`).
- `tests/bank.rs`: overlapping calls, double-spend, real-time order, unanswered requests, pruning measurement.
- `tests/jobs.rs`: background completion, run deadlines, timeout timers, deferred independent jobs.
- `examples/resonate/`: the Resonate spec as its own crate, written in Verus. `src/spec.rs` is the server (verified: no panics or overflow anywhere, and safety properties as `ensures`; so far `created_at <= settled_at <= timeout_at` for `promise_create`), `src/collections.rs` what it trusts, `src/model.rs` the glue to the checker, `src/explore.rs` its marks and suggestions. `cargo build` compiles it as ordinary Rust; `cargo verus verify -p resonate` verifies it. Its traces are in its `tests/`, its benchmark and fuzz driver in its `examples/`.
- `examples/tigerbeetle/`: TigerBeetle's state machine. `lean/` has it as a Lean `Model`, with a proof that debits never exceed credits (built by `lean/lakefile.toml`); `src/` has its data model in Rust, not yet a `Model`.
- `examples/porcupine/`: Porcupine's etcd and key-value histories, checked against its Go checker's verdicts (`cargo run --release --example porcupine -- all [--dfs] [--certify]`; `fetch.sh` gets the histories).
- `tests/certificate.rs`, `tests/time.rs`: `certify` on its own; deadlines on the clock, never early, in deadline order after a jump.
