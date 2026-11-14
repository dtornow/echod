# echod + Rover consolidation handoff

The consolidation this note describes has landed. The tree is the layout in
[README.md](README.md). What follows is the brief that produced it.

## Mission

The echod and Rover repositories will be placed together before any
restructure. Explore the resulting checkout first, establish green baselines,
and then consolidate the generic Rover framework, the independent abstract
Resonate model, the concrete specification of the real process, and their
refinement proof into echod.

Do not begin moving directories merely because this document names a target
layout.

## Operating rules

1. Do not restructure until discovery and baseline verification are complete.
2. Preserve both repositories' Git history. Inspect branches, remotes, and
   working-tree state before editing.
3. Read every applicable `AGENTS.md`, `README`, Cargo workspace manifest, Lean
   lakefile, toolchain pin, and verification script.
4. Treat existing architectural and proof claims as hypotheses. Verify them
   against the checkout.
5. Do not introduce `assume`, `admit`, `sorry`, or a new `external_body` to
   make a proof pass.
6. Do not make the abstract model import implementation logic. It must remain
   independently executable for trace checking.
7. Commit the migration in reviewable stages. Delete old copies only after
   behavior, test, and proof parity are established.

## Phase 1: discovery

Locate the two original repository roots rather than assuming their names.
Produce an inventory containing exact paths for the following.

### Rover

- Rust `RoverSpec::{Spec, Proc, State}` and `RoverExec::{Spec, Proc}`,
  world semantics, checker, certificate replay, and generic refinement theorem.
- Standalone Resonate protocol, abstract model, property catalogue, tests,
  benchmark, and fuzz driver.
- Lean `Rover.World`, Resonate abstract/concrete models, trace checker, and
  refinement proofs.
- Current unproved property obligations.
- Every trusted helper and axiom.

### echod

- The actual pure `State::on_event` implementation and Event/Effect
  vocabulary.
- The current kernel/domain helpers and which ones execute in production.
- The production effect interpreter for S3, HTTP, clocks, Tokio, replies, and
  crashes.
- The deterministic simulator and differential runner.
- The property catalogue and existing Verus proofs.

### Required discovery output

Before editing, return:

- A table of crates and Lean projects with purposes, dependencies, toolchains,
  and verification commands.
- A dependency DAG including proof-only dependencies.
- A duplicate/source-of-truth map.
- An exact old-path to target-path migration proposal.
- A blocker list: toolchain conflicts, dependency cycles, private APIs, stale
  branches, and incomplete proofs.
- A green baseline transcript for Rust tests, Verus verification, and Lean
  builds where available.

## Target repository structure

```text
echod/
├── impl/
│   ├── process/          # actual pure State::on_event(Event) -> Effects
│   ├── runtime/          # production S3/HTTP/clock/Tokio effect interpreter
│   └── cli/              # binary, configuration, startup
│
├── spec/
│   ├── rover/
│   │   ├── spec/         # generic Rover world and refinement
│   │   └── exec/         # checker and certificates
│   └── echod/
│       ├── abstract/
│       │   ├── spec/     # independent Resonate model and properties
│       │   └── exec/     # executable realization and coverage instrumentation
│       ├── concrete/
│       │   └── spec/     # mathematical concrete state and transitions
│       └── refinement/   # interpretation, relation, simulation proof
│
├── test/
│   ├── runtime/          # synchronous deterministic Effect interpreter
│   ├── sim/              # seeded simulation and trace capture
│   ├── diff/             # differential validation
│   ├── integration/      # real S3/HTTP tests
│   └── fixtures/
│
├── Cargo.toml
├── README.md
└── scripts/
```

Filesystem directories may be named `abstract` and `concrete`. Rust packages
should avoid the reserved keyword:

```text
echod-abstract-spec  -> echod_abstract_spec
echod-abstract-exec  -> echod_abstract_exec
echod-concrete-spec  -> echod_concrete_spec
echod-refinement     -> echod_refinement
```

## Layer responsibilities

### `impl/process`

The real pure implementation. It owns:

- `State`
- `Event`
- `Effect`
- executable `State::on_event(Event) -> Vec<Effect>`

The former kernel belongs here as internal promise, task, schedule,
membership, cache, and timer modules. It is not a separate conceptual
implementation.

The process contains no I/O, sleeping, locks, spawned tasks, or network
clients.

### `impl/runtime`

The production interpreter for Effects:

```text
Store Effect -> real S3 operation -> Completed Event
Send Effect  -> real HTTP operation
Wake Effect  -> Tokio timer -> Tick Event
Reply Effect -> complete client response
```

It contains no protocol decisions.

### `spec/rover/spec`

Domain-independent formal machinery:

- append-only network world
- ordered pid/process entries over a stateful `RoverSpec::Proc`
- generic process selection, message/timeout delivery, and routing
- clean boundary observation
- generic forward-simulation-to-trace-refinement theorem

### `spec/rover/exec`

The executable realization of Rover specifications:

- deterministic single-path execution with a strategy-selected action
- bounded trace and history search
- certificates and verified replay
- coverage labels from selected executable outcomes

### `spec/echod/abstract/spec`

The independent mathematical Resonate model. It owns the protocol transition
functions, mathematical state, and conformance properties meaningful under
Rover semantics. It contains no executable store, handlers, or Rover process.
`property_claim.rs` keeps every named protocol property and the aggregate
preservation claim; `property_proof.rs` contains the machine-checked proof.

It must not import `impl/process`, `spec/echod/concrete/spec`, or `impl/runtime`.

### `spec/echod/abstract/exec`

The executable realization of the abstract model: persistent store types,
verified handler bodies, the executable Echod abstract process, and coverage
marks. Client history translation and model-driven workloads live in
`test/model`.

### `spec/echod/concrete/spec`

The specification the kernel is proved against, not another implementation
and not a dependent of the process:

- the document catalogue and the `spec_*` handler functions
- the one step, `on_event`, which cites those functions
- the Echod concrete model in `model.rs`: one `Proc` process enum (`Node` or `Store`),
  nodes and one store in `spec_world`, and `RoverSpec::Proc::on_event` dispatching
  each enum variant to its local step
- the Rover adapter over those concrete semantics
- `property_claim.rs` for concrete integrity and `property_proof.rs` for its proof

The dependency on `echod-abstract-spec` is semantic rather than a refinement
proof dependency: concrete network messages use the shared
`Call`/`Output`/`Dispatch` boundary types, and schedule transitions use the
trusted cron and occurrence-expansion functions.

Executable `Doc`/`Obj`/store types, handlers, their `View` bridges, and
exec-to-spec proofs live under `impl/process/src/concrete`; production code
imports those local executable definitions.

### `spec/echod/refinement`

The model-specific proof boundary. It interprets concrete documents as the
abstract store, proves request and internal-work agreement, defines the
simulation relation, and exports `concrete_refines_abstract` and `refinement_proof`.
The claim is the crate root; all proof machinery is consolidated privately in
`refinement_proof.rs`. It depends only on Rover,
the two specification crates, protocol types, and Verus.

### `test/runtime`

A synchronous deterministic interpreter for the same Effects:

```text
Store Effect -> simulated object store
Send Effect  -> deterministic network queue
Wake Effect  -> fake-clock scheduler
Reply Effect -> recorded boundary trace
faults       -> crash, loss, delay, reordering, failed acknowledgement
```

The production and test runtimes must drive the exact same
`impl/process::State::on_event`.

`test/runtime/src/rover_sim.rs` is an isolated experiment: generic
`RoverExec::exec` drives production-backed concrete processes, projects their
boundary trace, and asks `echod_abstract_exec::Spec` to certify it. The existing DST
remains the primary simulator.

## Dependency direction

```text
spec/rover/spec ---> spec/echod/abstract/spec ---> spec/echod/concrete/spec ---> impl/process ---> impl/runtime ---> impl/cli
      |               |                              |
      v               v                              v
spec/rover/exec --> spec/echod/abstract/exec     spec/echod/refinement
                       |                              ^
                       +------------------------------+

impl + spec -----------------> test/*
```

Concrete depends on the Rover world and the abstract model's shared semantic
boundary. Refinement depends on both models. The process depends on concrete,
because a handler's `ensures` names `spec_promise_create`. Concrete and
refinement depend on neither the process nor the runtime. Production code must
never depend on test code. The ghost half of the concrete crate erases
under `cargo build`.

## Semantic decisions already made

### Process transition has no PID parameter

The pure transition is:

```text
on_event(state, event)
```

PID belongs only to Rover routing, network envelopes, world labels, and
certificates. A process's identity belongs in its state or configuration.

### Boundary hides all internal topology

Every `RoverSpec::Spec` owns:

```rust
type Boundary;
spec fn observe(label) -> Seq<Self::Boundary>;
```

Only traffic crossing `outside` (conceptually PID 0) is observable. Concrete
and abstract refinement shares only `Boundary`; internal PIDs and message
types may differ.

### Server receipt time is the transition clock

The `now` passed to process `on_event` is the server-observed request arrival
time. Do not carry a caller-supplied `requested_at` field in the request.

### Timers are runtime behavior, not timer processes

The process emits:

```text
Effect::Wake { after_ms }
```

The runtime later supplies:

```text
Event::Tick { clock }
```

No `Pid::Timer` or `TimerState` is required.

### Search and proof are separate

Bounded abstract search may return "not found" because its bounds are
insufficient. Acceptance is sound only after verified certificate replay.

## Proof chain

```text
impl/process::State::on_event
    implements
spec/echod/concrete/spec::spec_logic_on_event
    which is the node step of
Rover instantiated with the concrete model
    is proved by spec/echod/refinement to refine
Rover instantiated with the abstract model
```

The statement is `rover_spec::rover::refinement::refines` of
`echod_concrete_spec::Spec` against
`echod_abstract_spec::Spec`, exported as
`echod_refinement::concrete_refines_abstract` and proved by
`echod_refinement::refinement_proof`: every
boundary trace of the concrete world is a boundary trace of the abstract
world. `concrete_refines_abstract` proves it from a relation on the two
initial worlds and a forward simulation, at one boundary,
`resonate::BoundaryEvent`. The relation and the simulation are the open
proof.

The actual process contract should look like:

```rust
fn State::on_event(
    &mut self,
    event: Event,
) -> (effects: Vec<Effect>)
    ensures
        final(self)@
            == concrete_model.spec_on_event(old(self)@, event@).state,
        effects@.map_values(|effect: Effect| effect@)
            == concrete_model.spec_on_event(old(self)@, event@).effects;
```

The final public theorem should mention only clean boundary traces:

```rust
proof fn echod_refines_resonate()
    ensures
        forall|trace: Seq<Boundary>|
            valid_boundary_trace(concrete_model, trace)
            ==> valid_boundary_trace(abstract_model, trace);
```

The model-specific proof must establish:

1. Initial concrete and abstract worlds are related.
2. Every concrete step is matched by zero or more abstract steps.
3. Matched steps emit exactly the same clean boundary events.
4. Resulting worlds remain related.

The generic Rover theorem performs the induction over arbitrary finite
executions once.

## Dynamic validation path

```text
deterministic test runtime
    drives real process::on_event
    records clean Boundary events
              |
              v
Echod abstract checker
    searches for an abstract execution
              |
              v
verified certificate replay
    proves accepted trace is abstract-valid
```

This complements, but does not replace, the static process-to-concrete and
concrete-to-abstract proofs.

## Property catalogue migration

Start from the upstream named catalogue and preserve exact names for
cross-language diagnostics.

Classify every property as:

- state
- transition
- event/provenance
- response
- liveness
- algebraic

Do not force all categories into state-pair predicates.

Translate model differences explicitly:

- Map-backed uniqueness is structural.
- New-message consistency inspects emitted effects/messages.
- Outbox persistence becomes Rover's append-only-network theorem.
- True liveness requires infinite execution and fairness semantics.
- Algebraic claims are equations between `spec_on_event` compositions.

Do not count a predicate definition as a proof. Track initialization, every
request family, every internal step, and the final reachable-state theorem
separately.

## Migration sequence

1. **Baseline:** run and record all existing Rust, Verus, and Lean checks.
2. **Create target shells:** add directories and manifests without deleting
   source.
3. **Move generic Rover:** move Rust and Lean framework code together; preserve
   tests and proof counts.
4. **Move abstract:** move the independent model and property catalogue;
   verify trace-checker parity.
5. **Consolidate process:** move current pure logic and former kernel/domain
   helpers into `impl/process` without changing behavior.
6. **Align concrete:** add `View` implementations and concrete spec twins to
   the real process. Verify helpers before top-level `on_event`.
7. **Prove simulation:** define the relation, stutters/linearization points,
   per-step matching, and final theorem.
8. **Unify runtimes:** production and deterministic runtimes consume the same
   Effects and emit the same Events.
9. **Delete duplicates last:** remove old roots/manifests only after import,
   behavior, test, and proof parity.

## Acceptance criteria

- No production behavior depends on formal or test runtime code.
- `impl/process` is pure.
- Actual `on_event` is verified against concrete `spec_on_event`.
- Concrete and abstract models share only `Boundary` at the public refinement
  interface.
- Generic refinement remains model-independent and verified.
- Deterministic simulation records Boundary traces accepted by verified
  abstract certificate replay.
- Rust tests, Verus verification, and Lean builds pass from documented
  commands.
- No stale compatibility crate, duplicate model, or old path remains.
- Final documentation accurately states dependencies and trust boundaries.

## Initial prompt for the new agent

> Explore the merged checkout before editing. Identify both original
> repository roots, read all governing instructions and manifests, inspect Git
> status/branches/remotes, and map every Rust crate and Lean project. Locate
> the generic Rover world/checker/refinement code, standalone abstract
> Resonate model and properties, echod's actual `State::on_event` process,
> production runtime, simulator, property catalogue, and current proofs. Run
> the existing baseline checks without restructuring. Return an
> evidence-backed inventory, dependency DAG, duplicate/source-of-truth map,
> exact old-to-target path migration, toolchain conflicts, and phased migration
> plan using the target `impl/spec/test` structure in this handoff. Do not move
> files or introduce adapters until the inventory and baselines are complete.

