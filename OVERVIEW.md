# echod

A Resonate server whose only durable state is objects in an S3 bucket, with
Verus specifications and proof code for its document and process transitions.
The inherited trust limitations below prevent a formal correctness claim.

The server speaks the Resonate protocol, one `POST /` and one envelope. Every
origin is one document in the bucket, committed with a conditional write;
deadlines are keys; nodes find each other in the bucket. What the server does
to a document is `echod_logic::concrete`'s document machine, specified by
`echod_concrete_spec`; `echod_refinement` contains the concrete-to-abstract
refinement proof code. The process contract relates `State::on_event` to
`spec_on_event`, including membership, cache, deadline keys, and store-call
ordering. These checks depend on trusted assumptions, including declarations
in `rust/impl/process/src/verified/mod.rs` and the limitations below.
The deterministic simulator supplies runtime evidence under crashes, outages,
and lost acknowledgements.

## Layout

```text
rust/impl/process     the pure State::on_event around the concrete document machine, proved to compute spec_on_event
rust/impl/runtime     the production effect interpreter: store, clock, HTTP
rust/impl/cli         the echod binary
rust/spec/rover/spec  Rover mathematical state, steps, and refinement
rust/spec/rover/exec  Rover deterministic execution, bounded search, and verified replay
rust/spec/echod/abstract/spec  the mathematical Resonate protocol model
rust/spec/echod/abstract/exec  its executable store, handlers, and Echod abstract realization
rust/spec/echod/concrete/spec  mathematical Echod concrete model
rust/spec/echod/refinement  verified concrete-to-abstract refinement
rust/test/model       trace and workload support for abstract-model tests
rust/test/runtime     the synchronous deterministic effect interpreter
rust/test/cli         the simulator, the differential, the model driver, the store tests
lean/src/Rover        the Rover world, for experiment
lean/src/abstract     the Resonate model, for experiment
lean/src/concrete     nodes and one store, for experiment
examples/ts           the TypeScript SDK against the node
scripts               the store and end-to-end tests against a real S3 API
jeps                  Jepsen, from outside the process: a pass means the pipeline a client can see produced a correct result
```

The process's document steps live under `rust/impl/process/src/concrete`,
each proved equal to `rust/spec/echod/concrete/spec`'s specification; the process itself is proved to compute `spec_on_event`,
its bookkeeping and the sequence of store calls around each step included.
Shared boundary payloads live in `echod-types`; both models specialize Rover's
boundary events with unit routing identity. Their observations exclude clocks
and internal traffic. Concrete still depends on the abstract model for trusted
cron/occurrence algebra; it does not depend on the process.
What the process assumes — the text of keys, the bytes of documents — is
stated as specifications and listed in `src/verified/mod.rs`; its tests feed
it events by hand. The runtime performs what it asks. The simulator is the
evidence. [DESIGN.md](DESIGN.md) is the design; [BACKLOG.md](BACKLOG.md) is
what is next. Each crate root opens with a map of its files.

Both mathematical specification crates use `state.rs` for state and transition
definitions and `rover.rs` for process orchestration and the Rover adapter.
Concrete `state.rs` separates Node and Store with section comments; abstract
`state.rs` separates state, requests, and internal work. Concrete
`Proc::on_event` still delegates to `spec_node` or `spec_store`; the abstract
process delegates to `spec_service`. Model-specific document/protocol helpers
and claim/proof files remain separate.

## Document and request boundaries

Workflow and schedule objects store versioned partials rather than bare rows.
Each partial names its document, base and resulting versions, commit time,
next wake, and ordered upsert/remove changes. The executable values and codec
live in `rust/impl/process/src/concrete/values.rs`; their mathematical algebra
lives in `rust/spec/echod/concrete/spec/src/document.rs`, with composition
proofs in `document_proof.rs`.

Production workflow requests close due work before and after the raw handler.
If either closure exhausts its bound, the request returns 503 without committing
the intermediate document or notifications. Successful requests derive their
notifications from the initial and final documents, so an offer consumed within
the request is not sent. The executable transition is `request_transition` in
the process's concrete document module; its mathematical counterpart is
`spec_request_transition`.

These local transitions do not establish global document invariants.

## Verification scope and deferred trust repair

Runtime tests and successful Verus runs are separate evidence. The inherited
`axiom_next_cron_after` in `rust/spec/echod/abstract/spec/src/axioms.rs` asserts
that a `u64` result exceeds every `u64` input, which is inconsistent at
`u64::MAX`; executable cron wrappers also promise this unconditionally.
String, byte-vector, and dispatch realization contracts assume that arbitrary
mathematical views have Rust representatives. They need representability
premises and propagation through callers; a character-count bound alone does
not establish UTF-8 byte capacity.

Repair is deferred to the retained `prove-trust-contracts` work. No partial
contract tightening is included here. Until those assumptions and their
callers are repaired, passing Verus checks must not be treated as soundness or
formal correctness validation.

The simulator's Rover certificates target the finer-grained abstract model:
raw request handlers with separate internal work steps. They do not establish
the production request's atomic pre/post-closure contract. A bounded search
that finds no certificate reports `Unknown`, not a correctness verdict.
Verified atomic-checker alignment and representation redesign remain deferred.

## Build, verify, soak

```
cargo build --workspace                 # every crate, the ghost code erased
cargo test --workspace                  # unit and end-to-end tests, in memory
scripts/chaos.sh --seed 7               # isolated three-node container fleet under faults
cargo verus verify -p rover-spec -p rover-exec
cargo verus verify -p echod-abstract-spec -p echod-abstract-exec
cargo verus verify -p echod-concrete-spec -p echod-refinement
cargo verus verify -p echod-process     # State::on_event == spec_on_event, under Verus
cargo run --release -p echod-sim -- soak --from 1 --seeds 20   # the simulator
cargo run --release -p echod            # a node on an in-memory store, :8001
cargo run --release -p echod-diff -- --resonate <path to a resonate binary> --seeds 4   # the differential
```

The differential wants the reference server built from `resonatehq/resonate`
(`impl/server/core`, `cargo build --release --bin resonate`); it starts it
and echod in debug mode and drives both over HTTP. The model driver is
`cargo run --release -p echod-model`, in this same workspace.

`cargo verus` wants a Verus release (`cargo-verus`, `verus`, z3) on the
path. `cargo build` is the other compiler for the same sources: it sees the
executable code alone.
