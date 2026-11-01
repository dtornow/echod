# echod

A Resonate server whose only durable state is objects in an S3 bucket, with
the state machine it runs verified in Verus, from one document up through
the node's decisions.

The server speaks the Resonate protocol, one `POST /` and one envelope. Every
origin is one document in the bucket, committed with a conditional write;
deadlines are keys; nodes find each other in the bucket. What the server does
to a document is the kernel, proved against the specification's catalogue of
92 properties. What a node decides about membership, its cache and its
deadline keys is the kernel too, each decision proved to compute its
specification. What the proof stops at, the shim between the verified core
and S3, a deterministic simulator holds to the Resonate model under
crashes, outages and lost acks.

## Layout

```text
rust/impl/process     the pure State::on_event, and the verified kernel inside it
rust/impl/runtime     the production effect interpreter: store, clock, HTTP
rust/impl/cli         the echod binary
rust/spec/rover       the Rover world, replay, and refinement theorem
rust/spec/abstract    the Resonate protocol as a Rover model
rust/spec/concrete    the catalogue, the specifications on_event is proved against, and the Rover model
rust/test/runtime     the deterministic effect interpreter
rust/test/cli         the simulator, the differential, the model driver, the store tests
lean/rover            the Rover world, for experiment
lean/abstract         the Resonate model, for experiment
lean/concrete         nodes and one store, for experiment
examples/ts           the TypeScript SDK against the node
scripts               the store and end-to-end tests against a real S3 API
```

`rust/impl/process/kernel` is proved equal to `rust/spec/concrete`. Concrete
depends on the abstract model; it does not depend on the process. The process
around the kernel is the shim the proof stops at: nothing in it but the order
of calls, and its tests feed it events by hand. The runtime performs what it asks. The simulator is the
evidence. [DESIGN.md](DESIGN.md) is the design; [BACKLOG.md](BACKLOG.md) is
what is next. Each crate's `lib.rs` opens with a map of its files.

## Build, verify, soak

```
cargo build --workspace                 # every crate, the ghost code erased
cargo test --workspace                  # unit and end-to-end tests, in memory
(cd rust/impl/process/kernel && ./verify.sh)   # the kernel under Verus
cargo run --release -p echod-sim -- soak --from 1 --seeds 20   # the simulator
cargo run --release -p echod            # a node on an in-memory store, :8001
cargo run --release -p echod-diff -- --resonate <path to a resonate binary> --seeds 4   # the differential
```

The differential wants the reference server built from `resonatehq/resonate`
(`impl/server/core`, `cargo build --release --bin resonate`); it starts it
and echod in debug mode and drives both over HTTP. The model driver is
`cargo run --release -p echod-model`, in this same workspace.

`verify.sh` wants a Verus source tree with a release build in `VERUS_DIR`
(default `~/verus-lang/verus/source`) and z3 beside it. `cargo build` is
the other compiler for the same sources: it sees the executable code alone.
