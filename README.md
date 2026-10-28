# echod

A Resonate server whose only durable state is objects in an S3 bucket, with
the state machine it runs verified in Verus, from one document up to the
whole system.

The server speaks the Resonate protocol, one `POST /` and one envelope. Every
origin is one document in the bucket, committed with a conditional write;
deadlines are keys; nodes find each other in the bucket. What the server does
to a document is the kernel, proved against the specification's catalogue of
92 properties. What a node decides about membership, its cache and its
deadline keys is the kernel too, each decision proved to compute its
specification. What several nodes do to one bucket is the system model,
proved safe whatever the clocks do. What the proof stops at, the shim between
the verified core and S3, a deterministic simulator holds to the Resonate
model of [dtornow/accordant](https://github.com/dtornow/accordant) under
crashes, outages and lost acks.

## Layout

| | |
|---|---|
| [`abstract/`](abstract) | the independent executable Abstract Resonate machine: all 21 protocol handlers and all 6 autonomous actions, with observation bookkeeping separate from semantics; Verus-only dependencies, no kernel, Concrete, Accordant or checker dependency |
| [`kernel/`](kernel) | everything verified that runs: the Resonate state machine on one document, every step proved against the catalogue; and a node's decisions about membership, cache versions and deadline keys, the commit, the sweep, each proved to compute its specification |
| [`concrete/`](concrete) | the deterministic document model at its own level: persisted promise rows in order, with kernel maps only as derived views; normalization uses that row order directly |
| [`refinement/`](refinement) | the local Concrete-to-Abstract proof boundary: independent type/state translation and refinement relation, with no checker-framework dependency |
| [`system/`](system) | the system: nodes over one bucket as a TLA-style state machine over the kernel; four theorems, no clock assumed anything of; proof only |
| [`logic/`](logic) | the decision core: a pure state machine, events in, effects out, no I/O; every store call a submission, every answer a completion; the verified core takes every decision inside it |
| [`echod/`](echod) | the node: the core's effects performed against a real store, a real clock and HTTP; the `ResonateServer` and the binary |
| [`sim/`](sim) | `echod-sim`: the node under deterministic simulation, every run checked against the Resonate model of [dtornow/accordant](https://github.com/dtornow/accordant) |
| [`diff/`](diff) | `echod-diff`: echod against the Resonate reference server, both over HTTP, on one seeded request stream; every response, message and snapshot compared. `diff/accordant/`: echod driven by the Resonate model of [dtornow/accordant](https://github.com/dtornow/accordant), every trace checked against it |
| [`examples/ts/`](examples/ts) | the TypeScript SDK against the node |
| [`scripts/`](scripts) | the store and end-to-end tests against a real S3 API |

`abstract/`, `kernel/`, `concrete/` and `system/` verify independently.
The refinement links between those levels and the full `logic/` orchestration
remain to be proved. `logic/` runs with no runtime: its tests feed it events
by hand. `echod/` performs what it asks. `sim/` is the executable evidence.
[DESIGN.md](DESIGN.md) is the design;
[BACKLOG.md](BACKLOG.md) is what is next. Each crate's `lib.rs` opens with
a map of its files.

## Build, verify, soak

```
cargo build --workspace                 # every crate, the ghost code erased
cargo test --workspace                  # unit and end-to-end tests, in memory
(cd abstract && ./verify.sh)            # the independent Abstract protocol machine
(cd kernel && ./verify.sh)              # the kernel under Verus
(cd concrete && ./verify.sh)            # the row-native Concrete document model
(cd refinement && ./verify.sh)          # local Concrete-to-Abstract relation
(cd system && ./verify.sh)              # the system model under Verus, importing the kernel
cargo run --release -p echod-sim -- soak --from 1 --seeds 20   # the simulator
cargo run --release -p echod            # a node on an in-memory store, :8001
cargo run --release -p echod-diff -- --resonate <path to a resonate binary> --seeds 4   # the differential
```

The differential wants the reference server built from `resonatehq/resonate`
(`impl/server/core`, `cargo build --release --bin resonate`); it starts it
and echod in debug mode and drives both over HTTP. `diff/accordant` is a
workspace of its own (`cd diff/accordant && cargo run --release`): it
builds against accordant's pin of Verus's `vstd`, which is not the
kernel's.

`verify.sh` wants a Verus source tree with a release build in `VERUS_DIR`
(default `~/verus-lang/verus/source`) and z3 beside it. `cargo build` is
the other compiler for the same sources: it sees the executable code alone.
