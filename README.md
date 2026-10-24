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
the verified core and S3, a deterministic simulator holds to the same kernel
under crashes, outages, lost acks and clock jumps.

## Layout

| | |
|---|---|
| [`kernel/`](kernel) | everything verified that runs: the Resonate state machine on one document, every step proved against the catalogue; and a node's decisions about membership, cache versions and deadline keys, the commit, the sweep, each proved to compute its specification |
| [`system/`](system) | the system: nodes over one bucket as a TLA-style state machine over the kernel; four theorems, no clock assumed anything of; proof only |
| [`logic/`](logic) | the decision core: a pure state machine, events in, effects out, no I/O; every store call a submission, every answer a completion; the verified core takes every decision inside it |
| [`echod/`](echod) | the node: the core's effects performed against a real store, a real clock and HTTP; the `ResonateServer` and the binary |
| [`sim/`](sim) | `echod-sim`: the node under deterministic simulation, checked for linearizability against the kernel |
| [`diff/`](diff) | `echod-diff`: echod against the Resonate reference server, both over HTTP, on one seeded request stream; every response, message and snapshot compared. `diff/accordant/`: echod driven by the Resonate model of [dtornow/accordant](https://github.com/dtornow/accordant), every trace checked against it |
| [`examples/ts/`](examples/ts) | the TypeScript SDK against the node |
| [`scripts/`](scripts) | the store and end-to-end tests against a real S3 API |

`kernel/` and `system/` are proved. `logic/` is the shim the proof stops at,
with nothing in it but the order of calls, and it runs with no runtime:
its tests feed it events by hand. `echod/` performs what it asks. `sim/` is
the evidence for both. [DESIGN.md](DESIGN.md) is the design;
[BACKLOG.md](BACKLOG.md) is what is next. Each crate's `lib.rs` opens with
a map of its files.

## Build, verify, soak

```
cargo build --workspace                 # every crate, the ghost code erased
cargo test --workspace                  # unit and end-to-end tests, in memory
(cd kernel && ./verify.sh)              # the kernel under Verus
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
