# echod

A Resonate server whose only durable state is objects in an S3 bucket, with
the state machine it runs verified in Verus, from one document up to the
fleet.

The server speaks the Resonate protocol, one `POST /` and one envelope. Every
origin is one document in the bucket, committed with a conditional write;
deadlines are keys; nodes find each other in the bucket. What the server does
to a document is the kernel, proved against the specification's catalogue of
92 properties. What a fleet of servers does to the bucket is the fleet model,
proved safe whatever the clocks do. What the proof stops at, the shim between
the verified core and S3, a deterministic simulator holds to the same kernel
under crashes, partitions, lost acks and clock jumps.

## Layout

| | |
|---|---|
| [`kernel/`](kernel) | one document's machine: the Resonate state machine as executable Rust, every step proved against the catalogue |
| [`fleet/`](fleet) | the system: nodes over one bucket as a TLA-style state machine, the commit protocol, and the node's verified step functions; four theorems, no clock assumed anything of |
| [`server/`](server) | the `ResonateServer`: the trusted shim around the verified core, and the binary |
| [`sim/`](sim) | `echod-sim`: the server under deterministic simulation, checked for linearizability against the kernel |
| [`examples/ts/`](examples/ts) | the TypeScript SDK against the server |
| [`scripts/`](scripts) | the store and end-to-end tests against a real S3 API |

`kernel/` and `fleet/` are proved. `server/` is the shim the proof stops at.
`sim/` is the evidence for the shim. [DESIGN.md](DESIGN.md) is the design;
[BACKLOG.md](BACKLOG.md) is what is next. Each crate's `lib.rs` opens with
a map of its files.

## Build, verify, soak

```
cargo build --workspace                 # every crate, the ghost code erased
cargo test --workspace                  # unit and end-to-end tests, in memory
(cd kernel && ./verify.sh)              # the kernel under Verus
(cd fleet && ./verify.sh)               # the fleet under Verus, importing the kernel
cargo run --release -p echod-sim -- soak --from 1 --seeds 20   # the simulator
cargo run --release -p echod-server     # a server on an in-memory store, :8001
```

`verify.sh` wants a Verus source tree with a release build in `VERUS_DIR`
(default `~/verus-lang/verus/source`) and z3 beside it. `cargo build` is
the other compiler for the same sources: it sees the executable code alone.
