# echod

A Resonate server whose only durable state is objects in an S3 bucket, with
the state machine it runs verified in Verus, from one document up through
the whole process.

The server speaks the Resonate protocol, one `POST /` and one envelope. Every
origin is one document in the bucket, committed with a conditional write;
deadlines are keys; nodes find each other in the bucket. What the server does
to a document is `echod_logic::concrete`'s document machine, each step proved
to compute `echod_concrete_spec`'s specification, and
`echod_refinement` proves that model refines the abstract Resonate
model. The process around it, `echod_logic`, is proved
whole: `State::on_event`, the one step of the node — a request, a store
answer, the heartbeat, the wheel — ensures it computes `spec_on_event`, and
every function beneath it ensures its own specification, the membership, the
cache, the deadline keys, and the order of the store calls that commit a step
— key, document, previous key, fired key — included. What the proof assumes,
the text of keys, the bytes of documents, hashing, and S3 itself, is listed in
`rust/impl/process/src/verified/mod.rs`; a deterministic simulator holds the
whole to the Resonate model under crashes, outages and lost acks.

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
rust/impl/box         optional Docker/Nix development CLI (not a server dependency)
rust/experiment/claude-quickjs  optional Messages API agent-loop experiment
```

The process's document steps live under `rust/impl/process/src/concrete`,
each proved equal to `rust/spec/echod/concrete/spec`'s specification; the process itself is proved to compute `spec_on_event`,
its bookkeeping and the sequence of store calls around each step included.
Concrete depends on the abstract model only for shared boundary protocol
types and trusted cron/occurrence algebra; it does not depend on the process.
What the process assumes — the text of keys, the bytes of documents — is
stated as specifications and listed in `src/verified/mod.rs`; its tests feed
it events by hand. The runtime performs what it asks. The simulator is the
evidence. [DESIGN.md](DESIGN.md) is the design; [BACKLOG.md](BACKLOG.md) is
what is next. Each crate root opens with a map of its files.

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

## Optional development tools

Neither tool is started by the server or reads credentials during a normal
server build/run. Workspace tests include their offline tests.

The `box` binary opens the current directory at `/workspace` in an ephemeral
Docker container. It first applies `~/.box/.box.nix`, when present, and then
the current directory's `box.nix`, using nested `nix-shell` environments
before opening Bash. The global `~/.box` directory is mounted read-only; the
working directory is mounted read-write. Container deletion does not undo
changes to the working directory. Run only trusted Nix expressions and images.

```sh
cargo install --path rust/impl/box --locked
box
box -- cargo test
box --credential ANTHROPIC_API_KEY
BOX_CREDENTIALS=ANTHROPIC_API_KEY,OPENAI_API_KEY box
```

Credential forwarding is opt-in. Values are inherited by Docker rather than
placed in its command line, but are readable inside the container and by
Docker administrators. Do not use this mode as secret isolation.

`box.nix` is a normal Nix shell expression:

```nix
{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  packages = with pkgs; [ git rustc cargo ];
}
```

Docker and network access to pull `nixos/nix:latest` are required. Override
the runtime or image with `--runtime` / `BOX_RUNTIME` and `--image` /
`BOX_IMAGE`; for example, `BOX_RUNTIME=podman box`.

The vendored Strands credential and egress-gateway libraries retain their
licenses and upstream documentation under `rust/vendor/strands-box`.
They are excluded from workspace membership and disabled in normal builds.
`cargo check -p echod-box --features strands-proxy --locked` explicitly compiles
them, but **does not start a proxy or provide proxy custody of credentials**.
Their upstream guidance refers to the original Strands repository; those
upstream consumers and policy components are not part of echod.

The [QuickJS experiment](rust/experiment/claude-quickjs/README.md) runs a small
Messages API loop, not an agent SDK. It requires an explicit model, prompt, and
API key to make paid calls. Its unit tests use synthetic responses with no
external API calls:

```sh
cargo test -p echod-box -p claude-quickjs --locked
cargo run -p claude-quickjs -- --help
```
