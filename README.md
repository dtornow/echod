# echod

A Resonate server whose only durable state is objects in an S3 bucket, with
the state machine it runs verified in Verus, from one document up through
the whole process.

The server speaks the Resonate protocol, one `POST /` and one envelope. Every
origin is one document in the bucket, committed with a conditional write;
deadlines are keys; nodes find each other in the bucket. What the server does
to a document is `echod_concrete`'s document machine, each step proved to
compute its specification, and that concrete model is proved to refine the
abstract Resonate model. The process around it, `echod_logic`, is proved
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
rust/impl/box         the box binary: an ephemeral Docker terminal configured by box.nix
rust/spec/rover       the Rover world, replay, and refinement theorem
rust/spec/abstract    the Resonate protocol as a Rover model
rust/spec/concrete    the document machine the process runs, proved; the Rover model and its refinement
rust/test/runtime     the deterministic effect interpreter
rust/test/cli         the simulator, the differential, the model driver, the store tests
lean/src/Rover        the Rover world, for experiment
lean/src/abstract     the Resonate model, for experiment
lean/src/concrete     nodes and one store, for experiment
examples/ts           the TypeScript SDK against the node
scripts               the store and end-to-end tests against a real S3 API
```

The process's document steps are `rust/spec/concrete`'s, each proved equal to
its specification; the process itself is proved to compute `spec_on_event`,
its bookkeeping and the sequence of store calls around each step included.
Concrete depends on the abstract model; it does not depend on the process.
What the process assumes — the text of keys, the bytes of documents — is
stated as specifications and listed in `src/verified/mod.rs`; its tests feed
it events by hand. The runtime performs what it asks. The simulator is the
evidence. [DESIGN.md](DESIGN.md) is the design; [BACKLOG.md](BACKLOG.md) is
what is next. Each crate's `lib.rs` opens with a map of its files.

## Build, verify, soak

```
cargo build --workspace                 # every crate, the ghost code erased
cargo test --workspace                  # unit and end-to-end tests, in memory
cargo verus verify -p echod-concrete    # the document machine and the refinement, under Verus
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

## Development boxes

The `box` binary opens the current directory at `/workspace` in an ephemeral
Docker container. It first applies `~/.box/.box.nix`, when present, and then
the current directory's `box.nix`, using nested `nix-shell` environments
before opening Bash. The global `~/.box` directory is mounted read-only; the
working directory is mounted read-write, while everything else in the
container is discarded on exit.

```sh
cargo install --path rust/impl/box
box
box -- cargo test
```

Credentials can be copied explicitly from the host environment. Their values
are inherited by Docker rather than placed in its command line:

```sh
box --credential ANTHROPIC_API_KEY
BOX_CREDENTIALS=ANTHROPIC_API_KEY,OPENAI_API_KEY box
```

This initial mode deliberately makes those credentials readable inside the
container. The Strands credential and egress-gateway sources are vendored but
inactive by default; `--features strands-proxy` compiles them for the later
proxy-custody mode without changing runtime behavior yet.

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
