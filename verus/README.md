# The soundness statement and proof, in Verus

They live in the crate now, next to the code they are about:

- `src/semantics.rs`: what the checker promises. `step(m, c, label, d)` is the
  transition relation (`invoke`, `ret`, `receive`, `tick` observed; `effect`,
  `run` silent), `legal` an execution the system can take, `project` what it shows a
  client, `valid(m, init, trace)` "some legal execution from `initial(init)`
  projects to the trace". `check` carries the checker's contract:
  `Ok ==> valid`, `Ko ==> !valid` (`external_body`).
- `src/certificate.rs`: the replay `certify`, verified: it ensures
  `Ok(()) ==> valid(m, init, trace)`. This is the code that runs.
- `src/certificate/proof.rs`: the lemmas. `src/certificate/trusted.rs`: the two
  trusted helpers (`copy`, `same`).

The model's interface (`Model`, with `spec` twins of `external` and
`internal`) is in `src/lib.rs`, inside `verus!`.

## Rover

`src/rover/` is the Rust + Verus counterpart of the Lean Rover world:

- `RoverModel` is the pluggable executable protocol interface. `initial`,
  `injectable`, and `on_event` have `spec_*` twins, so a model must verify that
  its running transition code computes the relation used by proofs.
- `semantics.rs` defines the append-only message network, process steps,
  explicit outside observations, legal executions, boundary projection, and
  `valid_trace`.
- `checker.rs` performs bounded certificate search. Search failure is not a
  proof that a trace is invalid.
- `replay.rs` independently executes a certificate. Verus proves
  `replay(...).is_ok() ==> valid_trace(model, config, trace)`, so search is
  outside the trusted argument.
- `tests/rover.rs` is an executable counter protocol demonstrating delayed,
  reordered, and duplicate message delivery as well as rejected traces.
- `src/rover/resonate/` mirrors Lean's `Resonate` folder:
  it owns the complete standalone protocol (promises, callbacks, listeners,
  tasks, leases, schedules, dispatches and internal work), and
  `abstract_model.rs` owns the one-process reference model. Its executable
  `on_event` and mathematical `spec_on_event` are deliberately parallel.
  `examples/resonate` is now only a compatibility re-export for existing tests.

Use `rover::check` for bounded trace checking, or `rover::replay` to validate a
stored or externally generated certificate exactly. Model-specific invariants
can be stated over the public `rover::semantics::{World, step, legal,
valid_trace}` definitions.

## Running it

Checked with Verus `0.2026.10.13.96607e2` (a rolling release from
github.com/verus-lang/verus), which needs a recent Rust toolchain (1.99 here); `vstd` is pinned to the matching crates.io release:

```
cargo verus verify -p accordant
# verification results:: 216 verified, 0 errors
```
