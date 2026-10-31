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
- `refinement.rs` proves the generic Rover refinement theorem: related initial
  worlds plus a model-specific forward simulation imply inclusion of every
  concrete boundary trace in the abstract model. Concrete and abstract models
  may have different PID/message types through projections to one boundary
  type.
- `tests/rover.rs` is an executable counter protocol demonstrating delayed,
  reordered, and duplicate message delivery as well as rejected traces.
- `src/rover/resonate/` mirrors Lean's `Resonate` folder:
  it owns the complete standalone protocol (promises, callbacks, listeners,
  tasks, leases, schedules, dispatches and internal work), and
  `abstract_model.rs` owns the one-process reference model. Its executable
  `on_event` and mathematical `spec_on_event` are deliberately parallel.
  Its tests, benchmark and fuzz driver live in the root package alongside it.
- `src/rover/resonate/properties.rs` begins the named conformance catalogue:
  state and transition predicates are stated over `StateV`, initialization and
  representation-level properties are proved, and the complete
  `on_event_preserves_catalogue` formula is the explicit preservation
  obligation. Of upstream's 93 entries, 82 map to Rover state/transitions and
  11 mention its different outbox model. Outbox persistence is translated to
  Rover's generic proved `step_preserves_network` theorem; send-time,
  provenance, response, liveness and algebraic claims are classified
  separately where a state-pair predicate would lose information. Preservation
  is proved for no-op steps and all three read-only handlers (`promise.get`,
  `task.get`, `schedule.get`); mutating handlers remain explicit obligations.

Use `rover::check` for bounded trace checking, or `rover::replay` to validate a
stored or externally generated certificate exactly. Model-specific invariants
can be stated over the public `rover::semantics::{World, step, legal,
valid_trace}` definitions.

## Running it

Checked with Verus `0.2026.10.13.96607e2` (a rolling release from
github.com/verus-lang/verus), which needs a recent Rust toolchain (1.99 here); `vstd` is pinned to the matching crates.io release:

```
cargo verus verify -p accordant
# verification results:: 229 verified, 0 errors
```
