# Rover

Rover is an append-only, Kleppmann-style model and a proved promise-service
refinement.

## Layout

- `Rover/World.lean` — generic worlds, injection, process steps, append-only
  message history, legal executions, `Behavior`, and raw boundary traces.
- `Resonate.lean` — shared calls, responses, notifications, clean
  boundary events, and the promise transition reused from experiment 1.
- `Resonate/Abstract.lean` — exactly one real process containing the global
  promise state.
- `Resonate/Concrete.lean` — any duplicate-free list of stateless server
  addresses plus one versioned object store. Servers load, evaluate, and
  submit conditional-write candidates.
- `Resonate/Refinement.lean` — the forward simulation and end-to-end
  `boundary_refinement` theorem.
- `Resonate/Examples.lean` — executable checks for create, successful commit,
  duplicate stale commit, and a three-node theorem instantiation.

The network records every message ever sent. Receiving checks membership and
does not remove anything, so loss, delay, reordering, and arbitrary duplicate
delivery are all represented without extra rules. `outside` is not a process:
the environment appends injectable requests, while sends addressed to
`outside` are observations.

## Refinement

The concrete store is the linearization point. A server computes a candidate
from a versioned snapshot. Only a candidate whose version and prior state both
match may update the store and publish its response/notifications. Replaying a
successful CAS message therefore conflicts and requests a new snapshot.

`Resonate.Refinement.boundary_refinement` proves, without project-specific axioms
or admitted obligations, that every legal concrete boundary trace is a valid
trace of the single-process abstract model for arbitrary duplicate-free server
lists under conditional writes.

## Later trace checker

`Resonate.BoundaryEvent` is the stable checker-facing format. A checker can:

1. decode input/output records into `BoundaryEvent`;
2. replay candidate abstract states with `Resonate.run`;
3. report an executable witness or mismatch;
4. rely on `boundary_refinement` for concrete-to-abstract soundness.

The current `#guard` examples already exercise the pure transition data that
such a checker will consume; no unproved checker is trusted by the theorem.

Build with `lake build`.
