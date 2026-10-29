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
- `Resonate/TraceChecker.lean` — executable certificate search, verified
  replay into an abstract Rover execution, and checker soundness.
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

## Trace checker

Import `Resonate.TraceChecker`, construct a `List Resonate.BoundaryEvent`, and
call:

```lean
open Resonate

def result :=
  TraceChecker.check ({} : Resonate.Config) TraceChecker.createTrace

#guard result.isSome
```

`TraceChecker.check config events` returns
`Option (TraceChecker.Certificate × Rover.Execution Resonate.Abstract.model)`.
`some (certificate, execution)` means the trace was accepted and includes the
replayed concrete abstract execution; `none` means the bounded search found no
certificate. Search completeness is not claimed.

To validate a stored or externally produced certificate exactly, use:

```lean
def replayed :=
  match result with
  | some (certificate, _) =>
      TraceChecker.replay ({} : Resonate.Config)
        TraceChecker.createTrace certificate
  | none => none
```

Replay checks monotone times, request presence in Rover's append-only network,
membership in `Resonate.run`, and the exact output batch emitted by each
process step. `TraceChecker.check_sound` proves that every `some` result from
`check` implies `Resonate.Abstract.ValidBoundaryTrace` for the supplied config
and events; `TraceChecker.replay_valid` provides the corresponding theorem for
any successfully replayed certificate.

Build with `lake build`.
