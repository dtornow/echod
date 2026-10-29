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
- `Resonate/Concrete.lean` — any duplicate-free list of server addresses plus
  a per-document versioned object store. Node-local flights retain calls and
  handler outcomes; raw PUTs carry only protocol data.
- `Resonate/Refinement.lean` — ghost PUT provenance and its reachable-network
  invariant.
- `Resonate/TraceChecker.lean` — executable certificate search, verified
  replay into an abstract Rover execution, and checker soundness.
- `Resonate/Examples.lean` — executable checks for create, successful commit,
  duplicate stale commit, and all three flaky-write outcomes.

The network records every message ever sent. Receiving checks membership and
does not remove anything, so loss, delay, reordering, and arbitrary duplicate
delivery are all represented without extra rules. `outside` is not a process:
the environment appends injectable requests, and a separate outside-observe
step observes messages addressed to it without consuming them. Process sends
are hidden until that explicit observation.

## Refinement

The store payload protocol is `get/got/put/written/conflict/failed`. A PUT is
exactly a key, document, and optional expected per-document version. Operation
ids live only in the surrounding RPC call/reply envelope used for correlation.
Replaying a successful enveloped PUT therefore conflicts against its stale version.
Flaky writes have the three storage outcomes: landed/written, landed/failed,
and not-landed/failed.

`Resonate.Refinement.reachable_raw_put_valid` proves, without proof-carrying
messages, that every raw PUT in a reachable append-only network is a legitimate
selected handler outcome.

Explicit outside observation lets the abstract service linearize writes in
store order while client outputs are observed later in any delivery order.
For flaky storage, the intended refinement target is
`{ appConfig with unreliable := true }`: written maps to serve,
landed/failed to lose, and not-landed/failed to shed. Unobserved abstract
notifications may remain in the append-only network.

`Resonate.Refinement.boundary_refinement` proves end-to-end trace inclusion
for every duplicate-free node list when conditional writes are enabled. Its
reachable invariant connects op-only replies to node history, reconstructs
raw-PUT provenance, preserves the per-document store representation, and
tracks abstract output coverage until explicit outside observation.

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
