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

#guard result.isValid
```

`TraceChecker.check config events` returns `TraceChecker.Verdict`:

- `valid certificate execution` includes the independently replayed
  certificate and actual abstract Rover execution.
- `invalid` is a definitive rejection. The checker proves that a valid
  boundary trace can never receive this verdict. This includes nonmonotone
  traces and impossible 404 create responses.
- `unknown` carries no validity claim. It covers every resource cutoff and
  every exhausted case not justified by the checker’s proved refutation
  invariant.

Use `TraceChecker.checkWithBound bound config events` to select the resource
bound explicitly. For example,
`(TraceChecker.checkWithBound 0 {} TraceChecker.createTrace).isUnknown` is
true. Retained state-changing hidden processing consumes the bound.

Search removes hidden timeout/no-op actions (with a trace-existence erasure
proof), keeps only outputs relevant to the remaining trace, saturates duplicate
append-only outputs at one, and skips repeated semantic contexts. Full
finite-state completeness of the promise state quotient is not claimed:
ordered exhausted traces that satisfy the proved response-origin invariant
remain `unknown` when no certificate is found. This residual class includes
unsupported output values, notifications, and state-dependent impossibilities
other than the proved create/404 case.

To validate a stored or externally produced certificate exactly, use:

```lean
def replayed :=
  match result with
  | .valid certificate _ =>
      TraceChecker.replay ({} : Resonate.Config)
        TraceChecker.createTrace certificate
  | _ => none
```

Replay checks monotone times, request presence in Rover's append-only network,
membership in `Resonate.run`, and the exact output batch emitted by each
process step. `TraceChecker.check_valid_sound` proves that every `valid` result
implies `Resonate.Abstract.ValidBoundaryTrace`;
`TraceChecker.check_invalid_sound` proves that every `invalid` result implies
its negation. `TraceChecker.valid_ne_invalid` gives the equivalent statement
for every explicit bound. `TraceChecker.legal_normalizes` shows that arbitrary
legal abstract Rover executions—including timeout/no-op steps, duplicate
request processing, delayed/reordered observations, and append-only message
duplication—have exact replay certificates.
`TraceChecker.valid_has_noop_free_certificate` separately proves that those
inert steps can be erased without changing trace existence.

Build with `lake build`.
