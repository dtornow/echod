# echod-abstract

Independent executable Verus port of:

- `spec/01-protocol/types.lean` (plus the validation definitions needed by
  the abstract machine)
- `spec/02-abstract/state.lean`
- `spec/02-abstract/external.lean`
- `spec/02-abstract/internal.lean`
- `spec/02-abstract/system.lean`

The dependency graph ends at `vstd` and the Verus builtins. In particular,
this crate does not depend on `echod-kernel`, `echod-concrete`, `logic`,
`refine`, or Accordant.

## Shape

- `types.rs`: protocol records, every request/response type, ordered tags,
  first-match tag lookup, and generated ghost/spec twins.
- `state.rs`: fused promise/task objects, state, ordered writer effects,
  executable commit, and a pure `spec_apply_all` twin.
- `promise_spec.rs`: independent `AState`/`AEffect` reader-writer semantics
  for all six Promise external actions, including their committed next states.
- `external.rs`: one named semantic action for every external handler.
- `internal.rs`: one named semantic action for every internal handler.
- `system.rs`: the 21/6 dispatch sums and semantic runners. Observation
  bookkeeping is a separate type with no access to state or handlers.

Handlers read an immutable pre-state and emit effects. `apply_all` commits
those effects afterward. This preserves the Lean reader/writer rule that a
transition never observes one of its own writes. Upserts prepend and stable
filters retain relative order; task writes map in place.

## Coverage

All 21 external names are present and dispatched:

| Family | Actions | Semantics |
|---|---|---|
| Promise | get, create, settle, register callback, register listener | executable |
| Promise | search | exact Lean result: 501, no effects |
| Task | get, create, acquire, fence, heartbeat, suspend, fulfill, release, halt, continue | executable |
| Task | search | exact Lean result: 501, no effects |
| Schedule | get, create, delete | executable |
| Schedule | search | exact Lean result: 501, no effects |

All six internal names are executable: promise timeout, callback, listener,
task lease timeout, task retry timeout, and schedule timeout.

Each internal handler has an independently stated ghost semantics and an
executable postcondition proving its exact ordered `Seq<AEffect>` result.
The callback/resume and schedule folds always read the transition pre-state;
their effect sequences are concatenated in Lean writer order. Forced touches
materialize both projected faces, while lease/retry views project without
emitting either write.

There are no remaining handler bodies. The only unsupported operations are
the three searches, and they are unsupported in the Lean source itself.

Each executable Promise handler has a Verus contract proving that its response
and ordered effect sequence equal the independent ghost semantics, and that
committing those effects with `spec_apply_all` yields the specified next state.

## Explicit semantic boundaries

Lean declares `nextCron`, `occurrences`, and `expand` opaque. Executable
schedule requests therefore carry their computed witnesses:

- `ScheduleCreateReq.next_run_at`
- `ScheduleTimeoutReq.occurrences` (including expanded promise ids)
- `ScheduleTimeoutReq.next_run_at`

The action preserves the supplied occurrence list order and applies the same
stable `≤ now` filter as Lean. A future checker must obtain these witnesses
from its cron/expansion implementation and validate that boundary.

Lean uses unbounded `Nat`; the executable carrier is `u64`. Handlers do not
invent rejection responses at the carrier boundary: arithmetic saturates
only to keep the executable total. Refinement and checker-completeness
theorems restrict inputs to the no-overflow domain, where these operations
equal Lean arithmetic exactly. Values outside that domain are unsupported by
the executable twin, not protocol-level 400 responses.

`Text` stores Unicode scalar values, matching the kernel's `Seq<char>` view;
wire encoding remains outside this model. Equality and ASCII protocol tags
are exact, and the delay parser accepts decimal ASCII characters.

## Verification

```sh
./abstract/verify.sh
```

The script runs Verus directly (preferring `/tmp/verus-release`) and then
copies this crate into a one-member temporary workspace for Rust tests. That
second build makes accidental dependencies on another echod crate impossible.
