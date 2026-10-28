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

There are no remaining handler bodies. The only unsupported operations are
the three searches, and they are unsupported in the Lean source itself.

## Explicit semantic boundaries

Lean declares `nextCron`, `occurrences`, and `expand` opaque. Executable
schedule requests therefore carry their computed witnesses:

- `ScheduleCreateReq.next_run_at`
- `ScheduleTimeoutReq.occurrences` (including expanded promise ids)
- `ScheduleTimeoutReq.next_run_at`

The action preserves the supplied occurrence list order and applies the same
stable `≤ now` filter as Lean. A future checker must obtain these witnesses
from its cron/expansion implementation and validate that boundary.

Lean uses unbounded `Nat`; this executable uses the protocol-friendly `u64`
domain and `MAX_TIME = 2^62 - 1`. Create/acquire actions reject values outside
that sound arithmetic door with 400, and bounded delay parsing saturates at
the door. Inside the door, additions cannot overflow and the results match
the Lean arithmetic. Internal callers must likewise supply `now ≤ MAX_TIME`
and `Config::bounded()`. This is an explicit input-domain restriction, not a
successful result for an unimplemented case.

`Text` stores UTF-8 bytes. Equality and ASCII protocol tags are exact; the
delay parser is intended for the protocol's decimal ASCII delay values.

## Verification

```sh
./abstract/verify.sh
```

The script runs Verus directly (preferring `/tmp/verus-release`) and then
copies this crate into a one-member temporary workspace for Rust tests. That
second build makes accidental dependencies on another echod crate impossible.
