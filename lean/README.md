# The soundness statement, in Lean

`Accordant.lean` says how a system's evolution maps to what clients observe,
and states that the checker only accepts traces some run could produce.

- `Step m c label c'` is the system's transition relation. Each step is labeled
  with what a client sees: an observation (`invoke`, `ret`, `receive`) or
  nothing (`silent`: a call taking effect, internal work running, time passing).
- `Steps m c trace c'` chains steps; its observations, in order, are `trace`.
  Silent steps may come anywhere in between.
- `Valid m init start trace := ∃ c, Steps m (initial init start) trace c`.
- `accepted_implies_valid` states soundness for every model. Not proved (`sorry`).

Proved, as checks that the definitions mean what they say: the empty trace is
valid for every model, and for a one-call counter, "sent `incr`, got 1" is valid
via invoke (seen), effect (silent), return (seen).

Checked with Lean 4.31.0, core only:

```
lean lean/Accordant.lean
# Accordant.lean:175:8: warning: declaration uses `sorry`
```

It mirrors `verus/accordant.rs`, written as a relation rather than a replay
function. Not modeled yet: request lifetimes and `assert_idle`.

`TigerBeetle.lean` is TigerBeetle's state machine as a `Model`: accounts,
transfers, two-phase transfers, linked chains, expiry by pulse, lookups and
queries, read from `src/state_machine.zig`. It states the account rules
`debits_must_not_exceed_credits` and `credits_must_not_exceed_debits`, and runs
scenarios with `#guard`. It imports `Accordant`, so it builds with Lake:

```
cd lean && lake build
```

`TigerBeetleProofs.lean` proves, without `sorry`, that `debits_must_not_exceed_credits`
holds in every state TigerBeetle can reach from an empty cluster: for every
execution of `model lim` the accordant semantics allows, every account keeps the
rule. The proof carries a stronger invariant: each account's `debits_pending`
covers its still-pending debit transfers.
