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
