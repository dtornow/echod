# The soundness statement, in Verus

`accordant.rs` says the same thing as `lean/Accordant.lean`, in the same shape:
how a system's evolution maps to what clients observe, and that the checker
only accepts traces some run could produce.

- `step(m, c, label, d)` is the transition relation: the cases `invoke`,
  `ret`, `receive` (observed: the label is the observation) and `effect`,
  `run`, `advance` (silent). Lean's `Step` constructors, one predicate each.
- `is_run(m, configs, labels)`: every consecutive pair of configurations is a
  step with that label. Lean's `Steps`, unfolded into sequences.
- `visible(labels)`: the run's observations in order; silent steps show nothing.
- `valid(m, init, start, trace)`: some run from `initial(init, start)` has
  `visible(labels) == trace`.
- `check` carries the contract `accepted ==> valid(...)`, and
  `accepted_implies_valid` states it as a lemma. Not proved (`external_body`,
  `admit()`).

Proved: the empty trace is valid for every model, and for a one-call counter
"sent `incr`, got 1" is valid via invoke (seen), effect (silent), return (seen).
Changing the response to 2 makes that proof fail, as it should.

Not modeled yet: request lifetimes and `assert_idle`.

## Running it

Checked with Verus `0.2026.10.04.fc7d32e` (a rolling release from
github.com/verus-lang/verus), which needs Rust toolchain 1.98.1:

```
rustup install 1.98.1-x86_64-unknown-linux-gnu
verus --crate-type=lib verus/accordant.rs
# verification results:: 4 verified, 0 errors
```
