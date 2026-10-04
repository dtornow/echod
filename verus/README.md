# The soundness statement, in Verus

`accordant.rs` states, in Verus, the theorem the Lean spec states as
`accepted_trace_implies_valid_trace`: what the checker accepts is a valid trace,
meaning some run of the model produces exactly those observations.

- `Event` is what a client observes: `Invoke`, `Return`, `Receive`, each with a time.
- `Model` has `external` and `internal` as spec functions.
- A run is a sequence of `Move`s: the next observation, or something nobody sees
  (a call taking effect, internal work running, time passing). `step` says when
  each is allowed: overdue work runs first, time can't pass a deadline, a return
  must match the response the call took effect with, a received dispatch must
  have been sent.
- `valid(m, init, start, trace)`: some sequence of moves replays the whole trace.
- `check` carries the contract `accepted ==> valid(...)`; the Lean-style lemma
  says the same about an abstract `accepted` predicate.

The theorem is stated, not proved: `check` is `external_body` and the lemma is
`admit()`ted. `the_empty_trace_is_valid` is proved, as a check that `valid` is
well-formed and usable.

Not modeled yet: request lifetimes and `assert_idle`.

## Running it

Checked with Verus `0.2026.10.04.fc7d32e` (a rolling release from
github.com/verus-lang/verus), which needs Rust toolchain 1.98.1:

```
rustup install 1.98.1-x86_64-unknown-linux-gnu
verus --crate-type=lib verus/accordant.rs
# verification results:: 3 verified, 0 errors
```
