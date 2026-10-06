# The soundness statement and proof, in Verus

They live in the crate now, next to the code they are about:

- `src/semantics.rs`: what the checker promises. `step(m, c, label, d)` is the
  transition relation (`invoke`, `ret`, `receive` observed; `effect`, `run`
  silent), `legal` an execution the system can take, `project` what it shows a
  client, `valid(m, init, trace)` "some legal execution from `initial(init)`
  projects to the trace". `check` carries the checker's contract,
  `Ok ==> valid` and `Ko ==> !valid`, verified: the search only proposes, and
  `check` confirms with `certify` or `refute`.
- `src/certificate.rs`: the replay `certify`, verified: it ensures
  `Ok(()) ==> valid(m, init, trace)`. This is the code that runs.
- `src/certificate/refute.rs`: the refutation `refute`, verified: it ensures
  `Some(_) ==> !valid(m, init, trace)`, by enumerating every execution.
- `src/certificate/proof.rs`: the lemmas. `src/certificate/trusted.rs`: the two
  trusted helpers (`copy`, `same`).

The model's interface (`Model`, with `spec` twins of `external`, `internal`
and `now`) is in `src/lib.rs`, inside `verus!`.

## Running it

Checked with Verus `0.2026.10.04.fc7d32e` (a rolling release from
github.com/verus-lang/verus), which needs Rust toolchain 1.98.1:

```
cargo verus verify -p accordant
# verification results:: 68 verified, 0 errors
```
