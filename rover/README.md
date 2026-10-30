# Rover

Rover is an append-only message-passing model of the full public Resonate
abstract protocol pinned in `lakefile.toml`.

## Full abstract machine

- `Resonate/Machine.lean` defines a small Reader+State monad over the public
  fused `ServerState` (`objects`, `schedules`, and `outbox`). Bind threads the
  updated state, so handlers read their own writes. There is no effect list or
  materialisation boolean.
- `Resonate/Handlers.lean` implements all 21 external handlers.
- `Resonate/Internal.lean` implements all six internal handlers.
- `Resonate.lean` uses the public protocol request, response, record, task,
  schedule, and outbox types. Rover adds only client correlation and transport
  envelopes. `Resonate.run` executes external calls at `Call.requestedAt`;
  `runInternal` executes process-local actions at the Rover step time.
- `Resonate/Abstract.lean` has one service process. Only external calls are
  injectable. Internal work is represented by self-addressed messages derived
  from the fused state, so it is executable but cannot be supplied by the
  environment.
- `Resonate/TraceChecker.lean` searches the full request/response/outbox
  boundary protocol. A successful certificate is replayed against Rover and
  `check_valid_sound` proves that every `valid` verdict is a real abstract
  behavior. Exhaustion is conservatively `unknown`.
- `Resonate/Examples.lean` contains executable promise, task,
  read-your-own-writes, schedule, listener/outbox, promise-timeout, retry, and
  trace-checking tests.

The public protocol types under `01-protocol` are authoritative. The local
model reuses the public `PromiseObject`, `TaskObject`, `Object`, and
`ServerState` representation and its pure projection/record helpers.

## Narrow legacy concrete model

`Resonate.PromiseSlice.Concrete` retains the faithful raw conditional PUT
semantics for the former four-operation promise slice: replaying an old PUT
conflicts, and flaky writes have written, failed-after-land, and
failed-without-land outcomes.

The old end-to-end boundary refinement is intentionally not stated for the
full machine. Its concrete wire payload stores one legacy promise document,
whereas a full handler can atomically modify multiple fused promise/task rows,
schedules, and outbox entries. No representation relation can make that
single-document transition simulate the full atomic transition. The retained
facts are therefore isolated under `Resonate.PromiseSlice.Refinement`; they do
not pretend to prove full-protocol refinement.

Build with:

```sh
lake build
```
