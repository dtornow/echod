# Rover

Rover is an append-only message-passing model of the full public Resonate
abstract protocol pinned in `lakefile.toml`.

## Full abstract machine

- `Resonate/Machine.lean` defines Rover Resonate's state with only fused
  `objects` and `schedules`, reusing the public object and schedule types. Its
  Reader+State+Writer monad applies state writes immediately, so handlers read
  their own writes, while transient boundary messages append in order.
  `readObject` is the only projection-aware object read: it returns a projected
  view without persisting it; `readTaskObject` only adds a task-presence guard.
- `Resonate/Handlers.lean` implements all 21 external handlers.
- `Resonate/Internal.lean` implements all six internal handlers.
- `Resonate.lean` uses the public protocol request, response, record, task,
  schedule, and emitted-message types. Rover adds only client correlation and
  transport envelopes. `Resonate.run` executes external calls at `Call.requestedAt`;
  `runTimeout` executes process-local work at the Rover timeout time.
- `Resonate/Abstract.lean` has one service process. Only external calls are
  injectable. A timeout event carries no internal request: the service
  first projects every fused object at the timeout time in one state update,
  then snapshots `Direct.internalSteps` and executes that finite list in one
  deterministic Reader+State+Writer pass. The order is each object's callbacks,
  listeners, task lease timeout, and task retry timeout in stored order,
  followed by schedules in stored order. Later handlers observe earlier writes,
  and the Writer preserves message emission order; work newly enabled by the
  pass waits for a later timeout.
- The service sends Writer emissions directly into the Rover network alongside
  boundary responses. Internal work is never represented as a wire message.
- `Resonate/TraceChecker.lean` searches the full request/response/message
  boundary protocol. A successful certificate is replayed against Rover and
  `check_valid_sound` proves that every `valid` verdict is a real abstract
  behavior. Exhaustion is conservatively `unknown`.
- `Resonate/Examples.lean` contains executable promise, task,
  read-your-own-writes, schedule, ordered and non-deduplicated message,
  timeout-sweep, deferred-work, retry, and trace-checking tests.

The public protocol types under `01-protocol` are authoritative. The local
model reuses the public `PromiseObject`, `TaskObject`, `Object`, and
`Schedule` types and their pure projection/record helpers.

## Narrow legacy concrete model

`Resonate.PromiseSlice.Concrete` retains the faithful raw conditional PUT
semantics for the former four-operation promise slice: replaying an old PUT
conflicts, and flaky writes have written, failed-after-land, and
failed-without-land outcomes.

The old end-to-end boundary refinement is intentionally not stated for the
full machine. Its concrete wire payload stores one legacy promise document,
whereas a full handler can atomically modify multiple fused promise/task rows,
schedules, and emit boundary messages. No representation relation can make that
single-document transition simulate the full atomic transition. The retained
facts are therefore isolated under `Resonate.PromiseSlice.Refinement`; they do
not pretend to prove full-protocol refinement.

Build with:

```sh
lake build
```
