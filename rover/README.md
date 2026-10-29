# Rover

Rover is a minimal Lean model of a message-passing world.

Its local protocol signature is:

```text
Config →
Pid →
State →
Time →
Event Pid Msg →
Nonempty (State × List (Pid × Msg))
```

The world contains:

```lean
structure World where
  process : Pid → State
  network : List (Pid × Pid × Msg)
  now     : Time
```

The network follows Kleppmann's semantics: it records every message that was
sent. Receiving a message checks membership but does not remove it, so messages
may be delayed, lost, reordered, or duplicated.

`model.outside` is a distinguished stateless endpoint:

- an `inject` step appends an allowed request from `outside` to any process;
- messages sent by a process to `outside` are outputs;
- process 0/outside never has a transition of its own.

`trace` keeps only those boundary inputs and outputs. `ValidTrace` means that
some legal execution from an allowed initial state shows exactly that trace.

Build with:

```text
lake build
```
