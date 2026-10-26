# Resonate in Kleppmann's terms

The world modeled the way Martin Kleppmann does in
[Verifying distributed systems with Isabelle/HOL](https://martin.kleppmann.com/2022/10/12/verifying-distributed-systems-isabelle.html):
processes with local state and one step function, a step is one event at one
process, and the network is the list of every message ever sent. Delay,
reordering, duplication and loss are what is left unsaid.

- `Kleppmann/Network.lean`: his model, transcribed (`Event`, `StepFunc`,
  `ValidEvent`, `Execute`), and his proof method as one lemma
  (`Execute.invariant`). Two deviations, marked: every step happens at an
  instant `now` that never decreases, and `Timeout` names which timeout.
- `Kleppmann/Resonate.lean`: Resonate as such a world. The server's step
  function is the specification's own (`Abstraction.handleExternal`,
  `Abstraction.handleInternal`, from
  [resonate-specification](https://github.com/resonatehq/resonate-specification),
  pinned in `lakefile.toml`); its `setMessage` effects are sends to workers.
  Clients turn user input into requests and keep what they receive. A
  scenario runs under `#guard`, and `answered` proves, by induction over the
  execution, that every response a client can receive answers a request it
  sent.

`lake build` fetches the specification and checks everything.
