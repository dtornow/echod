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

## Checking traces in the same shape

- `Kleppmann/World.lean`: the same shape set up for trace checking. Three
  kinds of process: `sys` (the model: `external` for requests, `tick` for
  what it does on its own, `due` for what must have happened by), clients,
  and the clock. One rule, Kleppmann's, with four marked changes: a clock
  only the clock process moves; nothing but a tick while something is due;
  a step has a list of outcomes; a received message is gone. A trace is
  every step but the system's; `Valid` says some execution shows exactly it.
- `Kleppmann/Check.lean`: a certificate is the system's steps between
  observed events; `certify` replays it, `accepted_valid` proves what it
  accepts is valid, `search` finds one (`search_sound`). A counter with a
  timer exercises `due` and concurrency.
- `Kleppmann/ResonateCheck.lean`: Resonate as such a model, from the
  specification's handlers. `tick` runs every internal step the state makes
  a candidate and keeps those that change something; `due` reads leases,
  retries and schedules off the state. Scenarios: a promise read across its
  timeout, two clients whose window is message causality, a lease that runs
  out and must be released and re-offered before anything else is observed.

`lake build` fetches the specification and checks everything.
