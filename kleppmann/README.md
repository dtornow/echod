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

For driven runs (a test, a fuzzer, a server on debug time): every event
carries its time, and the ticks the driver gave the server are recorded.

- `Kleppmann/World.lean`: the same shape set up for trace checking. Two
  kinds of process: the `server`, whose step function is the model
  (`external` for a request, `tick` for a payload-free `timeout`, both
  reading the time, both returning a nonempty list of outcomes), and
  clients. Kleppmann's three events, delivered by the environment. One rule,
  his, with three marked changes: every step has a time `t`, never earlier
  than the last; a step has outcomes, not one result; a received message is
  gone. A trace is every step but the server receiving a request; `Valid`
  says some execution shows exactly it.
- `Kleppmann/Check.lean`: a certificate says, before each observed event,
  which requests the server took (and with which outcome); `certify`
  replays it, `accepted_valid` proves what it accepts is valid, `search`
  finds one (`search_sound`), `explain` prints it. Hidden steps happen at
  the time of the last step: the checker assumes time stands still between
  observed events (sound; possibly incomplete). A counter with a timer
  exercises ticks, concurrency, unasked-for responses and time order.
- `Kleppmann/ResonateCheck.lean`: Resonate as such a model, from the
  specification's handlers. `tick` sweeps every internal step the state
  makes a candidate until nothing changes. Scenarios: a promise read across
  its timeout (no tick needed: reads project), two clients whose window is
  message causality, and a lease that runs out: ticked at 50 the task is
  released and re-offered to `w`; not ticked, it is still held.

`lake build` fetches the specification and checks everything.
