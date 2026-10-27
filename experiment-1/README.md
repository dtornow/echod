# Experiment 1: handlers in a reader–state–writer monad

- `Experiment/Handler.lean`: the monad, from scratch, no transformers:
  `H E S W α := E → S → α × S × List W`. Read the configuration, update
  the state (a handler sees its own writes), emit. Time is a parameter.
- `Experiment/Promise.lean`: a slice of Resonate's promise protocol (get,
  create, settle, listen, timeouts) written that way. Everything that
  leaves is a message, a response to the requester as much as a
  notification to a listener, and both go out through one `send`; the
  writer also carries `always`/`sometimes` assertions. The top level is
  Kleppmann's step function, `receive sender msg now`, dispatching a
  request with a `match` to its handler. A scenario and a small fuzzer
  (216 runs) run under `#guard`.

`lake build` checks everything. No dependencies.
