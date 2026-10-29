# Experiment 1: one set of handlers, several shells

- `Experiment/Handler.lean`: the handler monad, from scratch, no
  transformers: `H E S W α := E → S → Some (α × S × List W)`. Read the
  configuration, update the state (a handler sees its own writes), emit
  messages and `always`/`sometimes` assertions, and `choose` where the
  specification allows more than one behavior. `Some` is a nonempty list,
  so every handler has at least one outcome by its type. Time is a
  parameter.
- `Experiment/Service.lean`: the contract. A service is a configuration,
  a state, a message type, and two handlers: `receive sender msg now` and
  `tick now`. A shell runs a service; the handlers never know which.
- `Experiment/Sequential.lean`: shell 1. The service alone: inputs one at
  a time, outputs collected. `SeqRun` is the relation, `runs` computes
  every run.
- `Experiment/Concurrent.lean`: shell 2. Kleppmann's world: a server,
  clients, a network, any interleaving, received at most once. Proved for
  every service:
  - `server_seq`: in any execution, the server's inputs in the order it
    took them are a sequential run that sends exactly what it sent;
  - `request_before`: the server only takes a request its client sent
    before; `answer_before`: a client only receives what the server sent
    it before.
- `Experiment/Fuzz.lean`: shell 3. The concurrent world driven by a seed;
  collects what the handlers asserted.
- `Experiment/Promise.lean`: a slice of Resonate's promise protocol
  written as handlers. A response and a notification are both messages,
  sent the same way; the top level dispatches a request by `match`; with
  `unreliable`, any request may be answered 503, done or not (a `choose`).
- `Experiment/Examples.lean`: the promise service in all three shells:
  a sequential scenario, a concurrent race in which a read overtakes a
  create, and 200 fuzzed runs in each of which the sequential shell
  explains the server.

- `Experiment/Network.lean`: shell 4, many processes, one service, each
  with its own state. Its executable step relation and legal executions are
  defined, and every returned schedule is proved legal.
- `Experiment/NetworkRefinement.lean`: forward simulation from that network
  shell to the single-service shell implies trace inclusion.
- `Experiment/Check.lean`: a search: could this trace of the concurrent
  shell have happened? Executable, unproved.
- `Experiment/Storage.lean`: a simplified echod. Nodes keep nothing; every
  promise is a document in a store process, under a version. A node loads,
  runs the abstract handler, writes conditionally, retries on a lost race,
  answers after the write lands, 503 when the store cannot say. Refinement
  is checked per run: the clients' trace against the abstract service.
- `Experiment/StorageExamples.lean`: two nodes and a store. Two settles
  racing: with conditional writes the second sees the first (refines);
  without, both win (does not refine). A write that fails having landed
  (refines: the abstract 503 may have been done).

Proved: the theorems in `Concurrent.lean`. Everything about storage is
checked by running it, not proved.

`lake build` checks everything. No dependencies, no `sorry`.
