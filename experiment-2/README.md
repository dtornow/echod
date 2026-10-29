# Experiment 2: processes as code, after Lynx

[josevalim/lynx](https://github.com/josevalim/lynx) models an Erlang
process as a resumable computation: an inductive whose constructors are the
process's requests to the runtime (`get`, `set`, `send`, selective
`receive`, `schedule` for spawn), each holding its continuation, run by a
scheduler. This experiment takes that shape and plugs it into experiment
1's world.

- `Exp2/Proc.lean`: `Proc E S M α`, a process as code: `ask`, `load`,
  `store`, `emit` (our handler monad's read, get, set, emit), `choose`
  (the specification's nondeterminism, which Lynx does not have), and
  selective `receive`, which also hands over the instant. `Proc.lift`
  runs a handler of the first monad inside a process. `toStep` turns a
  process into a step function: a message joins the mailbox, the code
  runs from where it was blocked until it blocks again, and starts over
  when it ends, as an Erlang server loop. A process's state is its data,
  its mailbox, and its continuation.
- `Exp2/Refinement.lean`: the proof that the common fragment refines
  experiment 1. A terminating evaluation relation for processes records
  results, state, and outputs. `eval_lift_iff` proves that `Proc.lift`
  introduces no handler outcome and loses none.
- `Exp2/SystemRefinement.lean`: the end-to-end statement and the generic
  trace-inclusion theorem specialized to this system. `clientView` is the
  client projection, and `drive_refines_of_simulation` proves a driven run
  valid once the node/store simulation relation is supplied.
- `Exp2/StorageSimulation.lean`: the system-specific core: canonical node
  control states, key-extensional store representation, local-to-global
  handler transport, and proved abstract linearization steps for unchanged
  reads, successful CAS writes, and writes that land but report failure.
  `storage_simulationOn` proves every driven transition is simulated;
  `system_refines` proves `Refines cfg` for every configuration.
- `Exp2/ProofExamples.lean`: semantic witnesses for `safe`, `queued`,
  `ghost` (a failed write that landed), and `delayedCas`.
  These do not trust the executable checker: each gives an explicit abstract
  schedule and proves it legal with exactly the concrete client trace.
- `Exp2/Node.lean`: experiment 1's storage node rewritten as code: take a
  request, ask the store, wait, decide with the abstract handler, write
  conditionally, wait, answer; retry on a lost race. The flight table and
  its phases are gone: they are where the code waits. Requests that
  arrive meanwhile wait in the mailbox. The store, messages and abstract
  handlers are experiment 1's. Checked as there: the race on two nodes
  refines with conditional writes and not without, a request queued
  behind another is served after it, and 30 fuzzed runs refine.
  `delayedCas` checks that request time survives an intervening read and a
  later CAS.

No spawn, so a node serves one request at a time. The handler embedding is
proved, as are four end-to-end examples. The general storage-node property
is `Refines cfg`; `system_refines` proves it. The property necessarily assumes
conditional writes, because `lost` is a counterexample without them.

`lake build` builds experiment 1 too (a path dependency).
