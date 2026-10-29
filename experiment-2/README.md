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
- `Exp2/ProofExamples.lean`: semantic witnesses for `safe`, `queued`, and
  `ghost` (a failed write that landed).
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
  `lateCas` is a counterexample even with conditional writes: a create
  computes its default timeout before a later read, but commits after it.

No spawn, so a node serves one request at a time. The handler embedding is
proved, as are three end-to-end examples. The general storage-node property
`Refines cfg` is false for the current protocol: conditional writes serialize
document changes, but they do not serialize the instant read by a handler.
A general proof needs either a protocol fix or a restriction to operations
whose outcome is stable from document read through commit.

`lake build` builds experiment 1 too (a path dependency).
