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
- `Exp2/Node.lean`: experiment 1's storage node rewritten as code: take a
  request, ask the store, wait, decide with the abstract handler, write
  conditionally, wait, answer; retry on a lost race. The flight table and
  its phases are gone: they are where the code waits. Requests that
  arrive meanwhile wait in the mailbox. The store, messages and abstract
  handlers are experiment 1's. Checked as there: the race on two nodes
  refines with conditional writes and not without, a request queued
  behind another is served after it, 30 fuzzed runs refine.

No spawn, so a node serves one request at a time. Nothing is proved.

`lake build` builds experiment 1 too (a path dependency).
