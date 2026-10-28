# Experiment 3: a process, and a process that calls

- `Exp3/Caller.lean`: two templates. A **process** is experiment 1's
  `Service`: one step per message; the shells, the checker and the proofs
  see only processes. A **caller** may call and wait, many calls at once:
  the author names where a request waits (`Wait`, plain data) and writes
  `receive` and `resume`; `call to req w` sends under a fresh id and waits
  at `w`. `Caller.toService` turns a caller into a process; the ids, the
  waiting calls and matching a reply to its call (`replyTo`) are there,
  once. Proved for every caller built from these operations (`Keeps`):
  routing (`step_reply`, `step_other`), fresh ids (`fresh_step`), and that
  a call is resumed at most once (`once`).
- `Exp3/Node.lean`: the storage node as a caller: two waiting points,
  `loading` and `writing`, and the protocol. Proved: it keeps the
  template's bookkeeping (`node_keeps`), so no call of a node is resumed
  twice (`node_once`). The store, the messages and the abstract handlers
  are experiment 1's.
- `Exp3/Examples.lean`: the race on two nodes (refines with conditional
  writes, not without), two requests in flight on one node (the later is
  answered first), 30 fuzzed runs, each checked against the abstract
  service.

Not proved: that the node refines the abstract service. That is checked
per run, by experiment 1's search, which is itself unproved.

`lake build` builds experiment 1 too (a path dependency).
