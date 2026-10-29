import Exp2.Node

/-!
# End-to-end refinement witnesses

These are semantic proofs, not calls to the unproved trace checker.  Each
concrete client trace is paired with an explicit schedule of the abstract
promise service; `schedule_legal` proves the schedule is a legal execution.

They exercise characteristic successful executions. They do not imply the
general property, which `lateCas` refutes.
-/

namespace Exp2

open Experiment

def safeAbstractSchedule : List (Time × Act Msg) :=
  [(0, .request "c" (.req 1 (.create "p" (some 100)))),
   (0, .deliver 0 0),
   (0, .deliver 0),
   (1, .request "a" (.req 2 (.settle "p" .resolved "x"))),
   (1, .request "b" (.req 3 (.settle "p" .rejected "y"))),
   (1, .deliver 0 0),
   (1, .deliver 0 0),
   (2, .deliver 0),
   (2, .deliver 0)]

def safeAbstract : Execution promises :=
  (schedule promises { unreliable := true } {} safeAbstractSchedule).getD []

theorem safeAbstract_runs :
    schedule promises { unreliable := true } {} safeAbstractSchedule = some safeAbstract := by
  rfl

/-- The conditional-write race has a legal abstract execution with exactly
the client trace produced by the process implementation. -/
theorem safe_valid :
    Valid promises { unreliable := true } {} (clientTrace safe) := by
  apply valid_of_schedule safeAbstract_runs
  native_decide

def queuedAbstractSchedule : List (Time × Act Msg) :=
  [(0, .request "a" (.req 1 (.create "p" (some 100)))),
   (0, .request "b" (.req 2 (.get "p"))),
   (0, .deliver 0 0),
   (0, .deliver 0 0),
   (0, .deliver 0),
   (0, .deliver 0)]

def queuedAbstract : Execution promises :=
  (schedule promises { unreliable := true } {} queuedAbstractSchedule).getD []

theorem queuedAbstract_runs :
    schedule promises { unreliable := true } {} queuedAbstractSchedule = some queuedAbstract := by
  rfl

/-- A request buffered in the process mailbox also has exactly the client
trace of a legal abstract execution. -/
theorem queued_valid :
    Valid promises { unreliable := true } {} (clientTrace queued) := by
  apply valid_of_schedule queuedAbstract_runs
  native_decide

/-! A write may land even though the store reports failure.  The concrete
node answers 503; the abstract unreliable service explains the same trace with
its `lose` outcome. -/

def ghost := (drive { flaky := true }
  ([(0, .send "a" "n1" (.req 1 (.create "p" (some 100)))), (0, .move "a" "n1"),
    (0, .move "n1" "s3"), (0, .move "s3" "n1"), (0, .move "n1" "s3" 1),
    (0, .move "s3" "n1"), (0, .move "n1" "a")] ++
   [(1, .send "b" "n2" (.req 2 (.get "p"))), (1, .move "b" "n2"),
    (1, .move "n2" "s3"), (1, .move "s3" "n2"), (1, .move "n2" "b")])).getD []

def ghostAbstractSchedule : List (Time × Act Msg) :=
  [(0, .request "a" (.req 1 (.create "p" (some 100)))),
   (0, .deliver 0 2),
   (0, .deliver 0),
   (1, .request "b" (.req 2 (.get "p"))),
   (1, .deliver 0 0),
   (1, .deliver 0)]

def ghostAbstract : Execution promises :=
  (schedule promises { unreliable := true } {} ghostAbstractSchedule).getD []

theorem ghostAbstract_runs :
    schedule promises { unreliable := true } {} ghostAbstractSchedule = some ghostAbstract := by
  rfl

theorem ghost_valid :
    Valid promises { unreliable := true } {} (clientTrace ghost) := by
  apply valid_of_schedule ghostAbstract_runs
  native_decide

end Exp2
