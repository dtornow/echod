import Exp2.Node

/-!
# End-to-end refinement witnesses

These are semantic proofs, not calls to the unproved trace checker.  Each
concrete client trace is paired with an explicit schedule of the abstract
promise service; `schedule_legal` proves the schedule is a legal execution.

They exercise the two characteristic examples while the general simulation
relation from `Experiment.NetworkRefinement` is instantiated for this system.
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

end Exp2
