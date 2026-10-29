import Exp2.Node
import Experiment.NetworkRefinement

/-!
# The system-level refinement statement

Unlike `eval_lift_iff`, this file speaks about complete executions.  The
concrete side is the node/store network and the abstract side is the promise
service.  Conditional writes are an explicit hypothesis: the `lost`
counterexample shows the statement is false without it.

`drive_refines_of_simulation` closes all generic semantic plumbing.  What
remains for the general theorem is the system-specific simulation invariant:
mailboxes and in-flight store operations must be related to pending abstract
requests, including writes that fail after landing.
-/

namespace Exp2

open Experiment

/-- The part of a concrete network step visible at the abstract interface. -/
def clientView : Network.Label system.Msg → Option (Experiment.Label Msg)
  | (.client a, t, .request _ (.app m)) => some (.client a, t, .request m)
  | (.client a, t, .receive _ (.app m)) => some (.client a, t, .receive .server m)
  | _ => none

theorem project_clientView (x : Network.Execution system) :
    Network.project (concrete := system) (abstract := promises) clientView x = clientTrace x := by
  induction x with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨⟨who, t, ev⟩, outs, c⟩ := step
    cases who with
    | proc a => cases ev <;> simp [Network.project, clientView, clientTrace, ih]
    | client a =>
      cases ev with
      | timeout => simp [Network.project, clientView, clientTrace, ih]
      | request to m => cases m <;> simp [Network.project, clientView, clientTrace, ih]
      | receive sender m => cases m <;> simp [Network.project, clientView, clientTrace, ih]

/-- The actual trace-inclusion property sought for experiment 2. -/
def Refines (cfg : Experiment.Storage.Config) : Prop :=
  cfg.conditional = true →
  ∀ script x, drive cfg script = some x →
    Valid promises { cfg.app with unreliable := true } {} (clientTrace x)

/-- Once the node/store simulation is supplied, every successful drive has a
legal abstract execution with exactly the same client trace. -/
theorem drive_refines_of_simulation
    {cfg : Experiment.Storage.Config}
    {rel : Network.Conf system → Experiment.Conf promises → Prop}
    (hsim : Network.Simulation cfg { cfg.app with unreliable := true } clientView rel)
    (hinit : rel (Network.initial world) (Experiment.initial {}))
    {script : List (Time × Script)} {x : Network.Execution system}
    (hdrive : drive cfg script = some x) :
    Valid promises { cfg.app with unreliable := true } {} (clientTrace x) := by
  rw [← project_clientView x]
  exact Network.refines hsim hinit (drive_legal hdrive)

end Exp2
