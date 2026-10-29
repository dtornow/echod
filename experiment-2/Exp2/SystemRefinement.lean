import Exp2.Node
import Experiment.NetworkRefinement

/-!
# The system-level refinement statement

Unlike `eval_lift_iff`, this file speaks about complete executions.  The
concrete side is the node/store network and the abstract side is the promise
service. Conditional writes are necessary: the `lost` counterexample shows
the statement is false without them. Request time is carried in `Msg.req` and
is kept through retries, independently of the later CAS instant.

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

/-- Client actions available through `Script.send` are application messages,
never forged node/store protocol replies. -/
def DriveSafe : Network.Label system.Msg → Prop
  | (.client _, _, .request _ (.app _)) => True
  | (.client _, _, .request _ _) => False
  | _ => True

theorem script_take_safe {c c' : Network.Conf system} {cfg : Experiment.Storage.Config}
    {t : Time} {s : Script} {act : Network.Act system.Msg}
    {l : Network.Label system.Msg} {outs : List (Out system.Msg)}
    (ha : s.act? c = some act) (ht : c.take cfg t act = some (l, outs, c')) :
    DriveSafe l := by
  cases s with
  | send a to m =>
    simp only [Script.act?] at ha
    simp only [Option.some.injEq] at ha
    subst act
    simp only [Network.Conf.take] at ht
    split at ht
    · simp only [Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl, rfl⟩ := ht
      trivial
    · simp at ht
  | move from_ to j =>
    simp only [Script.act?] at ha
    obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp ha
    simp only [Network.Conf.take] at ht
    split at ht <;> try simp at ht
    split at ht <;> try simp at ht
    · obtain ⟨rfl, rfl, rfl⟩ := ht
      trivial
    · obtain ⟨a, b, _, rfl, rfl, rfl⟩ := ht
      trivial

theorem driveFrom_admitted {cfg : Experiment.Storage.Config} {c : Network.Conf system}
    {script : List (Time × Script)} {x : Network.Execution system}
    (h : driveFrom cfg c script = some x) : Network.Admitted DriveSafe x := by
  induction script generalizing c x with
  | nil =>
    simp [driveFrom] at h
    subst h
    trivial
  | cons ts rest ih =>
    obtain ⟨t, s⟩ := ts
    simp only [driveFrom] at h
    obtain ⟨act, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨l, outs, c'⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    change some ((l, outs, c') :: xs) = some x at h
    simp only [Option.some.injEq] at h
    subst x
    exact ⟨script_take_safe ha ht, ih hxs⟩

theorem drive_admitted {cfg : Experiment.Storage.Config}
    {script : List (Time × Script)} {x : Network.Execution system}
    (h : drive cfg script = some x) : Network.Admitted DriveSafe x :=
  driveFrom_admitted h

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

/-- The trace-inclusion property sought for experiment 2. -/
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

/-- The useful form for `drive`: only application requests need simulation. -/
theorem drive_refines_of_simulationOn
    {cfg : Experiment.Storage.Config}
    {rel : Network.Conf system → Experiment.Conf promises → Prop}
    (hsim : Network.SimulationOn cfg { cfg.app with unreliable := true }
      clientView DriveSafe rel)
    (hinit : rel (Network.initial world) (Experiment.initial {}))
    {script : List (Time × Script)} {x : Network.Execution system}
    (hdrive : drive cfg script = some x) :
    Valid promises { cfg.app with unreliable := true } {} (clientTrace x) := by
  rw [← project_clientView x]
  exact Network.refinesOn hsim hinit (drive_legal hdrive) (drive_admitted hdrive)

end Exp2
