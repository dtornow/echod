import Experiment.Network

/-!
# Refinement from a network of processes to one abstract service

The concrete shell may take many internal node and store steps for every step
visible to a client.  A forward simulation therefore matches one concrete
step with a (possibly empty) abstract execution.  Its projection must be the
single translated client event, or empty for a hidden concrete step.
-/

namespace Experiment.Network

open Experiment

variable {concrete abstract : Service}

/-- Project the labels selected by `view`, forgetting all other concrete
steps.  For the storage systems, `view` keeps only application messages sent
or received by clients. -/
def project (view : Label concrete.Msg → Option (Experiment.Label abstract.Msg)) :
    Execution concrete → List (Experiment.Label abstract.Msg)
  | [] => []
  | (l, _, _) :: rest => (view l).toList ++ project view rest

/-- The configuration after an abstract execution. -/
def abstractEnd (c : Experiment.Conf abstract) :
    Experiment.Execution abstract → Experiment.Conf abstract
  | [] => c
  | (_, _, c') :: rest => abstractEnd c' rest

theorem abstractEnd_eq_endOf (c : Experiment.Conf abstract)
    (x : Experiment.Execution abstract) :
    abstractEnd c x = Experiment.endOf c x := by
  induction x generalizing c with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨l, outs, c'⟩ := step
    simpa [abstractEnd, Experiment.endOf] using ih c'

theorem abstract_legal_append {cfg : abstract.Config}
    {c : Experiment.Conf abstract} {x y : Experiment.Execution abstract}
    (hx : Experiment.Legal abstract cfg c x)
    (hy : Experiment.Legal abstract cfg (abstractEnd c x) y) :
    Experiment.Legal abstract cfg c (x ++ y) := by
  induction x generalizing c with
  | nil => exact hy
  | cons step rest ih =>
    obtain ⟨l, outs, c'⟩ := step
    exact ⟨hx.1, ih hx.2 hy⟩

theorem abstract_observe_append (x y : Experiment.Execution abstract) :
    Experiment.observe (x ++ y) = Experiment.observe x ++ Experiment.observe y := by
  induction x with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨l, outs, c⟩ := step
    simp only [List.cons_append, Experiment.observe]
    split <;> simp [ih]

theorem abstractEnd_append (c : Experiment.Conf abstract)
    (x y : Experiment.Execution abstract) :
    abstractEnd c (x ++ y) = abstractEnd (abstractEnd c x) y := by
  induction x generalizing c with
  | nil => rfl
  | cons step rest ih =>
    obtain ⟨l, outs, c'⟩ := step
    simpa [abstractEnd] using ih c'

/-- One concrete step is matched by abstract steps with the translated
observation and a related final configuration. -/
def Matches (cfg : abstract.Config) (view : Label concrete.Msg →
    Option (Experiment.Label abstract.Msg)) (c : Experiment.Conf abstract)
    (l : Label concrete.Msg) (c' : Experiment.Conf abstract) : Prop :=
  ∃ x, Experiment.Legal abstract cfg c x ∧
    Experiment.observe x = (view l).toList ∧ abstractEnd c x = c'

/-- A forward simulation from the executable multi-process shell to the
single abstract service. -/
def Simulation (ccfg : concrete.Config) (acfg : abstract.Config)
    (view : Label concrete.Msg → Option (Experiment.Label abstract.Msg))
    (rel : Conf concrete → Experiment.Conf abstract → Prop) : Prop :=
  ∀ {c l outs c' a}, rel c a → Step concrete ccfg c l outs c' →
    ∃ a', Matches acfg view a l a' ∧ rel c' a'

/-- Every concrete label in an execution is admitted by `ok`. -/
def Admitted (ok : Label concrete.Msg → Prop) : Execution concrete → Prop
  | [] => True
  | (l, _, _) :: rest => ok l ∧ Admitted ok rest

/-- A simulation restricted to the labels an actual driver can produce.
This excludes hostile client injections of a service's internal protocol
messages while retaining every process and delivery step. -/
def SimulationOn (ccfg : concrete.Config) (acfg : abstract.Config)
    (view : Label concrete.Msg → Option (Experiment.Label abstract.Msg))
    (ok : Label concrete.Msg → Prop)
    (rel : Conf concrete → Experiment.Conf abstract → Prop) : Prop :=
  ∀ {c l outs c' a}, rel c a → Step concrete ccfg c l outs c' → ok l →
    ∃ a', Matches acfg view a l a' ∧ rel c' a'

/-- A simulation matches every legal concrete execution, preserving exactly
its projected client trace. -/
theorem simulate {ccfg : concrete.Config} {acfg : abstract.Config}
    {view : Label concrete.Msg → Option (Experiment.Label abstract.Msg)}
    {rel : Conf concrete → Experiment.Conf abstract → Prop}
    (hsim : Simulation ccfg acfg view rel)
    {c : Conf concrete} {x : Execution concrete} {a : Experiment.Conf abstract}
    (hr : rel c a) (hx : Legal concrete ccfg c x) :
    ∃ ax, Experiment.Legal abstract acfg a ax ∧
      Experiment.observe ax = project view x ∧
      rel (endOf c x) (abstractEnd a ax) := by
  induction x generalizing c a with
  | nil => exact ⟨[], trivial, rfl, hr⟩
  | cons step rest ih =>
    obtain ⟨l, outs, c'⟩ := step
    obtain ⟨hstep, hrest⟩ := hx
    obtain ⟨a', ⟨mid, hmid, hobs, hend⟩, hr'⟩ := hsim hr hstep
    obtain ⟨tail, htail, htobs, htrel⟩ := ih hr' hrest
    refine ⟨mid ++ tail, abstract_legal_append hmid (hend ▸ htail), ?_, ?_⟩
    · rw [abstract_observe_append, hobs, htobs]
      rfl
    · rw [abstractEnd_append, hend]
      exact htrel

/-- The admitted-label form of `simulate`. -/
theorem simulateOn {ccfg : concrete.Config} {acfg : abstract.Config}
    {view : Label concrete.Msg → Option (Experiment.Label abstract.Msg)}
    {ok : Label concrete.Msg → Prop}
    {rel : Conf concrete → Experiment.Conf abstract → Prop}
    (hsim : SimulationOn ccfg acfg view ok rel)
    {c : Conf concrete} {x : Execution concrete} {a : Experiment.Conf abstract}
    (hr : rel c a) (hx : Legal concrete ccfg c x) (hok : Admitted ok x) :
    ∃ ax, Experiment.Legal abstract acfg a ax ∧
      Experiment.observe ax = project view x ∧
      rel (endOf c x) (abstractEnd a ax) := by
  induction x generalizing c a with
  | nil => exact ⟨[], trivial, rfl, hr⟩
  | cons step rest ih =>
    obtain ⟨l, outs, c'⟩ := step
    obtain ⟨hstep, hrest⟩ := hx
    obtain ⟨hokStep, hokRest⟩ := hok
    obtain ⟨a', ⟨mid, hmid, hobs, hend⟩, hr'⟩ := hsim hr hstep hokStep
    obtain ⟨tail, htail, htobs, htrel⟩ := ih hr' hrest hokRest
    refine ⟨mid ++ tail, abstract_legal_append hmid (hend ▸ htail), ?_, ?_⟩
    · rw [abstract_observe_append, hobs, htobs]
      rfl
    · rw [abstractEnd_append, hend]
      exact htrel

/-- Trace inclusion: a related initial pair and a forward simulation make
every legal concrete execution's client projection a valid abstract trace. -/
theorem refines {ccfg : concrete.Config} {acfg : abstract.Config}
    {view : Label concrete.Msg → Option (Experiment.Label abstract.Msg)}
    {rel : Conf concrete → Experiment.Conf abstract → Prop}
    (hsim : Simulation ccfg acfg view rel)
    {states : List (Addr × concrete.State)} {init : abstract.State}
    (hinit : rel (initial states) (Experiment.initial init))
    {x : Execution concrete} (hx : Legal concrete ccfg (initial states) x) :
    Experiment.Valid abstract acfg init (project view x) := by
  obtain ⟨ax, hlegal, hobs, _⟩ := simulate hsim hinit hx
  exact ⟨ax, hlegal, hobs⟩

/-- Trace inclusion from a simulation over the driver's admitted labels. -/
theorem refinesOn {ccfg : concrete.Config} {acfg : abstract.Config}
    {view : Label concrete.Msg → Option (Experiment.Label abstract.Msg)}
    {ok : Label concrete.Msg → Prop}
    {rel : Conf concrete → Experiment.Conf abstract → Prop}
    (hsim : SimulationOn ccfg acfg view ok rel)
    {states : List (Addr × concrete.State)} {init : abstract.State}
    (hinit : rel (initial states) (Experiment.initial init))
    {x : Execution concrete} (hx : Legal concrete ccfg (initial states) x)
    (hok : Admitted ok x) :
    Experiment.Valid abstract acfg init (project view x) := by
  obtain ⟨ax, hlegal, hobs, _⟩ := simulateOn hsim hinit hx hok
  exact ⟨ax, hlegal, hobs⟩

end Experiment.Network
