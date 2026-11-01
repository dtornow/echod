/-!
# Rover: a minimal message-passing world

Rover follows Kleppmann's model: the network is an append-only history of
messages that were sent. A process may receive any message addressed to it
that occurs in that history, any number of times and in any order. Delaying a
message means receiving it later; losing it means never receiving it.

One distinguished endpoint, `outside`, has no process state. The environment
may inject an allowed request from `outside` into the network, and may
separately observe any message addressed to `outside`. Observation does not
remove a message, so output delivery has the same delay, loss, reordering, and
duplication semantics as process delivery.
-/

namespace Rover

abbrev Time := Nat

/-- At least one possible result. -/
abbrev Outcomes (α : Type) := { values : List α // values ≠ [] }

def Outcomes.one {α : Type} (value : α) : Outcomes α :=
  ⟨[value], by simp⟩

/-- What one process receives. External requests first enter the network;
processes receive them through the same constructor as every other message. -/
inductive Event (Pid Msg : Type) where
  | receive (sender : Pid) (message : Msg)
  | timeout

/-- One possible local transition result. -/
structure Result (Pid State Msg : Type) where
  state : State
  send  : List (Pid × Msg)

/-- A protocol interpreted by the Rover world. -/
structure Model where
  Config : Type
  Pid    : Type
  State  : Type
  Msg    : Type

  decEqPid : DecidableEq Pid

  /-- The stateless endpoint representing everything outside the model. -/
  outside : Pid
  isProcess : Pid → Prop
  decIsProcess : DecidablePred isProcess
  outside_not_process : ¬ isProcess outside

  /-- Which messages the environment may inject as requests. -/
  injectable : Config → Msg → Prop
  decInjectable : ∀ config, DecidablePred (injectable config)

  /-- Allowed initial local states. The network initially contains nothing. -/
  init : Config → (Pid → State) → Prop

  /-- Local process behavior. -/
  step : Config → Pid → State → Time → Event Pid Msg →
    Outcomes (Result Pid State Msg)

/-- The whole modeled world. `process outside` is present only because the
state function is total; no transition may select `outside` as a process. -/
structure World (model : Model) where
  process : model.Pid → model.State
  network : List (model.Pid × model.Pid × model.Msg)
  now     : Time

def World.initial (process : model.Pid → model.State) : World model :=
  ⟨process, [], 0⟩

/-- A receive is possible whenever its message was sent. Messages from the
outside endpoint are injected by a separate world step, so they follow the
same rule after injection. -/
def Event.Valid (world : World model) (recipient : model.Pid) :
    Event model.Pid model.Msg → Prop
  | .receive sender message => (sender, recipient, message) ∈ world.network
  | .timeout => True

/-- Add one externally supplied request to the append-only network. -/
def World.inject (world : World model) (to : model.Pid) (message : model.Msg)
    (now : Time) : World model :=
  { world with
    network := world.network ++ [(model.outside, to, message)]
    now }

/-- Apply one local outcome and append every message it sends. -/
def World.land (world : World model) (process : model.Pid) (now : Time)
    (result : Result model.Pid model.State model.Msg) : World model :=
  letI := model.decEqPid
  { process := fun p => if p = process then result.state else world.process p
    network := world.network ++
      result.send.map fun (recipient, message) => (process, recipient, message)
    now }

/-- Observe one outside-addressed message without consuming it. -/
def World.observeOutside (world : World model) (now : Time) : World model :=
  { world with now }

/-- Labels retain exactly what happened in one world step. -/
inductive Label (model : Model) where
  | input (recipient : model.Pid) (now : Time) (message : model.Msg)
  | process (process : model.Pid) (now : Time)
      (event : Event model.Pid model.Msg)
      (send : List (model.Pid × model.Msg))
  | outside (sender : model.Pid) (now : Time) (message : model.Msg)

/-- The observable system boundary. -/
inductive BoundaryEvent (model : Model) where
  | input  (recipient : model.Pid) (now : Time) (message : model.Msg)
  | output (sender : model.Pid) (now : Time) (message : model.Msg)

/-- Inputs and explicit outside observations are visible. Process sends,
including sends addressed to outside, are hidden until separately observed. -/
def Label.observe (label : Label model) : List (BoundaryEvent model) :=
  match label with
  | .input recipient now message => [.input recipient now message]
  | .process _ _ _ _ => []
  | .outside sender now message => [.output sender now message]

/-- One atomic world transition. The network itself does not step:
injection appends one outside message; a process step validates one event,
updates that process, and appends its sends. Receive never removes a message,
which gives Kleppmann-style duplication. -/
inductive Step (model : Model) (config : model.Config) :
    World model → Label model → World model → Prop where
  | inject {world to now message} :
      world.now ≤ now →
      model.isProcess to →
      model.injectable config message →
      Step model config world (.input to now message)
        (world.inject to message now)

  | process {world process now event result} :
      world.now ≤ now →
      model.isProcess process →
      event.Valid world process →
      result ∈ (model.step config process (world.process process) now event).val →
      Step model config world
        (.process process now event result.send)
        (world.land process now result)

  | outside {world sender now message} :
      world.now ≤ now →
      (sender, model.outside, message) ∈ world.network →
      Step model config world
        (.outside sender now message)
        (world.observeOutside now)

abbrev Execution (model : Model) := List (Label model × World model)

/-- Every execution entry is a valid step from the world before it. -/
def Legal (model : Model) (config : model.Config) :
    World model → Execution model → Prop
  | _, [] => True
  | world, (label, next) :: rest =>
      Step model config world label next ∧ Legal model config next rest

def endOf (world : World model) : Execution model → World model
  | [] => world
  | (_, next) :: rest => endOf next rest

/-- Configurations reachable from some allowed initial process state. -/
inductive Reachable (model : Model) (config : model.Config) : World model → Prop where
  | init {process} :
      model.init config process →
      Reachable model config (World.initial process)
  | step {world label next} :
      Reachable model config world →
      Step model config world label next →
      Reachable model config next

/-- Standard induction principle for invariants over reachable worlds. -/
theorem Reachable.invariant {P : World model → Prop}
    (hinit : ∀ process, model.init config process → P (World.initial process))
    (hstep : ∀ {world label next},
      P world → Step model config world label next → P next)
    {world : World model} (h : Reachable model config world) : P world := by
  induction h with
  | init hi => exact hinit _ hi
  | step _ hs ih => exact hstep ih hs

/-- The boundary trace shown by an execution. -/
def trace : Execution model → List (BoundaryEvent model)
  | [] => []
  | (label, _) :: rest => label.observe ++ trace rest

/-- A complete finite behavior starts in an allowed process state and follows
only legal world transitions. -/
def Behavior (model : Model) (config : model.Config)
    (execution : Execution model) : Prop :=
  ∃ process,
    model.init config process ∧
    Legal model config (World.initial process) execution

/-- Trace checking asks whether some legal execution from an allowed initial
state shows exactly the supplied boundary trace. -/
def ValidTrace (model : Model) (config : model.Config)
    (events : List (BoundaryEvent model)) : Prop :=
  ∃ execution, Behavior model config execution ∧ trace execution = events

end Rover
