import Resonate.Abstract

/-!
# Executable checking for the full Resonate boundary protocol

Certificates use only legal Rover actions. Internal work is hidden behind a
timeout at the sole service process; no internal request can be supplied by
the environment. Observations consume the ordered Writer emissions that the
service placed directly in the network. Successful search results are
independently replayed before `valid` is returned. Resource exhaustion is
conservatively `unknown`.
-/

namespace Resonate.TraceChecker

open Rover

abbrev AModel := Abstract.model

inductive Action where
  | inject (time : Time) (call : Call)
  | external (time : Time) (call : Call)
  | timeout (time : Time)
  | observe (time : Time) (output : Output)
  deriving Repr

abbrev Certificate := List Action

def outputEvent (time : Time) : Output → BoundaryEvent
  | .response client id response => .response time client id response
  | .message entry => .message time entry

def eventTime : BoundaryEvent → Time
  | .request time _ => time
  | .response time _ _ _ => time
  | .message time _ => time

def monotoneFrom : Time → List BoundaryEvent → Bool
  | _, [] => true
  | previous, event :: rest =>
      decide (previous ≤ eventTime event) &&
        monotoneFrom (eventTime event) rest

def monotoneTimes (events : List BoundaryEvent) : Bool :=
  monotoneFrom 0 events

theorem monotoneFrom_weaken {earlier later : Time}
    (h : earlier ≤ later) {events : List BoundaryEvent}
    (hm : monotoneFrom later events = true) :
    monotoneFrom earlier events = true := by
  induction events generalizing earlier later with
  | nil => rfl
  | cons event rest ih =>
      simp only [monotoneFrom, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
      exact ⟨Nat.le_trans h hm.1, hm.2⟩

theorem legal_boundary_times (config : Config) (world : World AModel)
    (execution : Execution AModel)
    (h : Legal AModel config world execution) :
    monotoneFrom world.now (Abstract.boundaryTrace execution) = true := by
  induction execution generalizing world with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨hstep, hrest⟩ := h
      have htail := ih next hrest
      cases hstep with
      | inject htime hprocess hinjectable =>
          obtain ⟨call, rfl⟩ := hinjectable
          simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
            Abstract.boundaryEvent, Message.observeInput, monotoneFrom,
            eventTime, World.inject] using And.intro htime htail
      | process htime hprocess hevent hresult =>
          apply monotoneFrom_weaken htime
          simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
            World.land] using htail
      | outside htime hmessage =>
          rename_i sender time message
          cases message with
          | request call =>
              apply monotoneFrom_weaken htime
              simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                Abstract.boundaryEvent, Message.observeOutput,
                World.observeOutside] using htail
          | output output =>
              cases output with
              | response client id response =>
                  simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                    Abstract.boundaryEvent, Message.observeOutput,
                    monotoneFrom, eventTime, World.observeOutside] using
                      And.intro htime htail
              | message entry =>
                  simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                    Abstract.boundaryEvent, Message.observeOutput,
                    monotoneFrom, eventTime, World.observeOutside] using
                      And.intro htime htail

theorem valid_boundary_times {config : Config}
    {events : List BoundaryEvent}
    (h : Abstract.ValidBoundaryTrace config events) :
    monotoneTimes events = true := by
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := h
  subst events
  exact legal_boundary_times config
    (World.initial process) execution hlegal

def actionStep (config : Config) (world : World AModel) (action : Action) :
    Option (Label AModel × World AModel) :=
  match action with
  | .inject time call =>
      if world.now ≤ time then
        let label : Label AModel := .input .service time (.request call)
        some (label, world.inject .service (.request call) time)
      else none
  | .external time call =>
      if world.now ≤ time then
        if (Abstract.Pid.outside, Abstract.Pid.service,
            Message.request call) ∈ world.network then
          let (nextState, outputs) :=
            Resonate.run config call (world.process .service)
          let result : Result Abstract.Pid State Message := {
            state := nextState
            send := Abstract.sends outputs
          }
          let label : Label AModel :=
            .process .service time
              (.receive .outside (.request call)) result.send
          some (label, world.land .service time result)
        else none
      else none
  | .timeout time =>
      if world.now ≤ time then
        let (nextState, outputs) :=
          Resonate.runTimeout config time (world.process .service)
        let result : Result Abstract.Pid State Message := {
          state := nextState
          send := Abstract.sends outputs
        }
        let label : Label AModel :=
          .process .service time .timeout result.send
        some (label, world.land .service time result)
      else none
  | .observe time output =>
      if world.now ≤ time then
        if (Abstract.Pid.service, Abstract.Pid.outside,
            Message.output output) ∈ world.network then
          some (.outside .service time (.output output),
            world.observeOutside time)
        else none
      else none

theorem actionStep_sound {config : Config} {world : World AModel}
    {action : Action} {label : Label AModel} {next : World AModel}
    (h : actionStep config world action = some (label, next)) :
    Step AModel config world label next := by
  cases action with
  | inject time call =>
      simp only [actionStep] at h
      split at h
      next htime =>
        cases h
        exact Step.inject htime rfl ⟨call, rfl⟩
      next _ => contradiction
  | external time call =>
      simp only [actionStep] at h
      split at h
      next htime =>
        split at h
        next hrequest =>
          cases h
          refine Step.process
            (event := .receive Abstract.Pid.outside (Message.request call))
            (result := {
              state := (Resonate.run config call
                (world.process .service)).1
              send := Abstract.sends
                (Resonate.run config call (world.process .service)).2
            })
            htime rfl ?_ ?_
          · exact hrequest
          simp [Abstract.step, Outcomes.one]
        next _ => contradiction
      next _ => contradiction
  | timeout time =>
      simp only [actionStep] at h
      split at h
      next htime =>
        cases h
        refine Step.process
          (event := .timeout)
          (result := {
            state := (Resonate.runTimeout config time
              (world.process .service)).1
            send := Abstract.sends
              (Resonate.runTimeout config time
                (world.process .service)).2
          })
          htime rfl ?_ ?_
        · simp [Event.Valid]
        simp [Abstract.step, Outcomes.one]
      next _ => contradiction
  | observe time output =>
      simp only [actionStep] at h
      split at h
      next htime =>
        split at h
        next houtput =>
          cases h
          exact Step.outside htime houtput
        next _ => contradiction
      next _ => contradiction

def replayFrom (config : Config) :
    World AModel → Certificate → Option (Execution AModel)
  | _, [] => some []
  | world, action :: rest =>
      match actionStep config world action with
      | none => none
      | some (label, next) =>
          match replayFrom config next rest with
          | none => none
          | some execution => some ((label, next) :: execution)

def replay (config : Config) (events : List BoundaryEvent)
    (certificate : Certificate) : Option (Execution AModel) :=
  match replayFrom config (World.initial Abstract.initialProcess) certificate with
  | none => none
  | some execution =>
      if Abstract.boundaryTrace execution = events then some execution else none

theorem replayFrom_sound (config : Config) (world : World AModel)
    (certificate : Certificate) (execution : Execution AModel)
    (h : replayFrom config world certificate = some execution) :
    Legal AModel config world execution := by
  induction certificate generalizing world execution with
  | nil =>
      simp only [replayFrom, Option.some.injEq] at h
      subst execution
      trivial
  | cons action rest ih =>
      simp only [replayFrom] at h
      cases hs : actionStep config world action with
      | none => simp [hs] at h
      | some entry =>
          obtain ⟨label, next⟩ := entry
          simp only [hs] at h
          cases ht : replayFrom config next rest with
          | none => simp [ht] at h
          | some tail =>
              simp only [ht, Option.some.injEq] at h
              subst execution
              exact ⟨actionStep_sound hs, ih next tail ht⟩

theorem replay_sound {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : replay config events certificate = some execution) :
    Behavior AModel config execution ∧
      Abstract.boundaryTrace execution = events := by
  simp only [replay] at h
  cases hr : replayFrom config (World.initial Abstract.initialProcess)
      certificate with
  | none => simp [hr] at h
  | some replayed =>
      simp only [hr] at h
      split at h
      next htrace =>
        simp only [Option.some.injEq] at h
        subst execution
        exact ⟨
          ⟨Abstract.initialProcess, Abstract.initialProcess_valid config,
            replayFrom_sound config _ certificate replayed hr⟩,
          htrace⟩
      next _ => contradiction

theorem replay_valid {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : replay config events certificate = some execution) :
    Abstract.ValidBoundaryTrace config events := by
  obtain ⟨behavior, trace⟩ := replay_sound h
  exact ⟨execution, behavior, trace⟩

structure SearchContext where
  world : World AModel
  certificate : Certificate

def processActions (world : World AModel) (time : Time) : List Action :=
  (world.network.filterMap fun (sender, recipient, message) =>
    match sender, recipient, message with
    | .outside, .service, .request call => some (.external time call)
    | _, _, _ => none) ++ [.timeout time]

def observeActions (world : World AModel) (time : Time)
    (event : BoundaryEvent) : List Action :=
  world.network.filterMap fun (sender, recipient, message) =>
    match sender, recipient, message with
    | .service, .outside, .output output =>
        if outputEvent time output = event then some (.observe time output)
        else none
    | _, _, _ => none

def advance (config : Config) (context : SearchContext) (action : Action) :
    Option SearchContext :=
  match actionStep config context.world action with
  | none => none
  | some (_, next) =>
      some { world := next,
             certificate := context.certificate ++ [action] }

inductive BranchResult where
  | valid (certificate : Certificate)
  | unknown

def explore (values : List α) (f : α → BranchResult) : BranchResult :=
  match values with
  | [] => .unknown
  | value :: rest =>
      match f value with
      | .valid certificate => .valid certificate
      | .unknown => explore rest f

def searchFrom (config : Config) :
    Nat → SearchContext → List BoundaryEvent → BranchResult
  | _, context, [] => .valid context.certificate
  | 0, _, _ => .unknown
  | fuel + 1, context, (.request time call) :: rest =>
      match advance config context (.inject time call) with
      | none => .unknown
      | some next => searchFrom config fuel next rest
  | fuel + 1, context, events@(event :: rest) =>
      let time := eventTime event
      let observations :=
        (observeActions context.world time event).map fun action =>
          (action, true)
      let processing :=
        (processActions context.world time).map fun action => (action, false)
      explore (observations ++ processing) fun (action, consumed) =>
        match advance config context action with
        | none => .unknown
        | some next =>
            searchFrom config fuel next (if consumed then rest else events)

def search (config : Config) (bound : Nat) (events : List BoundaryEvent) :
    BranchResult :=
  searchFrom config bound
    { world := World.initial Abstract.initialProcess, certificate := [] }
    events

inductive Verdict where
  | valid (certificate : Certificate) (execution : Execution AModel)
  | invalid
  | unknown

def Verdict.isValid : Verdict → Bool
  | .valid _ _ => true
  | _ => false

def Verdict.isInvalid : Verdict → Bool
  | .invalid => true
  | _ => false

def Verdict.isUnknown : Verdict → Bool
  | .unknown => true
  | _ => false

def checkWithBound (bound : Nat) (config : Config)
    (events : List BoundaryEvent) : Verdict :=
  if monotoneTimes events then
    match search config bound events with
    | .valid certificate =>
        match replay config events certificate with
        | some execution => .valid certificate execution
        | none => .unknown
    | .unknown => .unknown
  else
    .invalid

def defaultBound (events : List BoundaryEvent) : Nat :=
  events.length * 6 + 1

def check (config : Config) (events : List BoundaryEvent) : Verdict :=
  checkWithBound (defaultBound events) config events

theorem checkWithBound_nonmonotone {bound : Nat} {config : Config}
    {events : List BoundaryEvent}
    (h : monotoneTimes events = false) :
    checkWithBound bound config events = .invalid := by
  simp [checkWithBound, h]

theorem check_nonmonotone {config : Config}
    {events : List BoundaryEvent}
    (h : monotoneTimes events = false) :
    check config events = .invalid :=
  checkWithBound_nonmonotone h

theorem checkWithBound_valid_sound {bound : Nat} {config : Config}
    {events : List BoundaryEvent} {certificate : Certificate}
    {execution : Execution AModel}
    (h : checkWithBound bound config events =
      .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events := by
  simp only [checkWithBound] at h
  split at h
  next _ =>
    cases hs : search config bound events with
    | unknown => simp [hs] at h
    | valid found =>
        simp only [hs] at h
        cases hr : replay config events found with
        | none => simp [hr] at h
        | some replayed =>
            simp only [hr] at h
            cases h
            exact replay_valid hr
  next _ => contradiction

theorem check_valid_sound {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : check config events = .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events :=
  checkWithBound_valid_sound h

theorem checkWithBound_invalid_sound {bound : Nat} {config : Config}
    {events : List BoundaryEvent}
    (h : checkWithBound bound config events = .invalid) :
    ¬ Abstract.ValidBoundaryTrace config events := by
  intro hvalid
  have hmono := valid_boundary_times hvalid
  cases hs : search config bound events with
  | unknown => simp [checkWithBound, hmono, hs] at h
  | valid certificate =>
      cases hr : replay config events certificate with
      | none => simp [checkWithBound, hmono, hs, hr] at h
      | some execution => simp [checkWithBound, hmono, hs, hr] at h

theorem check_invalid_sound {config : Config} {events : List BoundaryEvent}
    (h : check config events = .invalid) :
    ¬ Abstract.ValidBoundaryTrace config events :=
  checkWithBound_invalid_sound h

end Resonate.TraceChecker
