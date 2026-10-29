import Resonate.Abstract

/-!
# Executable checking of Resonate boundary traces

The search in this file is deliberately outside the trusted argument. It
chooses previously injected requests and hidden `Resonate.run` outcomes, then
chooses explicit outside observations from the resulting append-only network.
`replay` independently checks that certificate and constructs the
corresponding Rover execution. The soundness theorem uses only replay.
-/

namespace Resonate.TraceChecker

open Rover

/-- One abstract Rover step recorded by a trace-checking certificate. -/
inductive Action where
  | inject (time : Time) (call : Call)
  | process (time : Time) (call : Call) (state : State)
      (outputs : List Output)
  | observe (time : Time) (output : Output)
  deriving DecidableEq, Repr

abbrev Certificate := List Action
abbrev AModel := Abstract.model

def outputEvents (time : Time) : List Output → List BoundaryEvent
  | [] => []
  | .response client id response :: rest =>
      .response time client id response :: outputEvents time rest
  | .notification client record :: rest =>
      .notification time client record :: outputEvents time rest

def eventTime : BoundaryEvent → Time
  | .request time _ => time
  | .response time _ _ _ => time
  | .notification time _ _ => time

/-- Remove an exact prefix. -/
def consumePrefix [DecidableEq α] : List α → List α → Option (List α)
  | [], values => some values
  | expected :: expectedRest, actual :: actualRest =>
      if expected = actual then consumePrefix expectedRest actualRest else none
  | _ :: _, [] => none

/-- Execute and verify one certificate action from a concrete Rover world. -/
def actionStep (config : Config) (world : World AModel) (action : Action) :
    Option (Label AModel × World AModel) :=
  match action with
  | .inject time call =>
      if world.now ≤ time then
        let label : Label AModel :=
          .input .service time (.request call)
        some (label, world.inject .service (.request call) time)
      else
        none
  | .process time call state outputs =>
      if world.now ≤ time then
        if (Abstract.Pid.outside, Abstract.Pid.service,
            Message.request call) ∈ world.network then
          if (state, outputs) ∈ (Resonate.run config call
              (world.process .service)).val then
            let result : Result Abstract.Pid State Message := {
              state
              send := outputs.map fun output =>
                (Abstract.Pid.outside, Message.output output)
            }
            let label : Label AModel :=
              .process .service time
                (.receive .outside (.request call)) result.send
            some (label, world.land .service time result)
          else
            none
        else
          none
      else
        none
  | .observe time output =>
      if world.now ≤ time then
        if (Abstract.Pid.service, Abstract.Pid.outside,
            Message.output output) ∈ world.network then
          some (.outside .service time (.output output),
            world.observeOutside time)
        else
          none
      else
        none

/-- Replay all actions, returning the actual abstract Rover execution. -/
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

/-- Verified replay additionally checks the exact filtered boundary trace. -/
def replay (config : Config) (events : List BoundaryEvent)
    (certificate : Certificate) : Option (Execution AModel) :=
  match replayFrom config (World.initial Abstract.initialProcess) certificate with
  | none => none
  | some execution =>
      if Abstract.boundaryTrace execution = events then some execution else none

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
  | process time call state outputs =>
      simp only [actionStep] at h
      split at h
      next htime =>
        split at h
        next hrequest =>
          split at h
          next houtcome =>
            cases h
            refine Step.process
              (event := .receive Abstract.Pid.outside (Message.request call))
              (result := {
                state
                send := outputs.map fun output =>
                  (Abstract.Pid.outside, Message.output output)
              })
              htime rfl ?_ ?_
            · exact hrequest
            simp only [Abstract.step]
            exact List.mem_map.mpr ⟨(state, outputs), houtcome, rfl⟩
          next _ => contradiction
        next _ => contradiction
      next _ => contradiction
  | observe time output =>
      simp only [actionStep] at h
      split at h
      next htime =>
        split at h
        next hmessage =>
          cases h
          exact Step.outside htime hmessage
        next _ => contradiction
      next _ => contradiction

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
      | none =>
          simp [hs] at h
      | some entry =>
          obtain ⟨label, next⟩ := entry
          simp only [hs] at h
          cases ht : replayFrom config next rest with
          | none =>
              simp [ht] at h
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
  | none =>
      simp [hr] at h
  | some replayed =>
      simp only [hr] at h
      split at h
      next htrace =>
        simp only [Option.some.injEq] at h
        subst execution
        exact ⟨
          ⟨Abstract.initialProcess,
            Abstract.initialProcess_valid config,
            replayFrom_sound config _ certificate replayed hr⟩,
          htrace⟩
      next _ =>
        contradiction

theorem replay_valid {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : replay config events certificate = some execution) :
    Abstract.ValidBoundaryTrace config events := by
  obtain ⟨hbehavior, htrace⟩ := replay_sound h
  exact ⟨execution, hbehavior, htrace⟩

structure SearchContext where
  state : State
  calls : List Call
  available : List Output
  now : Time
  certificate : Certificate

def outputEvent (time : Time) : Output → BoundaryEvent
  | .response client id response => .response time client id response
  | .notification client record => .notification time client record

def observeCandidates (context : SearchContext)
    (events : List BoundaryEvent) :
    List (SearchContext × List BoundaryEvent) :=
  match events with
  | [] => []
  | event :: rest =>
      let time := eventTime event
      if context.now ≤ time then
        context.available.filterMap fun output =>
          if outputEvent time output = event then
            some ({
              context with
              now := time
              certificate := context.certificate ++ [.observe time output]
            }, rest)
          else none
      else []

/-- Hidden abstract processing. It consumes fuel but no boundary event; any
generated output may be observed later, in any order, or not at all. -/
def processCandidates (config : Config) (context : SearchContext)
    (time : Time) : List SearchContext :=
  if context.now ≤ time then
    context.calls.flatMap fun call =>
      (Resonate.run config call context.state).val.map fun outcome =>
        let state := outcome.1
        let outputs := outcome.2
        {
          state
          calls := context.calls
          available := context.available ++ outputs
          now := time
          certificate := context.certificate ++
            [.process time call state outputs]
        }
  else
    []

def firstSome (values : List α) (f : α → Option β) : Option β :=
  match values with
  | [] => none
  | value :: rest =>
      match f value with
      | some result => some result
      | none => firstSome rest f

/-- Bounded depth-first search. Every recursive step consumes a visible event. -/
def searchFrom (config : Config) :
    Nat → SearchContext → List BoundaryEvent → Option Certificate
  | 0, context, events =>
      if events.isEmpty then some context.certificate else none
  | _ + 1, context, [] => some context.certificate
  | fuel + 1, context, (.request time call) :: rest =>
      if context.now ≤ time then
        searchFrom config fuel {
          state := context.state
          calls := context.calls ++ [call]
          available := context.available
          now := time
          certificate := context.certificate ++ [.inject time call]
        } rest
      else
        none
  | fuel + 1, context, events@(.response _ _ _ _ :: _) =>
      match firstSome (observeCandidates context events) fun candidate =>
          searchFrom config fuel candidate.1 candidate.2 with
      | some certificate => some certificate
      | none =>
          let time := events.head?.map eventTime |>.getD context.now
          firstSome (processCandidates config context time) fun candidate =>
            searchFrom config fuel candidate events
  | fuel + 1, context, events@(.notification _ _ _ :: _) =>
      match firstSome (observeCandidates context events) fun candidate =>
          searchFrom config fuel candidate.1 candidate.2 with
      | some certificate => some certificate
      | none =>
          let time := events.head?.map eventTime |>.getD context.now
          firstSome (processCandidates config context time) fun candidate =>
            searchFrom config fuel candidate events

/-- Search for a candidate certificate. This function is not trusted. -/
def search (config : Config) (events : List BoundaryEvent) :
    Option Certificate :=
  searchFrom config (events.length * 3 + 1) {
    state := {}
    calls := []
    available := []
    now := 0
    certificate := []
  } events

/-- Search and then independently replay. `some` is the acceptance result. -/
def check (config : Config) (events : List BoundaryEvent) :
    Option (Certificate × Execution AModel) :=
  match search config events with
  | none => none
  | some certificate =>
      match replay config events certificate with
      | none => none
      | some execution => some (certificate, execution)

theorem check_sound {config : Config} {events : List BoundaryEvent}
    {result : Certificate × Execution AModel}
    (h : check config events = some result) :
    Abstract.ValidBoundaryTrace config events := by
  simp only [check] at h
  cases hs : search config events with
  | none =>
      simp [hs] at h
  | some certificate =>
      simp only [hs] at h
      cases hr : replay config events certificate with
      | none =>
          simp [hr] at h
      | some execution =>
          simp only [hr, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact replay_valid hr

/-! ## Executable examples -/

def createCall : Call := {
  client := "client-a"
  id := 1
  requestedAt := 0
  request := .create "promise-a" (some 10)
}

def createResponse : Response := {
  status := 200
  promise := some {
    id := "promise-a"
    state := .pending
    value := ""
    timeoutAt := 10
  }
}

def createTrace : List BoundaryEvent := [
  .request 0 createCall,
  .response 1 "client-a" 1 createResponse
]

#guard (check {} createTrace).isSome

def wrongCreateTrace : List BoundaryEvent := [
  .request 0 createCall,
  .response 1 "client-a" 1 { status := 404 }
]

#guard !(check {} wrongCreateTrace).isSome

def getCall : Call := {
  client := "client-b"
  id := 2
  requestedAt := 0
  request := .get "promise-a"
}

/-- The overlapping get is processed before the earlier-injected create. -/
def overlappingTrace : List BoundaryEvent := [
  .request 0 createCall,
  .request 0 getCall,
  .response 1 "client-b" 2 { status := 404 },
  .response 2 "client-a" 1 createResponse
]

#guard (check {} overlappingTrace).isSome

/-- Hidden processing can follow dependency order while outside observations
follow reversed acknowledgement order. -/
def settleCall : Call := {
  client := "client-c"
  id := 3
  requestedAt := 0
  request := .settle "promise-a" .resolved "done"
}

def settledResponse : Response := {
  status := 200
  promise := some {
    id := "promise-a"
    state := .resolved
    value := "done"
    timeoutAt := 10
  }
}

def reversedObservationTrace : List BoundaryEvent := [
  .request 0 createCall,
  .request 0 settleCall,
  .response 1 "client-c" 3 settledResponse,
  .response 2 "client-a" 1 createResponse
]

#guard (check {} reversedObservationTrace).isSome

/-- Boundary time cannot go backwards. -/
def nonmonotoneTrace : List BoundaryEvent := [
  .request 2 createCall,
  .response 1 "client-a" 1 createResponse
]

#guard !(check {} nonmonotoneTrace).isSome

end Resonate.TraceChecker
