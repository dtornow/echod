import Rover

/-!
# Generic executable checking for Rover models

An action names only a Rover system move and, for a process move, an index in
the model's finite nonempty outcome list. Replay recomputes every side
condition and outcome. Search is deliberately separate from replay: adapters
may prune or omit candidates, but no candidate is accepted without replay.
-/

namespace Rover.Check

open Rover

/-- An executable event name. A receive refers to the immutable network
history by index, avoiding any equality requirement on message payloads. -/
inductive ProcessEvent where
  | receive (networkIndex : Nat)
  | timeout

/-- An executable name for each of Rover's three system transitions. -/
inductive Action (model : Model) where
  | inject (recipient : model.Pid) (now : Time) (message : model.Msg)
  | process (process : model.Pid) (now : Time)
      (event : ProcessEvent) (outcome : Nat)
  | outside (networkIndex : Nat) (now : Time)

abbrev Certificate (model : Model) := List (Action model)

/-- Recompute one named move. No legality evidence is accepted from search. -/
def actionStep (model : Model) (config : model.Config)
    (system : System model) (action : Action model) :
    Option (Label model × System model) :=
  letI : DecidableEq model.Pid := model.decEqPid
  match action with
  | .inject recipient now message =>
      letI : Decidable (model.isProcess recipient) :=
        model.decIsProcess recipient
      letI : Decidable (model.injectable config message) :=
        model.decInjectable config message
      if _htime : system.now ≤ now then
        if _hprocess : model.isProcess recipient then
          if _hinjectable : model.injectable config message then
            some (.input recipient now message,
              system.inject recipient message now)
          else none
        else none
      else none
  | .process process now .timeout outcome =>
      letI : Decidable (model.isProcess process) :=
        model.decIsProcess process
      if _htime : system.now ≤ now then
        if _hprocess : model.isProcess process then
          match (model.step config process (system.process process)
              now .timeout).val[outcome]? with
          | some result =>
              some (.process process now .timeout result.send,
                system.land process now result)
          | none => none
        else none
      else none
  | .process process now (.receive networkIndex) outcome =>
      letI : Decidable (model.isProcess process) :=
        model.decIsProcess process
      match _hnetwork : system.network[networkIndex]? with
      | none => none
      | some (sender, recipient, message) =>
          if _hrecipient : recipient = process then
            if _htime : system.now ≤ now then
              if _hprocess : model.isProcess process then
                match (model.step config process (system.process process)
                    now (.receive sender message)).val[outcome]? with
                | some result =>
                    some (.process process now (.receive sender message)
                        result.send, system.land process now result)
                | none => none
              else none
            else none
          else none
  | .outside networkIndex now =>
      match _hnetwork : system.network[networkIndex]? with
      | none => none
      | some (sender, recipient, message) =>
        if _hrecipient : recipient = model.outside then
          if _htime : system.now ≤ now then
            some (.outside sender now message, system.observeOutside now)
          else none
        else none

theorem actionStep_sound {model : Model} {config : model.Config}
    {system : System model} {action : Action model}
    {label : Label model} {next : System model}
    (h : actionStep model config system action = some (label, next)) :
    Step model config system label next := by
  letI : DecidableEq model.Pid := model.decEqPid
  cases action with
  | inject recipient now message =>
      simp only [actionStep] at h
      split at h
      next htime =>
        split at h
        next hprocess =>
          split at h
          next hinjectable =>
            cases h
            exact .inject htime hprocess hinjectable
          next _ => contradiction
        next _ => contradiction
      next _ => contradiction
  | process process now event outcome =>
      cases event with
      | timeout =>
          simp only [actionStep] at h
          split at h
          next htime =>
            split at h
            next hprocess =>
              split at h
              next result hresult =>
                cases h
                exact .process htime hprocess trivial
                  (List.mem_of_getElem? hresult)
              next _ => contradiction
            next _ => contradiction
          next _ => contradiction
      | receive networkIndex =>
          simp only [actionStep] at h
          split at h
          next _ => contradiction
          next sender recipient message hnetwork =>
            split at h
            next hrecipient =>
              subst recipient
              split at h
              next htime =>
                split at h
                next hprocess =>
                  split at h
                  next result hresult =>
                    cases h
                    exact .process htime hprocess
                      (List.mem_of_getElem? hnetwork)
                      (List.mem_of_getElem? hresult)
                  next _ => contradiction
                next _ => contradiction
              next _ => contradiction
            next _ => contradiction
  | outside networkIndex now =>
      simp only [actionStep] at h
      split at h
      next _ => contradiction
      next sender recipient message hnetwork =>
        split at h
        next hrecipient =>
          subst recipient
          split at h
          next htime =>
            cases h
            exact .outside htime (List.mem_of_getElem? hnetwork)
          next _ => contradiction
        next _ => contradiction

/-- Every semantic Rover step has a canonical executable action. Network
messages and nondeterministic outcomes are named by their list indices. -/
theorem actionStep_complete {model : Model} {config : model.Config}
    {system : System model} {label : Label model} {next : System model}
    (h : Step model config system label next) :
    ∃ action, actionStep model config system action = some (label, next) := by
  letI : DecidableEq model.Pid := model.decEqPid
  cases h with
  | inject htime hprocess hinjectable =>
      rename_i recipient now message
      exact ⟨.inject recipient now message, by
        simp [actionStep, htime, hprocess, hinjectable]⟩
  | process htime hprocess hevent hresult =>
      rename_i process now event result
      obtain ⟨outcome, houtcome⟩ := List.mem_iff_getElem?.mp hresult
      cases event with
      | timeout =>
          exact ⟨.process process now .timeout outcome, by
            simp [actionStep, htime, hprocess, houtcome]⟩
      | receive sender message =>
          obtain ⟨networkIndex, hnetwork⟩ :=
            List.mem_iff_getElem?.mp hevent
          exact ⟨.process process now (.receive networkIndex) outcome, by
            simp only [actionStep]
            rw [hnetwork]
            simp [htime, hprocess, houtcome]⟩
  | outside htime hmessage =>
      rename_i sender now message
      obtain ⟨networkIndex, hnetwork⟩ :=
        List.mem_iff_getElem?.mp hmessage
      exact ⟨.outside networkIndex now, by
        simp only [actionStep]
        rw [hnetwork]
        simp [htime]⟩

/-- Replay every action, stopping at the first illegal move. -/
def replayFrom (model : Model) (config : model.Config) :
    System model → Certificate model → Option (Trace model)
  | _, [] => some []
  | system, action :: rest =>
      match actionStep model config system action with
      | none => none
      | some (label, next) =>
          (replayFrom model config next rest).map ((label, next) :: ·)

theorem replayFrom_sound (model : Model) (config : model.Config)
    (system : System model) (certificate : Certificate model)
    (trace : Trace model)
    (h : replayFrom model config system certificate = some trace) :
    Legal model config system trace := by
  induction certificate generalizing system trace with
  | nil =>
      simp only [replayFrom, Option.some.injEq] at h
      subst trace
      trivial
  | cons action rest ih =>
      simp only [replayFrom] at h
      cases hs : actionStep model config system action with
      | none => simp [hs] at h
      | some entry =>
          obtain ⟨label, next⟩ := entry
          simp only [hs] at h
          obtain ⟨tail, htail, rfl⟩ := Option.map_eq_some_iff.mp h
          exact ⟨actionStep_sound hs, ih next tail htail⟩

/-- A protocol-independent projection of Rover boundary events. -/
structure Observation (model : Model) where
  Event : Type
  decEqEvent : DecidableEq Event
  project : BoundaryEvent model → Option Event

def Observation.executionTrace (observation : Observation model)
    (trace : Trace model) : List observation.Event :=
  (Rover.observe trace).filterMap observation.project

@[simp] theorem Observation.executionTrace_nil
    (observation : Observation model) :
    observation.executionTrace [] = [] := rfl

def Observation.labelTrace (observation : Observation model)
    (label : Label model) : List observation.Event :=
  label.observe.filterMap observation.project

def labelTime : Label model → Time
  | .input _ now _ => now
  | .process _ now _ _ => now
  | .outside _ now _ => now

def Observation.Valid (observation : Observation model)
    (config : model.Config) (events : List observation.Event) : Prop :=
  ∃ trace,
    ValidTrace model config trace ∧
    observation.executionTrace trace = events

/-- Replay and independently compare the complete projected trace. -/
def replay (observation : Observation model) (config : model.Config)
    (initial : model.Pid → model.State) (events : List observation.Event)
    (certificate : Certificate model) : Option (Trace model) :=
  letI := observation.decEqEvent
  match replayFrom model config (System.initial initial) certificate with
  | none => none
  | some trace =>
      if observation.executionTrace trace = events then
        some trace
      else none

theorem replay_sound {observation : Observation model}
    {config : model.Config} {initial : model.Pid → model.State}
    (hinit : model.init config initial)
    {events : List observation.Event} {certificate : Certificate model}
    {trace : Trace model}
    (h : replay observation config initial events certificate =
      some trace) :
    ValidTrace model config trace ∧
      observation.executionTrace trace = events := by
  letI := observation.decEqEvent
  simp only [replay] at h
  cases hr : replayFrom model config (System.initial initial) certificate with
  | none => simp [hr] at h
  | some replayed =>
      simp only [hr] at h
      split at h
      next htrace =>
        simp only [Option.some.injEq] at h
        subst trace
        exact ⟨⟨initial, hinit,
          replayFrom_sound model config _ certificate replayed hr⟩, htrace⟩
      next _ => contradiction

theorem replay_valid {observation : Observation model}
    {config : model.Config} {initial : model.Pid → model.State}
    (hinit : model.init config initial)
    {events : List observation.Event} {certificate : Certificate model}
    {trace : Trace model}
    (h : replay observation config initial events certificate =
      some trace) :
    observation.Valid config events := by
  obtain ⟨hvalid, hobserved⟩ := replay_sound hinit h
  exact ⟨trace, hvalid, hobserved⟩

/-- Executable, potentially pruned candidates for one expected observation. -/
structure Adapter (model : Model) extends Observation model where
  initial : model.Config → model.Pid → model.State
  initial_valid : ∀ config, model.init config (initial config)
  /-- Every behavior starts in the executable initial state. Models with a
  semantically irrelevant difference may instead prove equality after their
  own normalization and expose that normalized state here. -/
  initial_complete : ∀ {config process},
    model.init config process → process = initial config
  actions : model.Config → System model → Event → List (Action model)
  /-- Incomplete adapters remain useful for sound search. Completeness
  theorems require this flag to be true. -/
  complete : Bool
  /-- Finite upper bound used to normalize hidden steps before the next
  expected observation. -/
  horizon : Event → Time
  /-- Every first step of a legal suffix producing the expected next event is
  no later than that event's finite horizon. -/
  horizon_sound : complete = true →
    ∀ {config system expected remaining label next rest},
      Reachable model config system →
      Step model config system label next →
      Legal model config next rest →
      toObservation.executionTrace ((label, next) :: rest) =
        expected :: remaining →
      labelTime label ≤ horizon expected
  /-- Every relevant legal hidden or next-observation step is represented by
  a finite executable candidate. -/
  actions_complete : complete = true → ∀ {config system expected label next},
    Reachable model config system →
    Step model config system label next →
    (toObservation.labelTrace label = [] ∨
      toObservation.labelTrace label = [expected]) →
    labelTime label ≤ horizon expected →
    ∃ action ∈ actions config system expected,
      actionStep model config system action = some (label, next)
  definitiveInvalid : model.Config → List Event → Bool
  definitiveInvalid_sound : ∀ {config events},
    definitiveInvalid config events = true →
      ¬ toObservation.Valid config events
  /-- Set only when exhaustion of the finite candidates is a proof of
  invalidity. The accompanying law is kept separate because it mentions the
  search defined below. -/
  exhaustive : Bool

structure Context (model : Model) where
  system : System model
  certificate : Certificate model

inductive RawResult (model : Model) where
  | found (certificate : Certificate model)
  | exhausted
  | cutoff

/-- Prefer a witness; otherwise retain whether any branch hit its fuel bound. -/
def explore (values : List α) (f : α → RawResult model) : RawResult model :=
  match values with
  | [] => .exhausted
  | value :: rest =>
      match f value with
      | .found certificate => .found certificate
      | .exhausted => explore rest f
      | .cutoff =>
          match explore rest f with
          | .found certificate => .found certificate
          | _ => .cutoff

theorem explore_found_of_mem {values : List α} {value : α}
    {f : α → RawResult model} {certificate : Certificate model}
    (hmem : value ∈ values)
    (hfound : f value = .found certificate) :
    ∃ found, explore values f = .found found := by
  induction values with
  | nil => contradiction
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [explore]
      cases hhead : f head with
      | found found => exact ⟨found, rfl⟩
      | exhausted =>
          apply ih
          rcases hmem with rfl | hmem
          · rw [hfound] at hhead
            contradiction
          · exact hmem
      | cutoff =>
          obtain ⟨found, htail⟩ := ih (by
            rcases hmem with rfl | hmem
            · rw [hfound] at hhead
              contradiction
            · exact hmem)
          rw [htail]
          exact ⟨found, rfl⟩

theorem explore_found {values : List α} {f : α → RawResult model}
    {certificate : Certificate model}
    (h : explore values f = .found certificate) :
    ∃ value ∈ values, f value = .found certificate := by
  induction values with
  | nil => simp [explore] at h
  | cons head tail ih =>
      simp only [explore] at h
      cases hhead : f head with
      | found found =>
          simp only [hhead, RawResult.found.injEq] at h
          subst found
          exact ⟨head, List.mem_cons_self, hhead⟩
      | exhausted =>
          simp only [hhead] at h
          obtain ⟨value, hmem, hvalue⟩ := ih h
          exact ⟨value, List.mem_cons_of_mem head hmem, hvalue⟩
      | cutoff =>
          simp only [hhead] at h
          cases htail : explore tail f with
          | exhausted => simp [htail] at h
          | cutoff => simp [htail] at h
          | found found =>
              simp only [htail, RawResult.found.injEq] at h
              subst found
              obtain ⟨value, hmem, hvalue⟩ := ih htail
              exact ⟨value, List.mem_cons_of_mem head hmem, hvalue⟩

theorem explore_ne_exhausted_of_mem {values : List α} {value : α}
    {f : α → RawResult model}
    (hmem : value ∈ values) (hne : f value ≠ .exhausted) :
    explore values f ≠ .exhausted := by
  induction values with
  | nil => contradiction
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      simp only [explore]
      cases hhead : f head with
      | found certificate => simp
      | cutoff =>
          cases htail : explore tail f <;> simp
      | exhausted =>
          rcases hmem with rfl | hmem
          · exact absurd hhead hne
          · exact ih hmem

def observed (adapter : Adapter model) (label : Label model) :
    List adapter.Event :=
  adapter.toObservation.labelTrace label

theorem observed_nil_or_singleton (adapter : Adapter model)
    (label : Label model) :
    observed adapter label = [] ∨
      ∃ event, observed adapter label = [event] := by
  cases label with
  | input recipient now message =>
      cases hproject : adapter.project (.input recipient now message) with
      | none =>
          left
          simp [observed, Observation.labelTrace, Label.observe, hproject]
      | some event =>
          right
          exact ⟨event, by
            simp [observed, Observation.labelTrace, Label.observe, hproject]⟩
  | process process now event send =>
      left
      simp [observed, Observation.labelTrace, Label.observe]
  | outside sender now message =>
      cases hproject : adapter.project (.output sender now message) with
      | none =>
          left
          simp [observed, Observation.labelTrace, Label.observe, hproject]
      | some event =>
          right
          exact ⟨event, by
            simp [observed, Observation.labelTrace, Label.observe, hproject]⟩

@[simp] theorem Observation.executionTrace_cons
    (observation : Observation model) (label : Label model)
    (next : System model) (rest : Trace model) :
    observation.executionTrace ((label, next) :: rest) =
      observation.labelTrace label ++ observation.executionTrace rest := by
  simp [Observation.executionTrace, Observation.labelTrace,
    Rover.observe, List.filterMap_append]

theorem Observation.executionTrace_append
    (observation : Observation model)
    (first second : Trace model) :
    observation.executionTrace (first ++ second) =
      observation.executionTrace first ++
        observation.executionTrace second := by
  induction first with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      simp [ih, List.append_assoc]

/-- Replay extends by one checked action at the system where the prefix ends. -/
theorem replayFrom_snoc {model : Model} {config : model.Config}
    {initial system : System model} {certificate : Certificate model}
    {trace : Trace model} {action : Action model}
    {label : Label model} {next : System model}
    (hreplay :
      replayFrom model config initial certificate = some trace)
    (hend : Rover.endOf initial trace = system)
    (hstep :
      actionStep model config system action = some (label, next)) :
    replayFrom model config initial (certificate ++ [action]) =
      some (trace ++ [(label, next)]) := by
  induction certificate generalizing initial trace with
  | nil =>
      simp only [replayFrom, Option.some.injEq] at hreplay
      subst trace
      simp only [Rover.endOf] at hend
      subst system
      simp [replayFrom, hstep]
  | cons first rest ih =>
      simp only [replayFrom] at hreplay
      cases hfirst :
          actionStep model config initial first with
      | none => simp [hfirst] at hreplay
      | some entry =>
          obtain ⟨firstLabel, firstSystem⟩ := entry
          simp only [hfirst] at hreplay
          obtain ⟨tail, htail, rfl⟩ :=
            Option.map_eq_some_iff.mp hreplay
          simp only [List.cons_append, replayFrom, hfirst]
          rw [ih htail hend]
          rfl

@[simp] theorem endOf_snoc (initial : System model)
    (trace : Trace model) (entry : Label model × System model) :
    Rover.endOf initial (trace ++ [entry]) = entry.2 := by
  induction trace generalizing initial with
  | nil => rfl
  | cons head rest ih => exact ih head.2

/-- Bounded depth-first search. Every enumerated move is checked by
`actionStep`; its actual projection, not an adapter claim, decides whether the
next event was consumed. -/
def searchFrom (adapter : Adapter model) (config : model.Config) :
    Nat → Context model → List adapter.Event → RawResult model
  | _, context, [] => .found context.certificate
  | 0, _, _ => .cutoff
  | fuel + 1, context, events@(expected :: rest) =>
      explore (adapter.actions config context.system expected) fun action =>
        match actionStep model config context.system action with
        | none => .exhausted
        | some (label, next) =>
            let nextContext := {
              system := next
              certificate := context.certificate ++ [action]
            }
            match observed adapter label with
            | [] => searchFrom adapter config fuel nextContext events
            | [event] =>
                if @decide (event = expected)
                    (adapter.decEqEvent event expected) then
                  searchFrom adapter config fuel nextContext rest
                else .exhausted
            | _ => .exhausted

def rawSearch (adapter : Adapter model) (bound : Nat)
    (config : model.Config) (events : List adapter.Event) : RawResult model :=
  searchFrom adapter config bound {
    system := System.initial (adapter.initial config)
    certificate := []
  } events

/-- Every reported search witness replays from the context's original system
and extends the already-replayed prefix by exactly the remaining trace. -/
theorem searchFrom_found_replays (adapter : Adapter model)
    (config : model.Config) {initial : System model}
    {fuel : Nat} {context : Context model} {events : List adapter.Event}
    {found : Certificate model} {preExecution : Trace model}
    (hprefix : replayFrom model config initial context.certificate =
      some preExecution)
    (hend : Rover.endOf initial preExecution = context.system)
    (hsearch :
      searchFrom adapter config fuel context events = .found found) :
    ∃ trace,
      replayFrom model config initial found = some trace ∧
      adapter.executionTrace trace =
        adapter.executionTrace preExecution ++ events := by
  induction fuel generalizing context events found preExecution with
  | zero =>
      cases events with
      | nil =>
          simp only [searchFrom, RawResult.found.injEq] at hsearch
          subst found
          exact ⟨preExecution, hprefix, by simp⟩
      | cons expected rest => simp [searchFrom] at hsearch
  | succ fuel ih =>
      cases events with
      | nil =>
          simp only [searchFrom, RawResult.found.injEq] at hsearch
          subst found
          exact ⟨preExecution, hprefix, by simp⟩
      | cons expected rest =>
          simp only [searchFrom] at hsearch
          obtain ⟨action, haction, hbranch⟩ :=
            explore_found hsearch
          cases hstep :
              actionStep model config context.system action with
          | none => simp [hstep] at hbranch
          | some entry =>
              obtain ⟨label, next⟩ := entry
              simp only [hstep] at hbranch
              have hreplay :
                  replayFrom model config initial
                    (context.certificate ++ [action]) =
                    some (preExecution ++ [(label, next)]) :=
                replayFrom_snoc hprefix hend hstep
              have hend' :
                  Rover.endOf initial
                    (preExecution ++ [(label, next)]) = next :=
                endOf_snoc initial preExecution (label, next)
              rcases observed_nil_or_singleton adapter label with
                hhidden | ⟨event, hobserved⟩
              · simp only [hhidden] at hbranch
                have hlabel :
                    adapter.toObservation.labelTrace label = [] := hhidden
                obtain ⟨trace, hexecution, htrace⟩ :=
                  ih hreplay hend' hbranch
                refine ⟨trace, hexecution, ?_⟩
                rw [Observation.executionTrace_append] at htrace
                simpa [hlabel, List.append_assoc] using htrace
              · by_cases heq : event = expected
                · subst event
                  simp [hobserved] at hbranch
                  have hlabel :
                      adapter.toObservation.labelTrace label = [expected] :=
                    hobserved
                  obtain ⟨trace, hexecution, htrace⟩ :=
                    ih hreplay hend' hbranch
                  refine ⟨trace, hexecution, ?_⟩
                  rw [Observation.executionTrace_append] at htrace
                  simpa [hlabel, List.append_assoc] using htrace
                · simp [hobserved, heq] at hbranch

/-- A raw search witness from the adapter's initial system independently
replays to exactly the requested observation trace. -/
theorem rawSearch_found_replays {adapter : Adapter model}
    {bound : Nat} {config : model.Config} {events : List adapter.Event}
    {certificate : Certificate model}
    (h : rawSearch adapter bound config events = .found certificate) :
    ∃ trace,
      replayFrom model config
        (System.initial (adapter.initial config)) certificate =
          some trace ∧
      adapter.executionTrace trace = events := by
  have hprefix :
      replayFrom model config (System.initial (adapter.initial config))
        ([] : Certificate model) = some [] := rfl
  have hend :
      Rover.endOf (System.initial (adapter.initial config)) [] =
        System.initial (adapter.initial config) := rfl
  obtain ⟨trace, hexecution, htrace⟩ :=
    searchFrom_found_replays adapter config hprefix hend h
  exact ⟨trace, hexecution, by
    simpa [Observation.executionTrace, Rover.observe] using htrace⟩

/-- Local action coverage is enough to find every legal trace. Its own
length is a sufficient fuel bound: each hidden or visible step consumes one
unit, while visible steps additionally consume one expected event. -/
theorem searchFrom_complete {adapter : Adapter model}
    (hcomplete : adapter.complete = true)
    {config : model.Config} {context : Context model}
    {events : List adapter.Event} {trace : Trace model}
    (hreachable : Reachable model config context.system)
    (hlegal : Legal model config context.system trace)
    (htrace : adapter.executionTrace trace = events) :
    ∃ certificate,
      searchFrom adapter config trace.length context events =
        .found certificate := by
  induction trace generalizing context events with
  | nil =>
      simp only [Observation.executionTrace_nil] at htrace
      subst events
      exact ⟨context.certificate, rfl⟩
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨hstep, hrest⟩ := hlegal
      cases events with
      | nil => exact ⟨context.certificate, rfl⟩
      | cons expected remaining =>
          have hupper : labelTime label ≤ adapter.horizon expected :=
            adapter.horizon_sound hcomplete hreachable hstep hrest htrace
          rw [Observation.executionTrace_cons] at htrace
          have hnext : Reachable model config next :=
            .step hreachable hstep
          rcases observed_nil_or_singleton adapter label with
            hhidden | ⟨event, hobserved⟩
          · have hlabel :
                adapter.toObservation.labelTrace label = [] := hhidden
            have htail :
                adapter.executionTrace rest =
                  expected :: remaining := by
              simpa [hlabel] using htrace
            obtain ⟨action, haction, hactionStep⟩ :=
              adapter.actions_complete hcomplete hreachable hstep
                (Or.inl hhidden) hupper
            let nextContext : Context model := {
              system := next
              certificate := context.certificate ++ [action]
            }
            obtain ⟨certificate, hcertificate⟩ :=
              ih (context := nextContext) hnext hrest htail
            let branch : Action model → RawResult model := fun candidate =>
              match actionStep model config context.system candidate with
                | none => RawResult.exhausted
                | some (branchLabel, branchNext) =>
                    let branchContext : Context model := {
                      system := branchNext
                      certificate := context.certificate ++ [candidate]
                    }
                    match observed adapter branchLabel with
                    | [] =>
                        searchFrom adapter config rest.length branchContext
                          (expected :: remaining)
                    | [branchEvent] =>
                        if @decide (branchEvent = expected)
                            (adapter.decEqEvent branchEvent expected) then
                          searchFrom adapter config rest.length branchContext
                            remaining
                        else .exhausted
                    | _ => .exhausted
            have hbranch : branch action =
                RawResult.found certificate := by
              simp [branch, hactionStep, hhidden, nextContext]
                at hcertificate ⊢
              exact hcertificate
            obtain ⟨found, hfound⟩ :=
              explore_found_of_mem (f := branch) haction hbranch
            exact ⟨found, by
              simpa [searchFrom, branch] using hfound⟩
          · have hlabel :
                adapter.toObservation.labelTrace label = [event] :=
              hobserved
            have hparts :
                event = expected ∧
                  adapter.executionTrace rest = remaining := by
              simpa [hlabel] using htrace
            have hevent : event = expected := hparts.1
            subst event
            have htail :
                adapter.executionTrace rest = remaining :=
              hparts.2
            obtain ⟨action, haction, hactionStep⟩ :=
              adapter.actions_complete hcomplete hreachable hstep
                (Or.inr hobserved) hupper
            let nextContext : Context model := {
              system := next
              certificate := context.certificate ++ [action]
            }
            obtain ⟨certificate, hcertificate⟩ :=
              ih (context := nextContext) hnext hrest htail
            let branch : Action model → RawResult model := fun candidate =>
              match actionStep model config context.system candidate with
                | none => RawResult.exhausted
                | some (branchLabel, branchNext) =>
                    let branchContext : Context model := {
                      system := branchNext
                      certificate := context.certificate ++ [candidate]
                    }
                    match observed adapter branchLabel with
                    | [] =>
                        searchFrom adapter config rest.length branchContext
                          (expected :: remaining)
                    | [branchEvent] =>
                        if @decide (branchEvent = expected)
                            (adapter.decEqEvent branchEvent expected) then
                          searchFrom adapter config rest.length branchContext
                            remaining
                        else .exhausted
                    | _ => .exhausted
            have hbranch : branch action =
                RawResult.found certificate := by
              simp [branch, hactionStep, hobserved, nextContext]
                at hcertificate ⊢
              exact hcertificate
            obtain ⟨found, hfound⟩ :=
              explore_found_of_mem (f := branch) haction hbranch
            exact ⟨found, by
              simpa [searchFrom, branch] using hfound⟩

/-- With local finite coverage, exhaustion is a proof of closure. Along any
legal explaining trace, every fuel bound either finds a witness or leaves
an explicit cutoff branch. -/
theorem searchFrom_ne_exhausted {adapter : Adapter model}
    (hcomplete : adapter.complete = true)
    {config : model.Config} {context : Context model}
    {events : List adapter.Event} {trace : Trace model}
    (hreachable : Reachable model config context.system)
    (hlegal : Legal model config context.system trace)
    (htrace : adapter.executionTrace trace = events)
    (fuel : Nat) :
    searchFrom adapter config fuel context events ≠ .exhausted := by
  induction fuel generalizing context events trace with
  | zero =>
      cases events <;> simp [searchFrom]
  | succ fuel ih =>
      cases events with
      | nil => simp [searchFrom]
      | cons expected remaining =>
          cases trace with
          | nil => simp at htrace
          | cons entry rest =>
              obtain ⟨label, next⟩ := entry
              obtain ⟨hstep, hrest⟩ := hlegal
              have hupper : labelTime label ≤ adapter.horizon expected :=
                adapter.horizon_sound hcomplete hreachable hstep hrest htrace
              have hnext : Reachable model config next :=
                .step hreachable hstep
              rw [Observation.executionTrace_cons] at htrace
              rcases observed_nil_or_singleton adapter label with
                hhidden | ⟨event, hobserved⟩
              · have hlabel :
                    adapter.toObservation.labelTrace label = [] := hhidden
                have htail :
                    adapter.executionTrace rest =
                      expected :: remaining := by
                  simpa [hlabel] using htrace
                obtain ⟨action, haction, hactionStep⟩ :=
                  adapter.actions_complete hcomplete hreachable hstep
                    (Or.inl hhidden) hupper
                let nextContext : Context model := {
                  system := next
                  certificate := context.certificate ++ [action]
                }
                have htailSearch :=
                  ih (context := nextContext) (trace := rest)
                    hnext hrest htail
                let branch : Action model → RawResult model :=
                  fun candidate =>
                    match actionStep model config context.system candidate with
                    | none => .exhausted
                    | some (branchLabel, branchNext) =>
                        let branchContext : Context model := {
                          system := branchNext
                          certificate := context.certificate ++ [candidate]
                        }
                        match observed adapter branchLabel with
                        | [] =>
                            searchFrom adapter config fuel branchContext
                              (expected :: remaining)
                        | [branchEvent] =>
                            if @decide (branchEvent = expected)
                                (adapter.decEqEvent branchEvent expected) then
                              searchFrom adapter config fuel branchContext
                                remaining
                            else .exhausted
                        | _ => .exhausted
                have hbranch : branch action ≠ .exhausted := by
                  simp [branch, hactionStep, hhidden]
                  exact htailSearch
                have hexplore :=
                  explore_ne_exhausted_of_mem
                    (f := branch) haction hbranch
                simpa [searchFrom, branch] using hexplore
              · have hlabel :
                    adapter.toObservation.labelTrace label = [event] :=
                  hobserved
                have hparts :
                    event = expected ∧
                      adapter.executionTrace rest = remaining := by
                  simpa [hlabel] using htrace
                cases hparts.1
                obtain ⟨action, haction, hactionStep⟩ :=
                  adapter.actions_complete hcomplete hreachable hstep
                    (Or.inr hobserved) hupper
                let nextContext : Context model := {
                  system := next
                  certificate := context.certificate ++ [action]
                }
                have htailSearch :=
                  ih (context := nextContext) (trace := rest)
                    hnext hrest hparts.2
                let branch : Action model → RawResult model :=
                  fun candidate =>
                    match actionStep model config context.system candidate with
                    | none => .exhausted
                    | some (branchLabel, branchNext) =>
                        let branchContext : Context model := {
                          system := branchNext
                          certificate := context.certificate ++ [candidate]
                        }
                        match observed adapter branchLabel with
                        | [] =>
                            searchFrom adapter config fuel branchContext
                              (expected :: remaining)
                        | [branchEvent] =>
                            if @decide (branchEvent = expected)
                                (adapter.decEqEvent branchEvent expected) then
                              searchFrom adapter config fuel branchContext
                                remaining
                            else .exhausted
                        | _ => .exhausted
                have hbranch : branch action ≠ .exhausted := by
                  simp [branch, hactionStep, hobserved]
                  exact htailSearch
                have hexplore :=
                  explore_ne_exhausted_of_mem
                    (f := branch) haction hbranch
                simpa [searchFrom, branch] using hexplore

/-- Search results expose only replayed validity. -/
inductive SearchResult (model : Model) where
  | valid (certificate : Certificate model) (trace : Trace model)
  | exhausted
  | cutoff

def boundedSearch (adapter : Adapter model) (bound : Nat)
    (config : model.Config) (events : List adapter.Event) :
    SearchResult model :=
  match rawSearch adapter bound config events with
  | .found certificate =>
      match replay adapter.toObservation config (adapter.initial config)
          events certificate with
      | some trace => .valid certificate trace
      | none => .cutoff
  | .exhausted => .exhausted
  | .cutoff => .cutoff

theorem boundedSearch_valid_sound {adapter : Adapter model}
    {bound : Nat} {config : model.Config} {events : List adapter.Event}
    {certificate : Certificate model} {trace : Trace model}
    (h : boundedSearch adapter bound config events =
      .valid certificate trace) :
    adapter.toObservation.Valid config events := by
  simp only [boundedSearch] at h
  cases hs : rawSearch adapter bound config events with
  | exhausted => simp [hs] at h
  | cutoff => simp [hs] at h
  | found found =>
      simp only [hs] at h
      cases hr : replay adapter.toObservation config (adapter.initial config)
          events found with
      | none => simp [hr] at h
      | some replayed =>
          simp only [hr] at h
          cases h
          exact replay_valid (adapter.initial_valid config) hr

/-- For a locally complete adapter, an exhausted result is a definitive
refutation: every valid trace would contribute either a witness or a
cutoff branch at this bound. -/
theorem boundedSearch_exhausted_sound {adapter : Adapter model}
    (hcomplete : adapter.complete = true)
    {bound : Nat} {config : model.Config} {events : List adapter.Event}
    (hsearch :
      boundedSearch adapter bound config events = .exhausted) :
    ¬ adapter.toObservation.Valid config events := by
  intro hvalid
  obtain ⟨trace, ⟨process, hinit, hlegal⟩, htrace⟩ := hvalid
  have hprocess : process = adapter.initial config :=
    adapter.initial_complete hinit
  subst process
  have hreachable :
      Reachable model config
        (System.initial (adapter.initial config)) :=
    .init (adapter.initial_valid config)
  have hne :
      rawSearch adapter bound config events ≠ .exhausted := by
    exact searchFrom_ne_exhausted hcomplete hreachable hlegal htrace bound
  simp only [boundedSearch] at hsearch
  cases hraw : rawSearch adapter bound config events with
  | found certificate =>
      cases hreplay :
          replay adapter.toObservation config (adapter.initial config)
            events certificate <;>
        simp [hraw, hreplay] at hsearch
  | cutoff => simp [hraw] at hsearch
  | exhausted => exact hne hraw

/-- Proof required before finite candidate exhaustion may become `invalid`. -/
structure ExhaustionLaw (adapter : Adapter model) : Prop where
  sound : ∀ {bound config events},
    adapter.exhaustive = true →
    boundedSearch adapter bound config events = .exhausted →
    ¬ adapter.toObservation.Valid config events

/-- A legal trace is found with its own length as fuel. This is derived
only from the adapter's local initial-state and action-enumeration laws. -/
theorem boundedSearch_complete {adapter : Adapter model}
    (hcomplete : adapter.complete = true)
    {config : model.Config} {events : List adapter.Event}
    {trace : Trace model}
    (hvalid : ValidTrace model config trace)
    (htrace : adapter.executionTrace trace = events) :
    ∃ certificate replayed,
      boundedSearch adapter trace.length config events =
        .valid certificate replayed := by
  obtain ⟨process, hinit, hlegal⟩ := hvalid
  have hprocess : process = adapter.initial config :=
    adapter.initial_complete hinit
  subst process
  let initialContext : Context model := {
    system := System.initial (adapter.initial config)
    certificate := []
  }
  have hinitialReachable :
      Reachable model config
        (System.initial (adapter.initial config)) :=
    .init (adapter.initial_valid config)
  obtain ⟨certificate, hsearch⟩ :=
    searchFrom_complete hcomplete
      (context := initialContext) hinitialReachable hlegal htrace
  have hraw :
      rawSearch adapter trace.length config events =
        .found certificate := by
    simpa [rawSearch, initialContext] using hsearch
  obtain ⟨replayed, hreplayed, hreplayedTrace⟩ :=
    rawSearch_found_replays hraw
  have hreplay :
      replay adapter.toObservation config (adapter.initial config)
        events certificate = some replayed := by
    letI := adapter.decEqEvent
    simp [replay, hreplayed, hreplayedTrace]
  exact ⟨certificate, replayed, by
    simp [boundedSearch, hraw, hreplay]⟩

/-- Historical architecture recovered generically: under finite local action
coverage, a trace is valid exactly when search succeeds at some finite bound. -/
theorem valid_iff_exists_bound {adapter : Adapter model}
    (hcomplete : adapter.complete = true) {config : model.Config}
    {events : List adapter.Event} :
    adapter.toObservation.Valid config events ↔
      ∃ bound certificate trace,
        boundedSearch adapter bound config events =
          .valid certificate trace := by
  constructor
  · rintro ⟨trace, hvalid, htrace⟩
    obtain ⟨certificate, replayed, hsearch⟩ :=
      boundedSearch_complete hcomplete hvalid htrace
    exact ⟨trace.length, certificate, replayed, hsearch⟩
  · rintro ⟨bound, certificate, trace, h⟩
    exact boundedSearch_valid_sound h

inductive Verdict (model : Model) where
  | valid (certificate : Certificate model) (trace : Trace model)
  | invalid
  | unknown

def Verdict.isValid : Verdict model → Bool
  | .valid _ _ => true
  | _ => false

def Verdict.isInvalid : Verdict model → Bool
  | .invalid => true
  | _ => false

def Verdict.isUnknown : Verdict model → Bool
  | .unknown => true
  | _ => false

/-- Tri-state checking. Fuel exhaustion and unproved candidate exhaustion are
`unknown`; `invalid` comes only from a proved invariant or closure law. -/
def checkWithBound (adapter : Adapter model)
    (_law : ExhaustionLaw adapter) (bound : Nat) (config : model.Config)
    (events : List adapter.Event) : Verdict model :=
  if adapter.definitiveInvalid config events then
    .invalid
  else
    match boundedSearch adapter bound config events with
    | .valid certificate trace => .valid certificate trace
    | .exhausted =>
        if adapter.exhaustive then .invalid else .unknown
    | .cutoff => .unknown

theorem checkWithBound_valid_sound {adapter : Adapter model}
    {law : ExhaustionLaw adapter} {bound : Nat} {config : model.Config}
    {events : List adapter.Event} {certificate : Certificate model}
    {trace : Trace model}
    (h : checkWithBound adapter law bound config events =
      .valid certificate trace) :
    adapter.toObservation.Valid config events := by
  simp only [checkWithBound] at h
  split at h
  next _ => contradiction
  next _ =>
    cases hs : boundedSearch adapter bound config events with
    | valid found replayed =>
        simp only [hs] at h
        cases h
        exact boundedSearch_valid_sound hs
    | exhausted =>
        simp only [hs] at h
        split at h <;> contradiction
    | cutoff => simp [hs] at h

theorem checkWithBound_invalid_sound {adapter : Adapter model}
    {law : ExhaustionLaw adapter} {bound : Nat} {config : model.Config}
    {events : List adapter.Event}
    (h : checkWithBound adapter law bound config events = .invalid) :
    ¬ adapter.toObservation.Valid config events := by
  simp only [checkWithBound] at h
  split at h
  next hinvalid => exact adapter.definitiveInvalid_sound hinvalid
  next _ =>
    cases hs : boundedSearch adapter bound config events with
    | valid certificate trace => simp [hs] at h
    | cutoff => simp [hs] at h
    | exhausted =>
        simp only [hs] at h
        split at h
        next hexhaustive => exact law.sound hexhaustive hs
        next _ => contradiction

end Rover.Check
