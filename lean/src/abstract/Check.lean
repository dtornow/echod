import Rover.Check
import «abstract».Model

/-!
# Resonate adapter for the generic Rover checker

This file contains only the Resonate projection, finite candidate enumeration,
initial state, and the protocol-specific monotone-time refutation. Search,
replay, verdicts, and their generic proofs live in `Rover.Check`.
-/

namespace Resonate.Check

open Rover

abbrev AModel := Abstract.model
abbrev Action := Rover.Check.Action AModel
abbrev Certificate := Rover.Check.Certificate AModel
abbrev Verdict := Rover.Check.Verdict AModel

def outputEvent (time : Time) : Output → BoundaryEvent
  | .response client id response => .response time client id response
  | .message entry => .message time entry

def eventTime : BoundaryEvent → Time
  | .request time _ => time
  | .response time _ _ _ => time
  | .message time _ => time

def observation : Rover.Check.Observation AModel where
  Event := BoundaryEvent
  decEqEvent := inferInstance
  project := Abstract.boundaryEvent

theorem observation_valid_iff {config : Config}
    {events : List BoundaryEvent} :
    observation.Valid config events ↔
      Abstract.ValidBoundaryTrace config events := by
  rfl

theorem step_send_outputs {config : Config} {pid : Abstract.Pid}
    {state : State} {now : Time} {event : Event Abstract.Pid Message}
    {result : Result Abstract.Pid State Message}
    (hprocess : AModel.isProcess pid)
    (hresult : result ∈ (AModel.step config pid state now event).val) :
    ∃ outputs, result.send = Abstract.sends outputs := by
  have hpid : pid = .service := Abstract.only_real_process hprocess
  subst pid
  cases event with
  | timeout =>
      simp only [Abstract.step, List.mem_map] at hresult
      obtain ⟨choice, hchoice, rfl⟩ := hresult
      exact ⟨choice.2, rfl⟩
  | receive sender message =>
      cases sender with
      | outside =>
          cases message with
          | request call =>
              simp only [Abstract.step, List.mem_cons] at hresult
              rcases hresult with hresult | hresult
              · subst result
                exact ⟨(Resonate.run config call state).2, rfl⟩
              · rcases hresult with hresult | hresult
                · subst result
                  exact ⟨(Resonate.runLose config call state).2, rfl⟩
                · rcases hresult with hresult | hresult
                  · subst result
                    exact ⟨(Resonate.runShed call state).2, rfl⟩
                  · contradiction
          | output output =>
              simp only [Abstract.step, Outcomes.one,
                List.mem_singleton] at hresult
              subst result
              exact ⟨[], rfl⟩
      | service =>
          cases message <;>
            simp only [Abstract.step, Outcomes.one,
              List.mem_singleton] at hresult
          all_goals
            subst result
            exact ⟨[], rfl⟩

theorem reachable_network_to_outside {config : Config}
    {world : World AModel} (hreachable : Reachable AModel config world)
    {sender : Abstract.Pid} {message : Message}
    (hmessage : (sender, Abstract.Pid.outside, message) ∈ world.network) :
    sender = .service ∧ ∃ output, message = .output output := by
  induction hreachable with
  | init hinit => simp [World.initial] at hmessage
  | step hreachable hstep ih =>
      cases hstep with
      | inject htime hprocess hinjectable =>
          simp only [World.inject, List.mem_append, List.mem_singleton]
            at hmessage
          rcases hmessage with hmessage | hmessage
          · exact ih hmessage
          · cases hmessage
            exact (AModel.outside_not_process hprocess).elim
      | process htime hprocess hevent hresult =>
          rename_i process now event result
          simp only [World.land, List.mem_append, List.mem_map] at hmessage
          rcases hmessage with hmessage | hmessage
          · exact ih hmessage
          · obtain ⟨send, hsend, hentry⟩ := hmessage
            obtain ⟨recipient, payload⟩ := send
            simp only [Prod.mk.injEq] at hentry
            obtain ⟨hprocessOutside, hpayload⟩ := hentry
            subst sender
            obtain ⟨rfl, rfl⟩ := hpayload
            obtain ⟨outputs, hsends⟩ :=
              step_send_outputs hprocess hresult
            rw [hsends] at hsend
            simp only [Abstract.sends, List.mem_map] at hsend
            obtain ⟨output, houtput, hsend⟩ := hsend
            cases hsend
            exact ⟨Abstract.only_real_process hprocess, output, rfl⟩
      | outside htime hmessageStep =>
          exact ih hmessage

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
    (h : observation.Valid config events) :
    monotoneTimes events = true := by
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := h
  rw [← htrace]
  exact legal_boundary_times config (World.initial process) execution hlegal

theorem legal_step_before_expected {config : Config}
    {world : World AModel} {expected : BoundaryEvent}
    {remaining : List BoundaryEvent} {label : Label AModel}
    {next : World AModel} {rest : Execution AModel}
    (hreachable : Reachable AModel config world)
    (hstep : Step AModel config world label next)
    (hrest : Legal AModel config next rest)
    (htrace :
      observation.executionTrace ((label, next) :: rest) =
        expected :: remaining) :
    Rover.Check.labelTime label ≤ eventTime expected := by
  cases hstep with
  | inject htime hprocess hinjectable =>
      obtain ⟨call, rfl⟩ := hinjectable
      simp only [Rover.Check.Observation.executionTrace_cons,
        Rover.Check.Observation.labelTrace, observation, Label.observe,
        List.filterMap_cons, Abstract.boundaryEvent, Message.observeInput,
        List.cons_append, List.cons.injEq] at htrace
      rw [← htrace.1]
      exact Nat.le_refl _
  | process htime hprocess hevent hresult =>
      rw [Rover.Check.Observation.executionTrace_cons] at htrace
      simp only [Rover.Check.Observation.labelTrace, Label.observe,
        List.filterMap_nil, List.nil_append] at htrace
      have htailObservation :
          observation.executionTrace rest = expected :: remaining := htrace
      have hmono := legal_boundary_times config
        (world.land _ _ _) rest hrest
      have htail : Abstract.boundaryTrace rest =
          expected :: remaining := by
        simpa [Rover.Check.Observation.executionTrace, observation,
          Abstract.boundaryTrace] using htailObservation
      rw [htail] at hmono
      simp only [World.land, monotoneFrom, Bool.and_eq_true,
        decide_eq_true_eq] at hmono
      simpa [Rover.Check.labelTime, eventTime] using hmono.1
  | outside htime hmessage =>
      rename_i sender now message
      obtain ⟨hsender, output, houtput⟩ :=
        reachable_network_to_outside hreachable hmessage
      subst sender
      subst message
      cases output <;>
        simp only [Rover.Check.Observation.executionTrace_cons,
          Rover.Check.Observation.labelTrace, observation, Label.observe,
          List.filterMap_cons, Abstract.boundaryEvent, Message.observeOutput,
          List.cons_append, List.cons.injEq] at htrace
      all_goals
        rw [← htrace.1]
        exact Nat.le_refl _

def processActions (config : Config) (world : World AModel)
    (horizon : Time) : List Action :=
  (List.range (horizon + 1)).flatMap fun time =>
    let receives :=
      (List.range world.network.length).flatMap fun networkIndex =>
        match world.network[networkIndex]? with
        | some (sender, Abstract.Pid.service, message) =>
            (List.range ((AModel.step config .service
                (world.process .service) time
                (.receive sender message)).val.length)).map fun outcome =>
              .process .service time (.receive networkIndex) outcome
        | _ => []
    let timeouts :=
      (List.range ((AModel.step config .service
        (world.process .service) time .timeout).val.length)).map fun outcome =>
          .process .service time .timeout outcome
    receives ++ timeouts

def observeActions (world : World AModel) (time : Time)
    (event : BoundaryEvent) : List Action :=
  (List.range world.network.length).flatMap fun networkIndex =>
    match world.network[networkIndex]? with
    | some (Abstract.Pid.service, Abstract.Pid.outside,
        Message.output output) =>
        if outputEvent time output = event then [.outside networkIndex time]
        else []
    | _ => []

def injectActions : BoundaryEvent → List Action
  | .request time call => [.inject .service time (.request call)]
  | _ => []

def actions (config : Config) (world : World AModel)
    (event : BoundaryEvent) : List Action :=
  let time := eventTime event
  injectActions event ++
    observeActions world time event ++
    processActions config world time

theorem process_receive_mem {config : Config} {world : World AModel}
    {horizon now : Time} {networkIndex outcome : Nat}
    {sender : Abstract.Pid} {message : Message}
    (htime : now ≤ horizon)
    (hnetwork :
      world.network[networkIndex]? =
        some (sender, Abstract.Pid.service, message))
    (houtcome :
      (AModel.step config .service (world.process .service) now
        (.receive sender message)).val[outcome]? = some result) :
    Rover.Check.Action.process (model := AModel) Abstract.Pid.service now
        (.receive networkIndex) outcome ∈
      processActions config world horizon := by
  simp only [processActions, List.mem_flatMap]
  refine ⟨now, List.mem_range.mpr (Nat.lt_succ_of_le htime), ?_⟩
  apply List.mem_append_left
  simp only [List.mem_flatMap]
  refine ⟨networkIndex, List.mem_range.mpr
    (List.getElem?_eq_some_iff.mp hnetwork).1, ?_⟩
  rw [hnetwork]
  simp only [List.mem_map]
  exact ⟨outcome, List.mem_range.mpr
    (List.getElem?_eq_some_iff.mp houtcome).1, rfl⟩

theorem process_timeout_mem {config : Config} {world : World AModel}
    {horizon now : Time} {outcome : Nat}
    (htime : now ≤ horizon)
    (houtcome :
      (AModel.step config .service (world.process .service) now
        .timeout).val[outcome]? = some result) :
    Rover.Check.Action.process (model := AModel) Abstract.Pid.service now
        .timeout outcome ∈
      processActions config world horizon := by
  simp only [processActions, List.mem_flatMap]
  refine ⟨now, List.mem_range.mpr (Nat.lt_succ_of_le htime), ?_⟩
  apply List.mem_append_right
  simp only [List.mem_map]
  exact ⟨outcome, List.mem_range.mpr
    (List.getElem?_eq_some_iff.mp houtcome).1, rfl⟩

theorem observe_mem {world : World AModel} {time : Time}
    {expected : BoundaryEvent} {networkIndex : Nat} {output : Output}
    (hnetwork :
      world.network[networkIndex]? =
        some (.service, .outside, .output output))
    (houtput : outputEvent time output = expected) :
    Rover.Check.Action.outside networkIndex time ∈
      observeActions world time expected := by
  simp only [observeActions, List.mem_flatMap]
  refine ⟨networkIndex, List.mem_range.mpr
    (List.getElem?_eq_some_iff.mp hnetwork).1, ?_⟩
  rw [hnetwork]
  simp [houtput]

theorem actions_complete {config : Config} {world : World AModel}
    {expected : BoundaryEvent} {label : Label AModel}
    {next : World AModel}
    (hreachable : Reachable AModel config world)
    (hstep : Step AModel config world label next)
    (hprojection :
      observation.labelTrace label = [] ∨
        observation.labelTrace label = [expected])
    (hupper : Rover.Check.labelTime label ≤ eventTime expected) :
    ∃ action ∈ actions config world expected,
      Rover.Check.actionStep AModel config world action =
        some (label, next) := by
  cases hstep with
  | inject htime hprocess hinjectable =>
      rename_i recipient now message
      obtain ⟨call, rfl⟩ := hinjectable
      have hrecipient : recipient = .service :=
        Abstract.only_real_process hprocess
      subst recipient
      rcases hprojection with hhidden | hvisible
      · simp [Rover.Check.Observation.labelTrace, observation,
          Label.observe, Abstract.boundaryEvent,
          Message.observeInput] at hhidden
      · have hexpected :
            expected = .request now call := by
          simpa [Rover.Check.Observation.labelTrace, observation,
            Label.observe, Abstract.boundaryEvent,
            Message.observeInput] using hvisible.symm
        subst expected
        refine ⟨.inject .service now (.request call), ?_, ?_⟩
        · simp [actions, injectActions]
        · simp [Rover.Check.actionStep, htime]
  | process htime hprocess hevent hresult =>
      rename_i process now event result
      have hpid : process = .service :=
        Abstract.only_real_process hprocess
      subst process
      obtain ⟨outcome, houtcome⟩ :=
        List.mem_iff_getElem?.mp hresult
      cases event with
      | timeout =>
          refine ⟨.process .service now .timeout outcome, ?_, ?_⟩
          · simp only [actions]
            exact List.mem_append_right _
              (process_timeout_mem hupper houtcome)
          · simp [Rover.Check.actionStep, htime, houtcome]
      | receive sender message =>
          obtain ⟨networkIndex, hnetwork⟩ :=
            List.mem_iff_getElem?.mp hevent
          refine ⟨.process .service now (.receive networkIndex) outcome,
            ?_, ?_⟩
          · simp only [actions]
            exact List.mem_append_right _
              (process_receive_mem hupper hnetwork houtcome)
          · simp only [Rover.Check.actionStep]
            rw [hnetwork]
            simp [htime, houtcome]
  | outside htime hmessage =>
      rename_i sender now message
      obtain ⟨hsender, output, houtput⟩ :=
        reachable_network_to_outside hreachable hmessage
      subst sender
      subst message
      obtain ⟨networkIndex, hnetwork⟩ :=
        List.mem_iff_getElem?.mp hmessage
      rcases hprojection with hhidden | hvisible
      · cases output <;>
          simp [Rover.Check.Observation.labelTrace, observation,
            Label.observe, Abstract.boundaryEvent,
            Message.observeOutput] at hhidden
      · have hexpected : outputEvent now output = expected := by
          cases output <;>
            simpa [Rover.Check.Observation.labelTrace, observation,
              Label.observe, Abstract.boundaryEvent,
              Message.observeOutput, outputEvent] using hvisible
        have htimeExpected : eventTime expected = now := by
          rw [← hexpected]
          cases output <;> rfl
        refine ⟨.outside networkIndex now, ?_, ?_⟩
        · simp only [actions]
          rw [htimeExpected]
          apply List.mem_append_left
          exact List.mem_append_right _
            (observe_mem hnetwork hexpected)
        · simp only [Rover.Check.actionStep]
          rw [hnetwork]
          simp [htime]

def adapter : Rover.Check.Adapter AModel where
  toObservation := observation
  initial := fun _ => Abstract.initialProcess
  initial_valid := Abstract.initialProcess_valid
  initial_complete := by
    intro config process hinit
    exact hinit
  actions := actions
  complete := true
  horizon := eventTime
  horizon_sound := by
    intro hcomplete config world expected remaining label next rest
      hreachable hstep hrest htrace
    exact legal_step_before_expected hreachable hstep hrest htrace
  actions_complete := by
    intro hcomplete
    exact actions_complete
  definitiveInvalid := fun _ events => !monotoneTimes events
  definitiveInvalid_sound := by
    intro config events hnonmonotone hvalid
    have hmono := valid_boundary_times hvalid
    simp only [Bool.not_eq_true'] at hnonmonotone
    rw [hmono] at hnonmonotone
    contradiction
  exhaustive := true

/-- Exhaustion is definitive because every relevant time and outcome is
enumerated. A branch that reaches its resource bound is still `unknown`. -/
def exhaustionLaw : Rover.Check.ExhaustionLaw adapter where
  sound := by
    intro bound config events hexhaustive hsearch
    exact Rover.Check.boundedSearch_exhausted_sound
      (adapter := adapter) rfl hsearch

def replay (config : Config) (events : List BoundaryEvent)
    (certificate : Certificate) : Option (Execution AModel) :=
  Rover.Check.replay observation config Abstract.initialProcess
    events certificate

def search (bound : Nat) (config : Config)
    (events : List BoundaryEvent) : Rover.Check.SearchResult AModel :=
  Rover.Check.boundedSearch adapter bound config events

def checkWithBound (bound : Nat) (config : Config)
    (events : List BoundaryEvent) : Verdict :=
  Rover.Check.checkWithBound adapter exhaustionLaw bound config events

def defaultBound (events : List BoundaryEvent) : Nat :=
  events.length * 6 + 1

def check (config : Config) (events : List BoundaryEvent) : Verdict :=
  checkWithBound (defaultBound events) config events

theorem checkWithBound_nonmonotone {bound : Nat} {config : Config}
    {events : List BoundaryEvent}
    (h : monotoneTimes events = false) :
    checkWithBound bound config events = .invalid := by
  simp [checkWithBound, Rover.Check.checkWithBound, adapter, h]

theorem check_nonmonotone {config : Config}
    {events : List BoundaryEvent}
    (h : monotoneTimes events = false) :
    check config events = .invalid :=
  checkWithBound_nonmonotone h

theorem valid_iff_exists_bound {config : Config}
    {events : List BoundaryEvent} :
    Abstract.ValidBoundaryTrace config events ↔
      ∃ bound certificate execution,
        search bound config events = .valid certificate execution := by
  rw [← observation_valid_iff]
  have h := Rover.Check.valid_iff_exists_bound
    (adapter := adapter) (config := config) (events := events) rfl
  change observation.Valid config events ↔
    (∃ bound certificate execution,
      Rover.Check.boundedSearch adapter bound config events =
        .valid certificate execution) at h
  simpa [search] using h

theorem replay_valid {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : replay config events certificate = some execution) :
    Abstract.ValidBoundaryTrace config events := by
  have hvalid := Rover.Check.replay_valid
    (observation := observation)
    (Abstract.initialProcess_valid config) h
  exact observation_valid_iff.mp hvalid

theorem checkWithBound_valid_sound {bound : Nat} {config : Config}
    {events : List BoundaryEvent} {certificate : Certificate}
    {execution : Execution AModel}
    (h : checkWithBound bound config events =
      .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events := by
  have hvalid := Rover.Check.checkWithBound_valid_sound
    (adapter := adapter) (law := exhaustionLaw) h
  change observation.Valid config events at hvalid
  exact observation_valid_iff.mp hvalid

theorem check_valid_sound {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : check config events = .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events :=
  checkWithBound_valid_sound h

theorem checkWithBound_invalid_sound {bound : Nat} {config : Config}
    {events : List BoundaryEvent}
    (h : checkWithBound bound config events = .invalid) :
    ¬ Abstract.ValidBoundaryTrace config events := by
  have hinvalid := Rover.Check.checkWithBound_invalid_sound
    (adapter := adapter) (law := exhaustionLaw) h
  intro hvalid
  apply hinvalid
  change observation.Valid config events
  exact observation_valid_iff.mpr hvalid

theorem check_invalid_sound {config : Config}
    {events : List BoundaryEvent}
    (h : check config events = .invalid) :
    ¬ Abstract.ValidBoundaryTrace config events :=
  checkWithBound_invalid_sound h

end Resonate.Check
