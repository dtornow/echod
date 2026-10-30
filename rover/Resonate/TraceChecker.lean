import Resonate.Abstract
import Experiment.PromiseFrame

/-!
# Executable checking of Resonate boundary traces

The bounded search chooses previously injected requests, every retained
`Resonate.run` outcome, and every matching outside observation from the
append-only network. It erases proved-inert actions and deduplicates semantic
contexts. Cutoffs are explicit `Unknown`; exhaustion becomes `Invalid` only
when an independently proved necessary trace invariant fails. `replay`
independently checks valid certificates and constructs the corresponding
Rover execution.
-/

namespace Resonate.TraceChecker

open Rover

/-- One abstract Rover step recorded by a trace-checking certificate. -/
inductive Action where
  | inject (time : Time) (call : Call)
  | process (time : Time) (call : Call) (state : State)
      (outputs : List Output)
  /-- An abstract step which cannot handle a client request. Such steps are
  semantically inert, but retaining them makes normalization of arbitrary
  Rover executions exact (in particular for timeouts). -/
  | noop (time : Time) (event : Event Abstract.Pid Message)
  /-- An exact outside observation. Search only constructs service outputs;
  normalization also retains any semantically possible hidden message shape. -/
  | observe (time : Time) (sender : Abstract.Pid) (message : Message)

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
  | .noop time event =>
      if world.now ≤ time then
        match event with
        | .receive .outside (.request _) => none
        | .receive sender message =>
            if (sender, Abstract.Pid.service, message) ∈ world.network then
              let result : Result Abstract.Pid State Message := {
                state := world.process Abstract.Pid.service
                send := []
              }
              let label : Label AModel :=
                .process .service time event []
              some (label, world.land .service time result)
            else
              none
        | .timeout =>
            let result : Result Abstract.Pid State Message := {
              state := world.process Abstract.Pid.service
              send := []
            }
            let label : Label AModel :=
              .process .service time event []
            some (label, world.land .service time result)
      else
        none
  | .observe time sender message =>
      if world.now ≤ time then
        if (sender, Abstract.Pid.outside, message) ∈ world.network then
          some (.outside sender time message,
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
  | noop time event =>
      cases event with
      | timeout =>
          simp only [actionStep] at h
          split at h
          next htime =>
            cases h
            refine Step.process
              (model := AModel) (config := config)
              (world := world) (process := Abstract.Pid.service)
              (now := time)
              (event := .timeout)
              (result := {
                state := world.process Abstract.Pid.service
                send := []
              })
              htime rfl (by trivial) ?_
            simp [Abstract.step, Outcomes.one]
          next _ => contradiction
      | receive sender message =>
          cases sender with
          | outside =>
              cases message with
              | request call =>
                  simp [actionStep] at h
              | output output =>
                  simp only [actionStep] at h
                  split at h
                  next htime =>
                    split at h
                    next hvalid =>
                      cases h
                      refine Step.process
                        (model := AModel) (config := config)
                        (world := world) (process := Abstract.Pid.service)
                        (now := time)
                        (event := (Event.receive Abstract.Pid.outside
                          (Message.output output) :
                            Event Abstract.Pid Message))
                        (result := {
                          state := world.process Abstract.Pid.service
                          send := []
                        })
                        htime rfl hvalid ?_
                      simp [Abstract.step, Outcomes.one]
                    next _ => contradiction
                  next _ => contradiction
          | service =>
              cases message with
              | request call =>
                  simp only [actionStep] at h
                  split at h
                  next htime =>
                    split at h
                    next hvalid =>
                      cases h
                      refine Step.process
                        (model := AModel) (config := config)
                        (world := world) (process := Abstract.Pid.service)
                        (now := time)
                        (event := (Event.receive Abstract.Pid.service
                          (Message.request call) :
                            Event Abstract.Pid Message))
                        (result := {
                          state := world.process Abstract.Pid.service
                          send := []
                        })
                        htime rfl hvalid ?_
                      simp [Abstract.step, Outcomes.one]
                    next _ => contradiction
                  next _ => contradiction
              | output output =>
                  simp only [actionStep] at h
                  split at h
                  next htime =>
                    split at h
                    next hvalid =>
                      cases h
                      refine Step.process
                        (model := AModel) (config := config)
                        (world := world) (process := Abstract.Pid.service)
                        (now := time)
                        (event := (Event.receive Abstract.Pid.service
                          (Message.output output) :
                            Event Abstract.Pid Message))
                        (result := {
                          state := world.process Abstract.Pid.service
                          send := []
                        })
                        htime rfl hvalid ?_
                      simp [Abstract.step, Outcomes.one]
                    next _ => contradiction
                  next _ => contradiction
  | observe time sender message =>
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

/-- Every legal abstract Rover execution has an exact replay certificate.
This normalization retains hidden no-op/timeout steps, every duplicate request
receive, the execution's monotone times, and each delayed or reordered outside
observation. Since replay uses the same append-only world operations, message
duplication is preserved rather than approximated. -/
theorem legal_normalizes (config : Config) (world : World AModel)
    (execution : Execution AModel)
    (hlegal : Legal AModel config world execution) :
    ∃ certificate, replayFrom config world certificate = some execution := by
  induction execution generalizing world with
  | nil =>
      exact ⟨[], rfl⟩
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨hstep, hrest⟩ := hlegal
      obtain ⟨tail, htail⟩ := ih next hrest
      cases hstep with
      | @inject to time message htime hprocess hinject =>
          have hto : _ = Abstract.Pid.service :=
            Abstract.only_real_process hprocess
          subst hto
          change ∃ call, _ = Message.request call at hinject
          obtain ⟨call, rfl⟩ := hinject
          refine ⟨.inject time call :: tail, ?_⟩
          simp [replayFrom, actionStep, htime, htail]
      | process htime hprocess hvalid houtcome =>
          have hp : _ = Abstract.Pid.service :=
            Abstract.only_real_process hprocess
          subst hp
          rename_i time event result
          cases event with
          | timeout =>
              have hr : result = {
                  state := world.process Abstract.Pid.service
                  send := []
                } := by
                simpa [Abstract.step, Outcomes.one] using houtcome
              subst result
              refine ⟨.noop time .timeout :: tail, ?_⟩
              simp [replayFrom, actionStep, htime, htail]
          | receive sender message =>
              cases sender with
              | outside =>
                  cases message with
                  | request call =>
                      change (Abstract.Pid.outside, Abstract.Pid.service,
                        Message.request call) ∈ world.network at hvalid
                      simp only [Abstract.step] at houtcome
                      obtain ⟨outcome, ho, hr⟩ :=
                        List.mem_map.mp houtcome
                      obtain ⟨state, outputs⟩ := outcome
                      subst result
                      refine ⟨.process time call state outputs :: tail, ?_⟩
                      simp [replayFrom, actionStep, htime, hvalid, ho, htail]
                  | output output =>
                      change (Abstract.Pid.outside, Abstract.Pid.service,
                        Message.output output) ∈ world.network at hvalid
                      have hr : result = {
                          state := world.process Abstract.Pid.service
                          send := []
                        } := by
                          simpa [Abstract.step, Outcomes.one] using houtcome
                      subst result
                      refine ⟨.noop time
                        (.receive .outside (.output output)) :: tail, ?_⟩
                      simp [replayFrom, actionStep, htime, hvalid, htail]
              | service =>
                  cases message with
                  | request call =>
                      change (Abstract.Pid.service, Abstract.Pid.service,
                        Message.request call) ∈ world.network at hvalid
                      have hr : result = {
                          state := world.process Abstract.Pid.service
                          send := []
                        } := by
                          simpa [Abstract.step, Outcomes.one] using houtcome
                      subst result
                      refine ⟨.noop time
                        (.receive .service (.request call)) :: tail, ?_⟩
                      simp [replayFrom, actionStep, htime, hvalid, htail]
                  | output output =>
                      change (Abstract.Pid.service, Abstract.Pid.service,
                        Message.output output) ∈ world.network at hvalid
                      have hr : result = {
                          state := world.process Abstract.Pid.service
                          send := []
                        } := by
                          simpa [Abstract.step, Outcomes.one] using houtcome
                      subst result
                      refine ⟨.noop time
                        (.receive .service (.output output)) :: tail, ?_⟩
                      simp [replayFrom, actionStep, htime, hvalid, htail]
      | outside htime hmessage =>
          rename_i sender time message
          refine ⟨.observe time sender message :: tail, ?_⟩
          simp [replayFrom, actionStep, htime, hmessage, htail]

/-- Semantic trace validity always supplies a certificate replaying the exact
underlying abstract execution. This is the normalization bridge used to keep
the executable search model aligned with arbitrary Rover behaviors. -/
theorem valid_has_replay_certificate {config : Config}
    {events : List BoundaryEvent}
    (hvalid : Abstract.ValidBoundaryTrace config events) :
    ∃ process certificate execution,
      AModel.init config process ∧
      replayFrom config (World.initial process) certificate =
        some execution ∧
      Abstract.boundaryTrace execution = events := by
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := hvalid
  obtain ⟨certificate, hreplay⟩ :=
    legal_normalizes config (World.initial process) execution hlegal
  exact ⟨process, certificate, execution, hinit, hreplay, htrace⟩

/-- Hidden no-op actions carry no semantic information beyond advancing time.
An earlier world with the same process state and network can therefore omit
one and still precede its result. -/
def SemanticEarlier (earlier later : World AModel) : Prop :=
  earlier.process = later.process ∧
  earlier.network = later.network ∧
  earlier.now ≤ later.now

theorem semanticEarlier_refl (world : World AModel) :
    SemanticEarlier world world :=
  ⟨rfl, rfl, Nat.le_refl _⟩

theorem noop_erased {config : Config} {earlier world next : World AModel}
    {time : Time} {event : Event Abstract.Pid Message}
    {label : Label AModel}
    (hearlier : SemanticEarlier earlier world)
    (hstep : actionStep config world (.noop time event) =
      some (label, next)) :
    SemanticEarlier earlier next := by
  obtain ⟨hprocess, hnetwork, hnow⟩ := hearlier
  cases event with
  | timeout =>
      simp only [actionStep] at hstep
      split at hstep
      next htime =>
        cases hstep
        refine ⟨?_, ?_, Nat.le_trans hnow htime⟩
        · rw [hprocess]
          funext pid
          by_cases hp : pid = Abstract.Pid.service <;>
            simp [World.land, hp]
        · simp [World.land, hnetwork]
      next _ => contradiction
  | receive sender message =>
      cases sender with
      | outside =>
          cases message with
          | request call => simp [actionStep] at hstep
          | output output =>
              simp only [actionStep] at hstep
              split at hstep
              next htime =>
                split at hstep
                next _ =>
                  cases hstep
                  refine ⟨?_, ?_, Nat.le_trans hnow htime⟩
                  · rw [hprocess]
                    funext pid
                    by_cases hp : pid = Abstract.Pid.service <;>
                      simp [World.land, hp]
                  · simp [World.land, hnetwork]
                next _ => contradiction
              next _ => contradiction
      | service =>
          cases message with
          | request call =>
              simp only [actionStep] at hstep
              split at hstep
              next htime =>
                split at hstep
                next _ =>
                  cases hstep
                  refine ⟨?_, ?_, Nat.le_trans hnow htime⟩
                  · rw [hprocess]
                    funext pid
                    by_cases hp : pid = Abstract.Pid.service <;>
                      simp [World.land, hp]
                  · simp [World.land, hnetwork]
                next _ => contradiction
              next _ => contradiction
          | output output =>
              simp only [actionStep] at hstep
              split at hstep
              next htime =>
                split at hstep
                next _ =>
                  cases hstep
                  refine ⟨?_, ?_, Nat.le_trans hnow htime⟩
                  · rw [hprocess]
                    funext pid
                    by_cases hp : pid = Abstract.Pid.service <;>
                      simp [World.land, hp]
                  · simp [World.land, hnetwork]
                next _ => contradiction
              next _ => contradiction

theorem noop_observe_empty {config : Config} {world next : World AModel}
    {time : Time} {event : Event Abstract.Pid Message}
    {label : Label AModel}
    (hstep : actionStep config world (.noop time event) =
      some (label, next)) :
    Label.observe label = [] := by
  cases event with
  | timeout =>
      simp only [actionStep] at hstep
      split at hstep
      next _ => cases hstep; rfl
      next _ => contradiction
  | receive sender message =>
      cases sender with
      | outside =>
          cases message with
          | request call => simp [actionStep] at hstep
          | output output =>
              simp only [actionStep] at hstep
              split at hstep
              next _ =>
                split at hstep
                next _ => cases hstep; rfl
                next _ => contradiction
              next _ => contradiction
      | service =>
          cases message with
          | request call =>
              simp only [actionStep] at hstep
              split at hstep
              next _ =>
                split at hstep
                next _ => cases hstep; rfl
                next _ => contradiction
              next _ => contradiction
          | output output =>
              simp only [actionStep] at hstep
              split at hstep
              next _ =>
                split at hstep
                next _ => cases hstep; rfl
                next _ => contradiction
              next _ => contradiction

theorem inject_transport {config : Config} {earlier world next : World AModel}
    {time : Time} {call : Call} {label : Label AModel}
    (hearlier : SemanticEarlier earlier world)
    (hstep : actionStep config world (.inject time call) =
      some (label, next)) :
    ∃ next',
      actionStep config earlier (.inject time call) = some (label, next') ∧
      SemanticEarlier next' next := by
  obtain ⟨hprocess, hnetwork, hnow⟩ := hearlier
  simp only [actionStep] at hstep
  split at hstep
  next htime =>
    cases hstep
    let next' := earlier.inject Abstract.Pid.service (.request call) time
    refine ⟨next', ?_, ?_⟩
    · simp [actionStep, next', Nat.le_trans hnow htime]
    · refine ⟨?_, ?_, Nat.le_refl _⟩
      · exact hprocess
      · simp [next', World.inject, hnetwork]
  next _ => contradiction

theorem process_transport {config : Config} {earlier world next : World AModel}
    {time : Time} {call : Call} {state : State} {outputs : List Output}
    {label : Label AModel}
    (hearlier : SemanticEarlier earlier world)
    (hstep : actionStep config world (.process time call state outputs) =
      some (label, next)) :
    ∃ next',
      actionStep config earlier (.process time call state outputs) =
        some (label, next') ∧
      SemanticEarlier next' next := by
  obtain ⟨hprocess, hnetwork, hnow⟩ := hearlier
  simp only [actionStep] at hstep
  split at hstep
  next htime =>
    split at hstep
    next hrequest =>
      split at hstep
      next houtcome =>
        cases hstep
        have hrequest' :
            (Abstract.Pid.outside, Abstract.Pid.service,
              Message.request call) ∈ earlier.network := by
          simpa [hnetwork] using hrequest
        have houtcome' :
            (state, outputs) ∈
              (Resonate.run config call
                (earlier.process Abstract.Pid.service)).val := by
          simpa [hprocess] using houtcome
        let result : Result Abstract.Pid State Message := {
          state
          send := outputs.map fun output =>
            (Abstract.Pid.outside, Message.output output)
        }
        let next' := earlier.land Abstract.Pid.service time result
        refine ⟨next', ?_, ?_⟩
        · simp [actionStep, next', result, Nat.le_trans hnow htime,
            hrequest', houtcome']
        · refine ⟨?_, ?_, Nat.le_refl _⟩
          · funext pid
            by_cases hp : pid = Abstract.Pid.service <;>
              simp [next', result, World.land, hp, hprocess]
          · simp [next', result, World.land, hnetwork]
      next _ => contradiction
    next _ => contradiction
  next _ => contradiction

theorem observe_transport {config : Config}
    {earlier world next : World AModel} {time : Time}
    {sender : Abstract.Pid} {message : Message} {label : Label AModel}
    (hearlier : SemanticEarlier earlier world)
    (hstep : actionStep config world (.observe time sender message) =
      some (label, next)) :
    ∃ next',
      actionStep config earlier (.observe time sender message) =
        some (label, next') ∧
      SemanticEarlier next' next := by
  obtain ⟨hprocess, hnetwork, hnow⟩ := hearlier
  simp only [actionStep] at hstep
  split at hstep
  next htime =>
    split at hstep
    next hmessage =>
      cases hstep
      let next' := earlier.observeOutside time
      refine ⟨next', ?_, ?_⟩
      · simp [actionStep, next', Nat.le_trans hnow htime,
          show (sender, Abstract.Pid.outside, message) ∈ earlier.network by
            simpa [hnetwork] using hmessage]
      · exact ⟨hprocess, hnetwork, Nat.le_refl _⟩
    next _ => contradiction
  next _ => contradiction

def eraseNoops : Certificate → Certificate
  | [] => []
  | .noop _ _ :: rest => eraseNoops rest
  | action :: rest => action :: eraseNoops rest

theorem eraseNoops_idempotent (certificate : Certificate) :
    eraseNoops (eraseNoops certificate) = eraseNoops certificate := by
  induction certificate with
  | nil => rfl
  | cons action rest ih =>
      cases action <;> simp [eraseNoops, ih]

/-- Exact certificate normalization may retain inert steps, but trace
existence never needs them: deleting every no-op yields another replay with
the same filtered boundary trace. -/
theorem eraseNoops_replayFrom {config : Config}
    {earlier world : World AModel} {certificate : Certificate}
    {execution : Execution AModel}
    (hearlier : SemanticEarlier earlier world)
    (hreplay : replayFrom config world certificate = some execution) :
    ∃ erased,
      replayFrom config earlier (eraseNoops certificate) = some erased ∧
      Abstract.boundaryTrace erased =
        Abstract.boundaryTrace execution := by
  induction certificate generalizing earlier world execution with
  | nil =>
      simp only [replayFrom, Option.some.injEq] at hreplay
      subst execution
      exact ⟨[], rfl, rfl⟩
  | cons action rest ih =>
      simp only [replayFrom] at hreplay
      cases hs : actionStep config world action with
      | none => simp [hs] at hreplay
      | some entry =>
          obtain ⟨label, next⟩ := entry
          simp only [hs] at hreplay
          cases ht : replayFrom config next rest with
          | none => simp [ht] at hreplay
          | some tail =>
              simp only [ht, Option.some.injEq] at hreplay
              subst execution
              cases action with
              | noop time event =>
                  obtain ⟨erased, herased, htrace⟩ :=
                    ih (noop_erased hearlier hs) ht
                  exact ⟨erased, by simpa [eraseNoops] using herased, by
                    have hobserve := noop_observe_empty hs
                    simpa [Abstract.boundaryTrace, Rover.trace,
                      hobserve] using htrace⟩
              | inject time call =>
                  obtain ⟨next', hnext', hsemantic⟩ :=
                    inject_transport hearlier hs
                  obtain ⟨erased, herased, htrace⟩ :=
                    ih hsemantic ht
                  refine ⟨(label, next') :: erased, ?_, ?_⟩
                  · simp [eraseNoops, replayFrom, hnext', herased]
                  · simpa [Abstract.boundaryTrace, Rover.trace] using htrace
              | process time call state outputs =>
                  obtain ⟨next', hnext', hsemantic⟩ :=
                    process_transport hearlier hs
                  obtain ⟨erased, herased, htrace⟩ :=
                    ih hsemantic ht
                  refine ⟨(label, next') :: erased, ?_, ?_⟩
                  · simp [eraseNoops, replayFrom, hnext', herased]
                  · simpa [Abstract.boundaryTrace, Rover.trace] using htrace
              | observe time sender message =>
                  obtain ⟨next', hnext', hsemantic⟩ :=
                    observe_transport hearlier hs
                  obtain ⟨erased, herased, htrace⟩ :=
                    ih hsemantic ht
                  refine ⟨(label, next') :: erased, ?_, ?_⟩
                  · simp [eraseNoops, replayFrom, hnext', herased]
                  · simpa [Abstract.boundaryTrace, Rover.trace] using htrace

theorem valid_has_noop_free_certificate {config : Config}
    {events : List BoundaryEvent}
    (hvalid : Abstract.ValidBoundaryTrace config events) :
    ∃ process certificate execution,
      AModel.init config process ∧
      replayFrom config (World.initial process) certificate =
        some execution ∧
      Abstract.boundaryTrace execution = events ∧
      eraseNoops certificate = certificate := by
  obtain ⟨process, certificate, execution, hinit, hreplay, htrace⟩ :=
    valid_has_replay_certificate hvalid
  obtain ⟨erased, hreplay', htrace'⟩ :=
    eraseNoops_replayFrom
      (semanticEarlier_refl (World.initial process)) hreplay
  refine ⟨process, eraseNoops certificate, erased, hinit, hreplay',
    htrace'.trans htrace, ?_⟩
  exact eraseNoops_idempotent certificate

/-- A create handler can only return success. The unreliable wrapper may
replace this with 503, but it can never manufacture 404. -/
theorem promiseCreate_returns_200 (id : Experiment.Ident)
    (timeoutAt : Option Time) (now : Time) :
    Experiment.Returns (Experiment.promiseCreate id timeoutAt now)
      (fun response => response.status = 200) := by
  unfold Experiment.promiseCreate
  apply Experiment.Returns.bind
  intro document
  cases document with
  | some promise =>
      apply Experiment.Returns.bind
      intro _
      exact Experiment.Returns.pure _ _ rfl
  | none =>
      apply Experiment.Returns.bind
      intro defaultTimeout
      apply Experiment.Returns.bind
      intro _
      exact Experiment.Returns.pure _ _ rfl

theorem createRequest_ne_404 (id : Experiment.Ident)
    (timeoutAt : Option Time) (now : Time) :
    Experiment.Returns
      (Experiment.request (.create id timeoutAt) now)
      (fun response => response.status ≠ 404) := by
  unfold Experiment.request
  apply Experiment.Returns.bind
  intro unreliable
  split
  · apply Experiment.Returns.bind
    intro fate
    cases fate with
    | serve =>
        intro config state result hresult
        have hstatus := promiseCreate_returns_200 id timeoutAt now
          config state result hresult
        omega
    | shed =>
        exact Experiment.Returns.pure _ _ (by decide)
    | lose =>
        apply Experiment.Returns.bind
        intro _
        exact Experiment.Returns.pure _ _ (by decide)
  · intro config state result hresult
    have hstatus := promiseCreate_returns_200 id timeoutAt now
      config state result hresult
    omega

/-- Internal create-handler effects are notifications and assertions, never
response messages. The response is appended once by `receive`. -/
def noResponseMessages (outputs : List (Experiment.Out Experiment.Msg)) : Prop :=
  ∀ client id response,
    .send client (.res id response) ∉ outputs

def emitsNoResponses (handler : Experiment.Handler α) : Prop :=
  ∀ config state result, result ∈ (handler config state).val →
    noResponseMessages result.2.2

theorem emitsNoResponses_pure (value : α) :
    emitsNoResponses (Pure.pure value : Experiment.Handler α) := by
  intro config state result hresult
  change result ∈ [(value, state, [])] at hresult
  simp only [List.mem_singleton] at hresult
  subst result
  simp [noResponseMessages]

theorem emitsNoResponses_bind {first : Experiment.Handler α}
    {next : α → Experiment.Handler β}
    (hfirst : emitsNoResponses first)
    (hnext : ∀ value, emitsNoResponses (next value)) :
    emitsNoResponses (first >>= next) := by
  intro config state result hresult
  simp only [Bind.bind, Experiment.Some.bind, Experiment.Some.map,
    List.mem_flatMap, List.mem_map] at hresult
  obtain ⟨⟨value, middle, before⟩, hbefore,
    ⟨answer, after, later⟩, hlater, rfl⟩ := hresult
  intro client id response hmember
  simp only [List.mem_append] at hmember
  cases hmember with
  | inl h =>
      exact hfirst config state _ hbefore client id response h
  | inr h =>
      exact hnext value config middle _ hlater client id response h

theorem emitsNoResponses_lookup (id : Experiment.Ident) :
    emitsNoResponses (Experiment.lookup id) := by
  simp [emitsNoResponses, noResponseMessages, Experiment.lookup,
    Experiment.Some.one]

theorem emitsNoResponses_readDefaultTimeout :
    emitsNoResponses Experiment.readDefaultTimeout := by
  simp [emitsNoResponses, noResponseMessages,
    Experiment.readDefaultTimeout, Experiment.Some.one]

theorem emitsNoResponses_save (promise : Promise) :
    emitsNoResponses (Experiment.save promise) := by
  intro config state result hresult
  change result ∈ [((), {
    promises := promise :: state.promises.filter (·.id != promise.id)
  }, [])] at hresult
  simp only [List.mem_singleton] at hresult
  subst result
  simp [noResponseMessages]

theorem emitsNoResponses_always (name : String) (ok : Bool) :
    emitsNoResponses (Experiment.always name ok) := by
  simp [emitsNoResponses, noResponseMessages, Experiment.always,
    Experiment.emit, Experiment.Some.one]

theorem emitsNoResponses_sometimes (name : String) (hit : Bool) :
    emitsNoResponses (Experiment.sometimes name hit) := by
  simp [emitsNoResponses, noResponseMessages, Experiment.sometimes,
    Experiment.emit, Experiment.Some.one]

theorem emitsNoResponses_notify (client : Experiment.Addr)
    (record : Experiment.Record) :
    emitsNoResponses (Experiment.send client (.notify record)) := by
  simp [emitsNoResponses, noResponseMessages, Experiment.send,
    Experiment.emit, Experiment.Some.one]

theorem emitsNoResponses_notifyAll (record : Experiment.Record) :
    ∀ clients, emitsNoResponses (Experiment.notifyAll record clients)
  | [] => emitsNoResponses_pure ()
  | client :: rest =>
      emitsNoResponses_bind (emitsNoResponses_notify client record)
        (fun _ => emitsNoResponses_notifyAll record rest)

theorem emitsNoResponses_settle (promise : Promise)
    (state : PromiseState) (value : String) :
    emitsNoResponses (Experiment.settle promise state value) := by
  unfold Experiment.settle
  apply emitsNoResponses_bind (emitsNoResponses_always _ _)
  intro _
  apply emitsNoResponses_bind (emitsNoResponses_always _ _)
  intro _
  apply emitsNoResponses_bind (emitsNoResponses_save _)
  intro _
  apply emitsNoResponses_bind (emitsNoResponses_notifyAll _ _)
  intro _
  exact emitsNoResponses_pure _

theorem emitsNoResponses_load (id : Experiment.Ident) (now : Time) :
    emitsNoResponses (Experiment.load id now) := by
  unfold Experiment.load
  apply emitsNoResponses_bind (emitsNoResponses_lookup id)
  intro document
  cases document with
  | none =>
      change emitsNoResponses
        (Pure.pure none : Experiment.Handler (Option Promise))
      exact emitsNoResponses_pure _
  | some promise =>
      change emitsNoResponses
        (if promise.state == .pending && decide (promise.timeoutAt ≤ now) then
          do
            let settled ←
              Experiment.settle promise .rejectedTimedout ""
            return some settled
         else
          (Pure.pure (some promise) :
            Experiment.Handler (Option Promise)))
      split
      · apply emitsNoResponses_bind
          (emitsNoResponses_settle promise .rejectedTimedout "")
        intro _
        exact emitsNoResponses_pure _
      · exact emitsNoResponses_pure _

theorem emitsNoResponses_promiseCreate (id : Experiment.Ident)
    (timeoutAt : Option Time) (now : Time) :
    emitsNoResponses (Experiment.promiseCreate id timeoutAt now) := by
  unfold Experiment.promiseCreate
  apply emitsNoResponses_bind (emitsNoResponses_load id now)
  intro document
  cases document with
  | some promise =>
      apply emitsNoResponses_bind (emitsNoResponses_sometimes _ _)
      intro _
      exact emitsNoResponses_pure _
  | none =>
      apply emitsNoResponses_bind emitsNoResponses_readDefaultTimeout
      intro defaultTimeout
      apply emitsNoResponses_bind (emitsNoResponses_save _)
      intro _
      exact emitsNoResponses_pure _

theorem emitsNoResponses_promiseGet (id : Experiment.Ident) (now : Time) :
    emitsNoResponses (Experiment.promiseGet id now) := by
  unfold Experiment.promiseGet
  apply emitsNoResponses_bind (emitsNoResponses_load id now)
  intro document
  cases document <;> exact emitsNoResponses_pure _

theorem emitsNoResponses_promiseSettle (id : Experiment.Ident)
    (state : PromiseState) (value : String) (now : Time) :
    emitsNoResponses (Experiment.promiseSettle id state value now) := by
  unfold Experiment.promiseSettle
  split
  · exact emitsNoResponses_pure _
  · apply emitsNoResponses_bind (emitsNoResponses_pure ())
    intro _
    apply emitsNoResponses_bind (emitsNoResponses_load id now)
    intro document
    cases document with
    | none =>
        change emitsNoResponses
          (Pure.pure { status := 404 } :
            Experiment.Handler Response)
        exact emitsNoResponses_pure _
    | some promise =>
        change emitsNoResponses
          (if promise.state == .pending then
            do
              let settled ← Experiment.settle promise state value
              return Experiment.ok settled
           else
            do
              Experiment.sometimes
                "settle arrives after the timeout"
                (promise.state == .rejectedTimedout)
              return Experiment.ok promise)
        split
        · apply emitsNoResponses_bind
            (emitsNoResponses_settle promise state value)
          intro _
          exact emitsNoResponses_pure _
        · apply emitsNoResponses_bind (emitsNoResponses_sometimes _ _)
          intro _
          exact emitsNoResponses_pure _

theorem emitsNoResponses_promiseListen (id : Experiment.Ident)
    (address : Addr) (now : Time) :
    emitsNoResponses (Experiment.promiseListen id address now) := by
  unfold Experiment.promiseListen
  apply emitsNoResponses_bind (emitsNoResponses_load id now)
  intro document
  cases document with
  | none =>
      change emitsNoResponses
        (Pure.pure { status := 404 } : Experiment.Handler Response)
      exact emitsNoResponses_pure _
  | some promise =>
      change emitsNoResponses
        (if promise.state == .pending &&
            !promise.listeners.contains address then
          let next := {
            promise with listeners := promise.listeners ++ [address]
          }
          do
            Experiment.save next
            return Experiment.ok next
         else
          Pure.pure (Experiment.ok promise))
      split
      · apply emitsNoResponses_bind (emitsNoResponses_save _)
        intro _
        exact emitsNoResponses_pure _
      · exact emitsNoResponses_pure _

theorem emitsNoResponses_dispatch (request : Request) (now : Time) :
    emitsNoResponses (Experiment.dispatch request now) := by
  cases request with
  | get id => exact emitsNoResponses_promiseGet id now
  | create id timeoutAt =>
      exact emitsNoResponses_promiseCreate id timeoutAt now
  | settle id state value =>
      exact emitsNoResponses_promiseSettle id state value now
  | listen id address =>
      exact emitsNoResponses_promiseListen id address now

theorem emitsNoResponses_request (request : Request) (now : Time) :
    emitsNoResponses (Experiment.request request now) := by
  unfold Experiment.request
  apply emitsNoResponses_bind
  · simp [emitsNoResponses, noResponseMessages,
      Experiment.readUnreliable, Experiment.Some.one]
  intro unreliable
  split
  · apply emitsNoResponses_bind
    · simp [emitsNoResponses, noResponseMessages, Experiment.choose,
        Experiment.Some.map]
    intro fate
    cases fate with
    | serve => exact emitsNoResponses_dispatch request now
    | shed => exact emitsNoResponses_pure _
    | lose =>
        apply emitsNoResponses_bind (emitsNoResponses_dispatch request now)
        intro _
        exact emitsNoResponses_pure _
  · exact emitsNoResponses_dispatch request now

theorem emitsNoResponses_createRequest (id : Experiment.Ident)
    (timeoutAt : Option Time) (now : Time) :
    emitsNoResponses (Experiment.request (.create id timeoutAt) now) := by
  unfold Experiment.request
  apply emitsNoResponses_bind
  · simp [emitsNoResponses, noResponseMessages,
      Experiment.readUnreliable, Experiment.Some.one]
  intro unreliable
  split
  · apply emitsNoResponses_bind
    · simp [emitsNoResponses, noResponseMessages, Experiment.choose,
        Experiment.Some.map]
    intro fate
    cases fate with
    | serve => exact emitsNoResponses_promiseCreate id timeoutAt now
    | shed => exact emitsNoResponses_pure _
    | lose =>
        apply emitsNoResponses_bind
          (emitsNoResponses_promiseCreate id timeoutAt now)
        intro _
        exact emitsNoResponses_pure _
  · exact emitsNoResponses_promiseCreate id timeoutAt now

theorem outputs_response_source {raw : List (Experiment.Out Experiment.Msg)}
    {client : Addr} {id : CallId} {response : Response}
    (h : .response client id response ∈ Resonate.outputs raw) :
    Experiment.Out.send client (.res id response) ∈ raw := by
  induction raw with
  | nil => simp [Resonate.outputs] at h
  | cons output rest ih =>
      cases output with
      | always name ok =>
          simp only [Resonate.outputs, List.filterMap_cons] at h
          exact List.mem_cons_of_mem _ (ih h)
      | sometimes name hit =>
          simp only [Resonate.outputs, List.filterMap_cons] at h
          exact List.mem_cons_of_mem _ (ih h)
      | send recipient message =>
          cases message with
          | req callId now request =>
              simp only [Resonate.outputs, List.filterMap_cons] at h
              exact List.mem_cons_of_mem _ (ih h)
          | notify record =>
              simp only [Resonate.outputs, List.filterMap_cons,
                List.mem_cons] at h
              cases h with
              | inl heq => contradiction
              | inr hrest =>
                  exact List.mem_cons_of_mem _ (ih hrest)
          | res callId result =>
              simp only [Resonate.outputs, List.filterMap_cons,
                List.mem_cons, Output.response.injEq] at h
              cases h with
              | inl heq =>
                  obtain ⟨rfl, rfl, rfl⟩ := heq
                  exact List.mem_cons_self
              | inr hrest =>
                  exact List.mem_cons_of_mem _ (ih hrest)

theorem run_response_identity (config : Config) (call : Call)
    (before after : State) (outputs : List Output)
    (hrun : (after, outputs) ∈ (Resonate.run config call before).val)
    {client : Addr} {callId : CallId} {response : Response}
    (houtput : .response client callId response ∈ outputs) :
    client = call.client ∧ callId = call.id := by
  simp only [Resonate.run, List.mem_map] at hrun
  obtain ⟨⟨next, rawOutputs⟩, hstep, heq⟩ := hrun
  cases heq
  simp only [Experiment.Service.step, Experiment.promises,
    Experiment.receive, Experiment.H.run, Experiment.Some.map,
    List.mem_map] at hstep
  obtain ⟨⟨ignored, next', internal⟩, hrequest, heq⟩ := hstep
  cases heq
  simp only [Bind.bind, Experiment.Some.bind, Experiment.Some.map,
    List.mem_flatMap, List.mem_map] at hrequest
  obtain ⟨⟨result, middle, emitted⟩, hresult,
    ⟨unit', final, sent⟩, hsend, heq⟩ := hrequest
  simp only [Experiment.send, Experiment.emit, Experiment.Some.one,
    List.mem_singleton] at hsend
  cases hsend
  cases heq
  simp only [Resonate.outputs, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil,
    List.mem_append, List.mem_singleton] at houtput
  cases houtput with
  | inl h =>
      have hraw :=
        outputs_response_source (client := client) (id := callId)
          (response := response) h
      have hnone := emitsNoResponses_request call.request call.requestedAt
        config before (result, middle, emitted) hresult
      exact (hnone client callId response hraw).elim
  | inr h =>
      have heq : client = call.client ∧ callId = call.id ∧
          response = result := by
        simpa using h
      exact ⟨heq.1, heq.2.1⟩

theorem createRun_no_404 (config : Config) (client : Addr) (callId : CallId)
    (requestedAt : Time) (promiseId : Experiment.Ident)
    (timeoutAt : Option Time) (before after : State) (outputs : List Output)
    (hrun : (after, outputs) ∈
      (Resonate.run config {
        client
        id := callId
        requestedAt
        request := .create promiseId timeoutAt
      } before).val) :
    ∀ response, response.status = 404 →
      .response client callId response ∉ outputs := by
  simp only [Resonate.run, List.mem_map] at hrun
  obtain ⟨⟨next, rawOutputs⟩, hstep, heq⟩ := hrun
  cases heq
  simp only [Experiment.Service.step, Experiment.promises,
    Experiment.receive, Experiment.H.run, Experiment.Some.map,
    List.mem_map] at hstep
  obtain ⟨⟨ignored, next', internal⟩, hrequest, heq⟩ := hstep
  cases heq
  simp only [Bind.bind, Experiment.Some.bind, Experiment.Some.map,
    List.mem_flatMap, List.mem_map] at hrequest
  obtain ⟨⟨response, middle, emitted⟩, hresponse,
    ⟨unit', final, sent⟩, hsend, heq⟩ := hrequest
  simp only [Experiment.send, Experiment.emit, Experiment.Some.one,
    List.mem_singleton] at hsend
  cases hsend
  cases heq
  intro bad hstatus hmember
  have hbad : response.status ≠ 404 :=
    createRequest_ne_404 promiseId timeoutAt requestedAt
      config before (response, middle, emitted) hresponse
  have hinternal :=
    emitsNoResponses_createRequest promiseId timeoutAt requestedAt
      config before (response, middle, emitted) hresponse
  simp only [Resonate.outputs, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil,
    List.mem_append, List.mem_singleton] at hmember
  cases hmember with
  | inl h =>
      have hraw :=
        outputs_response_source (client := client) (id := callId)
          (response := bad) h
      exact hinternal client callId bad hraw
  | inr h =>
      have heq : response = bad := by
        simpa using h.symm
      subst bad
      exact hbad hstatus

theorem createRun_no_404_of_request (config : Config) (call : Call)
    (promiseId : Experiment.Ident) (timeoutAt : Option Time)
    (before after : State) (outputs : List Output)
    (hrequest : call.request = .create promiseId timeoutAt)
    (hrun : (after, outputs) ∈ (Resonate.run config call before).val) :
    ∀ response, response.status = 404 →
      .response call.client call.id response ∉ outputs := by
  obtain ⟨client, id, requestedAt, request⟩ := call
  simp only at hrequest
  subst request
  exact createRun_no_404 config client id requestedAt promiseId timeoutAt
    before after outputs hrun

structure SearchContext where
  state : State
  calls : List Call
  available : List Output
  now : Time
  certificate : Certificate
  /-- Semantic contexts already seen while searching for the current visible
  output. Certificates and time are intentionally absent: hidden processing
  is at that output's time, and neither affects future protocol behavior. -/
  visited : List (State × List Output)

def outputEvent (time : Time) : Output → BoundaryEvent
  | .response client id response => .response time client id response
  | .notification client record => .notification time client record

/-- Whether an output can discharge a visible event, ignoring the event time.
The observation itself supplies that time. -/
def outputMatches : Output → BoundaryEvent → Bool
  | .response client id response, .response _ client' id' response' =>
      client == client' && id == id' && response == response'
  | .notification client record, .notification _ client' record' =>
      client == client' && record == record'
  | _, _ => false

/-- Keep only outputs that can still be observed. Since Rover's network is
append-only and observation is non-consuming, one copy of an output satisfies
any remaining multiplicity of the same observation. Thus `eraseDups` is the
tight multiplicity cap for this promise model. -/
def normalizeAvailable (events : List BoundaryEvent)
    (available : List Output) : List Output :=
  (available.filter fun output =>
    events.any fun event => outputMatches output event).eraseDups

def semanticContext (context : SearchContext) : State × List Output :=
  (context.state, context.available)

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
              available := normalizeAvailable rest context.available
              now := time
              certificate := context.certificate ++
                [.observe time .service (.output output)]
              visited := []
            }, rest)
          else none
      else []

/-- Hidden abstract processing. It consumes fuel but no boundary event; any
generated output may be observed later, in any order, or not at all. -/
def processCandidates (config : Config) (context : SearchContext)
    (events : List BoundaryEvent) (time : Time) : List SearchContext :=
  if context.now ≤ time then
    context.calls.flatMap fun call =>
      (Resonate.run config call context.state).val.filterMap fun outcome =>
        let state := outcome.1
        let outputs := outcome.2
        let next : SearchContext := {
          state
          calls := context.calls
          available :=
            normalizeAvailable events (context.available ++ outputs)
          now := time
          certificate := context.certificate ++
            [.process time call state outputs]
          visited := semanticContext context :: context.visited
        }
        let key := semanticContext next
        if key = semanticContext context || key ∈ context.visited then
          none
        else
          some next
  else
    []

inductive BranchResult where
  | valid (certificate : Certificate)
  | invalid
  | unknown

/-- Disjunction over branches. A witness dominates every other result;
otherwise one cutoff makes the whole disjunction unknown, and only a list of
definitive refutations is invalid. -/
def explore (values : List α) (f : α → BranchResult) : BranchResult :=
  match values with
  | [] => .invalid
  | value :: rest =>
      match f value with
      | .valid certificate => .valid certificate
      | .invalid => explore rest f
      | .unknown =>
          match explore rest f with
          | .valid certificate => .valid certificate
          | _ => .unknown

/-- Bounded branching search over normalized semantic contexts. Hidden
timeouts and inert receives are erased; irrelevant output history is removed;
append-only duplicate outputs are saturated at one; and hidden cycles at the
same visible event are skipped. Every retained recursive edge consumes fuel. -/
def searchFrom (config : Config) :
    Nat → SearchContext → List BoundaryEvent → BranchResult
  | 0, context, events =>
      if events.isEmpty then .valid context.certificate else .unknown
  | _ + 1, context, [] => .valid context.certificate
  | fuel + 1, context, (.request time call) :: rest =>
      if context.now ≤ time then
        searchFrom config fuel {
          state := context.state
          calls := context.calls ++ [call]
          available := context.available
          now := time
          certificate := context.certificate ++ [.inject time call]
          visited := []
        } rest
      else
        .invalid
  | fuel + 1, context, events@(.response _ _ _ _ :: _) =>
      let time := events.head?.map eventTime |>.getD context.now
      let observations := observeCandidates context events
      let processing :=
        (processCandidates config context events time).map fun next =>
        (next, events)
      explore (observations ++ processing) fun candidate =>
        searchFrom config fuel candidate.1 candidate.2
  | fuel + 1, context, events@(.notification _ _ _ :: _) =>
      let time := events.head?.map eventTime |>.getD context.now
      let observations := observeCandidates context events
      let processing :=
        (processCandidates config context events time).map fun next =>
        (next, events)
      explore (observations ++ processing) fun candidate =>
        searchFrom config fuel candidate.1 candidate.2

/-- Search from the initial abstract state with a caller-selected bound. -/
def search (config : Config) (bound : Nat) (events : List BoundaryEvent) :
    BranchResult :=
  searchFrom config bound {
    state := {}
    calls := []
    available := []
    now := 0
    certificate := []
    visited := []
  } events

/-- The public three-way result. Valid includes both the replay certificate and
the actual abstract Rover execution reconstructed from it. -/
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

def callIsCreate (call : Call) : Bool :=
  match call.request with
  | .create _ _ => true
  | _ => false

def nonCreateSource (calls : List Call) (client : Addr)
    (id : CallId) : Bool :=
  calls.any fun call =>
    call.client == client && call.id == id && !callIsCreate call

theorem nonCreateSource_of_mem {calls : List Call} {call : Call}
    {client : Addr} {id : CallId}
    (hcall : call ∈ calls) (hclient : call.client = client)
    (hid : call.id = id) (hcreate : callIsCreate call = false) :
    nonCreateSource calls client id = true := by
  apply List.any_eq_true.mpr
  refine ⟨call, hcall, ?_⟩
  simp [hclient, hid, hcreate]

theorem nonCreateSource_append {calls extra : List Call}
    {client : Addr} {id : CallId}
    (h : nonCreateSource calls client id = true) :
    nonCreateSource (calls ++ extra) client id = true := by
  apply List.any_eq_true.mpr
  obtain ⟨call, hcall, hmatch⟩ := List.any_eq_true.mp h
  exact ⟨call, List.mem_append_left _ hcall, hmatch⟩

/-- Necessary response-origin condition. A 404 must come from an earlier call
with the same response identity, and create calls are proved never to emit
404. Other statuses and notifications are left unconstrained here. -/
def create404SafeFrom : List Call → List BoundaryEvent → Bool
  | _, [] => true
  | calls, .request _ call :: rest =>
      create404SafeFrom (calls ++ [call]) rest
  | calls, .response _ client id response :: rest =>
      (if response.status == 404 then
        nonCreateSource calls client id
       else true) &&
      create404SafeFrom calls rest
  | calls, .notification _ _ _ :: rest =>
      create404SafeFrom calls rest

def create404Safe (events : List BoundaryEvent) : Bool :=
  create404SafeFrom [] events

structure SupportedWorld (calls : List Call) (world : World AModel) : Prop where
  requests :
    ∀ call,
      (Abstract.Pid.outside, Abstract.Pid.service,
        Message.request call) ∈ world.network →
      call ∈ calls
  responses :
    ∀ sender client id response,
      response.status = 404 →
      (sender, Abstract.Pid.outside,
        Message.output (.response client id response)) ∈ world.network →
      nonCreateSource calls client id = true

theorem supportedWorld_initial (process : Abstract.Pid → State) :
    SupportedWorld [] (World.initial process) := by
  constructor <;> simp [World.initial]

theorem supportedWorld_step {config : Config} {calls : List Call}
    {world next : World AModel} {label : Label AModel}
    (hsupported : SupportedWorld calls world)
    (hstep : Step AModel config world label next) :
    SupportedWorld
      (match label with
       | .input .service _ (.request call) => calls ++ [call]
       | _ => calls)
      next := by
  cases hstep with
  | @inject to time message htime hprocess hinject =>
      have hto : to = Abstract.Pid.service :=
        Abstract.only_real_process hprocess
      subst to
      change ∃ call, message = Message.request call at hinject
      obtain ⟨call, rfl⟩ := hinject
      constructor
      · intro candidate hcandidate
        simp only [World.inject, List.mem_append, List.mem_singleton,
          Prod.mk.injEq, Message.request.injEq] at hcandidate
        cases hcandidate with
        | inl hold =>
            exact List.mem_append_left _ (hsupported.requests _ hold)
        | inr hnew =>
            exact List.mem_append_right _ (by simpa using hnew)
      · intro sender client id response hstatus hresponse
        simp only [World.inject, List.mem_append, List.mem_singleton] at hresponse
        cases hresponse with
        | inl hold =>
            have hs := hsupported.responses sender client id response
              hstatus hold
            exact nonCreateSource_append hs
        | inr hnew =>
            have hmessages :
                Message.output (.response client id response) =
                  Message.request call :=
              congrArg (fun entry => entry.2.2) hnew
            contradiction
  | process htime hprocess hvalid houtcome =>
      rename_i process time event result
      have hp : process = Abstract.Pid.service :=
        Abstract.only_real_process hprocess
      subst process
      change SupportedWorld calls (world.land Abstract.Pid.service time result)
      constructor
      · intro call hrequest
        simp only [World.land, List.mem_append, List.mem_map,
          Prod.mk.injEq] at hrequest
        cases hrequest with
        | inl hold => exact hsupported.requests _ hold
        | inr hnew =>
            obtain ⟨sent, _, heq⟩ := hnew
            cases heq.1
      · intro sender client id response hstatus hresponse
        simp only [World.land, List.mem_append, List.mem_map,
          Prod.mk.injEq] at hresponse
        cases hresponse with
        | inl hold =>
            exact hsupported.responses sender client id response hstatus hold
        | inr hnew =>
            cases event with
            | timeout =>
                simp [Abstract.step, Outcomes.one] at houtcome
                subst result
                simp at hnew
            | receive sender message =>
                cases sender with
                | service =>
                    simp [Abstract.step, Outcomes.one] at houtcome
                    subst result
                    simp at hnew
                | outside =>
                    cases message with
                    | output output =>
                        simp [Abstract.step, Outcomes.one] at houtcome
                        subst result
                        simp at hnew
                    | request call =>
                        simp only [Abstract.step, List.mem_map] at houtcome
                        obtain ⟨⟨after, outputs⟩, hrun, heq⟩ := houtcome
                        subst result
                        obtain ⟨sent, hsent, heq⟩ := hnew
                        obtain ⟨_, hrecipient, hmessage⟩ := heq
                        have houtput :
                            Output.response client id response ∈ outputs := by
                          simp only [List.mem_map] at hsent
                          obtain ⟨output, houtput, hsentEq⟩ := hsent
                          rw [← hsentEq] at hmessage
                          simp only [Message.output.injEq] at hmessage
                          subst output
                          exact houtput
                        have hid := run_response_identity config call
                          (world.process Abstract.Pid.service) after outputs
                          hrun houtput
                        have hcall := hsupported.requests call hvalid
                        cases hr : call.request with
                        | get key =>
                            exact nonCreateSource_of_mem hcall hid.1.symm
                              hid.2.symm (by simp [callIsCreate, hr])
                        | settle key state value =>
                            exact nonCreateSource_of_mem hcall hid.1.symm
                              hid.2.symm (by simp [callIsCreate, hr])
                        | listen key address =>
                            exact nonCreateSource_of_mem hcall hid.1.symm
                              hid.2.symm (by simp [callIsCreate, hr])
                        | create promiseId timeoutAt =>
                            have hnone := createRun_no_404_of_request config
                              call promiseId timeoutAt
                              (world.process Abstract.Pid.service) after outputs
                              hr hrun
                              response hstatus
                            exact (hnone
                              (by simpa [hid.1, hid.2] using houtput)).elim
  | @outside sender time message htime hmessage =>
      constructor
      · exact hsupported.requests
      · exact hsupported.responses

theorem legal_create404SafeFrom {config : Config} {calls : List Call}
    {world : World AModel} {execution : Execution AModel}
    (hsupported : SupportedWorld calls world)
    (hlegal : Legal AModel config world execution) :
    create404SafeFrom calls (Abstract.boundaryTrace execution) = true := by
  induction execution generalizing calls world with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨hstep, hrest⟩ := hlegal
      have hsnext := supportedWorld_step hsupported hstep
      have htail := ih hsnext hrest
      cases hstep with
      | inject htime hprocess hinject =>
          have hto : _ = Abstract.Pid.service :=
            Abstract.only_real_process hprocess
          subst hto
          change ∃ call, _ = Message.request call at hinject
          obtain ⟨call, rfl⟩ := hinject
          simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
            Abstract.boundaryEvent, Message.observeInput,
            create404SafeFrom] using htail
      | process htime hprocess hvalid houtcome =>
          simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
            Abstract.boundaryEvent] using htail
      | outside htime hmessage =>
          rename_i sender time message
          cases message with
          | request call =>
              simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                Abstract.boundaryEvent, Message.observeOutput] using htail
          | output output =>
              cases output with
              | notification client record =>
                  simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                    Abstract.boundaryEvent, Message.observeOutput,
                    create404SafeFrom] using htail
              | response client id response =>
                  by_cases hstatus : response.status = 404
                  · have hsource := hsupported.responses sender client id
                      response hstatus hmessage
                    simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                      Abstract.boundaryEvent, Message.observeOutput,
                      create404SafeFrom, hstatus, hsource] using htail
                  · have hstatus' : (response.status == 404) = false :=
                      beq_eq_false_iff_ne.mpr hstatus
                    simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                      Abstract.boundaryEvent, Message.observeOutput,
                      create404SafeFrom, hstatus'] using htail

theorem valid_create404Safe {config : Config}
    {events : List BoundaryEvent}
    (hvalid : Abstract.ValidBoundaryTrace config events) :
    create404Safe events = true := by
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := hvalid
  subst events
  exact legal_create404SafeFrom (supportedWorld_initial process) hlegal

/-- One necessary trace invariant used to turn exhausted search into a proved
`Invalid`. Ordered exhaustion which satisfies every proved refutation
invariant remains `Unknown`. -/
def orderedFrom : Time → List BoundaryEvent → Bool
  | _, [] => true
  | now, event :: rest =>
      decide (now ≤ eventTime event) && orderedFrom (eventTime event) rest

/-- Search and independently replay any successful certificate. -/
def checkWithBound (bound : Nat) (config : Config)
    (events : List BoundaryEvent) : Verdict :=
  match search config bound events with
  | .valid certificate =>
      match replay config events certificate with
      | some execution => .valid certificate execution
      | none => .unknown
  | .invalid =>
      if orderedFrom 0 events && create404Safe events then
        .unknown
      else
        .invalid
  | .unknown => .unknown

def defaultBound (events : List BoundaryEvent) : Nat :=
  events.length * 3 + 1

def check (config : Config) (events : List BoundaryEvent) : Verdict :=
  checkWithBound (defaultBound events) config events

theorem orderedFrom_weaken {earlier later : Time}
    {events : List BoundaryEvent} (h : earlier ≤ later)
    (ho : orderedFrom later events = true) :
    orderedFrom earlier events = true := by
  cases events with
  | nil => rfl
  | cons event rest =>
      simp only [orderedFrom, Bool.and_eq_true, decide_eq_true_eq] at ho ⊢
      exact ⟨Nat.le_trans h ho.1, ho.2⟩

/-- Every legal abstract Rover execution has monotone filtered boundary time,
including across hidden process and timeout steps. -/
theorem legal_boundary_ordered {config : Config} {world : World AModel}
    {execution : Execution AModel}
    (h : Legal AModel config world execution) :
    orderedFrom world.now (Abstract.boundaryTrace execution) = true := by
  induction execution generalizing world with
  | nil =>
      simp [Abstract.boundaryTrace, Rover.trace, orderedFrom]
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨hstep, hrest⟩ := h
      have htail := ih hrest
      cases hstep with
      | inject htime hprocess hinject =>
          have hto : _ = Abstract.Pid.service :=
            Abstract.only_real_process hprocess
          subst hto
          change ∃ call, _ = Message.request call at hinject
          obtain ⟨call, rfl⟩ := hinject
          simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
            Abstract.boundaryEvent, Message.observeInput, orderedFrom,
            eventTime, World.inject, htime] using htail
      | process htime hprocess hvalid houtcome =>
          apply orderedFrom_weaken htime
          simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
            World.land] using htail
      | outside htime hmessage =>
          rename_i sender time message
          cases message with
          | request call =>
              apply orderedFrom_weaken htime
              simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                Abstract.boundaryEvent, Message.observeOutput,
                World.observeOutside] using htail
          | output output =>
              cases output <;>
                simpa [Abstract.boundaryTrace, Rover.trace, Label.observe,
                  Abstract.boundaryEvent, Message.observeOutput, orderedFrom,
                  eventTime, World.observeOutside, htime] using htail

theorem valid_boundary_ordered {config : Config}
    {events : List BoundaryEvent}
    (h : Abstract.ValidBoundaryTrace config events) :
    orderedFrom 0 events = true := by
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := h
  subst events
  exact legal_boundary_ordered hlegal

theorem check_valid_sound {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : check config events = .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events := by
  simp only [check, checkWithBound] at h
  cases hs : search config (defaultBound events) events with
  | invalid =>
      simp only [hs] at h
      split at h <;> contradiction
  | unknown =>
      simp [hs] at h
  | valid found =>
      simp only [hs] at h
      cases hr : replay config events found with
      | none =>
          simp [hr] at h
      | some replayed =>
          simp only [hr] at h
          cases h
          exact replay_valid hr

theorem check_sound {config : Config} {events : List BoundaryEvent}
    {certificate : Certificate} {execution : Execution AModel}
    (h : check config events = .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events :=
  check_valid_sound h

theorem checkWithBound_valid_sound {bound : Nat} {config : Config}
    {events : List BoundaryEvent} {certificate : Certificate}
    {execution : Execution AModel}
    (h : checkWithBound bound config events =
      .valid certificate execution) :
    Abstract.ValidBoundaryTrace config events := by
  simp only [checkWithBound] at h
  cases hs : search config bound events with
  | invalid =>
      simp only [hs] at h
      split at h <;> contradiction
  | unknown =>
      simp [hs] at h
  | valid found =>
      simp only [hs] at h
      cases hr : replay config events found with
      | none =>
          simp [hr] at h
      | some replayed =>
          simp only [hr] at h
          cases h
          exact replay_valid hr

/-- `Invalid` is definitive. Search exhaustion alone is not trusted: the
checker emits this verdict only when an independently proved necessary
trace invariant is violated. -/
theorem checkWithBound_invalid_sound {bound : Nat} {config : Config}
    {events : List BoundaryEvent}
    (h : checkWithBound bound config events = .invalid) :
    ¬ Abstract.ValidBoundaryTrace config events := by
  intro hvalid
  have hordered := valid_boundary_ordered hvalid
  have hcreate := valid_create404Safe hvalid
  simp only [checkWithBound] at h
  cases hs : search config bound events with
  | valid certificate =>
      simp only [hs] at h
      cases hr : replay config events certificate <;> simp [hr] at h
  | unknown =>
      simp [hs] at h
  | invalid =>
      simp only [hs] at h
      rw [hordered, hcreate] at h
      contradiction

theorem check_invalid_sound {config : Config}
    {events : List BoundaryEvent}
    (h : check config events = .invalid) :
    ¬ Abstract.ValidBoundaryTrace config events :=
  checkWithBound_invalid_sound h

/-- Equivalent contrapositive form: a semantically valid trace is never
classified as invalid, at any resource bound. -/
theorem valid_ne_invalid {bound : Nat} {config : Config}
    {events : List BoundaryEvent}
    (hvalid : Abstract.ValidBoundaryTrace config events) :
    checkWithBound bound config events ≠ .invalid := by
  intro h
  exact checkWithBound_invalid_sound h hvalid

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

#guard (check {} createTrace).isValid

def wrongCreateTrace : List BoundaryEvent := [
  .request 0 createCall,
  .response 1 "client-a" 1 { status := 404 }
]

#guard (check {} wrongCreateTrace).isInvalid

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

#guard (check {} overlappingTrace).isValid

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

#guard (check {} reversedObservationTrace).isValid

/-- Boundary time cannot go backwards. -/
def nonmonotoneTrace : List BoundaryEvent := [
  .request 2 createCall,
  .response 1 "client-a" 1 createResponse
]

#guard (check {} nonmonotoneTrace).isInvalid

-- A resource bound of zero cannot inspect this valid nonempty trace.
#guard (checkWithBound 0 {} createTrace).isUnknown

end Resonate.TraceChecker
