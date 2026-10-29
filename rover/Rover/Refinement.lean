import Rover.Abstract.Model
import Rover.Concrete.Model

/-!
# Concrete-to-abstract Rover refinement

The simulation keeps the concrete store equal to the single abstract process.
It also records the causal fact needed by an append-only network: every
internal message carrying a call is backed by the corresponding injectable
request in the abstract network. A successful conditional write is the sole
linearization point. All loads, snapshots, conflicts, retries, timeouts, and
duplicate deliveries are hidden stuttering steps.
-/

namespace Rover.Refinement

open Protocol

abbrev AModel := Abstract.model
abbrev CModel (nodes : List Addr) (appConfig : Protocol.Config) :=
  Concrete.model nodes appConfig

structure Related (nodes : List Addr) (appConfig : Protocol.Config)
    (concrete : World (CModel nodes appConfig))
    (abstract : World AModel) : Prop where
  time : abstract.now ≤ concrete.now
  store : ∃ version,
    concrete.process .store =
      .store (abstract.process .service) version
  known : ∀ {sender recipient message call},
    (sender, recipient, message) ∈ concrete.network →
    Concrete.Msg.call? message = some call →
    (Abstract.Pid.outside, Abstract.Pid.service, Message.request call) ∈
      abstract.network

theorem result_sent_call
    {appConfig : Protocol.Config} {config : Concrete.Config}
    {pid : Concrete.Pid} {localState : Concrete.Local} {time : Time}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid} {message : Concrete.Msg appConfig} {call : Call}
    (hresult : result ∈
      (Concrete.step appConfig config pid localState time event).val)
    (hsend : (recipient, message) ∈ result.send)
    (hcall : Concrete.Msg.call? message = some call) :
    ∃ sender incoming,
      event = .receive sender incoming ∧
      Concrete.Msg.call? incoming = some call := by
  cases event with
  | timeout =>
      cases pid <;> cases localState <;>
        simp_all [Concrete.step, Outcomes.one]
  | receive sender incoming =>
      refine ⟨sender, incoming, rfl, ?_⟩
      cases pid <;> cases localState <;> cases sender <;>
        cases incoming <;>
        grind [Concrete.step, Concrete.candidateResults,
          Concrete.Msg.call?, Outcomes.one]

theorem known_after_land
    {nodes : List Addr} {appConfig : Protocol.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)} {abstract : World AModel}
    {pid : Concrete.Pid} {time : Time}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (related : Related nodes appConfig concrete abstract)
    (hvalid : event.Valid concrete pid)
    (hresult : result ∈
      (Concrete.step appConfig config pid (concrete.process pid) time event).val) :
    ∀ {sender recipient message call},
      (sender, recipient, message) ∈ (concrete.land pid time result).network →
      Concrete.Msg.call? message = some call →
      (Abstract.Pid.outside, Abstract.Pid.service, Message.request call) ∈
        abstract.network := by
  intro sender recipient message call hmem hcall
  change (sender, recipient, message) ∈
    (concrete.network :
      List (Concrete.Pid × Concrete.Pid × Concrete.Msg appConfig)) ++
      result.send.map (fun pair => (pid, pair.1, pair.2)) at hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · exact related.known hold hcall
  · obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp hnew
    obtain ⟨target, sent⟩ := pair
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl, rfl⟩ := heq
    obtain ⟨origin, incoming, rfl, hincoming⟩ :=
      result_sent_call hresult hpair hcall
    exact related.known hvalid hincoming

theorem server_result_internal
    {appConfig : Protocol.Config} {config : Concrete.Config}
    {address : Addr} {localState : Concrete.Local} {time : Time}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult : result ∈
      (Concrete.step appConfig config (.server address) localState time event).val) :
    result.send = [] ∨
      ∃ message, result.send = [(.store, message)] := by
  cases localState <;> cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender incoming =>
      cases sender <;> cases incoming <;>
        grind [Concrete.step, Concrete.candidateResults, Outcomes.one]

theorem store_result_classify
    {appConfig : Protocol.Config} {config : Concrete.Config}
    {state : State} {version time : Nat}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult : result ∈
      (Concrete.step appConfig config .store (.store state version) time event).val) :
    (∃ server candidate,
      event = .receive (.server server) (.cas candidate) ∧
      config.conditional = true ∧ candidate.version = version ∧
      candidate.before = state ∧
      result = {
        state := .store candidate.after (version + 1)
        send := candidate.outputs.map fun output =>
          (.outside, .output output) }) ∨
    (result.state = .store state version ∧
      (result.send = [] ∨
        ∃ server message, result.send = [(.server server, message)])) := by
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender incoming =>
      cases sender <;> cases incoming <;>
        grind [Concrete.step, Outcomes.one]

def concreteObservation {nodes : List Addr} {appConfig : Protocol.Config}
    (label : Label (CModel nodes appConfig)) : List Protocol.BoundaryEvent :=
  label.observe.filterMap (Concrete.boundaryEvent nodes appConfig)

def abstractObservation (label : Label AModel) :
    List Protocol.BoundaryEvent :=
  label.observe.filterMap Abstract.boundaryEvent

def labelTime {model : Model} : Label model → Time
  | .input _ time _ => time
  | .process _ time _ _ => time

def labelPid {model : Model} : Label model → model.Pid
  | .input pid _ _ => pid
  | .process pid _ _ _ => pid

theorem concrete_process_cases {nodes : List Addr}
    {appConfig : Protocol.Config} {pid : Concrete.Pid}
    (h : (CModel nodes appConfig).isProcess pid) :
    (∃ address, pid = .server address) ∨ pid = .store := by
  cases pid with
  | outside => contradiction
  | server address => exact .inl ⟨address, rfl⟩
  | store => exact .inr rfl

@[simp] theorem abstract_boundary_response (time : Time) (client : Addr)
    (id : CallId) (response : Response) :
    Abstract.boundaryEvent
      (.output .service time
        (.output (.response client id response))) =
      some (.response time client id response) := rfl

@[simp] theorem abstract_boundary_notification (time : Time) (client : Addr)
    (record : Notification) :
    Abstract.boundaryEvent
      (.output .service time
        (.output (.notification client record))) =
      some (.notification time client record) := rfl

theorem outputs_observe_same (nodes : List Addr)
    (appConfig : Protocol.Config) (time : Time)
    (abstractEvent : Event Abstract.Pid Message)
    (concreteEvent : Event Concrete.Pid (Concrete.Msg appConfig))
    (outputs : List Output) :
    abstractObservation
        (.process .service time abstractEvent
          (outputs.map fun output =>
            (Abstract.Pid.outside, Message.output output))) =
      concreteObservation
        (nodes := nodes) (appConfig := appConfig)
        (.process .store time concreteEvent
          (outputs.map fun output =>
            (Concrete.Pid.outside,
              Concrete.Msg.output (config := appConfig) output))) := by
  induction outputs with
  | nil =>
      rfl
  | cons output rest ih =>
      cases output with
      | response client id response =>
          change (.response time client id response) ::
              abstractObservation
                (.process .service time abstractEvent
                  (rest.map fun output =>
                    (Abstract.Pid.outside, Message.output output))) =
            (.response time client id response) ::
              concreteObservation (nodes := nodes) (appConfig := appConfig)
                (.process .store time concreteEvent
                  (rest.map fun output =>
                    (Concrete.Pid.outside,
                      Concrete.Msg.output (config := appConfig) output)))
          exact congrArg (List.cons (.response time client id response)) ih
      | notification client record =>
          change (.notification time client record) ::
              abstractObservation
                (.process .service time abstractEvent
                  (rest.map fun output =>
                    (Abstract.Pid.outside, Message.output output))) =
            (.notification time client record) ::
              concreteObservation (nodes := nodes) (appConfig := appConfig)
                (.process .store time concreteEvent
                  (rest.map fun output =>
                    (Concrete.Pid.outside,
                      Concrete.Msg.output (config := appConfig) output)))
          exact congrArg (List.cons (.notification time client record)) ih

theorem simulate_step
    {nodes : List Addr} {appConfig : Protocol.Config}
    {config : Concrete.Config} (_hconditional : config.conditional = true)
    {concrete next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    (step : Step (CModel nodes appConfig) config concrete label next) :
    ∃ abstractExecution,
      Legal AModel appConfig abstract abstractExecution ∧
      Related nodes appConfig next
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution =
        concreteObservation label := by
  let stepTime := labelTime label
  cases step with
  | inject htime hprocess hinject =>
      obtain ⟨call, rfl⟩ := hinject
      let abstractNext :=
        abstract.inject .service (.request call) stepTime
      let abstractLabel : Label AModel :=
        .input .service stepTime (.request call)
      refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, ?_⟩
      · refine ⟨Step.inject (Nat.le_trans related.time htime) rfl
          ⟨call, rfl⟩, trivial⟩
      · refine {
          time := Nat.le_refl _
          store := ?_
          known := ?_ }
        · obtain ⟨version, hstore⟩ := related.store
          exact ⟨version, hstore⟩
        · intro sender recipient message knownCall hmem hcall
          simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
          rcases hmem with hold | hnew
          · exact List.mem_append_left _ (related.known hold hcall)
          · simp only [Prod.mk.injEq] at hnew
            obtain ⟨rfl, rfl, rfl⟩ := hnew
            simp only [Concrete.Msg.call?, Option.some.injEq] at hcall
            subst knownCall
            simp [abstractNext, World.inject, endOf]
      · simp [Abstract.boundaryTrace, concreteObservation,
          abstractLabel, Rover.trace, Label.observe, Concrete.boundaryEvent,
          stepTime, labelTime]
        rfl
  | process htime hprocess hvalid hresult =>
      rcases concrete_process_cases hprocess with hserver | hstorePid
      · obtain ⟨address, rfl⟩ := hserver
        have hsend := server_result_internal (time := stepTime) hresult
        refine ⟨[], trivial, ?_, ?_⟩
        · refine {
            time := Nat.le_trans related.time htime
            store := ?_
            known := known_after_land related hvalid hresult }
          obtain ⟨version, hstore⟩ := related.store
          refine ⟨version, ?_⟩
          simpa [World.land, endOf] using hstore
        · rcases hsend with hsend | ⟨message, hsend⟩ <;>
            simp [Abstract.boundaryTrace, concreteObservation,
              Rover.trace, Label.observe, hsend]
      · cases hstorePid
        obtain ⟨version, hstore⟩ := related.store
        have hresult' := hresult
        rw [hstore] at hresult'
        rcases store_result_classify (time := stepTime) hresult' with
          hcommit | hstutter
        · obtain ⟨server, candidate, hevent, _, hcversion,
              hcbefore, rfl⟩ := hcommit
          cases hevent
          have hrequest :
              (Abstract.Pid.outside, Abstract.Pid.service,
                Message.request candidate.call) ∈ abstract.network := by
            apply related.known hvalid
            rfl
          have habstractResult :
              ({ state := candidate.after
                 send := candidate.outputs.map fun output =>
                   (Abstract.Pid.outside, Message.output output) } :
                  Result Abstract.Pid State Message) ∈
                (Abstract.step appConfig .service
                  (abstract.process .service) stepTime
                  (.receive .outside (.request candidate.call))).val := by
            simp only [Abstract.step]
            apply List.mem_map.mpr
            exact ⟨(candidate.after, candidate.outputs),
              hcbefore ▸ candidate.valid, rfl⟩
          let abstractResult : Result Abstract.Pid State Message := {
            state := candidate.after
            send := candidate.outputs.map fun output =>
              (.outside, .output output) }
          let abstractLabel : Label AModel :=
            .process .service stepTime
              (.receive .outside (.request candidate.call))
              abstractResult.send
          let abstractNext :=
            abstract.land .service stepTime abstractResult
          refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, ?_⟩
          · refine ⟨Step.process
              (Nat.le_trans related.time htime) rfl hrequest ?_, trivial⟩
            exact habstractResult
          · refine {
              time := Nat.le_refl _
              store := ?_
              known := ?_ }
            · refine ⟨version + 1, ?_⟩
              simp [World.land, abstractNext, abstractResult, endOf]
            · intro sender' recipient message call hmem hcall
              exact List.mem_append_left _
                (known_after_land related hvalid hresult hmem hcall)
          · simpa [Abstract.boundaryTrace, abstractObservation,
              abstractLabel, abstractResult, Rover.trace, stepTime,
              labelTime] using
              outputs_observe_same nodes appConfig stepTime
                (.receive .outside (.request candidate.call))
                (.receive (.server server) (.cas candidate))
                candidate.outputs
        · obtain ⟨hstate, hsend⟩ := hstutter
          refine ⟨[], trivial, ?_, ?_⟩
          · refine {
              time := Nat.le_trans related.time htime
              store := ?_
              known := known_after_land related hvalid hresult }
            exact ⟨version, by
              simpa [World.land, hstore, endOf] using hstate⟩
          · rcases hsend with hsend | ⟨server, message, hsend⟩ <;>
              simp [Abstract.boundaryTrace, concreteObservation,
                Rover.trace, Label.observe, hsend]

theorem legal_append {model : Model} {config : model.Config}
    {world : World model} {first second : Execution model}
    (hfirst : Legal model config world first)
    (hsecond : Legal model config (endOf world first) second) :
    Legal model config world (first ++ second) := by
  induction first generalizing world with
  | nil => exact hsecond
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      exact ⟨hfirst.1, ih hfirst.2 hsecond⟩

theorem endOf_append {model : Model} (world : World model)
    (first second : Execution model) :
    endOf world (first ++ second) =
      endOf (endOf world first) second := by
  induction first generalizing world with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      exact ih next

theorem abstract_boundaryTrace_append
    (first second : Execution AModel) :
    Abstract.boundaryTrace (first ++ second) =
      Abstract.boundaryTrace first ++
        Abstract.boundaryTrace second := by
  simp only [Abstract.boundaryTrace]
  rw [show Rover.trace (first ++ second) =
      Rover.trace first ++ Rover.trace second by
    induction first with
    | nil => rfl
    | cons entry rest ih =>
        obtain ⟨label, next⟩ := entry
        simp [Rover.trace, ih, List.append_assoc]]
  exact List.filterMap_append

theorem concrete_boundaryTrace_cons
    {nodes : List Addr} {appConfig : Protocol.Config}
    (label : Label (CModel nodes appConfig))
    (next : World (CModel nodes appConfig))
    (rest : Execution (CModel nodes appConfig)) :
    Concrete.boundaryTrace nodes appConfig ((label, next) :: rest) =
      concreteObservation label ++
        Concrete.boundaryTrace nodes appConfig rest := by
  simp [Concrete.boundaryTrace, concreteObservation, Rover.trace,
    List.filterMap_append]

theorem simulate_execution
    {nodes : List Addr} {appConfig : Protocol.Config}
    {config : Concrete.Config} (hconditional : config.conditional = true)
    {concrete : World (CModel nodes appConfig)}
    {execution : Execution (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    (legal : Legal (CModel nodes appConfig) config concrete execution) :
    ∃ abstractExecution,
      Legal AModel appConfig abstract abstractExecution ∧
      Related nodes appConfig (endOf concrete execution)
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution =
        Concrete.boundaryTrace nodes appConfig execution := by
  induction execution generalizing concrete abstract with
  | nil =>
      exact ⟨[], trivial, related, rfl⟩
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨abstractHead, headLegal, headRelated, headTrace⟩ :=
        simulate_step hconditional related legal.1
      obtain ⟨abstractTail, tailLegal, tailRelated, tailTrace⟩ :=
        ih headRelated legal.2
      refine ⟨abstractHead ++ abstractTail,
        legal_append headLegal tailLegal, ?_, ?_⟩
      · simpa only [endOf, endOf_append] using tailRelated
      · rw [abstract_boundaryTrace_append, headTrace, tailTrace,
          concrete_boundaryTrace_cons]

theorem initial_related
    {nodes : List Addr} {appConfig : Protocol.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    Related nodes appConfig (World.initial process)
      (World.initial Abstract.initialProcess) := by
  refine {
    time := Nat.le_refl 0
    store := ?_
    known := ?_ }
  · exact ⟨0, by
      simpa [World.initial, Abstract.initialProcess] using hinit.2.1⟩
  · intros
    contradiction

/-- End-to-end trace inclusion. For every duplicate-free server deployment,
every legal append-only concrete boundary trace is a boundary trace of the
one-process abstract promise service. -/
theorem boundary_refinement
    (nodes : List Addr) (appConfig : Protocol.Config) (config : Concrete.Config)
    (hconditional : config.conditional = true) :
    ∀ events,
      Concrete.ValidBoundaryTrace nodes appConfig config events →
      Abstract.ValidBoundaryTrace appConfig events := by
  intro events hvalid
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := hvalid
  obtain ⟨abstractExecution, abstractLegal, _, abstractTrace⟩ :=
    simulate_execution hconditional (initial_related hinit) hlegal
  exact ⟨abstractExecution,
    ⟨Abstract.initialProcess, Abstract.initialProcess_valid appConfig,
      abstractLegal⟩,
    abstractTrace.trans htrace⟩

end Rover.Refinement
