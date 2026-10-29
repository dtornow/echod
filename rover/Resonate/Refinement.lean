import Resonate.Abstract
import Resonate.Concrete
import Experiment.PromiseFrame

/-!
# Ghost validity for the concrete Resonate protocol

The concrete `put` constructor deliberately carries no semantic witness.
This file reconstructs that provenance as a ghost predicate and proves that
every raw PUT emitted by a concrete step—and therefore every raw PUT in a
reachable append-only Rover network—is a selected `Resonate.run` outcome.

Rover observes outputs through explicit, non-consuming outside receives, so
store commits may be linearized in order while acknowledgements and client
outputs are delivered later in arbitrary order.
-/

namespace Resonate.Refinement

open Rover

abbrev AModel := Abstract.model
abbrev CModel (nodes : List Addr) (appConfig : Resonate.Config) :=
  Concrete.model nodes appConfig

theorem dispatch_as_run_serve
    {config : Resonate.Config} {call : Call} {before after : State}
    {outputs : List Output}
    (h : (after, outputs) ∈
      (Resonate.dispatch { config with unreliable := true }
        call before).val) :
    (after, outputs) ∈
      (Resonate.run { config with unreliable := true } call before).val := by
  simp only [Resonate.dispatch, List.mem_map] at h
  obtain ⟨⟨response, next, outs⟩, hdispatch, heq⟩ := h
  change (next, Resonate.outputs
    (outs ++ [.send call.client (.res call.id response)])) =
      (after, outputs) at heq
  obtain ⟨rfl, rfl⟩ := heq
  simp only [Resonate.run, List.mem_map]
  refine ⟨(after, outs ++
    [.send call.client (.res call.id response)]), ?_, rfl⟩
  exact Experiment.request_step_mem
    (Experiment.dispatch_as_serve hdispatch)

theorem dispatch_as_run_lose
    {config : Resonate.Config} {call : Call} {before after : State}
    {outputs : List Output}
    (h : (after, outputs) ∈
      (Resonate.dispatch { config with unreliable := true }
        call before).val) :
    ∃ failureOutputs,
      (after, failureOutputs) ∈
        (Resonate.run { config with unreliable := true } call before).val ∧
      Concrete.unavailable call ∈ failureOutputs := by
  simp only [Resonate.dispatch, List.mem_map] at h
  obtain ⟨⟨response, next, outs⟩, hdispatch, heq⟩ := h
  change (next, Resonate.outputs
    (outs ++ [.send call.client (.res call.id response)])) =
      (after, outputs) at heq
  have hnext : next = after := congrArg Prod.fst heq
  subst next
  let failureOutputs :=
    Resonate.outputs
      (outs ++ [.send call.client (.res call.id { status := 503 })])
  refine ⟨failureOutputs, ?_, ?_⟩
  · simp only [Resonate.run, List.mem_map]
    refine ⟨(after, outs ++
      [.send call.client (.res call.id { status := 503 })]), ?_, rfl⟩
    exact Experiment.request_step_mem
      (Experiment.dispatch_as_lose hdispatch)
  · simp [failureOutputs, Resonate.outputs, Concrete.unavailable]

theorem run_shed
    (config : Resonate.Config) (call : Call) (before : State) :
    (before, [Concrete.unavailable call]) ∈
      (Resonate.run { config with unreliable := true } call before).val := by
  simp only [Resonate.run, List.mem_map]
  refine ⟨(before,
    [.send call.client (.res call.id { status := 503 })]), ?_, ?_⟩
  · exact Experiment.request_step_mem
      (Experiment.request_shed_mem config before call.request call.requestedAt)
  · simp [Resonate.outputs, Concrete.unavailable]

/-- Ghost provenance reconstructed for a raw wire PUT.  None of these fields
is part of `Concrete.StoreRequest.put`. -/
structure PutProvenance (appConfig : Resonate.Config)
    (key : Concrete.Key) (document : Promise)
    (expectedVersion : Option Concrete.Version) where
  call : Call
  loaded : Option (Promise × Concrete.Version)
  after : State
  outputs : List Output
  key_eq : Concrete.requestKey call = key
  expected_eq : loaded.map (·.2) = expectedVersion
  loaded_key : ∀ value ∈ loaded, value.1.id = key
  outcome :
    (after, outputs) ∈
      (Resonate.dispatch { appConfig with unreliable := true }
        call (Concrete.documentState loaded)).val
  document_eq :
    after.promises.find? (·.id == key) = some document
  singleton : after.promises = [document]

def ValidPut (appConfig : Resonate.Config)
    (key : Concrete.Key) (document : Promise)
    (expectedVersion : Option Concrete.Version) : Prop :=
  Nonempty (PutProvenance appConfig key document expectedVersion)

def StoreRep (store : Concrete.Store) (state : State) : Prop :=
  ∀ key, (store.document key).map (·.1) = Experiment.promiseAt state key

theorem find?_filter_store_other
    (docs : List (Concrete.Key × Promise × Concrete.Version))
    {keep drop : Concrete.Key} (h : keep ≠ drop) :
    (docs.filter (·.1 != drop)).find? (·.1 == keep) =
      docs.find? (·.1 == keep) := by
  induction docs with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.filter_cons, List.find?_cons]
      by_cases hd : entry.1 = drop
      · have hk : entry.1 ≠ keep := by
          intro he
          exact h (he.symm.trans hd)
        rw [show (entry.1 != drop) = false from bne_eq_false_iff_eq.mpr hd]
        rw [show (entry.1 == keep) = false from beq_eq_false_iff_ne.mpr hk]
        simp only [Bool.false_eq_true, if_false]
        exact ih
      · rw [show (entry.1 != drop) = true from bne_iff_ne.mpr hd]
        change (entry :: rest.filter (·.1 != drop)).find? (·.1 == keep) =
          (entry :: rest).find? (·.1 == keep)
        by_cases hk : entry.1 = keep
        · rw [List.find?_cons, List.find?_cons,
            show (entry.1 == keep) = true from beq_iff_eq.mpr hk]
        · rw [List.find?_cons, List.find?_cons,
            show (entry.1 == keep) = false from beq_eq_false_iff_ne.mpr hk]
          exact ih

theorem Store.document_commit (store : Concrete.Store)
    (key : Concrete.Key) (document : Promise) (other : Concrete.Key) :
    (store.commit key document).document other =
      if other = key then
        some (document, (store.version key).getD 0 + 1)
      else store.document other := by
  by_cases h : other = key
  · subst other
    simp [Concrete.Store.document, Concrete.Store.commit,
      Concrete.Store.version]
  · simp only [Concrete.Store.document, Concrete.Store.commit,
      List.find?_cons]
    rw [show (key == other) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]
    rw [if_neg h]
    simp only
    rw [find?_filter_store_other _ h]

def Snapshot (store : Concrete.Store) (key : Concrete.Key) :
    Option (Promise × Concrete.Version) → Prop
  | none => True
  | some (document, version) =>
      ∃ currentDocument currentVersion,
        store.document key = some (currentDocument, currentVersion) ∧
        version ≤ currentVersion ∧
        (version = currentVersion → document = currentDocument)

theorem Snapshot.of_document {store : Concrete.Store} {key : Concrete.Key}
    {loaded : Option (Promise × Concrete.Version)}
    (h : store.document key = loaded) : Snapshot store key loaded := by
  cases loaded with
  | none => trivial
  | some value =>
      obtain ⟨document, version⟩ := value
      exact ⟨document, version, h, Nat.le_refl _, fun _ => rfl⟩

theorem Snapshot.commit {store : Concrete.Store}
    {loadedKey writtenKey : Concrete.Key}
    {loaded : Option (Promise × Concrete.Version)} {written : Promise}
    (h : Snapshot store loadedKey loaded) :
    Snapshot (store.commit writtenKey written) loadedKey loaded := by
  cases loaded with
  | none => trivial
  | some value =>
      obtain ⟨document, version⟩ := value
      simp only [Snapshot] at h ⊢
      obtain ⟨currentDocument, currentVersion, hlookup, hle, hdocument⟩ := h
      by_cases hk : loadedKey = writtenKey
      · subst writtenKey
        rw [Store.document_commit, if_pos rfl]
        refine ⟨written, currentVersion + 1, ?_,
          Nat.le_trans hle (Nat.le_succ currentVersion), ?_⟩
        · simp [Concrete.Store.version, hlookup]
        · intro heq
          exact (Nat.ne_of_lt (Nat.lt_succ_of_le hle) heq).elim
      · refine ⟨currentDocument, currentVersion, ?_, hle, hdocument⟩
        rw [Store.document_commit, if_neg hk]
        exact hlookup

theorem Snapshot.eq_of_versions {store : Concrete.Store}
    {key : Concrete.Key} {loaded : Option (Promise × Concrete.Version)}
    (hsnapshot : Snapshot store key loaded)
    (hversion : loaded.map (·.2) = (store.document key).map (·.2)) :
    store.document key = loaded := by
  cases loaded with
  | none =>
      cases hcurrent : store.document key with
      | none => rfl
      | some current => simp [hcurrent] at hversion
  | some loaded =>
      obtain ⟨document, version⟩ := loaded
      obtain ⟨currentDocument, currentVersion, hlookup, hle, heq⟩ := hsnapshot
      simp only [Option.map_some] at hversion
      rw [hlookup] at hversion
      simp only [Option.map_some, Option.some.injEq] at hversion
      subst currentVersion
      rw [hlookup, heq rfl]

theorem StoreRep.commit {store : Concrete.Store} {global : State}
    (hrep : StoreRep store global) {key : Concrete.Key}
    {document : Promise} (hid : document.id = key) :
    StoreRep (store.commit key document)
      { promises := document :: global.promises.filter (·.id != key) } := by
  intro other
  rw [Store.document_commit]
  by_cases h : other = key
  · subst other
    simp [Experiment.promiseAt, hid]
  · rw [if_neg h]
    change (store.document other).map (·.1) =
      Experiment.promiseAt
        ({ promises := document :: global.promises.filter (·.id != key) } :
          State) other
    rw [← hid]
    rw [Experiment.promiseAt_saved]
    rw [if_neg (by simpa [hid] using h)]
    exact hrep other

theorem PutProvenance.document_id
    {appConfig : Resonate.Config} {key : Concrete.Key}
    {document : Promise} {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion) :
    document.id = key := by
  have h := List.find?_some provenance.document_eq
  exact beq_iff_eq.mp h

theorem provenance_transport
    {appConfig : Resonate.Config} {store : Concrete.Store}
    {global : State} (hrep : StoreRep store global)
    {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    (hloaded : store.document key = provenance.loaded) :
    ∃ globalAfter,
      (globalAfter, provenance.outputs) ∈
        (Resonate.run { appConfig with unreliable := true }
          provenance.call global).val ∧
      StoreRep (store.commit key document) globalAfter := by
  have houtcome := provenance.outcome
  simp only [Resonate.dispatch, List.mem_map] at houtcome
  obtain ⟨⟨response, localAfter, outs⟩, hdispatch, heq⟩ :=
    houtcome
  have hafter : localAfter = provenance.after := congrArg Prod.fst heq
  subst localAfter
  have hkey : provenance.call.request.key = key := by
    exact provenance.key_eq
  have hdoc :
      Experiment.promiseAt global provenance.call.request.key =
        provenance.loaded.map (·.1) := by
    calc
      Experiment.promiseAt global provenance.call.request.key =
          (store.document provenance.call.request.key).map (·.1) :=
        (hrep _).symm
      _ = (store.document key).map (·.1) := by
        rw [hkey]
      _ = provenance.loaded.map (·.1) := by rw [hloaded]
  have hdispatch' :
      (response, provenance.after, outs) ∈
        (Experiment.dispatch provenance.call.request
          provenance.call.requestedAt
          { appConfig with unreliable := true }
          { promises := (provenance.loaded.map (·.1)).toList }).val := by
    have hlist :
        (provenance.loaded.map (·.1)).toList =
          provenance.loaded.toList.map (·.1) := by
      cases provenance.loaded <;> rfl
    simpa [Concrete.documentState, hlist] using hdispatch
  obtain ⟨globalAfter, hglobal, hsame⟩ :=
    Experiment.dispatch_transport provenance.call.request
      provenance.call.requestedAt
      { appConfig with unreliable := true }
      global provenance.after (provenance.loaded.map (·.1))
      response outs hdoc hdispatch'
  refine ⟨globalAfter, ?_, ?_⟩
  · simp only [Resonate.run, List.mem_map]
    refine ⟨(globalAfter,
      outs ++ [.send provenance.call.client
        (.res provenance.call.id response)]), ?_, ?_⟩
    · exact Experiment.request_step_mem
        (Experiment.dispatch_as_serve hglobal)
    · have houtputs := congrArg Prod.snd heq
      simpa using houtputs
  · have hcommit := StoreRep.commit hrep provenance.document_id
    rw [hkey] at hsame
    intro other
    rw [hcommit other]
    rw [← hsame other]
    simp [Experiment.State.withFrame, provenance.singleton]

theorem provenance_transport_lose
    {appConfig : Resonate.Config} {store : Concrete.Store}
    {global : State} (hrep : StoreRep store global)
    {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    (hloaded : store.document key = provenance.loaded) :
    ∃ globalAfter failureOutputs,
      (globalAfter, failureOutputs) ∈
        (Resonate.run { appConfig with unreliable := true }
          provenance.call global).val ∧
      StoreRep (store.commit key document) globalAfter ∧
      Concrete.unavailable provenance.call ∈ failureOutputs := by
  have houtcome := provenance.outcome
  simp only [Resonate.dispatch, List.mem_map] at houtcome
  obtain ⟨⟨response, localAfter, outs⟩, hdispatch, heq⟩ := houtcome
  have hafter : localAfter = provenance.after := congrArg Prod.fst heq
  subst localAfter
  have hkey : provenance.call.request.key = key := provenance.key_eq
  have hdoc :
      Experiment.promiseAt global provenance.call.request.key =
        provenance.loaded.map (·.1) := by
    calc
      Experiment.promiseAt global provenance.call.request.key =
          (store.document provenance.call.request.key).map (·.1) :=
        (hrep _).symm
      _ = (store.document key).map (·.1) := by rw [hkey]
      _ = provenance.loaded.map (·.1) := by rw [hloaded]
  have hdispatch' :
      (response, provenance.after, outs) ∈
        (Experiment.dispatch provenance.call.request
          provenance.call.requestedAt
          { appConfig with unreliable := true }
          { promises := (provenance.loaded.map (·.1)).toList }).val := by
    have hlist :
        (provenance.loaded.map (·.1)).toList =
          provenance.loaded.toList.map (·.1) := by
      cases provenance.loaded <;> rfl
    simpa [Concrete.documentState, hlist] using hdispatch
  obtain ⟨globalAfter, hglobal, hsame⟩ :=
    Experiment.dispatch_transport provenance.call.request
      provenance.call.requestedAt
      { appConfig with unreliable := true }
      global provenance.after (provenance.loaded.map (·.1))
      response outs hdoc hdispatch'
  let failureOutputs :=
    Resonate.outputs
      (outs ++ [.send provenance.call.client
        (.res provenance.call.id { status := 503 })])
  refine ⟨globalAfter, failureOutputs, ?_, ?_, ?_⟩
  · simp only [Resonate.run, List.mem_map]
    refine ⟨(globalAfter, outs ++
      [.send provenance.call.client
        (.res provenance.call.id { status := 503 })]), ?_, rfl⟩
    exact Experiment.request_step_mem
      (Experiment.dispatch_as_lose hglobal)
  · have hcommit := StoreRep.commit hrep provenance.document_id
    rw [hkey] at hsame
    intro other
    rw [hcommit other]
    rw [← hsame other]
    simp [Experiment.State.withFrame, provenance.singleton]
  · simp [failureOutputs, Resonate.outputs, Concrete.unavailable]

theorem decideResults_put_valid
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {flight : Concrete.Flight}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈ (Concrete.decideResults appConfig node flight loaded).val)
    (hloaded :
      loaded.all (fun value =>
        value.1.id == Concrete.requestKey flight.call) = true)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ValidPut appConfig key document expectedVersion := by
  simp only [Concrete.decideResults, List.mem_map] at hresult
  obtain ⟨outcome, houtcome, rfl⟩ := hresult
  obtain ⟨after, outputs⟩ := outcome
  split at hsend
  · simp [Concrete.sendOutputs] at hsend
  · rename_i nextDocument hdocument
    split at hsend
    · rename_i hsingleton
      simp only [List.mem_singleton] at hsend
      cases hsend
      exact ⟨{
        call := flight.call
        loaded := loaded
        after := after
        outputs := outputs
        key_eq := rfl
        expected_eq := rfl
        loaded_key := by
          intro value hvalue
          cases loaded with
          | none => contradiction
          | some loaded =>
              simp only [Option.mem_def, Option.some.injEq] at hvalue
              subst value
              simpa using hloaded
        outcome := houtcome
        document_eq := by
          simpa using hdocument
        singleton := beq_iff_eq.mp hsingleton
      }⟩
    · simp [Concrete.sendOutputs] at hsend

theorem nodeGotResults_put_valid
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {gotOp : Concrete.OpId}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.nodeGotResults appConfig node gotOp loaded).val)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ValidPut appConfig key document expectedVersion := by
  generalize htake : Concrete.Node.takeFlight node gotOp = taken
  obtain ⟨flight, nextNode⟩ := taken
  simp only [Concrete.nodeGotResults, htake] at hresult
  cases flight with
  | none =>
      simp [Outcomes.one] at hresult
      subst result
      contradiction
  | some flight =>
      cases hphase : flight.phase with
      | loading =>
          simp only [hphase] at hresult
          split at hresult
          · rename_i hloaded
            have hvalid := decideResults_put_valid hresult hloaded hsend
            exact hvalid
          · simp [Outcomes.one] at hresult
            subst result
            contradiction
      | writing =>
          simp [hphase, Outcomes.one] at hresult
          subst result
          contradiction

/-- A raw PUT can only be emitted while handling a `got`; its semantic
validity follows from the node-local continuation, not from wire data. -/
theorem step_sent_put_valid
    {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {pid : Concrete.Pid} {localState : Concrete.Local}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.step appConfig config pid localState 0 event).val)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ValidPut appConfig key document expectedVersion := by
  cases pid <;> cases localState <;> cases event with
  | timeout =>
      simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.Node.await,
          Concrete.Node.takeFlight, Concrete.storePutResults,
          Concrete.sendOutputs, Outcomes.one]
      all_goals try { split at hresult }
      all_goals
        try simp_all
      all_goals
        first
        | exact nodeGotResults_put_valid hresult hsend
        | grind [Concrete.StoreRequest, Concrete.StoreReply,
            nodeGotResults_put_valid]

def RawPutsValid {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {sender recipient op key document expectedVersion},
    (sender, recipient,
      Concrete.Msg.call op (.put key document expectedVersion)) ∈
        world.network →
    ValidPut appConfig key document expectedVersion

theorem rawPutsValid_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    RawPutsValid
      (nodes := nodes) (appConfig := appConfig) (World.initial process) := by
  intro sender recipient op key document expectedVersion h
  contradiction

theorem rawPutsValid_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : RawPutsValid world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    RawPutsValid next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro sender recipient op key document expectedVersion hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hold
      · obtain ⟨rfl, rfl, heq⟩ := hnew
        obtain ⟨call, hrequest⟩ := hinject
        cases hrequest
  | process htime hprocess hvalid hresult =>
      intro sender recipient op key document expectedVersion hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hold
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact step_sent_put_valid hresult hsent
  | outside htime hmessage =>
      intro sender recipient op key document expectedVersion hmem
      exact hinvariant hmem

/-- Reachability turns the local ghost argument into a network invariant.
Old PUTs remain valid when Rover retains them for arbitrary duplicate
delivery. -/
theorem reachable_raw_put_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    RawPutsValid world := by
  induction hreachable with
  | init hinit =>
      exact rawPutsValid_initial _
  | step hreachable hstep hinvariant =>
      exact rawPutsValid_step hinvariant hstep

theorem server_step_history_mono
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val) :
    ∃ nextNode,
      result.state = .node nextNode ∧
      ∀ entry ∈ node.history, entry ∈ nextNode.history := by
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      exact ⟨node, rfl, fun _ h => h⟩
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
      all_goals try { split at hresult }
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

def FlightOwns
    {appConfig : Resonate.Config} {key : Concrete.Key}
    {document : Promise} {expectedVersion : Option Concrete.Version}
    (flight : Concrete.Flight)
    (provenance : PutProvenance appConfig key document expectedVersion) : Prop :=
  flight.call = provenance.call ∧
  flight.loaded = provenance.loaded ∧
  flight.after = some provenance.after ∧
  flight.document = some document ∧
  flight.selected = provenance.outputs ∧
  flight.phase = .writing

theorem decideResults_put_owned
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {flight : Concrete.Flight}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈ (Concrete.decideResults appConfig node flight loaded).val)
    (hloaded :
      loaded.all (fun value =>
        value.1.id == Concrete.requestKey flight.call) = true)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ∃ nextNode writing,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      result.state = .node nextNode ∧
      (op, writing) ∈ nextNode.history ∧
      FlightOwns writing provenance ∧
      provenance.loaded = loaded := by
  simp only [Concrete.decideResults, List.mem_map] at hresult
  obtain ⟨outcome, houtcome, rfl⟩ := hresult
  obtain ⟨after, outputs⟩ := outcome
  split at hsend
  · simp [Concrete.sendOutputs] at hsend
  · rename_i nextDocument hdocument
    split at hsend
    · rename_i hsingleton
      simp only [List.mem_singleton] at hsend
      cases hsend
      let writing : Concrete.Flight := {
        flight with
        loaded := loaded
        after := some after
        document := some document
        selected := outputs
        phase := .writing
      }
      let provenance : PutProvenance appConfig
          (Concrete.requestKey flight.call) document
          (loaded.map (·.2)) := {
        call := flight.call
        loaded := loaded
        after := after
        outputs := outputs
        key_eq := rfl
        expected_eq := rfl
        loaded_key := by
          intro value hvalue
          cases loaded with
          | none => contradiction
          | some loaded =>
              simp only [Option.mem_def, Option.some.injEq] at hvalue
              subst value
              simpa using hloaded
        outcome := houtcome
        document_eq := by simpa using hdocument
        singleton := beq_iff_eq.mp hsingleton
      }
      refine ⟨
        { nextOp := node.nextOp + 1
          flights := (node.nextOp, writing) :: node.flights
          history := (node.nextOp, writing) :: node.history },
        writing, provenance, ?_, by simp, ?_, rfl⟩
      · simp [hsingleton, Concrete.Node.await, writing]
      simp [FlightOwns, writing, provenance]
    · simp [Concrete.sendOutputs] at hsend

theorem nodeGotResults_put_owned
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {gotOp : Concrete.OpId}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.nodeGotResults appConfig node gotOp loaded).val)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ∃ nextNode writing,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      result.state = .node nextNode ∧
      (op, writing) ∈ nextNode.history ∧
      FlightOwns writing provenance ∧
      provenance.loaded = loaded := by
  generalize htake : Concrete.Node.takeFlight node gotOp = taken
  obtain ⟨flight, nextNode⟩ := taken
  simp only [Concrete.nodeGotResults, htake] at hresult
  cases flight with
  | none =>
      simp [Outcomes.one] at hresult
      subst result
      contradiction
  | some flight =>
      cases hphase : flight.phase with
      | loading =>
          simp only [hphase] at hresult
          split at hresult
          · rename_i hloaded
            exact decideResults_put_owned hresult hloaded hsend
          · simp [Outcomes.one] at hresult
            subst result
            contradiction
      | writing =>
          simp [hphase, Outcomes.one] at hresult
          subst result
          contradiction

theorem server_step_put_owned
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ∃ nextNode writing,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      result.state = .node nextNode ∧
      (op, writing) ∈ nextNode.history ∧
      FlightOwns writing provenance := by
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        try { split at hresult }
      all_goals
        first
        | (obtain ⟨nextNode, writing, provenance, hstate,
              hhistory, howns, hloaded⟩ :=
              nodeGotResults_put_owned hresult hsend
           exact ⟨nextNode, writing, provenance,
             hstate, hhistory, howns⟩)
        | grind [Concrete.StoreRequest, Concrete.StoreReply,
            Concrete.Msg.call, Concrete.Msg.reply,
            Concrete.step, Concrete.Node.await,
            Concrete.Node.takeFlight, Concrete.sendOutputs, Outcomes.one,
            nodeGotResults_put_owned]

def OwnedPuts {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op key document expectedVersion},
    (.server address, .store,
      Concrete.Msg.call op (.put key document expectedVersion)) ∈
        world.network →
    ∃ node writing,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      world.process (.server address) = .node node ∧
      (op, writing) ∈ node.history ∧
      FlightOwns writing provenance

theorem ownedPuts_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    OwnedPuts
      (nodes := nodes) (appConfig := appConfig) (World.initial process) := by
  intro address op key document expectedVersion h
  contradiction

theorem ownedPuts_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : OwnedPuts world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    OwnedPuts next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro address op key document expectedVersion hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨node, writing, provenance, hstate, hhistory, howns⟩ :=
          hinvariant hold
        exact ⟨node, writing, provenance, hstate, hhistory, howns⟩
      · obtain ⟨_, _, heq⟩ := hnew
  | outside htime hmessage =>
      intro address op key document expectedVersion hmem
      exact hinvariant hmem
  | @process process now event result htime hprocess hvalid hresult =>
      intro address op key document expectedVersion hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨node, writing, provenance, hstate, hhistory, howns⟩ :=
          hinvariant hold
        by_cases hp : process = Concrete.Pid.server address
        · subst process
          have hresult' := hresult
          rw [hstate] at hresult'
          obtain ⟨nextNode, hnextState, hmono⟩ :=
            server_step_history_mono hresult'
          refine ⟨nextNode, writing, provenance, ?_, hmono _ hhistory, howns⟩
          simp [World.land, hnextState]
        · refine ⟨node, writing, provenance, ?_, hhistory, howns⟩
          simp [World.land, Ne.symm hp, hstate]
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        cases hlocal : world.process (.server address) with
        | node node =>
            have hresult' := hresult
            rw [hlocal] at hresult'
            obtain ⟨nextNode, writing, provenance,
                hnextState, hhistory, howns⟩ :=
              server_step_put_owned hresult' hsent
            refine ⟨nextNode, writing, provenance, ?_, hhistory, howns⟩
            simp [World.land, hnextState]
        | outside =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction
        | store store =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction

theorem reachable_owned_puts
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    OwnedPuts world := by
  induction hreachable with
  | init hinit => exact ownedPuts_initial _
  | step hreachable hstep hinvariant =>
      exact ownedPuts_step hinvariant hstep

theorem store_written_origin
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {localState : Concrete.Local}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {address : Addr} {op : Concrete.OpId}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store localState 0 event).val)
    (hsend :
      (.server address, Concrete.Msg.reply op .written) ∈ result.send) :
    ∃ key document expectedVersion,
      event = .receive (.server address)
        (.call op (.put key document expectedVersion)) := by
  simp only [Concrete.Msg.reply] at hsend
  change ∃ key document expectedVersion,
    event = .receive (.server address)
      (.callPut op key document expectedVersion)
  cases localState <;> cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        try { split at hresult }
      all_goals
        grind [Concrete.StoreRequest, Concrete.StoreReply,
          Concrete.Msg.call, Concrete.Msg.reply,
          Concrete.step, Concrete.storePutResults, Outcomes.one]

theorem store_failed_origin
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {localState : Concrete.Local}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {address : Addr} {op : Concrete.OpId}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store localState 0 event).val)
    (hsend :
      (.server address, Concrete.Msg.reply op .failed) ∈ result.send) :
    ∃ key document expectedVersion,
      event = .receive (.server address)
        (.call op (.put key document expectedVersion)) := by
  simp only [Concrete.Msg.reply] at hsend
  change ∃ key document expectedVersion,
    event = .receive (.server address)
      (.callPut op key document expectedVersion)
  cases localState <;> cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        try { split at hresult }
      all_goals
        grind [Concrete.StoreRequest, Concrete.StoreReply,
          Concrete.Msg.call, Concrete.Msg.reply,
          Concrete.step, Concrete.storePutResults, Outcomes.one]

def RepliesHavePut {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op},
    ((.store, .server address, Concrete.Msg.reply op .written) ∈
        world.network ∨
      (.store, .server address, Concrete.Msg.reply op .failed) ∈
        world.network) →
    ∃ key document expectedVersion,
      (.server address, .store,
        Concrete.Msg.call op (.put key document expectedVersion)) ∈
          world.network

theorem reachable_replies_have_put
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    RepliesHavePut world := by
  induction hreachable with
  | init hinit =>
      intro address op h
      rcases h with h | h <;> contradiction
  | step hreachable hstep hinvariant =>
      cases hstep with
      | inject htime hprocess hinject =>
          intro address op h
          rcases h with h | h
          · simp only [World.inject, List.mem_append, List.mem_singleton] at h
            rcases h with hold | hnew
            · obtain ⟨key, document, expectedVersion, hput⟩ :=
                hinvariant (.inl hold)
              exact ⟨key, document, expectedVersion,
                List.mem_append_left _ hput⟩
            · cases hnew
          · simp only [World.inject, List.mem_append, List.mem_singleton] at h
            rcases h with hold | hnew
            · obtain ⟨key, document, expectedVersion, hput⟩ :=
                hinvariant (.inr hold)
              exact ⟨key, document, expectedVersion,
                List.mem_append_left _ hput⟩
            · cases hnew
      | outside htime hmessage =>
          exact hinvariant
      | @process process now event result htime hprocess hvalid hresult =>
          intro address op h
          rcases h with h | h
          · simp only [World.land, List.mem_append] at h
            rcases h with hold | hnew
            · obtain ⟨key, document, expectedVersion, hput⟩ :=
                hinvariant (.inl hold)
              exact ⟨key, document, expectedVersion,
                List.mem_append_left _ hput⟩
            · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
              obtain ⟨target, message⟩ := sent
              simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl, rfl⟩ := heq
              obtain ⟨key, document, expectedVersion, hevent⟩ :=
                store_written_origin hresult hsent
              cases hevent
              exact ⟨key, document, expectedVersion,
                List.mem_append_left _ hvalid⟩

          · simp only [World.land, List.mem_append] at h
            rcases h with hold | hnew
            · obtain ⟨key, document, expectedVersion, hput⟩ :=
                hinvariant (.inr hold)
              exact ⟨key, document, expectedVersion,
                List.mem_append_left _ hput⟩
            · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
              obtain ⟨target, message⟩ := sent
              simp only [Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl, rfl⟩ := heq
              obtain ⟨key, document, expectedVersion, hevent⟩ :=
                store_failed_origin hresult hsent
              cases hevent
              exact ⟨key, document, expectedVersion,
                List.mem_append_left _ hvalid⟩

def NodeValid (node : Concrete.Node) : Prop :=
  (node.history.map (·.1)).Nodup ∧
  (∀ {op flight}, (op, flight) ∈ node.history → op < node.nextOp) ∧
  (∀ {op flight}, (op, flight) ∈ node.flights →
    (op, flight) ∈ node.history)

theorem NodeValid.empty : NodeValid ({} : Concrete.Node) := by
  simp [NodeValid]

theorem NodeValid.await {node : Concrete.Node} (hvalid : NodeValid node)
    (flight : Concrete.Flight) (message : Concrete.OpId → Concrete.Msg appConfig) :
    NodeValid (node.await flight message).1 := by
  rcases hvalid with ⟨hnodup, hlt, hflights⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [Concrete.Node.await, List.map_cons]
    apply List.nodup_cons.mpr
    refine ⟨?_, hnodup⟩
    intro hmem
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
    obtain ⟨op, oldFlight⟩ := entry
    simp only at heq
    subst op
    exact (Nat.lt_irrefl _ (hlt hentry))
  · intro op current hmem
    simp only [Concrete.Node.await, List.mem_cons] at hmem
    rcases hmem with hnew | hold
    · cases hnew
      exact Nat.lt_succ_self _
    · exact Nat.lt_trans (hlt hold) (Nat.lt_succ_self _)
  · intro op current hmem
    simp only [Concrete.Node.await, List.mem_cons] at hmem ⊢
    rcases hmem with hnew | hold
    · exact .inl hnew
    · exact .inr (hflights hold)

theorem NodeValid.takeFlight {node : Concrete.Node} (hvalid : NodeValid node)
    (op : Concrete.OpId) :
    NodeValid (node.takeFlight op).2 := by
  rcases hvalid with ⟨hnodup, hlt, hflights⟩
  refine ⟨hnodup, hlt, ?_⟩
  intro current flight hmem
  exact hflights (List.mem_filter.mp hmem).1

theorem history_eq_of_nodup
    {history : List (Concrete.OpId × Concrete.Flight)}
    (hnodup : (history.map (·.1)).Nodup)
    {op : Concrete.OpId} {left right : Concrete.Flight}
    (hleft : (op, left) ∈ history)
    (hright : (op, right) ∈ history) :
    left = right := by
  induction history with
  | nil => simp at hleft
  | cons entry rest ih =>
      obtain ⟨entryOp, entryFlight⟩ := entry
      simp only [List.map_cons, List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hleft hright
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright
      · cases hleft
        cases hright
        rfl
      · cases hleft
        exfalso
        exact hnodup.1 (List.mem_map.mpr
          ⟨(op, right), hright, rfl⟩)
      · cases hright
        exfalso
        exact hnodup.1 (List.mem_map.mpr
          ⟨(op, left), hleft, rfl⟩)
      · exact ih hnodup.2 hleft hright

theorem NodeValid.history_eq {node : Concrete.Node}
    (hvalid : NodeValid node)
    {op : Concrete.OpId} {left right : Concrete.Flight}
    (hleft : (op, left) ∈ node.history)
    (hright : (op, right) ∈ node.history) :
    left = right :=
  history_eq_of_nodup hvalid.1 hleft hright

theorem decideResults_node_valid
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {flight : Concrete.Flight}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hvalid : NodeValid node)
    (hresult :
      result ∈ (Concrete.decideResults appConfig node flight loaded).val) :
    ∃ nextNode,
      result.state = .node nextNode ∧ NodeValid nextNode := by
  simp only [Concrete.decideResults, List.mem_map] at hresult
  obtain ⟨outcome, houtcome, rfl⟩ := hresult
  obtain ⟨after, outputs⟩ := outcome
  split
  · exact ⟨node, rfl, hvalid⟩
  · split
    · exact ⟨_, rfl, NodeValid.await hvalid _ _⟩
    · exact ⟨node, rfl, hvalid⟩

theorem nodeGotResults_node_valid
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {op : Concrete.OpId}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hvalid : NodeValid node)
    (hresult :
      result ∈
        (Concrete.nodeGotResults appConfig node op loaded).val) :
    ∃ nextNode,
      result.state = .node nextNode ∧ NodeValid nextNode := by
  generalize htake : Concrete.Node.takeFlight node op = taken
  obtain ⟨flight, nextNode⟩ := taken
  have hnextValid : NodeValid nextNode := by
    simpa [htake] using NodeValid.takeFlight hvalid op
  simp only [Concrete.nodeGotResults, htake] at hresult
  cases flight with
  | none =>
      simp [Outcomes.one] at hresult
      subst result
      exact ⟨node, rfl, hvalid⟩
  | some flight =>
      cases hphase : flight.phase with
      | loading =>
          simp only [hphase] at hresult
          split at hresult
          · exact decideResults_node_valid hnextValid hresult
          · simp [Outcomes.one] at hresult
            subst result
            exact ⟨nextNode, rfl, hnextValid⟩
      | writing =>
          simp only [hphase] at hresult
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨nextNode, rfl, hnextValid⟩

theorem server_step_node_valid
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hvalid : NodeValid node)
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val) :
    ∃ nextNode,
      result.state = .node nextNode ∧ NodeValid nextNode := by
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      exact ⟨node, rfl, hvalid⟩
  | receive sender message =>
      cases sender <;> cases message
      all_goals simp only [Concrete.step] at hresult
      case receive.outside.request call =>
        simp [Outcomes.one] at hresult
        subst result
        exact ⟨_, rfl, NodeValid.await hvalid _ _⟩
      case receive.store.replyGot op loaded =>
            exact nodeGotResults_node_valid hvalid hresult
      case receive.store.replyWritten op =>
          generalize htake : Concrete.Node.takeFlight node op = taken
          obtain ⟨flight, nextNode⟩ := taken
          have hnextValid : NodeValid nextNode := by
            simpa [htake] using NodeValid.takeFlight hvalid op
          simp only [htake] at hresult
          cases flight with
          | none =>
              simp [Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hvalid⟩
          | some flight =>
              cases hphase : flight.phase <;>
                simp [hphase, Outcomes.one] at hresult
              all_goals
                subst result
                exact ⟨nextNode, rfl, hnextValid⟩
      case receive.store.replyFailed op =>
          generalize htake : Concrete.Node.takeFlight node op = taken
          obtain ⟨flight, nextNode⟩ := taken
          have hnextValid : NodeValid nextNode := by
            simpa [htake] using NodeValid.takeFlight hvalid op
          simp only [htake] at hresult
          cases flight with
          | none =>
              simp [Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hvalid⟩
          | some flight =>
              simp [Outcomes.one] at hresult
              subst result
              exact ⟨nextNode, rfl, hnextValid⟩
      case receive.store.replyConflict op =>
          generalize htake : Concrete.Node.takeFlight node op = taken
          obtain ⟨flight, nextNode⟩ := taken
          have hnextValid : NodeValid nextNode := by
            simpa [htake] using NodeValid.takeFlight hvalid op
          simp only [htake] at hresult
          cases flight with
          | none =>
              simp [Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hvalid⟩
          | some flight =>
              cases hphase : flight.phase with
              | loading =>
                  simp [hphase, Outcomes.one] at hresult
                  subst result
                  exact ⟨nextNode, rfl, hnextValid⟩
              | writing =>
                  simp only [hphase] at hresult
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, NodeValid.await hnextValid _ _⟩
                  · simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨nextNode, rfl, hnextValid⟩
      all_goals
        simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hvalid⟩

def NodesValid {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address ∈ nodes, ∀ node,
    world.process (.server address) = .node node → NodeValid node

theorem nodesValid_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesValid (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress node hnode
  change process (.server address) = .node node at hnode
  rw [hinit.2.2 address haddress] at hnode
  cases hnode
  exact NodeValid.empty

theorem nodesValid_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : NodesValid world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesValid next := by
  cases hstep with
  | inject htime hprocess hinject =>
      exact hinvariant
  | outside htime hmessage =>
      exact hinvariant
  | @process process now event result htime hprocess hvalid hresult =>
      intro address haddress node hnode
      by_cases hp : process = .server address
      · subst process
        have hold : NodeValid node := by
          have hstate : result.state = .node node := by
            simpa [World.land] using hnode
          cases hlocal : world.process (.server address) with
          | node old =>
              have holdValid := hinvariant address haddress old hlocal
              have hresult' := hresult
              rw [hlocal] at hresult'
              obtain ⟨nextNode, hnext, hnextValid⟩ :=
                server_step_node_valid holdValid hresult'
              rw [hnext] at hstate
              cases hstate
              exact hnextValid
          | outside =>
              simp [hlocal, Concrete.step, Outcomes.one] at hresult
              subst result
              contradiction
          | store store =>
              simp [hlocal, Concrete.step, Outcomes.one] at hresult
              subst result
              contradiction
        exact hold
      · apply hinvariant address haddress node
        simpa [World.land, Ne.symm hp] using hnode

theorem reachable_nodes_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesValid world := by
  induction hreachable with
  | init hinit => exact nodesValid_initial hinit
  | step hreachable hstep hinvariant =>
      exact nodesValid_step hinvariant hstep

theorem reachable_server_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes) :
    ∃ node, world.process (.server address) = .node node := by
  induction hreachable with
  | init hinit =>
      exact ⟨{}, hinit.2.2 address haddress⟩
  | @step world label next hreachable hstep ih =>
      obtain ⟨node, hnode⟩ := ih
      cases hstep with
      | inject htime hprocess hinject =>
          exact ⟨node, hnode⟩
      | outside htime hmessage =>
          exact ⟨node, hnode⟩
      | @process process now event result htime hprocess hvalid hresult =>
          by_cases hp : process = .server address
          · subst process
            have hresult' := hresult
            rw [hnode] at hresult'
            obtain ⟨nextNode, hstate, hnextValid⟩ :=
              server_step_node_valid
                (reachable_nodes_valid hreachable address haddress node hnode)
                hresult'
            exact ⟨nextNode, by simp [World.land, hstate]⟩
          · exact ⟨node, by
              simpa [World.land, Ne.symm hp] using hnode⟩

theorem find_flight_mem
    {flights : List (Concrete.OpId × Concrete.Flight)}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (h :
      (flights.find? (·.1 == op)).map (·.2) = some flight) :
    (op, flight) ∈ flights := by
  cases hfind : flights.find? (·.1 == op) with
  | none => simp [hfind] at h
  | some entry =>
      obtain ⟨foundOp, foundFlight⟩ := entry
      simp only [hfind, Option.map_some, Option.some.injEq] at h
      subst foundFlight
      have hmem := List.mem_of_find?_eq_some hfind
      have hkey := beq_iff_eq.mp
        (List.find?_some
          (p := fun entry : Concrete.OpId × Concrete.Flight =>
            entry.1 == op) hfind)
      change foundOp = op at hkey
      subst op
      exact hmem

theorem decideResults_history_origin
    {appConfig : Resonate.Config} {node nextNode : Concrete.Node}
    {source : Concrete.Flight}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.decideResults appConfig node source loaded).val)
    (hstate : result.state = .node nextNode)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hmem : (op, flight) ∈ nextNode.history) :
    (∃ oldOp oldFlight,
      (oldOp, oldFlight) ∈ node.history ∧
      oldFlight.call = flight.call) ∨
    source.call = flight.call := by
  simp only [Concrete.decideResults, List.mem_map] at hresult
  obtain ⟨outcome, houtcome, heq⟩ := hresult
  obtain ⟨after, outputs⟩ := outcome
  subst result
  split at hstate
  · simp only [Concrete.Local.node.injEq] at hstate
    subst nextNode
    exact .inl ⟨op, flight, hmem, rfl⟩
  · split at hstate
    · simp only [Concrete.Local.node.injEq] at hstate
      subst nextNode
      simp only [Concrete.Node.await, List.mem_cons] at hmem
      rcases hmem with hnew | hold
      · cases hnew
        exact .inr rfl
      · exact .inl ⟨op, flight, hold, rfl⟩
    · simp only [Concrete.Local.node.injEq] at hstate
      subst nextNode
      exact .inl ⟨op, flight, hmem, rfl⟩

theorem history_call_origin
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node nextNode : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hvalid : NodeValid node)
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val)
    (hstate : result.state = .node nextNode)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hmem : (op, flight) ∈ nextNode.history) :
    (∃ oldOp oldFlight,
      (oldOp, oldFlight) ∈ node.history ∧
      oldFlight.call = flight.call) ∨
    event = .receive .outside (.request flight.call) := by
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      simp only [Concrete.Local.node.injEq] at hstate
      subst nextNode
      exact .inl ⟨op, flight, hmem, rfl⟩
  | receive sender message =>
      cases sender <;> cases message
      all_goals simp only [Concrete.step] at hresult
      case receive.outside.request call =>
        simp [Outcomes.one] at hresult
        subst result
        simp only [Concrete.Local.node.injEq] at hstate
        subst nextNode
        simp only [Concrete.Node.await, List.mem_cons] at hmem
        rcases hmem with hnew | hold
        · cases hnew
          exact .inr rfl
        · exact .inl ⟨op, flight, hold, rfl⟩
      case receive.store.replyGot gotOp loaded =>
        generalize htake : Concrete.Node.takeFlight node gotOp = taken
        obtain ⟨active, takenNode⟩ := taken
        have hhistory : takenNode.history = node.history := by
          have hx := congrArg (fun pair => pair.2.history) htake
          simp only [Concrete.Node.takeFlight] at hx
          exact hx.symm
        simp only [Concrete.nodeGotResults, htake] at hresult
        cases active with
        | none =>
            simp [Outcomes.one] at hresult
            subst result
            simp only [Concrete.Local.node.injEq] at hstate
            subst nextNode
            exact .inl ⟨op, flight, hmem, rfl⟩
        | some active =>
            have hactive :
                (gotOp, active) ∈ node.history := by
              apply hvalid.2.2
              apply find_flight_mem
              simpa [Concrete.Node.takeFlight] using
                congrArg Prod.fst htake
            cases hphase : active.phase with
            | loading =>
                simp only [hphase] at hresult
                split at hresult
                · rcases decideResults_history_origin
                    hresult hstate hmem with hold | hcall
                  · obtain ⟨oldOp, oldFlight, hold, hcall⟩ := hold
                    exact .inl ⟨oldOp, oldFlight,
                      hhistory ▸ hold, hcall⟩
                  · exact .inl ⟨gotOp, active, hactive, hcall⟩
                · simp [Outcomes.one] at hresult
                  subst result
                  simp only [Concrete.Local.node.injEq] at hstate
                  subst nextNode
                  exact .inl ⟨op, flight, hhistory ▸ hmem, rfl⟩
            | writing =>
                simp [hphase, Outcomes.one] at hresult
                subst result
                simp only [Concrete.Local.node.injEq] at hstate
                subst nextNode
                exact .inl ⟨op, flight, hhistory ▸ hmem, rfl⟩
      case receive.store.replyConflict conflictOp =>
        generalize htake :
            Concrete.Node.takeFlight node conflictOp = taken
        obtain ⟨active, takenNode⟩ := taken
        have hhistory : takenNode.history = node.history := by
          have hx := congrArg (fun pair => pair.2.history) htake
          simp only [Concrete.Node.takeFlight] at hx
          exact hx.symm
        simp only [htake] at hresult
        cases active with
        | none =>
            simp [Outcomes.one] at hresult
            subst result
            simp only [Concrete.Local.node.injEq] at hstate
            subst nextNode
            exact .inl ⟨op, flight, hmem, rfl⟩
        | some active =>
            have hactive : (conflictOp, active) ∈ node.history := by
              apply hvalid.2.2
              apply find_flight_mem
              simpa [Concrete.Node.takeFlight] using
                congrArg Prod.fst htake
            cases hphase : active.phase with
            | loading =>
                simp [hphase, Outcomes.one] at hresult
                subst result
                simp only [Concrete.Local.node.injEq] at hstate
                subst nextNode
                exact .inl ⟨op, flight, hhistory ▸ hmem, rfl⟩
            | writing =>
                simp only [hphase] at hresult
                split at hresult
                · simp [Outcomes.one] at hresult
                  subst result
                  simp only [Concrete.Local.node.injEq] at hstate
                  subst nextNode
                  simp only [Concrete.Node.await, List.mem_cons] at hmem
                  rcases hmem with hnew | hold
                  · cases hnew
                    exact .inl ⟨conflictOp, active, hactive, rfl⟩
                  · exact .inl ⟨op, flight, hhistory ▸ hold, rfl⟩
                · simp [Outcomes.one] at hresult
                  subst result
                  simp only [Concrete.Local.node.injEq] at hstate
                  subst nextNode
                  exact .inl ⟨op, flight, hhistory ▸ hmem, rfl⟩
      all_goals
        simp_all [Concrete.Node.takeFlight, Concrete.Node.await,
          Outcomes.one, NodeValid]
      all_goals grind [find_flight_mem]

def HistoryCalls {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address ∈ nodes, ∀ node op flight,
    world.process (.server address) = .node node →
    (op, flight) ∈ node.history →
    (.outside, .server address, Concrete.Msg.request flight.call) ∈
      world.network

theorem historyCalls_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    HistoryCalls (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress node op flight hnode hmem
  change process (.server address) = .node node at hnode
  rw [hinit.2.2 address haddress] at hnode
  cases hnode
  contradiction

theorem historyCalls_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hnodes : NodesValid world)
    (hinvariant : HistoryCalls world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    HistoryCalls next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro address haddress node op flight hnode hmem
      exact List.mem_append_left _ (hinvariant address haddress node op flight
        hnode hmem)
  | outside htime hmessage =>
      exact hinvariant
  | @process process now event result htime hprocess hvalid hresult =>
      intro address haddress node op flight hnode hmem
      by_cases hp : process = .server address
      · subst process
        have hstate : result.state = .node node := by
          simpa [World.land] using hnode
        cases hlocal : world.process (.server address) with
        | node oldNode =>
            have holdValid := hnodes address haddress oldNode hlocal
            have hresult' := hresult
            rw [hlocal] at hresult'
            rcases history_call_origin holdValid hresult' hstate hmem with
              hold | hrequest
            · obtain ⟨oldOp, oldFlight, hhistory, hcall⟩ := hold
              apply List.mem_append_left
              simpa [hcall] using
                (hinvariant address haddress oldNode oldOp oldFlight
                  hlocal hhistory)
            · cases hrequest
              exact List.mem_append_left _ hvalid
        | outside =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction
        | store store =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction
      · have hold :
            world.process (.server address) = .node node := by
          simpa [World.land, Ne.symm hp] using hnode
        exact List.mem_append_left _
          (hinvariant address haddress node op flight hold hmem)

theorem reachable_history_calls
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    HistoryCalls world := by
  induction hreachable with
  | init hinit => exact historyCalls_initial hinit
  | step hreachable hstep hinvariant =>
      exact historyCalls_step (reachable_nodes_valid hreachable)
        hinvariant hstep

theorem server_step_get_owned
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val)
    (hsend :
      (recipient, Concrete.Msg.call op (.get key)) ∈ result.send) :
    ∃ nextNode loading,
      result.state = .node nextNode ∧
      (op, loading) ∈ nextNode.history ∧
      loading.phase = .loading ∧
      Concrete.requestKey loading.call = key := by
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

def OwnedGets {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op key},
    (.server address, .store, Concrete.Msg.call op (.get key)) ∈
      world.network →
    ∃ node loading,
      world.process (.server address) = .node node ∧
      (op, loading) ∈ node.history ∧
      loading.phase = .loading ∧
      Concrete.requestKey loading.call = key

theorem ownedGets_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    OwnedGets
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address op key h
  contradiction

theorem ownedGets_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : OwnedGets world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    OwnedGets next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro address op key hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hold
      · obtain ⟨_, _, heq⟩ := hnew
  | outside htime hmessage =>
      exact hinvariant
  | @process process now event result htime hprocess hvalid hresult =>
      intro address op key hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨node, loading, hstate, hhistory, hphase, hkey⟩ :=
          hinvariant hold
        by_cases hp : process = .server address
        · subst process
          have hresult' := hresult
          rw [hstate] at hresult'
          obtain ⟨nextNode, hnextState, hmono⟩ :=
            server_step_history_mono hresult'
          refine ⟨nextNode, loading, ?_,
            hmono _ hhistory, hphase, hkey⟩
          simp [World.land, hnextState]
        · refine ⟨node, loading, ?_, hhistory, hphase, hkey⟩
          simp [World.land, Ne.symm hp, hstate]
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        cases hlocal : world.process (.server address) with
        | node node =>
            have hresult' := hresult
            rw [hlocal] at hresult'
            obtain ⟨nextNode, loading, hnextState,
                hhistory, hphase, hkey⟩ :=
              server_step_get_owned hresult' hsent
            refine ⟨nextNode, loading, ?_,
              hhistory, hphase, hkey⟩
            simp [World.land, hnextState]
        | outside =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction
        | store store =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction

theorem reachable_owned_gets
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    OwnedGets world := by
  induction hreachable with
  | init hinit => exact ownedGets_initial _
  | step hreachable hstep hinvariant =>
      exact ownedGets_step hinvariant hstep

theorem store_step_effect
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {store : Concrete.Store}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store (.store store)
          0 event).val) :
    ∃ nextStore,
      result.state = .store nextStore ∧
      (nextStore = store ∨
        ∃ key document, nextStore = store.commit key document) := by
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      exact ⟨store, rfl, .inl rfl⟩
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.storePutResults, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

def StoreExists {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∃ store, world.process .store = .store store

theorem reachable_store_exists
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    StoreExists world := by
  induction hreachable with
  | init hinit =>
      exact ⟨{}, hinit.2.1⟩
  | @step world label next hreachable hstep hinvariant =>
      obtain ⟨store, hstore⟩ := hinvariant
      cases hstep with
      | inject htime hprocess hinject =>
          exact ⟨store, hstore⟩
      | outside htime hmessage =>
          exact ⟨store, hstore⟩
      | @process process now event result htime hprocess hvalid hresult =>
          by_cases hp : process = Concrete.Pid.store
          · subst process
            have hresult' := hresult
            rw [hstore] at hresult'
            obtain ⟨nextStore, hnext, heffect⟩ :=
              store_step_effect hresult'
            exact ⟨nextStore, by simp [World.land, hnext]⟩
          · exact ⟨store, by
              simpa [World.land, Ne.symm hp] using hstore⟩

theorem sent_got_origin
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {pid : Concrete.Pid} {localState : Concrete.Local}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {address : Addr} {op : Concrete.OpId}
    {document : Option (Promise × Concrete.Version)}
    (hresult :
      result ∈
        (Concrete.step appConfig config pid localState 0 event).val)
    (hsend :
      (.server address, Concrete.Msg.reply op (.got document)) ∈
        result.send) :
    ∃ store key,
      pid = .store ∧ localState = .store store ∧
      event = .receive (.server address) (.call op (.get key)) ∧
      document = store.document key ∧ result.state = .store store := by
  cases pid <;> cases localState <;> cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.storePutResults,
          Concrete.sendOutputs, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

def GotSnapshots {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {store address op document},
    world.process .store = .store store →
    (.store, .server address, Concrete.Msg.reply op (.got document)) ∈
      world.network →
    ∃ key,
      (.server address, .store, Concrete.Msg.call op (.get key)) ∈
        world.network ∧
      Snapshot store key document

theorem gotSnapshots_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    GotSnapshots
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro store address op document hstore hmem
  contradiction

theorem gotSnapshots_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hstoreExists : StoreExists world)
    (hinvariant : GotSnapshots world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    GotSnapshots next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro store address op document hstore hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨key, hget, hsnapshot⟩ :=
          hinvariant hstore hold
        exact ⟨key, List.mem_append_left _ hget, hsnapshot⟩
      · obtain ⟨_, _, heq⟩ := hnew
  | outside htime hmessage =>
      exact hinvariant
  | @process process now event result htime hprocess hvalid hresult =>
      intro nextStore address op document hnextStore hmem
      obtain ⟨store, hstore⟩ := hstoreExists
      have heffect :
          nextStore = store ∨
            ∃ key written, nextStore = store.commit key written := by
        by_cases hp : process = Concrete.Pid.store
        · subst process
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          exact heffect
        · have heq : store = nextStore := by
            have : world.process .store = .store nextStore := by
              simpa [World.land, Ne.symm hp] using hnextStore
            rw [hstore] at this
            exact Concrete.Local.store.inj this
          exact .inl heq.symm
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨key, hget, hsnapshot⟩ :=
          hinvariant hstore hold
        refine ⟨key, List.mem_append_left _ hget, ?_⟩
        rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
        · exact hsnapshot
        · exact Snapshot.commit hsnapshot
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨originStore, key, _hpid, hlocal, hevent,
            hdocument, hstate⟩ := sent_got_origin hresult hsent
        rw [hstore] at hlocal
        cases Concrete.Local.store.inj hlocal
        cases hevent
        have hsame : nextStore = store := by
          have hx : store = nextStore := by
            simpa [World.land, hstate] using hnextStore
          exact hx.symm
        subst nextStore
        refine ⟨key, List.mem_append_left _ hvalid, ?_⟩
        exact Snapshot.of_document hdocument.symm

theorem reachable_got_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    GotSnapshots world := by
  induction hreachable with
  | init hinit => exact gotSnapshots_initial _
  | step hreachable hstep hinvariant =>
      exact gotSnapshots_step (reachable_store_exists hreachable)
        hinvariant hstep

theorem nodeGot_put_source
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {gotOp : Concrete.OpId}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.nodeGotResults appConfig node gotOp loaded).val)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ∃ source,
      (gotOp, source) ∈ node.flights ∧
      source.phase = .loading ∧
      Concrete.requestKey source.call = key := by
  simp_all [Concrete.nodeGotResults, Concrete.decideResults,
    Concrete.Node.takeFlight, Concrete.Node.await,
    Concrete.sendOutputs, Outcomes.one]
  all_goals grind [find_flight_mem]

theorem new_put_owned_snapshot
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {recipient : Concrete.Pid}
    {op : Concrete.OpId} {key : Concrete.Key} {document : Promise}
    {expectedVersion : Option Concrete.Version}
    (hstore : world.process .store = .store store)
    (hnode : world.process (.server address) = .node node)
    (hnodeValid : NodeValid node)
    (hgets : OwnedGets world)
    (hgots : GotSnapshots world)
    (hevent : event.Valid world (.server address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val)
    (hsend :
      (recipient, Concrete.Msg.call op
        (.put key document expectedVersion)) ∈
        result.send) :
    ∃ nextNode writing,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      result.state = .node nextNode ∧
      (op, writing) ∈ nextNode.history ∧
      FlightOwns writing provenance ∧
      Snapshot store key provenance.loaded := by
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases sender <;> cases message
      all_goals simp only [Concrete.step] at hresult
      case receive.store.replyGot gotOp loaded =>
        obtain ⟨nextNode, writing, provenance, hstate,
            hhistory, howns, hloaded⟩ :=
          nodeGotResults_put_owned hresult hsend
        obtain ⟨source, hsource, hphase, hkey⟩ :=
          nodeGot_put_source hresult hsend
        obtain ⟨loadedKey, hget, hsnapshot⟩ :=
          hgots hstore hevent
        obtain ⟨ownerNode, loading, hownerState, hownerHistory,
            hloadingPhase, hloadedKey⟩ := hgets hget
        rw [hnode] at hownerState
        cases Concrete.Local.node.inj hownerState
        have hsourceHistory := hnodeValid.2.2 hsource
        have hsame := hnodeValid.history_eq hsourceHistory hownerHistory
        subst loading
        have hkeys : loadedKey = key :=
          hloadedKey.symm.trans hkey
        subst loadedKey
        subst loaded
        exact ⟨nextNode, writing, provenance, hstate,
          hhistory, howns, by simpa [hkey] using hsnapshot⟩
      all_goals
        simp_all [Concrete.Node.takeFlight, Concrete.Node.await,
          Concrete.sendOutputs, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

def OwnedPutSnapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {store address op key document expectedVersion},
    world.process .store = .store store →
    (.server address, .store,
      Concrete.Msg.call op (.put key document expectedVersion)) ∈
        world.network →
    ∃ node writing,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      world.process (.server address) = .node node ∧
      (op, writing) ∈ node.history ∧
      FlightOwns writing provenance ∧
      Snapshot store key provenance.loaded

theorem ownedPutSnapshots_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    OwnedPutSnapshots
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro store address op key document expectedVersion hstore hmem
  contradiction

theorem ownedPutSnapshots_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hstoreExists : StoreExists world)
    (hnodes : NodesValid world)
    (hgets : OwnedGets world)
    (hgots : GotSnapshots world)
    (hinvariant : OwnedPutSnapshots world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    OwnedPutSnapshots next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro store address op key document expectedVersion hstore hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨node, writing, provenance, hnode, hhistory,
            howns, hsnapshot⟩ := hinvariant hstore hold
        exact ⟨node, writing, provenance, hnode, hhistory,
          howns, hsnapshot⟩
      · obtain ⟨_, _, heq⟩ := hnew
  | outside htime hmessage =>
      exact hinvariant
  | @process process now event result htime hprocess hvalid hresult =>
      intro nextStore address op key document expectedVersion
        hnextStore hmem
      obtain ⟨store, hstore⟩ := hstoreExists
      have heffect :
          nextStore = store ∨
            ∃ writtenKey written,
              nextStore = store.commit writtenKey written := by
        by_cases hp : process = Concrete.Pid.store
        · subst process
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          exact heffect
        · have heq : store = nextStore := by
            have hx : world.process .store = .store nextStore := by
              simpa [World.land, Ne.symm hp] using hnextStore
            rw [hstore] at hx
            exact Concrete.Local.store.inj hx
          exact .inl heq.symm
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨node, writing, provenance, hnode, hhistory,
            howns, hsnapshot⟩ := hinvariant hstore hold
        by_cases hp : process = .server address
        · subst process
          have hresult' := hresult
          rw [hnode] at hresult'
          obtain ⟨updated, hstate, hmono⟩ :=
            server_step_history_mono hresult'
          refine ⟨updated, writing, provenance, ?_,
            hmono _ hhistory, howns, ?_⟩
          · simp [World.land, hstate]
          · rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
            · exact hsnapshot
            · exact Snapshot.commit hsnapshot
        · refine ⟨node, writing, provenance, ?_,
            hhistory, howns, ?_⟩
          · simp [World.land, Ne.symm hp, hnode]
          · rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
            · exact hsnapshot
            · exact Snapshot.commit hsnapshot
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        have haddress : address ∈ nodes := hprocess
        cases hlocal : world.process (.server address) with
        | node node =>
            have hnodeValid := hnodes address haddress node hlocal
            have hresult' := hresult
            rw [hlocal] at hresult'
            obtain ⟨updated, writing, provenance, hstate,
                hhistory, howns, hsnapshot⟩ :=
              new_put_owned_snapshot hstore hlocal hnodeValid
                hgets hgots hvalid hresult' hsent
            have hsame : nextStore = store := by
              have hx :
                  world.process .store = .store nextStore := by
                simpa [World.land] using hnextStore
              rw [hstore] at hx
              exact (Concrete.Local.store.inj hx).symm
            refine ⟨updated, writing, provenance, ?_,
              hhistory, howns, ?_⟩
            · simp [World.land, hstate]
            · simpa [hsame] using hsnapshot
        | outside =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction
        | store store =>
            simp [hlocal, Concrete.step, Outcomes.one] at hresult
            subst result
            contradiction

theorem reachable_owned_put_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    OwnedPutSnapshots world := by
  induction hreachable with
  | init hinit => exact ownedPutSnapshots_initial _
  | step hreachable hstep hinvariant =>
      exact ownedPutSnapshots_step
        (reachable_store_exists hreachable)
        (reachable_nodes_valid hreachable)
        (reachable_owned_gets hreachable)
        (reachable_got_snapshots hreachable)
        hinvariant hstep

theorem reachable_put_address
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} {op : Concrete.OpId} {key : Concrete.Key}
    {document : Promise} {expectedVersion : Option Concrete.Version}
    (hput :
      (.server address, .store,
        Concrete.Msg.call op (.put key document expectedVersion)) ∈
          world.network) :
    address ∈ nodes := by
  induction hreachable with
  | init hinit => contradiction
  | step hreachable hstep ih =>
      cases hstep with
      | inject htime hprocess hinject =>
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at hput
          rcases hput with hold | hnew
          · exact ih hold
          · obtain ⟨_, _, heq⟩ := hnew
      | outside htime hmessage =>
          exact ih hput
      | @process process now event result htime hprocess hvalid hresult =>
          simp only [World.land, List.mem_append] at hput
          rcases hput with hold | hnew
          · exact ih hold
          · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
            obtain ⟨target, message⟩ := sent
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            exact hprocess

def Covered (abstract : World AModel) (outputs : List Output) : Prop :=
  ∀ output ∈ outputs,
    (Abstract.Pid.service, Abstract.Pid.outside,
      Message.output output) ∈ abstract.network

structure Related (nodes : List Addr) (appConfig : Resonate.Config)
    (concrete : World (CModel nodes appConfig))
    (abstract : World AModel) : Prop where
  time : abstract.now ≤ concrete.now
  store : ∃ store,
    concrete.process .store = .store store ∧
    StoreRep store (abstract.process .service)
  known : ∀ {address call},
    (.outside, .server address, Concrete.Msg.request call) ∈
      concrete.network →
    (Abstract.Pid.outside, Abstract.Pid.service,
      Message.request call) ∈ abstract.network
  outputs : ∀ {address output},
    (.server address, .outside, Concrete.Msg.output output) ∈
      concrete.network →
    (Abstract.Pid.service, Abstract.Pid.outside,
      Message.output output) ∈ abstract.network
  written : ∀ {address op},
    (.store, .server address, Concrete.Msg.reply op .written) ∈
      concrete.network →
    ∃ node writing key document expectedVersion,
      ∃ provenance :
          PutProvenance appConfig key document expectedVersion,
      concrete.process (.server address) = .node node ∧
      (op, writing) ∈ node.history ∧
      FlightOwns writing provenance ∧
      Covered abstract provenance.outputs

theorem covered_append {abstract : World AModel}
    {outputs : List Output} (h : Covered abstract outputs)
    (messages : List (Abstract.Pid × Abstract.Pid × Message)) :
    ∀ output ∈ outputs,
      (Abstract.Pid.service, Abstract.Pid.outside,
        Message.output output) ∈ abstract.network ++ messages := by
  intro output houtput
  exact List.mem_append_left _ (h output houtput)

theorem nodeGot_output_source
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {gotOp : Concrete.OpId}
    {loaded : Option (Promise × Concrete.Version)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {output : Output}
    (hvalid : NodeValid node)
    (hresult :
      result ∈
        (Concrete.nodeGotResults appConfig node gotOp loaded).val)
    (hsend :
      (.outside, Concrete.Msg.output output) ∈ result.send) :
    ∃ flight,
      (gotOp, flight) ∈ node.history ∧
      output = Concrete.unavailable flight.call := by
  generalize htake : Concrete.Node.takeFlight node gotOp = taken
  obtain ⟨active, nextNode⟩ := taken
  simp only [Concrete.nodeGotResults, htake] at hresult
  cases active with
  | none =>
      simp [Outcomes.one] at hresult
      subst result
      contradiction
  | some flight =>
      have hflight : (gotOp, flight) ∈ node.history := by
        apply hvalid.2.2
        apply find_flight_mem
        simpa [Concrete.Node.takeFlight] using congrArg Prod.fst htake
      cases hphase : flight.phase with
      | writing =>
          simp [hphase, Outcomes.one] at hresult
          subst result
          contradiction
      | loading =>
          simp only [hphase] at hresult
          split at hresult
          · simp only [Concrete.decideResults, List.mem_map] at hresult
            obtain ⟨outcome, houtcome, rfl⟩ := hresult
            obtain ⟨after, outputs⟩ := outcome
            split at hsend
            · simp only [Concrete.sendOutputs, List.mem_singleton,
                Prod.mk.injEq, Concrete.Msg.output.injEq] at hsend
              have heq : output = Concrete.unavailable flight.call := by
                simpa [Concrete.sendOutputs] using hsend
              exact ⟨flight, hflight, heq⟩
            · split at hsend
              · contradiction
              · simp only [Concrete.sendOutputs, List.mem_singleton,
                  Prod.mk.injEq, Concrete.Msg.output.injEq] at hsend
                have heq : output = Concrete.unavailable flight.call := by
                  simpa [Concrete.sendOutputs] using hsend
                exact ⟨flight, hflight, heq⟩
          · simp [Outcomes.one, Concrete.sendOutputs] at hresult
            subst result
            simp only [List.mem_singleton, Prod.mk.injEq,
              Concrete.Msg.output.injEq] at hsend
            exact ⟨flight, hflight, hsend.2⟩

theorem server_output_classify
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {output : Output}
    (hvalid : NodeValid node)
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val)
    (hsend : (.outside, Concrete.Msg.output output) ∈ result.send) :
    (∃ op, event = .receive .store (.reply op .written)) ∨
    (∀ written, event ≠ .receive .store (.reply written .written)) ∧
      ∃ op flight,
        (op, flight) ∈ node.history ∧
        output = Concrete.unavailable flight.call := by
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases sender <;> cases message
      all_goals simp only [Concrete.step] at hresult
      case receive.store.replyGot gotOp loaded =>
        obtain ⟨flight, hhistory, houtput⟩ :=
          nodeGot_output_source hvalid hresult hsend
        exact .inr ⟨by simp, gotOp, flight, hhistory, houtput⟩
      case receive.store.replyWritten op =>
        exact .inl ⟨op, rfl⟩
      case receive.store.replyFailed op =>
        generalize htake : Concrete.Node.takeFlight node op = taken
        obtain ⟨active, nextNode⟩ := taken
        simp only [htake] at hresult
        cases active with
        | none =>
            simp [Outcomes.one] at hresult
            subst result
            contradiction
        | some flight =>
            have hhistory : (op, flight) ∈ node.history := by
              apply hvalid.2.2
              apply find_flight_mem
              simpa [Concrete.Node.takeFlight] using
                congrArg Prod.fst htake
            simp [Outcomes.one] at hresult
            subst result
            have houtput : output = Concrete.unavailable flight.call := by
              simpa [Concrete.sendOutputs] using hsend
            exact .inr ⟨by simp, op, flight, hhistory, houtput⟩
      case receive.store.replyConflict op =>
        generalize htake : Concrete.Node.takeFlight node op = taken
        obtain ⟨active, nextNode⟩ := taken
        simp only [htake] at hresult
        cases active with
        | none =>
            simp [Outcomes.one] at hresult
            subst result
            contradiction
        | some flight =>
            have hhistory : (op, flight) ∈ node.history := by
              apply hvalid.2.2
              apply find_flight_mem
              simpa [Concrete.Node.takeFlight] using
                congrArg Prod.fst htake
            cases hphase : flight.phase with
            | loading =>
                simp [hphase, Outcomes.one] at hresult
                subst result
                contradiction
            | writing =>
                simp only [hphase] at hresult
                split at hresult
                · simp [Outcomes.one] at hresult
                  subst result
                  contradiction
                · simp [Outcomes.one] at hresult
                  subst result
                  have houtput :
                      output = Concrete.unavailable flight.call := by
                    simpa [Concrete.sendOutputs] using hsend
                  exact .inr ⟨by simp, op, flight, hhistory, houtput⟩
      all_goals
        simp_all [Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.sendOutputs, Outcomes.one,
          NodeValid]
      all_goals grind [find_flight_mem]

theorem written_output_covered
    {nodes : List Addr} {appConfig : Resonate.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    {config : Concrete.Config} {address : Addr} {node : Concrete.Node}
    {op : Concrete.OpId}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hnode : concrete.process (.server address) = .node node)
    (hvalid : NodeValid node)
    (hevent :
      Event.Valid concrete (.server address)
        (.receive .store (.reply op .written)))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node) 0
          (.receive .store (.reply op .written))).val) :
    ∀ output,
      (.outside, Concrete.Msg.output output) ∈ result.send →
      (Abstract.Pid.service, Abstract.Pid.outside,
        Message.output output) ∈ abstract.network := by
  obtain ⟨ownerNode, writing, key, document, expectedVersion,
      provenance, howner, hhistory, howns, hcovered⟩ :=
    related.written hevent
  rw [hnode] at howner
  cases Concrete.Local.node.inj howner
  generalize htake : Concrete.Node.takeFlight node op = taken
  obtain ⟨active, nextNode⟩ := taken
  simp only [Concrete.Msg.reply, Concrete.step, htake] at hresult
  cases active with
  | none =>
      simp [Outcomes.one] at hresult
      subst result
      intro output hsend
      contradiction
  | some active =>
      have hactive : (op, active) ∈ node.history := by
        apply hvalid.2.2
        apply find_flight_mem
        simpa [Concrete.Node.takeFlight] using
          congrArg Prod.fst htake
      have heq := hvalid.history_eq hactive hhistory
      subst writing
      rcases howns with ⟨hcall, hloaded, hafter, hdocument,
        hselectedEq, hwriting⟩
      cases hphase : active.phase with
      | loading =>
          simp [hphase, Outcomes.one] at hresult
          subst result
          intro output hsend
          contradiction
      | writing =>
          simp [hphase, Outcomes.one] at hresult
          subst result
          intro output hsend
          have hselected : output ∈ active.selected := by
            simpa [Concrete.sendOutputs] using hsend
          rw [hselectedEq] at hselected
          exact hcovered output hselected

theorem nonwritten_output_singleton
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    {output : Output}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val)
    (hnotWritten :
      ∀ op, event ≠ .receive .store (.reply op .written))
    (hsend : (.outside, Concrete.Msg.output output) ∈ result.send) :
    result.send = [(.outside, Concrete.Msg.output output)] := by
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.sendOutputs, Concrete.Msg.reply,
          Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply,
        Concrete.Msg.call, Concrete.Msg.reply]

theorem result_sends_no_request
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {pid : Concrete.Pid} {localState : Concrete.Local}
    {stepNow : Time} {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config pid localState stepNow event).val) :
    ∀ recipient call,
      (recipient, Concrete.Msg.request call) ∉ result.send := by
  intro recipient call hsend
  cases pid <;> cases localState <;> cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.storePutResults,
          Concrete.sendOutputs, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

theorem server_sends_no_written
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val) :
    ∀ target op,
      (target, Concrete.Msg.reply op .written) ∉ result.send := by
  intro target op hsend
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.nodeGotResults,
          Concrete.decideResults, Concrete.Node.takeFlight,
          Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

theorem store_sends_no_output
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {store : Concrete.Store}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store (.store store)
          0 event).val) :
    ∀ output, (.outside, Concrete.Msg.output output) ∉ result.send := by
  intro output hsend
  cases event with
  | timeout => simp_all [Concrete.step, Outcomes.one]
  | receive sender message =>
      cases message
      all_goals try { rename_i _ payload; cases payload }
      all_goals cases sender
      all_goals try { cases ‹Concrete.StoreRequest› }
      all_goals try { cases ‹Concrete.StoreReply› }
      all_goals
        simp_all [Concrete.step, Concrete.storePutResults, Outcomes.one]
      all_goals grind [Concrete.StoreRequest, Concrete.StoreReply]

theorem related_after_land
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract abstractNext : World AModel}
    (related : Related nodes appConfig concrete abstract)
    {pid : Concrete.Pid} {now stepNow : Time}
    {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config pid (concrete.process pid)
          stepNow event).val)
    (htime : abstractNext.now ≤ now)
    (hnet : ∀ {message},
      message ∈ abstract.network → message ∈ abstractNext.network)
    (hstore : ∃ store,
      (concrete.land pid now result).process .store = .store store ∧
      StoreRep store (abstractNext.process .service))
    (hnewOutput : ∀ {output},
      (Concrete.Pid.outside, Concrete.Msg.output output) ∈ result.send →
      (Abstract.Pid.service, Abstract.Pid.outside,
        Message.output output) ∈ abstractNext.network)
    (hnewWritten : ∀ {address op},
      (Concrete.Pid.server address, Concrete.Msg.reply op .written) ∈
        result.send →
      ∃ node writing key document expectedVersion,
        ∃ provenance :
            PutProvenance appConfig key document expectedVersion,
        (concrete.land pid now result).process (.server address) =
          .node node ∧
        (op, writing) ∈ node.history ∧
        FlightOwns writing provenance ∧
        Covered abstractNext provenance.outputs) :
    Related nodes appConfig (concrete.land pid now result)
      abstractNext := by
  refine {
    time := htime
    store := hstore
    known := ?_
    outputs := ?_
    written := ?_ }
  · intro address call hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · exact hnet (related.known hold)
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨recipient, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact (result_sends_no_request hresult _ _ hsent).elim
  · intro address output hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · exact hnet (related.outputs hold)
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨recipient, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hnewOutput hsent
  · intro address op hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · obtain ⟨node, writing, key, document, expectedVersion,
          provenance, hnode, hhistory, howns, hcovered⟩ :=
        related.written hold
      by_cases hp : pid = .server address
      · subst pid
        have hresult' := hresult
        rw [hnode] at hresult'
        obtain ⟨nextNode, hstate, hmono⟩ :=
          server_step_history_mono
            (by simpa [Concrete.step] using hresult')
        refine ⟨nextNode, writing, key, document, expectedVersion,
          provenance, ?_, hmono _ hhistory, howns, ?_⟩
        · simp [World.land, hstate]
        · exact fun output houtput => hnet (hcovered output houtput)
      · refine ⟨node, writing, key, document, expectedVersion,
          provenance, ?_, hhistory, howns, ?_⟩
        · simp [World.land, Ne.symm hp, hnode]
        · exact fun output houtput => hnet (hcovered output houtput)
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨recipient, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hnewWritten hsent

theorem linearize_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    {store : Concrete.Store}
    (hstoreLocal : concrete.process .store = .store store)
    {now : Time} {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store
          (concrete.process .store) now event).val)
    (htime : concrete.now ≤ now)
    {call : Call} {after : State} {outputs : List Output}
    (hrequest :
      (Abstract.Pid.outside, Abstract.Pid.service,
        Message.request call) ∈ abstract.network)
    (hrun :
      (after, outputs) ∈
        (Resonate.run { appConfig with unreliable := true }
          call (abstract.process .service)).val)
    (hstore : ∃ nextStore,
      (concrete.land .store now result).process .store =
        .store nextStore ∧ StoreRep nextStore after)
    (hnewWritten : ∀ {address op},
      (.server address, Concrete.Msg.reply op .written) ∈ result.send →
      ∃ node writing key document expectedVersion,
        ∃ provenance :
            PutProvenance appConfig key document expectedVersion,
        (concrete.land .store now result).process (.server address) =
          .node node ∧
        (op, writing) ∈ node.history ∧
        FlightOwns writing provenance ∧
        Covered
          (abstract.land .service now {
            state := after
            send := outputs.map fun value =>
              (.outside, .output value) })
          provenance.outputs) :
    ∃ abstractExecution,
      Legal AModel { appConfig with unreliable := true }
        abstract abstractExecution ∧
      Related nodes appConfig (concrete.land .store now result)
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution = [] := by
  let abstractResult : Result Abstract.Pid State Message := {
    state := after
    send := outputs.map fun output => (.outside, .output output)
  }
  let abstractLabel : Label AModel :=
    .process .service now (.receive .outside (.request call))
      abstractResult.send
  let abstractNext := abstract.land .service now abstractResult
  refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, rfl⟩
  · refine ⟨Step.process
      (Nat.le_trans related.time htime) rfl hrequest ?_, trivial⟩
    simp only [Abstract.step]
    exact List.mem_map.mpr ⟨(after, outputs), hrun, rfl⟩
  · apply related_after_land related hresult
    · exact Nat.le_refl now
    · intro message hmessage
      exact List.mem_append_left _ hmessage
    · simpa [endOf, abstractNext, abstractResult, World.land] using hstore
    · intro output hsent
      have hresult0 :
          result ∈
            (Concrete.step appConfig config .store (.store store)
              0 event).val := by
        simpa [Concrete.step, hstoreLocal] using hresult
      exact (store_sends_no_output hresult0 _ hsent).elim
    · intro address op hsent
      obtain ⟨node, writing, key, document, expectedVersion,
          provenance, hnode, hhistory, howns, hcover⟩ :=
        hnewWritten hsent
      refine ⟨node, writing, key, document, expectedVersion,
        provenance, hnode, hhistory, howns, ?_⟩
      intro output houtput
      exact hcover output houtput

theorem stutter_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    {store : Concrete.Store}
    (hstoreLocal : concrete.process .store = .store store)
    {now : Time} {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store
          (concrete.process .store) now event).val)
    (htime : concrete.now ≤ now)
    (hstate : result.state = .store store)
    (hnoWritten : ∀ {address op},
      (.server address, Concrete.Msg.reply op .written) ∉ result.send) :
    Related nodes appConfig (concrete.land .store now result) abstract := by
  apply related_after_land related hresult
  · exact Nat.le_trans related.time htime
  · exact fun h => h
  · obtain ⟨represented, hrepresented, hrep⟩ := related.store
    rw [hstoreLocal] at hrepresented
    cases Concrete.Local.store.inj hrepresented
    exact ⟨store, by simp [World.land, hstate], hrep⟩
  · intro output hsent
    have hresult0 :
        result ∈
          (Concrete.step appConfig config .store (.store store)
            0 event).val := by
      simpa [Concrete.step, hstoreLocal] using hresult
    exact (store_sends_no_output hresult0 _ hsent).elim
  · intro address op hsent
    exact (hnoWritten hsent).elim

def concreteObservation {nodes : List Addr} {appConfig : Resonate.Config}
    (label : Label (CModel nodes appConfig)) :
    List Resonate.BoundaryEvent :=
  label.observe.filterMap (Concrete.boundaryEvent nodes appConfig)

def labelTime {model : Model} : Label model → Time
  | .input _ time _ => time
  | .process _ time _ _ => time
  | .outside _ time _ => time

theorem simulate_server_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {now : Time} {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.server address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.server address)
          (concrete.process (.server address)) now event).val) :
    ∃ abstractExecution,
      Legal AModel { appConfig with unreliable := true }
        abstract abstractExecution ∧
      Related nodes appConfig
        (concrete.land (.server address) now result)
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution = [] := by
  obtain ⟨node, hnode⟩ :=
    reachable_server_node hreachable haddress
  have hresult0 :
      result ∈
        (Concrete.step appConfig config (.server address) (.node node)
          0 event).val := by
    simpa [Concrete.step, hnode] using hresult
  have hnodeValid :=
    reachable_nodes_valid hreachable address haddress node hnode
  by_cases hsend :
      ∃ output, (.outside, Concrete.Msg.output output) ∈ result.send
  · obtain ⟨output, houtput⟩ := hsend
    rcases server_output_classify hnodeValid hresult0 houtput with
      ⟨op, hevent⟩ |
        ⟨hnotWritten, op, flight, hhistory, hout⟩
    · subst event
      have hall := written_output_covered related hnode hnodeValid
        hvalid hresult0
      refine ⟨[], trivial, ?_, rfl⟩
      apply related_after_land related hresult
      · exact Nat.le_trans related.time htime
      · exact fun h => h
      · obtain ⟨store, hstore, hrep⟩ := related.store
        exact ⟨store, by simpa [World.land] using hstore, hrep⟩
      · exact fun hsent => hall _ hsent
      · intro target written hsent
        exact (server_sends_no_written hresult0 _ _ hsent).elim
    · have hrequestC :=
        reachable_history_calls hreachable address haddress node op flight
          hnode hhistory
      have hrequestA := related.known hrequestC
      have hsingle :=
        nonwritten_output_singleton hresult0 hnotWritten houtput
      subst output
      let abstractResult : Result Abstract.Pid State Message := {
        state := abstract.process .service
        send := [(.outside, .output (Concrete.unavailable flight.call))]
      }
      let abstractLabel : Label AModel :=
        .process .service now
          (.receive .outside (.request flight.call))
          abstractResult.send
      let abstractNext := abstract.land .service now abstractResult
      refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, ?_⟩
      · refine ⟨Step.process
          (Nat.le_trans related.time htime) rfl hrequestA ?_, trivial⟩
        simp only [Abstract.step]
        exact List.mem_map.mpr
          ⟨(abstract.process .service,
            [Concrete.unavailable flight.call]),
            run_shed appConfig flight.call (abstract.process .service),
            rfl⟩
      · apply related_after_land related hresult
        · exact Nat.le_refl now
        · intro message hmessage
          exact List.mem_append_left _ hmessage
        · obtain ⟨store, hstore, hrep⟩ := related.store
          refine ⟨store, ?_, ?_⟩
          · simpa [World.land] using hstore
          · change StoreRep store (abstractNext.process .service)
            simpa [abstractNext, abstractResult, World.land] using hrep
        · intro sent hsent
          rw [hsingle] at hsent
          simp only [List.mem_singleton, Prod.mk.injEq,
            Concrete.Msg.output.injEq] at hsent
          have heq : sent = Concrete.unavailable flight.call := hsent.2
          subst sent
          simp [endOf, abstractNext, abstractResult, World.land]
        · intro target written hsent
          exact (server_sends_no_written hresult0 _ _ hsent).elim
      · rfl
  · refine ⟨[], trivial, ?_, rfl⟩
    apply related_after_land related hresult
    · exact Nat.le_trans related.time htime
    · exact fun h => h
    · obtain ⟨store, hstore, hrep⟩ := related.store
      exact ⟨store, by simpa [World.land] using hstore, hrep⟩
    · intro output houtput
      exact (hsend ⟨output, houtput⟩).elim
    · intro target written hsent
      exact (server_sends_no_written hresult0 _ _ hsent).elim

theorem simulate_store_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config} (hconditional : config.conditional = true)
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig concrete abstract)
    {now : Time} {event : Event Concrete.Pid (Concrete.Msg appConfig)}
    {result : Result Concrete.Pid Concrete.Local (Concrete.Msg appConfig)}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete .store)
    (hresult :
      result ∈
        (Concrete.step appConfig config .store
          (concrete.process .store) now event).val) :
    ∃ abstractExecution,
      Legal AModel { appConfig with unreliable := true }
        abstract abstractExecution ∧
      Related nodes appConfig (concrete.land .store now result)
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution = [] := by
  obtain ⟨store, hstoreLocal, hrep⟩ := related.store
  have hresult0 :
      result ∈
        (Concrete.step appConfig config .store (.store store)
          0 event).val := by
    simpa [Concrete.step, hstoreLocal] using hresult
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult0
      subst result
      exact ⟨[], trivial,
        stutter_store related hstoreLocal hresult htime rfl (by simp),
        rfl⟩
  | receive sender message =>
      cases sender <;> cases message
      all_goals simp only [Concrete.step] at hresult0
      case receive.server.callPut address op key document expectedVersion =>
        have hput :
            (.server address, .store,
              Concrete.Msg.call op (.put key document expectedVersion)) ∈
                concrete.network := hvalid
        obtain ⟨node, writing, provenance, hnode, hhistory,
            howns, hsnapshot⟩ :=
          reachable_owned_put_snapshots hreachable hstoreLocal hput
        have haddress := reachable_put_address hreachable hput
        have hrequestC :=
          reachable_history_calls hreachable address haddress node op writing
            hnode hhistory
        rcases howns with ⟨hcall, hloaded, hafter, hdocument,
          hselected, hphase⟩
        have hrequestA := related.known (by simpa [hcall] using hrequestC)
        by_cases hmatch :
            expectedVersion = store.version key
        · have hloadedVersion :
              provenance.loaded.map (·.2) =
                (store.document key).map (·.2) := by
            rw [provenance.expected_eq, hmatch]
            rfl
          have hloadedCurrent :=
            Snapshot.eq_of_versions hsnapshot hloadedVersion
          by_cases hflaky : config.flaky
          · simp [Concrete.storePutResults, hconditional, hmatch,
              hflaky] at hresult0
            rcases hresult0 with rfl | rfl | rfl
            · obtain ⟨globalAfter, hrun, hrepAfter⟩ :=
                provenance_transport hrep provenance hloadedCurrent
              apply linearize_store related hstoreLocal hresult htime
                hrequestA hrun
              · exact ⟨store.commit key document,
                  by simp [World.land], hrepAfter⟩
              · intro target writtenOp hsent
                simp only [Concrete.Msg.reply, List.mem_singleton,
                  Prod.mk.injEq, Concrete.Msg.replyWritten.injEq] at hsent
                obtain ⟨htarget, hop⟩ := hsent
                cases Concrete.Pid.server.inj htarget
                subst writtenOp
                refine ⟨node, writing, key, document, expectedVersion,
                  provenance, by simpa [World.land] using hnode,
                  hhistory, ?_, ?_⟩
                · exact ⟨hcall, hloaded, hafter, hdocument,
                    hselected, hphase⟩
                · intro output houtput
                  exact List.mem_append_right _
                    (List.mem_map.mpr
                      ⟨(.outside, .output output),
                        List.mem_map.mpr ⟨output, houtput, rfl⟩,
                        rfl⟩)
            · obtain ⟨globalAfter, failureOutputs, hrun,
                  hrepAfter, hunavailable⟩ :=
                provenance_transport_lose hrep provenance hloadedCurrent
              apply linearize_store related hstoreLocal hresult htime
                hrequestA hrun
              · exact ⟨store.commit key document,
                  by simp [World.land], hrepAfter⟩
              · intro target writtenOp hsent
                contradiction
            · apply linearize_store related hstoreLocal hresult htime
                hrequestA
                (run_shed appConfig provenance.call
                  (abstract.process .service))
              · exact ⟨store, by simp [World.land], hrep⟩
              · intro target writtenOp hsent
                contradiction
          · simp [Concrete.storePutResults, hconditional, hmatch,
              hflaky, Outcomes.one] at hresult0
            subst result
            obtain ⟨globalAfter, hrun, hrepAfter⟩ :=
              provenance_transport hrep provenance hloadedCurrent
            apply linearize_store related hstoreLocal hresult htime
              hrequestA hrun
            · exact ⟨store.commit key document,
                by simp [World.land], hrepAfter⟩
            · intro target writtenOp hsent
              simp only [Concrete.Msg.reply, List.mem_singleton,
                Prod.mk.injEq, Concrete.Msg.replyWritten.injEq] at hsent
              obtain ⟨htarget, hop⟩ := hsent
              cases Concrete.Pid.server.inj htarget
              subst writtenOp
              refine ⟨node, writing, key, document, expectedVersion,
                provenance, by simpa [World.land] using hnode,
                hhistory, ?_, ?_⟩
              · exact ⟨hcall, hloaded, hafter, hdocument,
                  hselected, hphase⟩
              · intro output houtput
                exact List.mem_append_right _
                  (List.mem_map.mpr
                    ⟨(.outside, .output output),
                      List.mem_map.mpr ⟨output, houtput, rfl⟩,
                      rfl⟩)
        · have hconflict :
              (expectedVersion != store.version key) = true :=
            bne_iff_ne.mpr hmatch
          simp [Concrete.storePutResults, hconditional,
            hconflict, Outcomes.one] at hresult0
          subst result
          exact ⟨[], trivial,
            stutter_store related hstoreLocal hresult htime rfl (by simp),
            rfl⟩
      all_goals
        simp [Outcomes.one] at hresult0
        subst result
        exact ⟨[], trivial,
          stutter_store related hstoreLocal hresult htime rfl (by simp),
          rfl⟩

theorem reachable_output_sender
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {sender : Concrete.Pid} {output : Output}
    (houtput :
      (sender, Concrete.Pid.outside, Concrete.Msg.output output) ∈
        world.network) :
    ∃ address, sender = .server address := by
  induction hreachable with
  | init hinit =>
      contradiction
  | @step previous label next hprevious hstep ih =>
      cases hstep with
      | inject htime hprocess hinject =>
          obtain ⟨call, rfl⟩ := hinject
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at houtput
          rcases houtput with hold | hnew
          · exact ih hold
          · simp only [Prod.mk.injEq] at hnew
            cases hnew.2.2
      | outside htime hmessage =>
          exact ih houtput
      | @process pid now event result htime hprocess hvalid hresult =>
          simp only [World.land, List.mem_append] at houtput
          rcases houtput with hold | hnew
          · exact ih hold
          · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
            obtain ⟨recipient, message⟩ := sent
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            cases pid with
            | outside => contradiction
            | server address => exact ⟨address, rfl⟩
            | store =>
                obtain ⟨store, hstore⟩ :=
                  reachable_store_exists hprevious
                have hresult0 :
                    result ∈
                      (Concrete.step appConfig config .store (.store store)
                        0 event).val := by
                  simpa [Concrete.step, hstore] using hresult
                exact (store_sends_no_output hresult0 output hsent).elim

theorem related_observeOutside
    {nodes : List Addr} {appConfig : Resonate.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    {now : Time} (hconcrete : concrete.now ≤ now)
    (habstract : abstract.now ≤ now) :
    Related nodes appConfig (concrete.observeOutside now)
      (abstract.observeOutside now) := by
  refine {
    time := Nat.le_refl now
    store := ?_
    known := ?_
    outputs := ?_
    written := ?_
  }
  · simpa only [World.observeOutside] using related.store
  · intro address call hmessage
    exact related.known hmessage
  · intro address output hmessage
    exact related.outputs hmessage
  · intro address op hmessage
    exact related.written hmessage

theorem related_after_concrete_observeOutside
    {nodes : List Addr} {appConfig : Resonate.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig concrete abstract)
    {now : Time} (htime : concrete.now ≤ now) :
    Related nodes appConfig (concrete.observeOutside now) abstract := by
  refine {
    time := Nat.le_trans related.time htime
    store := ?_
    known := ?_
    outputs := ?_
    written := ?_
  }
  · simpa only [World.observeOutside] using related.store
  · intro address call hmessage
    exact related.known hmessage
  · intro address output hmessage
    exact related.outputs hmessage
  · intro address op hmessage
    exact related.written hmessage

theorem simulate_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config} (hconditional : config.conditional = true)
    {concrete next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig concrete abstract)
    (step : Step (CModel nodes appConfig) config concrete label next) :
    ∃ abstractExecution,
      Legal AModel { appConfig with unreliable := true }
        abstract abstractExecution ∧
      Related nodes appConfig next
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution =
        concreteObservation label := by
  cases step with
  | @inject to now message htime hprocess hinject =>
      obtain ⟨call, rfl⟩ := hinject
      let abstractNext :=
        abstract.inject .service (.request call) now
      let abstractLabel : Label AModel :=
        .input .service now (.request call)
      refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, ?_⟩
      · refine ⟨Step.inject (Nat.le_trans related.time htime) rfl
          ⟨call, rfl⟩, trivial⟩
      · refine {
          time := Nat.le_refl _
          store := ?_
          known := ?_
          outputs := ?_
          written := ?_ }
        · simpa [World.inject, abstractNext, endOf] using related.store
        · intro address knownCall hmem
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hold | hnew
          · exact List.mem_append_left _ (related.known hold)
          · simp only [Prod.mk.injEq] at hnew
            obtain ⟨_, _, hmessage⟩ := hnew
            cases Concrete.Msg.request.inj hmessage
            exact List.mem_append_right _
              (by simp [abstractNext, World.inject, endOf])
        · intro address output hmem
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hold | hnew
          · exact List.mem_append_left _ (related.outputs hold)
          · simp only [Prod.mk.injEq] at hnew
            exact Concrete.Pid.noConfusion hnew.1
        · intro address op hmem
          obtain ⟨node, writing, key, document, expectedVersion,
              provenance, hnode, hhistory, howns, hcovered⟩ :=
            related.written (by
              simpa [World.inject] using hmem)
          refine ⟨node, writing, key, document, expectedVersion,
            provenance, ?_, hhistory, howns, ?_⟩
          · simpa [World.inject, abstractNext, endOf] using hnode
          · exact covered_append hcovered _
      · rfl
  | @process pid now event result htime hprocess hvalid hresult =>
      cases pid with
      | outside => contradiction
      | server address =>
          obtain ⟨execution, hlegal, hrelated, htrace⟩ :=
            simulate_server_step hreachable related hprocess htime hvalid hresult
          exact ⟨execution, hlegal, hrelated, by
            simpa only [concreteObservation, Label.observe,
              List.filterMap_nil] using htrace⟩
      | store =>
          obtain ⟨execution, hlegal, hrelated, htrace⟩ :=
            simulate_store_step hconditional hreachable related htime
              hvalid hresult
          exact ⟨execution, hlegal, hrelated, by
            simpa only [concreteObservation, Label.observe,
              List.filterMap_nil] using htrace⟩
  | @outside sender now message htime hmessage =>
      cases message with
      | output output =>
          obtain ⟨address, rfl⟩ :=
            reachable_output_sender hreachable hmessage
          have habstractMessage := related.outputs hmessage
          let abstractNext := abstract.observeOutside now
          let abstractLabel : Label AModel :=
            .outside .service now (.output output)
          refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, ?_⟩
          · exact ⟨Step.outside
              (Nat.le_trans related.time htime) habstractMessage, trivial⟩
          · exact related_observeOutside related htime
              (Nat.le_trans related.time htime)
          · cases output <;> rfl
      | request call =>
          refine ⟨[], trivial, ?_, rfl⟩
          exact related_after_concrete_observeOutside related htime
      | callGet op key
      | callPut op key document expectedVersion
      | replyGot op document
      | replyWritten op
      | replyConflict op
      | replyFailed op =>
            refine ⟨[], trivial, ?_, rfl⟩ <;>
            exact related_after_concrete_observeOutside related htime

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
    {nodes : List Addr} {appConfig : Resonate.Config}
    (label : Label (CModel nodes appConfig))
    (next : World (CModel nodes appConfig))
    (rest : Execution (CModel nodes appConfig)) :
    Concrete.boundaryTrace nodes appConfig ((label, next) :: rest) =
      concreteObservation label ++
        Concrete.boundaryTrace nodes appConfig rest := by
  simp [Concrete.boundaryTrace, concreteObservation, Rover.trace,
    List.filterMap_append]

theorem simulate_execution
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config} (hconditional : config.conditional = true)
    {concrete : World (CModel nodes appConfig)}
    {execution : Execution (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig concrete abstract)
    (legal : Legal (CModel nodes appConfig) config concrete execution) :
    ∃ abstractExecution,
      Legal AModel { appConfig with unreliable := true }
        abstract abstractExecution ∧
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
        simulate_step hconditional hreachable related legal.1
      have hnextReachable := Reachable.step hreachable legal.1
      obtain ⟨abstractTail, tailLegal, tailRelated, tailTrace⟩ :=
        ih hnextReachable headRelated legal.2
      refine ⟨abstractHead ++ abstractTail,
        legal_append headLegal tailLegal, ?_, ?_⟩
      · simpa only [endOf, endOf_append] using tailRelated
      · rw [abstract_boundaryTrace_append, headTrace, tailTrace,
          concrete_boundaryTrace_cons]

theorem initial_related
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    Related nodes appConfig (World.initial process)
      (World.initial Abstract.initialProcess) := by
  refine {
    time := Nat.le_refl 0
    store := ?_
    known := ?_
    outputs := ?_
    written := ?_
  }
  · refine ⟨{}, ?_, ?_⟩
    · simpa [World.initial] using hinit.2.1
    · intro key
      simp [World.initial, Concrete.Store.document, Experiment.promiseAt,
        Abstract.initialProcess]
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction

/-- End-to-end trace inclusion. For every duplicate-free server deployment,
every legal append-only concrete boundary trace is a boundary trace of the
unreliable one-process abstract promise service. -/
theorem boundary_refinement
    (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config)
    (hconditional : config.conditional = true) :
    ∀ events,
      Concrete.ValidBoundaryTrace nodes appConfig config events →
      Abstract.ValidBoundaryTrace
        { appConfig with unreliable := true } events := by
  intro events hvalid
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := hvalid
  have hreachable :
      Reachable (CModel nodes appConfig) config
        (World.initial process) :=
    Reachable.init hinit
  obtain ⟨abstractExecution, abstractLegal, _, abstractTrace⟩ :=
    simulate_execution hconditional hreachable (initial_related hinit) hlegal
  exact ⟨abstractExecution,
    ⟨Abstract.initialProcess,
      Abstract.initialProcess_valid
        { appConfig with unreliable := true },
      abstractLegal⟩,
    abstractTrace.trans htrace⟩

end Resonate.Refinement
