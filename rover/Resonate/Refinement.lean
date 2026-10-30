import Resonate.Concrete

/-!
# Concrete-to-abstract refinement infrastructure

The wire protocol remains untrusted and proof-free. Semantic provenance is
reconstructed here as a ghost predicate over node-local flights and reachable
network messages. The final simulation is factored into a one-step obligation
and an execution fold, so delayed/reordered outside observations do not need a
special trace argument.
-/

namespace Resonate.Refinement

open Rover
open Concrete

abbrev AModel := Abstract.model
abbrev CModel (nodes : List Addr) (appConfig : Resonate.Config) :=
  Concrete.model nodes appConfig

theorem committed_version (store : Concrete.Store)
    (key : DocumentKey) (document : Document key) :
    (store.commit key document).version key =
      some ((store.version key).getD 0 + 1) := by
  simp [Concrete.Store.commit, Concrete.Store.version]

theorem commit_frames (store : Concrete.Store)
    (key other : DocumentKey) (document : Document key)
    (h : other ≠ key) :
    (store.commit key document).read other = store.read other :=
  Concrete.Store.read_commit_other store key other document h

/-- Replaying an absent-version conditional PUT after it landed selects only
the conflict branch. This is the store-level duplicate-PUT safety fact. -/
theorem duplicate_absent_put_conflicts
    (sender : Concrete.Pid) (op : Concrete.OpId)
    (key : DocumentKey) (document : Document key) :
    (Concrete.storePut { conditional := true }
      sender (({} : Concrete.Store).commit key document)
      op key document none).val =
      [({
        state := .store (({} : Concrete.Store).commit key document)
        send := [(sender, .storeReply { op, payload := .conflict })]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg)] := by
  simp [Concrete.storePut, Concrete.Store.commit,
    Concrete.Store.version, Rover.Outcomes.one]

/-- Without conditional writes, replaying the same raw PUT commits again.
This is the protocol counterexample that makes `conditional = true` necessary
for boundary refinement under append-only duplicate delivery. -/
theorem unconditional_duplicate_put_relands
    (sender : Concrete.Pid) (op : Concrete.OpId)
    (key : DocumentKey) (document : Document key) :
    (Concrete.storePut { conditional := false, flaky := false }
      sender (({} : Concrete.Store).commit key document)
      op key document none).val =
      [({
        state := .store
          ((({} : Concrete.Store).commit key document).commit key document)
        send := [(sender, .storeReply { op, payload := .written })]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg)] := by
  simp [Concrete.storePut, Rover.Outcomes.one]

/-- Ghost meaning of a selected transaction. No field of this predicate is
serialized in `StoreRequest.put`. -/
inductive Selected (appConfig : Resonate.Config) :
    (key : DocumentKey) → Concrete.Transaction →
    Document key → Document key → List Output → List WorkflowEntry → Prop
  | external {key call before after outputs} :
      (Concrete.Transaction.external call).key? = some key →
      Resonate.run { appConfig with unreliable := true } call
          (Concrete.singleState key before) =
        (after, outputs) →
      Selected appConfig key (.external call) before
        (after.store.read key) outputs after.workflow.pending
  | work {item now rest before after outputs} :
      Resonate.runWork { appConfig with unreliable := true } item now rest
          (Concrete.singleState item.key before) =
        (after, outputs) →
      Selected appConfig item.key (.work item now rest) before
        (after.store.read item.key) outputs after.workflow.pending
  | scan {key now rest before after outputs} :
      Resonate.runScan { appConfig with unreliable := true } key now rest
          (Concrete.singleState key before) =
        (after, outputs) →
      Selected appConfig key (.scan key now rest) before
        (after.store.read key) outputs after.workflow.pending

theorem originSettledWork_key {origin : String}
    {object : OriginObject origin} {item : WorkItem}
    (h : item ∈ Direct.originSettledWork object) :
    item.key = .origin origin := by
  simp only [Direct.originSettledWork] at h
  split at h
  · contradiction
  · simp only [List.mem_append, List.mem_map] at h
    rcases h with ⟨awaiter, _, rfl⟩ | ⟨address, _, rfl⟩ <;>
      rfl

theorem originTaskWork_key {origin : String}
    {object : OriginObject origin} {now : Nat} {item : WorkItem}
    (h : item ∈ Direct.originTaskWork object now) :
    item.key = .origin origin := by
  cases ht : object.task with
  | none => simp [Direct.originTaskWork, ht] at h
  | some task =>
      simp only [Direct.originTaskWork, ht, List.mem_append] at h
      rcases h with h | h
      · cases hd : task.leaseTimeoutAt with
        | none => simp [hd] at h
        | some due =>
            split at h <;>
              simp_all [WorkItem.key, OriginObject.id]
      · cases hd : task.retryTimeoutAt with
        | none => simp [hd] at h
        | some due =>
            split at h <;>
              simp_all [WorkItem.key, OriginObject.id]

theorem originObjectWork_key {origin : String}
    {object : OriginObject origin} {now : Nat} {item : WorkItem}
    (h : item ∈ Direct.originObjectWork object now) :
    item.key = .origin origin := by
  simp only [Direct.originObjectWork, List.mem_append] at h
  rcases h with h | h
  · rcases h with h | h
    · split at h <;> simp_all [WorkItem.key, OriginObject.id]
    · exact originSettledWork_key h
  · exact originTaskWork_key h

theorem originWork_key {origin : String}
    {document : OriginDocument origin} {now : Nat} {item : WorkItem}
    (h : item ∈ Direct.originWork origin document now) :
    item.key = .origin origin := by
  simp only [Direct.originWork, List.mem_flatMap] at h
  obtain ⟨object, _, hitem⟩ := h
  exact originObjectWork_key hitem

theorem select_valid {appConfig : Resonate.Config}
    {flight : Concrete.Flight}
    {loaded : Option (Document flight.key × Concrete.Version)}
    {candidate : Concrete.Candidate flight.key}
    (hkey : flight.transaction.key? = some flight.key)
    (hselect : Concrete.select appConfig flight loaded = some candidate) :
    Selected appConfig flight.key flight.transaction
      (loaded.map (·.1) |>.getD (emptyDocument flight.key))
      candidate.document candidate.outputs candidate.continuations := by
  cases flight with
  | mk flightKey transaction flightLoaded flightDocument flightSelected
      flightContinuations flightAttempt flightPhase =>
    cases transaction
    case external call =>
      simp only [Concrete.select] at hselect
      cases hselect
      exact .external hkey rfl
    case work item now rest =>
      simp only [Concrete.select] at hselect
      split at hselect
      next heq =>
        subst flightKey
        cases hselect
        exact .work rfl
      next _ => contradiction
    case scan key now rest =>
      simp only [Concrete.select] at hselect
      split at hselect
      next heq =>
        subst flightKey
        cases hselect
        exact .scan rfl
      next _ => contradiction

/-- Reachable raw-PUT provenance. `loaded`, transaction, response/emissions,
and continuation work are ghost facts, not request payload fields. -/
structure PutProvenance (appConfig : Resonate.Config)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) where
  transaction : Concrete.Transaction
  loaded : Option (Document key × Concrete.Version)
  outputs : List Output
  continuations : List WorkflowEntry
  expected_eq : loaded.map (·.2) = expectedVersion
  selected : Selected appConfig key transaction
    (loaded.map (·.1) |>.getD (emptyDocument key))
    document outputs continuations

def ValidPut (appConfig : Resonate.Config)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) : Prop :=
  Nonempty (PutProvenance appConfig key document expectedVersion)

def Snapshot (store : Concrete.Store) (key : DocumentKey) :
    Option (Document key × Concrete.Version) → Prop
  | none => True
  | some (document, version) =>
      ∃ currentDocument currentVersion,
        store.read key = some (currentDocument, currentVersion) ∧
        version ≤ currentVersion ∧
        (version = currentVersion → document = currentDocument)

theorem Snapshot.of_read {store : Concrete.Store} {key : DocumentKey}
    {loaded : Option (Document key × Concrete.Version)}
    (h : store.read key = loaded) : Snapshot store key loaded := by
  cases loaded with
  | none => trivial
  | some value =>
      exact ⟨value.1, value.2, h, Nat.le_refl _, fun _ => rfl⟩

theorem Snapshot.commit {store : Concrete.Store}
    {loadedKey writtenKey : DocumentKey}
    {loaded : Option (Document loadedKey × Concrete.Version)}
    {written : Document writtenKey}
    (h : Snapshot store loadedKey loaded) :
    Snapshot (store.commit writtenKey written) loadedKey loaded := by
  cases loaded with
  | none => trivial
  | some value =>
      obtain ⟨document, version⟩ := value
      obtain ⟨current, currentVersion, hread, hle, heq⟩ := h
      by_cases hk : loadedKey = writtenKey
      · subst writtenKey
        refine ⟨written, currentVersion + 1, ?_, Nat.le_trans hle
          (Nat.le_succ _), ?_⟩
        · simp [Concrete.Store.version_eq_read, hread]
        · intro hversion
          exact (Nat.ne_of_lt (Nat.lt_succ_of_le hle) hversion).elim
      · exact ⟨current, currentVersion,
          by simpa [hk] using hread, hle, heq⟩

theorem Snapshot.eq_of_version {store : Concrete.Store}
    {key : DocumentKey}
    {loaded : Option (Document key × Concrete.Version)}
    (hsnapshot : Snapshot store key loaded)
    (hversion : loaded.map (·.2) = store.version key) :
    store.read key = loaded := by
  cases loaded with
  | none =>
      cases hcurrent : store.read key with
      | none => simpa using hcurrent
      | some current =>
          have : store.version key = some current.2 := by
            simp [Concrete.Store.version_eq_read, hcurrent]
          simp [this] at hversion
  | some loaded =>
      obtain ⟨document, version⟩ := loaded
      obtain ⟨current, currentVersion, hread, hle, heq⟩ := hsnapshot
      have hv : store.version key = some currentVersion := by
        simp [Concrete.Store.version_eq_read, hread]
      simp [hv] at hversion
      cases hversion
      rw [hread, heq rfl]

theorem Snapshot.expected_ne_commit_version
    {store : Concrete.Store} {key : DocumentKey}
    {loaded : Option (Document key × Concrete.Version)}
    {document : Document key}
    (hsnapshot : Snapshot store key loaded) :
    loaded.map (·.2) ≠ (store.commit key document).version key := by
  cases loaded with
  | none =>
      simp [committed_version]
  | some value =>
      obtain ⟨loadedDocument, loadedVersion⟩ := value
      obtain ⟨currentDocument, currentVersion, hread, hle, heq⟩ :=
        hsnapshot
      have hversion :
          store.version key = some currentVersion := by
        simpa [Concrete.Store.version_eq_read, hread]
      rw [committed_version, hversion]
      simp only [Option.getD, Option.map_some]
      intro hversionEq
      exact Nat.ne_of_lt (Nat.lt_succ_of_le hle)
        (Option.some.inj hversionEq)

/-- A typed external transaction depends only on its selected document.
Lifting it from a singleton store to a represented global store preserves the
response/emissions and frames every other document. -/
theorem external_locality
    (config : Resonate.Config) (call : Call)
    (key : DocumentKey) (before : Document key) (global : State)
    (hkey : (Concrete.Transaction.external call).key? = some key)
    (hread : global.store.read key = before) :
    let selected := Resonate.run config call
      (Concrete.singleState key before)
    let lifted := Resonate.run config call global
    lifted.1.store.read key = selected.1.store.read key ∧
    lifted.1.workflow = global.workflow ∧
    lifted.2 = selected.2 := by
  cases request : call.request <;>
    simp only [Concrete.Transaction.key?, request] at hkey
  case taskHeartbeat req =>
    cases tasks : req.tasks with
    | nil => simp [tasks] at hkey
    | cons first rest =>
        simp only [tasks] at hkey
        split at hkey
        next hsame =>
          simp only [Option.some.injEq] at hkey
          subst key
          simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
            Concrete.singleState, Direct.runWith, hread, tasks, request,
            hsame]
        next _ => contradiction
  all_goals
    first
    | contradiction
    | rename_i req
      first
      | (split at hkey
         all_goals try contradiction
         all_goals simp only [Option.some.injEq] at hkey
         all_goals subst key
         all_goals
           simp [Resonate.run, Resonate.handleExternal,
             Resonate.runDocument, Concrete.singleState, Direct.runWith,
             hread, request] <;>
           split <;> simp [Resonate.pureRequest, hread])
      | (cases hkey
         simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
           Concrete.singleState, Direct.runWith, hread, request]
         all_goals split <;> simp [Resonate.pureRequest, hread])

theorem Selected.external_continuations_nil
    {appConfig : Resonate.Config} {key : DocumentKey} {call : Call}
    {before after : Document key} {outputs : List Output}
    {continuations : List WorkflowEntry}
    (hselected :
      Selected appConfig key (.external call) before after outputs
        continuations) :
    continuations = [] := by
  cases hselected with
  | external hkey hrun =>
      have hlocal :=
        external_locality { appConfig with unreliable := true } call key
          before (Concrete.singleState key before) hkey (by
            exact Resonate.Store.read_write_same _ _ _)
      rw [hrun] at hlocal
      have hworkflow :=
        congrArg WorkflowState.pending hlocal.2.1
      simpa [Concrete.singleState] using hworkflow

theorem external_frame
    (config : Resonate.Config) (call : Call)
    (key other : DocumentKey) (global : State)
    (hkey : (Concrete.Transaction.external call).key? = some key)
    (hne : other ≠ key) :
    (Resonate.run config call global).1.store.read other =
      global.store.read other := by
  cases request : call.request <;>
    simp only [Concrete.Transaction.key?, request] at hkey
  case taskHeartbeat req =>
    cases tasks : req.tasks with
    | nil => simp [tasks] at hkey
    | cons first rest =>
        simp only [tasks] at hkey
        split at hkey
        next hsame =>
          simp only [Option.some.injEq] at hkey
          subst key
          simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
            Direct.runWith, tasks, request, hne, hsame]
        next _ => contradiction
  all_goals
    first
    | contradiction
    | rename_i req
      first
      | (split at hkey
         all_goals try contradiction
         all_goals simp only [Option.some.injEq] at hkey
         all_goals subst key
         all_goals
           simp [Resonate.run, Resonate.handleExternal,
             Resonate.runDocument, Direct.runWith, request, hne] <;>
           split <;> simp [Resonate.pureRequest, hne])
      | (cases hkey
         simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
           Direct.runWith, request, hne]
         all_goals split <;> simp [Resonate.pureRequest, hne])

/-- Internal work has the same document-local lifting property, including its
process-local continuation result. -/
theorem work_locality
    (config : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (key : DocumentKey)
    (before : Document key) (global : State)
    (hkey : item.key = key)
    (hread : global.store.read key = before) :
    let selected := Resonate.runWork config item now rest
      (Concrete.singleState key before)
    let lifted := Resonate.runWork config item now rest global
    lifted.1.store.read key = selected.1.store.read key ∧
    lifted.1.workflow = selected.1.workflow ∧
    lifted.2 = selected.2 := by
  subst key
  cases item <;>
    simp [Resonate.runWork, Resonate.runDocument,
      Concrete.singleState, Direct.runWith, WorkItem.key] at hread ⊢
  all_goals rw [hread]
  all_goals simp

theorem work_store_locality
    (config : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (key : DocumentKey)
    (before : Document key) (global : State)
    (hkey : item.key = key)
    (hread : global.store.read key = before) :
    let selected := Resonate.runWork config item now rest
      (Concrete.singleState key before)
    let lifted := Resonate.runWork config item now rest global
    lifted.1 =
      { global with
        store := global.store.write key (selected.1.store.read key)
        workflow := selected.1.workflow } ∧
    lifted.2 = selected.2 := by
  subst key
  cases item <;>
    simp [Resonate.runWork, Resonate.runDocument,
      Concrete.singleState, Direct.runWith, WorkItem.key] at hread ⊢
  all_goals rw [hread]
  all_goals simp

theorem scan_locality
    (config : Resonate.Config) (key : DocumentKey) (now : Time)
    (rest : List WorkflowEntry) (before : Document key) (global : State)
    (hread : global.store.read key = before) :
    let selected := Resonate.runScan config key now rest
      (Concrete.singleState key before)
    let lifted := Resonate.runScan config key now rest global
    lifted.1.store.read key = selected.1.store.read key ∧
    lifted.1.workflow = selected.1.workflow ∧
    lifted.2 = selected.2 := by
  cases key <;>
    simp [Resonate.runScan, Resonate.runDocument,
      Concrete.singleState, Direct.runWith] at hread ⊢ <;>
    rw [hread] <;> simp

theorem external_key_mem
    (config : Resonate.Config) (call : Call) (state : State)
    (key : DocumentKey)
    (hkey : (Concrete.Transaction.external call).key? = some key) :
    key ∈ (Resonate.run config call state).1.store.keys := by
  cases request : call.request <;>
    simp only [Concrete.Transaction.key?, request] at hkey
  case taskHeartbeat req =>
    cases tasks : req.tasks with
    | nil => simp [tasks] at hkey
    | cons first rest =>
        simp only [tasks] at hkey
        split at hkey
        next hsame =>
          simp only [Option.some.injEq] at hkey
          subst key
          simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
            Direct.runWith, tasks, request, hsame]
        next _ => contradiction
  all_goals
    first
    | contradiction
    | rename_i req
      first
      | (split at hkey
         all_goals try contradiction
         all_goals simp only [Option.some.injEq] at hkey
         all_goals subst key
         all_goals
           simp [Resonate.run, Resonate.handleExternal,
             Resonate.runDocument, Direct.runWith, request] <;>
           split <;> simp [Resonate.pureRequest])
      | (cases hkey
         simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
           Direct.runWith, request]
         all_goals split <;> simp [Resonate.pureRequest])
  all_goals simp_all

theorem external_key_none
    (config : Resonate.Config) (call : Call) (state : State)
    (hkey : (Concrete.Transaction.external call).key? = none) :
    let selected := Resonate.run config call {}
    let lifted := Resonate.run config call state
    (∀ key, lifted.1.store.read key = state.store.read key) ∧
      lifted.1.workflow = state.workflow ∧ lifted.2 = selected.2 := by
  cases request : call.request <;>
    simp only [Concrete.Transaction.key?, request] at hkey
  case taskHeartbeat req =>
    cases tasks : req.tasks with
    | nil =>
        simp [Resonate.run, Resonate.handleExternal,
          Resonate.pureRequest, request, tasks]
    | cons first rest =>
        simp only [tasks] at hkey
        split at hkey
        · contradiction
        · simp [Resonate.run, Resonate.handleExternal,
            Resonate.pureRequest, request, tasks, *]
  case taskFence req =>
    split at hkey
    next _ => contradiction
    next hcondition =>
      cases hs : req.action.targetId.sameOrigin req.id with
      | false =>
          simp [Resonate.run, Resonate.handleExternal,
            Resonate.pureRequest, request, hs]
      | true =>
          have hid : req.action.targetId = req.id := by
            simpa [hs] using hcondition
          have hself : req.id.sameOrigin req.id = true := by
            simpa [hid] using hs
          simp [Resonate.run, Resonate.handleExternal,
            Resonate.pureRequest, Resonate.runDocument, Direct.runWith,
            Direct.taskFence, Direct.Handler, request, hs, hid, hself]
          have hpure (document : Document (.origin req.id.origin)) :
              (pure { status := 400 } :
                Direct.Handler (.origin req.id.origin)
                  ServerModel.TaskFenceRes)
                  { config := config.toServerConfig } document =
                ({ status := 400 }, document, []) := rfl
          rw [hpure, hpure]
          simp only [Prod.fst, Prod.snd]
          change
            (∀ key,
              (state.store.write (.origin req.id.origin)
                (state.store.read (.origin req.id.origin))).read key =
                  state.store.read key) ∧ True ∧ True
          refine ⟨?_, trivial, trivial⟩
          intro key
          by_cases hsame : key = .origin req.id.origin
          · subst key
            simp
          · simp [hsame]
  case taskSuspend req =>
    split at hkey
    · simp [Resonate.run, Resonate.handleExternal,
        Resonate.pureRequest, request, *]
    · contradiction
  case promiseSearch req =>
    simp [Resonate.run, Resonate.handleExternal,
      Resonate.pureRequest, request]
  case scheduleSearch req =>
    simp [Resonate.run, Resonate.handleExternal,
      Resonate.pureRequest, request]
  case taskSearch req =>
    simp [Resonate.run, Resonate.handleExternal,
      Resonate.pureRequest, request]
  all_goals
    rename_i req
    first
    | (split at hkey
       · contradiction
       · simp [Resonate.run, Resonate.handleExternal,
           Resonate.pureRequest, request, *])
    | simp at hkey

theorem work_key_mem
    (config : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) :
    item.key ∈ (Resonate.runWork config item now rest state).1.store.keys := by
  cases item <;>
    simp [Resonate.runWork, Resonate.runDocument, Direct.runWith,
      WorkItem.key]

theorem scan_key_mem
    (config : Resonate.Config) (key : DocumentKey) (now : Time)
    (rest : List WorkflowEntry) (state : State) :
    key ∈ (Resonate.runScan config key now rest state).1.store.keys := by
  cases key <;>
    simp [Resonate.runScan, Resonate.runDocument, Direct.runWith]

@[simp] theorem Store.key_mem_write_of_mem
    (store : Resonate.Store) (writtenKey other : DocumentKey)
    (document : Document writtenKey) (hmem : other ∈ store.keys) :
    other ∈ (store.write writtenKey document).keys := by
  by_cases hcontains : writtenKey ∈ store.keys <;>
    simp [Resonate.Store.write, hcontains, hmem]

theorem external_keys_mono
    (config : Resonate.Config) (call : Call) (state : State) :
    ∀ key ∈ state.store.keys,
      key ∈ (Resonate.run config call state).1.store.keys := by
  intro key hkey
  cases request : call.request <;>
    simp [Resonate.run, Resonate.handleExternal, Resonate.runDocument,
      Direct.runWith, Resonate.pureRequest, request, hkey] <;>
    (try split) <;> (try split) <;> simp_all [hkey]

theorem work_keys_mono
    (config : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) :
    ∀ key ∈ state.store.keys,
      key ∈ (Resonate.runWork config item now rest state).1.store.keys := by
  intro key hkey
  cases item <;>
    simp [Resonate.runWork, Resonate.runDocument, Direct.runWith,
      WorkItem.key, hkey]

theorem scan_keys_mono
    (config : Resonate.Config) (scanKey : DocumentKey) (now : Time)
    (rest : List WorkflowEntry) (state : State) :
    ∀ key ∈ state.store.keys,
      key ∈ (Resonate.runScan config scanKey now rest state).1.store.keys := by
  intro key hkey
  cases scanKey <;>
    simp [Resonate.runScan, Resonate.runDocument, Direct.runWith, hkey]

/-- Per-document representation. The concrete finite key index may contain
empty documents produced by rejected requests, but those cannot yield work. -/
def StoreRep (physical : Concrete.Store) (abstract : State) : Prop :=
  ∀ key, physical.toAbstract.read key = abstract.store.read key

theorem StoreRep.read {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract) (key : DocumentKey) :
    physical.toAbstract.read key = abstract.store.read key :=
  hrep key

theorem StoreRep.commit {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract) (key : DocumentKey)
    (document : Document key) :
    StoreRep (physical.commit key document)
      { abstract with store := abstract.store.write key document } := by
  intro other
  rw [Concrete.Store.toAbstract_commit]
  by_cases h : other = key
  · subst other
    simp
  · simp [h, hrep other]

theorem StoreRep.fence {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract) (key : DocumentKey) :
    StoreRep (physical.fence key) abstract := by
  intro other
  rw [Concrete.Store.toAbstract_read_fence]
  exact hrep other

theorem toAbstract_read_eq_loaded
    {physical : Concrete.Store} {key : DocumentKey}
    {loaded : Option (Document key × Concrete.Version)}
    (hread : physical.read key = loaded) :
    physical.toAbstract.read key =
      (loaded.map (·.1)).getD (emptyDocument key) := by
  cases hvalue : physical.values key with
  | none =>
      simp [Concrete.Store.read, hvalue] at hread
      cases hread
      simp [Concrete.Store.toAbstract, Resonate.Store.read, hvalue]
  | some value =>
      simp [Concrete.Store.read, hvalue] at hread
      cases hread
      simp [Concrete.Store.toAbstract, Resonate.Store.read, hvalue]

theorem external_cas_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {call : Call}
    (htransaction : provenance.transaction = .external call)
    (hcurrent : physical.read key = provenance.loaded) :
    let lifted :=
      Resonate.run { appConfig with unreliable := true } call abstract
    StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 = provenance.outputs ∧
      lifted.1.workflow = abstract.workflow := by
  cases provenance with
  | mk transaction loaded outputs continuations expected_eq selected =>
    simp only at htransaction ⊢
    subst transaction
    cases selected with
    | external hkey hselected =>
      have hbefore := toAbstract_read_eq_loaded hcurrent
      have habstract :
          abstract.store.read key =
            (loaded.map (·.1)).getD
              (emptyDocument key) := by
        rw [← hrep key, hbefore]
      have hlocal := external_locality
        { appConfig with unreliable := true } call key
        ((loaded.map (·.1)).getD (emptyDocument key))
        abstract hkey habstract
      rw [hselected] at hlocal
      refine ⟨?_, hlocal.2.2, hlocal.2.1⟩
      intro other
      by_cases hother : other = key
      · subst other
        simp [hlocal.1]
      · rw [Concrete.Store.toAbstract_commit]
        simp [hother, external_frame
          { appConfig with unreliable := true } call key other
          abstract hkey hother, hrep other]

/-- The landed-failed external outcome has the same committed state as serve,
but selects the abstract lose response. -/
theorem external_cas_transport_lose
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {call : Call}
    (htransaction : provenance.transaction = .external call)
    (hcurrent : physical.read key = provenance.loaded) :
    let lifted :=
      Resonate.runLose { appConfig with unreliable := true } call abstract
    StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 =
        Resonate.unavailable call :: provenance.outputs.drop 1 ∧
      lifted.1.workflow = abstract.workflow := by
  have hserved :=
    external_cas_transport hrep provenance htransaction hcurrent
  simp only [Resonate.runLose]
  exact ⟨hserved.1, by rw [hserved.2.1], hserved.2.2⟩

theorem work_cas_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {item : WorkItem} {now : Time} {rest : List WorkflowEntry}
    (htransaction : provenance.transaction = .work item now rest)
    (hcurrent : physical.read key = provenance.loaded) :
    let lifted := Resonate.runWork
      { appConfig with unreliable := true } item now rest abstract
    StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 = provenance.outputs ∧
      lifted.1.workflow.pending = provenance.continuations := by
  cases provenance with
  | mk transaction loaded outputs continuations expected_eq selected =>
    simp only at htransaction ⊢
    subst transaction
    cases selected with
    | work hselected =>
      have hbefore := toAbstract_read_eq_loaded hcurrent
      have habstract :
          abstract.store.read item.key =
            (loaded.map (·.1)).getD
              (emptyDocument item.key) := by
        rw [← hrep item.key, hbefore]
      have hlocal := work_locality
        { appConfig with unreliable := true } item now rest item.key
        ((loaded.map (·.1)).getD
          (emptyDocument item.key))
        abstract rfl habstract
      rw [hselected] at hlocal
      refine ⟨?_, hlocal.2.2,
        congrArg WorkflowState.pending hlocal.2.1⟩
      intro other
      by_cases hother : other = item.key
      · subst other
        simp [hlocal.1]
      · rw [Concrete.Store.toAbstract_commit]
        simp [hother, Resonate.runWork_frame
          { appConfig with unreliable := true } item now rest
          abstract other hother, hrep other]

theorem scan_cas_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {now : Time} {rest : List WorkflowEntry}
    (htransaction : provenance.transaction = .scan key now rest)
    (hcurrent : physical.read key = provenance.loaded) :
    let lifted := Resonate.runScan
      { appConfig with unreliable := true } key now rest abstract
    StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 = provenance.outputs ∧
      lifted.1.workflow.pending = provenance.continuations := by
  cases provenance with
  | mk transaction loaded outputs continuations expected_eq selected =>
    simp only at htransaction ⊢
    subst transaction
    cases selected with
    | scan hselected =>
      have hbefore := toAbstract_read_eq_loaded hcurrent
      have habstract :
          abstract.store.read key =
            (loaded.map (·.1)).getD (emptyDocument key) := by
        rw [← hrep key, hbefore]
      have hlocal := scan_locality
        { appConfig with unreliable := true } key now rest
        ((loaded.map (·.1)).getD (emptyDocument key))
        abstract habstract
      rw [hselected] at hlocal
      refine ⟨?_, hlocal.2.2,
        congrArg WorkflowState.pending hlocal.2.1⟩
      intro other
      by_cases hother : other = key
      · subst other
        simp [hlocal.1]
      · rw [Concrete.Store.toAbstract_commit]
        simp [hother, Resonate.runScan_frame
          { appConfig with unreliable := true } key now rest
          abstract other hother, hrep other]

theorem takeFlight_once (node : Concrete.Node) (op : Concrete.OpId) :
    ((node.takeFlight op).2.takeFlight op).1 = none := by
  simp [Concrete.Node.takeFlight]

def concreteObservation
    {nodes : List Addr} {appConfig : Resonate.Config}
    (label : Label (CModel nodes appConfig)) :
    List Resonate.BoundaryEvent :=
  label.observe.filterMap Concrete.boundaryEvent

/-- Local flight provenance, reconstructed from the continuation rather than
carried by a store request. -/
def FlightValid (appConfig : Resonate.Config)
    (flight : Concrete.Flight) : Prop :=
  flight.transaction.key? = some flight.key ∧
  match flight.phase with
  | .loading => True
  | .writing =>
      ∃ document,
        flight.document = some document ∧
        Selected appConfig flight.key flight.transaction
          (flight.loaded.map (·.1) |>.getD
            (emptyDocument flight.key))
          document flight.selected flight.continuations

theorem FlightValid.writingProvenance
    {appConfig : Resonate.Config} {flight : Concrete.Flight}
    (hvalid : FlightValid appConfig flight)
    (hphase : flight.phase = .writing) :
    ∃ document,
      flight.document = some document ∧
      ∃ provenance :
          PutProvenance appConfig flight.key document
            (flight.loaded.map (·.2)),
        provenance.transaction = flight.transaction ∧
        provenance.loaded = flight.loaded ∧
        provenance.outputs = flight.selected ∧
        provenance.continuations = flight.continuations := by
  rw [FlightValid, hphase] at hvalid
  obtain ⟨document, hdocument, hselected⟩ := hvalid.2
  refine ⟨document, hdocument, {
    transaction := flight.transaction
    loaded := flight.loaded
    outputs := flight.selected
    continuations := flight.continuations
    expected_eq := rfl
    selected := hselected
  }, rfl, rfl, rfl, rfl⟩

theorem FlightValid.select_ne_none
    {appConfig : Resonate.Config} {flight : Concrete.Flight}
    (hvalid : FlightValid appConfig flight)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    Concrete.select appConfig flight loaded ≠ none := by
  cases flight with
  | mk key transaction oldLoaded document selected continuations attempt phase =>
      cases transaction with
      | external call => simp [Concrete.select]
      | work item instant rest =>
          simp only [FlightValid, Concrete.Transaction.key?,
            Option.some.injEq] at hvalid
          simp [Concrete.select, hvalid.1]
      | scan scanKey instant rest =>
          simp only [FlightValid, Concrete.Transaction.key?,
            Option.some.injEq] at hvalid
          simp [Concrete.select, hvalid.1]

def NodeValid (appConfig : Resonate.Config)
    (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights →
    FlightValid appConfig flight

theorem NodeValid.empty (appConfig : Resonate.Config) :
    NodeValid appConfig ({} : Concrete.Node) := by
  simp [NodeValid]

theorem NodeValid.remember {appConfig : Resonate.Config}
    {node : Concrete.Node} (h : NodeValid appConfig node)
    (key : DocumentKey) :
    NodeValid appConfig (node.remember key) := by
  intro op flight hmem
  simp only [Concrete.Node.remember] at hmem
  split at hmem
  · exact h op flight hmem
  · exact h op flight hmem

theorem NodeValid.takeFlight {appConfig : Resonate.Config}
    {node : Concrete.Node} (h : NodeValid appConfig node)
    (op : Concrete.OpId) :
    NodeValid appConfig (node.takeFlight op).2 := by
  intro other flight hmem
  simp only [Concrete.Node.takeFlight] at hmem
  exact h other flight (List.mem_filter.mp hmem).1

theorem takeFlight_some_mem {node : Concrete.Node} {op : Concrete.OpId}
    {flight : Concrete.Flight} {next : Concrete.Node}
    (h : node.takeFlight op = (some flight, next)) :
    (op, flight) ∈ node.flights := by
  have hfirst := congrArg Prod.fst h
  simp only [Concrete.Node.takeFlight] at hfirst
  obtain ⟨pair, hfind, hpair⟩ := Option.map_eq_some_iff.mp hfirst
  obtain ⟨foundOp, foundFlight⟩ := pair
  simp only at hpair
  subst foundFlight
  have hmem := List.mem_of_find?_eq_some hfind
  have hop := List.find?_some hfind
  simp only [beq_iff_eq] at hop
  subst foundOp
  exact hmem

theorem takeFlight_remaining_mem {node next : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : node.takeFlight op = (taken, next))
    {currentOp : Concrete.OpId} {flight : Concrete.Flight}
    (hmem : (currentOp, flight) ∈ next.flights) :
    (currentOp, flight) ∈ node.flights := by
  simp only [Concrete.Node.takeFlight] at h
  have hsnd := congrArg Prod.snd h
  simp only at hsnd
  rw [← hsnd] at hmem
  exact (List.mem_filter.mp hmem).1

theorem takeFlight_nextOp {node next : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : node.takeFlight op = (taken, next)) :
    next.nextOp = node.nextOp := by
  simp only [Concrete.Node.takeFlight] at h
  have hsnd := congrArg Prod.snd h
  simp only at hsnd
  rw [← hsnd]

theorem takeFlight_pending {node next : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : node.takeFlight op = (taken, next)) :
    next.pending = node.pending := by
  have hsnd := congrArg
    (fun pair : Option Concrete.Flight × Concrete.Node => pair.2.pending) h
  simpa [Concrete.Node.takeFlight] using hsnd.symm

theorem takeFlight_known {node next : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : node.takeFlight op = (taken, next)) :
    next.known = node.known := by
  have hsnd := congrArg
    (fun pair : Option Concrete.Flight × Concrete.Node => pair.2.known) h
  simpa [Concrete.Node.takeFlight] using hsnd.symm

theorem takeFlight_blocked {node next : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : node.takeFlight op = (taken, next)) :
    next.workflowBlocked = node.workflowBlocked := by
  have hsnd := congrArg
    (fun pair : Option Concrete.Flight × Concrete.Node =>
      pair.2.workflowBlocked) h
  simpa [Concrete.Node.takeFlight] using hsnd.symm

theorem NodeValid.await {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {flight : Concrete.Flight} (hflight : FlightValid appConfig flight)
    (payload : Concrete.StoreRequest) :
    NodeValid appConfig (node.await flight payload).1 := by
  intro op current hmem
  simp only [Concrete.Node.await, List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · cases hmem
    exact hflight
  · exact hnode op current hmem

theorem NodeValid.start {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    (hkey : transaction.key? = some key) :
    ∃ next, (Concrete.start node transaction key).state = .node next ∧
      NodeValid appConfig next := by
  refine ⟨node.await { key, transaction } (.get key) |>.1,
    rfl, ?_⟩
  exact NodeValid.await hnode ⟨hkey, trivial⟩ _

theorem NodeValid.decide {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {flight : Concrete.Flight} (hflight : FlightValid appConfig flight)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    ∃ next, (Concrete.decide appConfig node flight loaded).state = .node next ∧
      NodeValid appConfig next := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      exact ⟨node, by simp [Concrete.decide, hselect], hnode⟩
  | some candidate =>
      let writing : Concrete.Flight := {
        flight with
        loaded
        document := some candidate.document
        selected := candidate.outputs
        continuations := candidate.continuations
        phase := .writing
      }
      refine ⟨(node.await writing
          (.put flight.key candidate.document (loaded.map (·.2)))).1,
        by simp [Concrete.decide, hselect, writing], ?_⟩
      apply NodeValid.await hnode
      exact ⟨hflight.1, candidate.document, rfl,
        select_valid hflight.1 hselect⟩

theorem NodeValid.retry {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {flight : Concrete.Flight} (hflight : FlightValid appConfig flight) :
    ∃ next, (Concrete.retry config node flight).state = .node next ∧
      NodeValid appConfig next := by
  simp only [Concrete.retry]
  split
  · let loading : Concrete.Flight := {
      flight with
      loaded := none
      document := none
      selected := []
      continuations := []
      attempt := flight.attempt + 1
      phase := .loading
    }
    refine ⟨(node.await loading (.get flight.key)).1,
      by simp [loading], ?_⟩
    apply NodeValid.await hnode
    simp [FlightValid, loading, hflight.1]
  · exact ⟨node, rfl, hnode⟩

theorem node_step_valid
    {appConfig : Resonate.Config}
    {config : Concrete.Config} {address : Addr}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val) :
    ∃ next, result.state = .node next ∧ NodeValid appConfig next := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hnode⟩
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
            | some key =>
                simp only [hk, Outcomes.one, List.mem_singleton] at hresult
                subst result
                exact ⟨{ node with pending := [.scan key now] },
                  rfl, by
                    intro op flight hmem
                    exact hnode op flight hmem⟩
        | cons entry rest =>
            simp only [hp, Outcomes.one, List.mem_singleton] at hresult
            subst result
            cases entry with
            | scan key instant =>
                exact NodeValid.start
                  (node := { node with pending := [] }) hnode
                  (.scan key instant rest) key rfl
            | work item instant =>
                exact NodeValid.start
                  (node := { node with pending := [] }) hnode
                  (.work item instant rest) item.key rfl
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hnode⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hnode⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hnode⟩
          | some key =>
              simp only [hk, Outcomes.one, List.mem_singleton] at hresult
              subst result
              exact NodeValid.start hnode (.external call) key hk
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload with
        | got key loaded =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight op = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
            | some flight =>
                simp only [Prod.fst, Prod.snd] at hresult
                have hnext := NodeValid.takeFlight hnode op
                rw [ht] at hnext
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      have hflight :=
                        hnode op flight (takeFlight_some_mem ht)
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      exact NodeValid.decide hnext hflight _
                  | writing =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨next, rfl, hnext⟩
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  exact ⟨next, rfl, hnext⟩
        | written =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight op = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
            | some flight =>
                have hnext := NodeValid.takeFlight hnode op
                rw [ht] at hnext
                cases hp : flight.phase with
                | loading =>
                    simp [hp, Outcomes.one] at hresult
                    subst result
                    exact ⟨next, rfl, hnext⟩
                | writing =>
                    simp [hp, Outcomes.one] at hresult
                    subst result
                    exact ⟨{ next.remember flight.key with
                        pending := flight.continuations ++ next.pending },
                      rfl, by
                        intro currentOp current hmem
                        exact NodeValid.remember hnext flight.key
                          currentOp current hmem⟩
        | conflict =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight op = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
            | some flight =>
                have hnext := NodeValid.takeFlight hnode op
                rw [ht] at hnext
                cases hp : flight.phase with
                | loading =>
                    simp [hp, Outcomes.one] at hresult
                    subst result
                    exact ⟨next, rfl, hnext⟩
                | writing =>
                    simp only [hp] at hresult
                    split at hresult
                    · have hflight :=
                        hnode op flight (takeFlight_some_mem ht)
                      simp only [Outcomes.one,
                        List.mem_singleton] at hresult
                      subst result
                      exact NodeValid.retry hnext hflight
                    · simp [Outcomes.one] at hresult
                      subst result
                      exact ⟨{ next with workflowBlocked := true },
                        rfl, by
                          intro currentOp current hmem
                          exact hnext currentOp current hmem⟩
        | failed =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight op = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
            | some flight =>
                have hnext := NodeValid.takeFlight hnode op
                rw [ht] at hnext
                simp [Outcomes.one] at hresult
                subst result
                exact ⟨{ next with workflowBlocked :=
                    next.workflowBlocked ||
                      !flight.transaction.isExternal },
                  rfl, by
                    intro currentOp current hmem
                    exact hnext currentOp current hmem⟩

theorem node_step_ids
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧
      node.nextOp ≤ next.nextOp ∧
      (∀ recipient rpc,
        (recipient, Concrete.Msg.storeRequest rpc) ∈ result.send →
        rpc.op = node.nextOp ∧ next.nextOp = node.nextOp + 1) ∧
      (∀ recipient₁ rpc₁ recipient₂ rpc₂,
        (recipient₁, Concrete.Msg.storeRequest rpc₁) ∈ result.send →
        (recipient₂, Concrete.Msg.storeRequest rpc₂) ∈ result.send →
        rpc₁ = rpc₂) := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
            | some key =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨{ node with pending := [.scan key now] },
                  rfl, Nat.le_refl _, by simp, by simp⟩
        | cons entry rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            refine ⟨_, rfl, by simp [Concrete.Node.await], ?_, ?_⟩
            · simp [Concrete.Node.await]
            · intros
              simp_all [Concrete.Node.await]
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, Nat.le_refl _, by
                intro recipient rpc h
                simp [Concrete.sendOutputs] at h, by
                intros
                simp_all [Concrete.sendOutputs]⟩
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              refine ⟨_, rfl, by simp [Concrete.Node.await], ?_, ?_⟩
              · simp [Concrete.Node.await]
              · intros
                simp_all [Concrete.Node.await]
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload with
        | got key loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
              | some flight =>
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : flight.phase with
                    | loading =>
                        simp only [hp] at hresult
                        cases hs : Concrete.select appConfig flight
                            (heq ▸ loaded) with
                        | none =>
                            simp [Concrete.decide, hs, Outcomes.one] at hresult
                            subst result
                            refine ⟨remaining, rfl,
                              Nat.le_of_eq (takeFlight_nextOp ht).symm,
                              by simp, by simp⟩
                        | some candidate =>
                            simp [Concrete.decide, hs, Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_, ?_, ?_⟩
                            · simp [Concrete.Node.await,
                                takeFlight_nextOp ht]
                            · simp [Concrete.Node.await,
                                takeFlight_nextOp ht]
                            · intros
                              simp_all [Concrete.Node.await]
                    | writing =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        refine ⟨remaining, rfl,
                          Nat.le_of_eq (takeFlight_nextOp ht).symm,
                          by simp, by simp⟩
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    refine ⟨remaining, rfl,
                      Nat.le_of_eq (takeFlight_nextOp ht).symm,
                      by simp, by simp⟩
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
              | some flight =>
                  cases hp : flight.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      refine ⟨remaining, rfl,
                        Nat.le_of_eq (takeFlight_nextOp ht).symm,
                        by simp, by simp⟩
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      refine ⟨_, rfl, ?_, by
                        intro recipient rpc h
                        simp [Concrete.sendOutputs] at h, by
                        intros
                        simp_all [Concrete.sendOutputs]⟩
                      simp [Concrete.Node.remember,
                        takeFlight_nextOp ht]
                      split <;> simp [takeFlight_nextOp ht]
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
              | some flight =>
                  cases hp : flight.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      refine ⟨remaining, rfl,
                        Nat.le_of_eq (takeFlight_nextOp ht).symm,
                        by simp, by simp⟩
                  | writing =>
                      cases hext : flight.transaction.isExternal with
                      | false =>
                          simp [ht, hp, hext, Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_, by simp, by simp⟩
                          simpa [takeFlight_nextOp ht]
                      | true =>
                          by_cases hattempt :
                              flight.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_, ?_, ?_⟩
                            · simp [Concrete.Node.await,
                                takeFlight_nextOp ht]
                            · simp [Concrete.Node.await,
                                takeFlight_nextOp ht]
                            · intros
                              simp_all [Concrete.Node.await]
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨remaining, rfl,
                              Nat.le_of_eq (takeFlight_nextOp ht).symm,
                              by
                                intro recipient rpc h
                                simp [Concrete.sendOutputs] at h, by
                                intros
                                simp_all [Concrete.sendOutputs]⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, Nat.le_refl _, by simp, by simp⟩
              | some flight =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  refine ⟨_, rfl, ?_, by
                    intro recipient rpc h
                    simp [Concrete.sendOutputs] at h, by
                    intros
                    simp_all [Concrete.sendOutputs]⟩
                  simpa [takeFlight_nextOp ht]

theorem node_step_old_flight
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hop : op < node.nextOp)
    (hmem : (op, flight) ∈ next.flights) :
    (op, flight) ∈ node.flights := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        have hflights := congrArg (fun localState =>
          match localState with
          | .node value => value.flights
          | _ => []) hstate
        change node.flights = next.flights at hflights
        exact hflights ▸ hmem
      · cases hpending : node.pending with
        | nil =>
            simp only [hpending] at hresult
            cases hknown : node.known.head? with
            | none =>
                simp [hknown, Outcomes.one] at hresult
                subst result
                have hflights := congrArg (fun localState =>
                  match localState with
                  | .node value => value.flights
                  | _ => []) hstate
                change node.flights = next.flights at hflights
                exact hflights ▸ hmem
            | some key =>
                simp [hknown, Outcomes.one] at hresult
                subst result
                have hflights := congrArg (fun localState =>
                  match localState with
                  | .node value => value.flights
                  | _ => []) hstate
                change node.flights = next.flights at hflights
                exact hflights ▸ hmem
        | cons entry rest =>
            cases entry with
            | scan key instant =>
                simp [hpending, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                have hflights := congrArg (fun localState =>
                  match localState with
                  | .node value => value.flights
                  | _ => []) hstate
                change
                  (node.nextOp,
                    ({ key := key
                       transaction := .scan key instant rest } :
                      Concrete.Flight)) ::
                    node.flights = next.flights at hflights
                rw [← hflights] at hmem
                simp only [List.mem_cons] at hmem
                rcases hmem with hnew | hold
                · have heq : op = node.nextOp := by
                    simpa using congrArg Prod.fst hnew
                  exact (Nat.ne_of_lt hop heq).elim
                · exact hold
            | work item instant =>
                simp [hpending, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                have hflights := congrArg (fun localState =>
                  match localState with
                  | .node value => value.flights
                  | _ => []) hstate
                change
                  (node.nextOp,
                    ({ key := item.key
                       transaction := .work item instant rest } :
                      Concrete.Flight)) ::
                    node.flights = next.flights at hflights
                rw [← hflights] at hmem
                simp only [List.mem_cons] at hmem
                rcases hmem with hnew | hold
                · have heq : op = node.nextOp := by
                    simpa using congrArg Prod.fst hnew
                  exact (Nat.ne_of_lt hop heq).elim
                · exact hold
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          have hflights := congrArg (fun localState =>
            match localState with
            | .node value => value.flights
            | _ => []) hstate
          change node.flights = next.flights at hflights
          exact hflights ▸ hmem
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          have hflights := congrArg (fun localState =>
            match localState with
            | .node value => value.flights
            | _ => []) hstate
          change node.flights = next.flights at hflights
          exact hflights ▸ hmem
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              have hflights := congrArg (fun localState =>
                match localState with
                | .node value => value.flights
                | _ => []) hstate
              change node.flights = next.flights at hflights
              exact hflights ▸ hmem
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              have hflights := congrArg (fun localState =>
                match localState with
                | .node value => value.flights
                | _ => []) hstate
              change
                (node.nextOp,
                  ({ key := key
                     transaction := .external call } :
                    Concrete.Flight)) ::
                  node.flights = next.flights at hflights
              rw [← hflights] at hmem
              simp only [List.mem_cons] at hmem
              rcases hmem with hnew | hold
              · have heq : op = node.nextOp := by
                  simpa using congrArg Prod.fst hnew
                exact (Nat.ne_of_lt hop heq).elim
              · exact hold
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got key loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change node.flights = next.flights at hflights
                  exact hflights ▸ hmem
              | some taken =>
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : taken.phase with
                    | loading =>
                        simp only [hp] at hresult
                        cases hs : Concrete.select appConfig taken
                            (heq ▸ loaded) with
                        | none =>
                            simp [Concrete.decide, hs, Outcomes.one] at hresult
                            subst result
                            have hflights := congrArg (fun localState =>
                              match localState with
                              | .node value => value.flights
                              | _ => []) hstate
                            change remaining.flights = next.flights at hflights
                            apply takeFlight_remaining_mem ht
                            exact hflights ▸ hmem
                        | some candidate =>
                            simp [Concrete.decide, hs, Outcomes.one] at hresult
                            subst result
                            have hflights := congrArg (fun localState =>
                              match localState with
                              | .node value => value.flights
                              | _ => []) hstate
                            change
                              (remaining.nextOp, {
                                key := taken.key
                                transaction := taken.transaction
                                loaded := heq ▸ loaded
                                document := some candidate.document
                                selected := candidate.outputs
                                continuations := candidate.continuations
                                attempt := taken.attempt
                                phase := .writing }) ::
                                remaining.flights = next.flights at hflights
                            rw [← hflights] at hmem
                            simp only [List.mem_cons] at hmem
                            rcases hmem with hnew | hold
                            · have hopNew : op = remaining.nextOp := by
                                simpa using congrArg Prod.fst hnew
                              have hopOld : op = node.nextOp :=
                                hopNew.trans (takeFlight_nextOp ht)
                              exact (Nat.ne_of_lt hop hopOld).elim
                            · exact takeFlight_remaining_mem ht hold
                    | writing =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        have hflights := congrArg (fun localState =>
                          match localState with
                          | .node value => value.flights
                          | _ => []) hstate
                        change remaining.flights = next.flights at hflights
                        apply takeFlight_remaining_mem ht
                        exact hflights ▸ hmem
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    have hflights := congrArg (fun localState =>
                      match localState with
                      | .node value => value.flights
                      | _ => []) hstate
                    change remaining.flights = next.flights at hflights
                    apply takeFlight_remaining_mem ht
                    exact hflights ▸ hmem
        | written =>
            simp_all [Concrete.Node.takeFlight, Concrete.Node.remember,
              Outcomes.one]
            all_goals grind
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change node.flights = next.flights at hflights
                  exact hflights ▸ hmem
              | some taken =>
                  cases hp : taken.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      change remaining.flights = next.flights at hflights
                      apply takeFlight_remaining_mem ht
                      exact hflights ▸ hmem
                  | writing =>
                      cases hext : taken.transaction.isExternal with
                      | false =>
                          simp [ht, hp, hext, Outcomes.one] at hresult
                          subst result
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          change remaining.flights = next.flights at hflights
                          apply takeFlight_remaining_mem ht
                          exact hflights ▸ hmem
                      | true =>
                          by_cases hattempt :
                              taken.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            have hflights := congrArg (fun localState =>
                              match localState with
                              | .node value => value.flights
                              | _ => []) hstate
                            change
                              (remaining.nextOp, {
                                key := taken.key
                                transaction := taken.transaction
                                attempt := taken.attempt + 1 }) ::
                                remaining.flights = next.flights at hflights
                            rw [← hflights] at hmem
                            simp only [List.mem_cons] at hmem
                            rcases hmem with hnew | hold
                            · have hopNew : op = remaining.nextOp := by
                                simpa using congrArg Prod.fst hnew
                              have hopOld : op = node.nextOp :=
                                hopNew.trans (takeFlight_nextOp ht)
                              exact (Nat.ne_of_lt hop hopOld).elim
                            · exact takeFlight_remaining_mem ht hold
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            have hflights := congrArg (fun localState =>
                              match localState with
                              | .node value => value.flights
                              | _ => []) hstate
                            change remaining.flights = next.flights at hflights
                            apply takeFlight_remaining_mem ht
                            exact hflights ▸ hmem
        | failed =>
            simp_all [Concrete.Node.takeFlight, Outcomes.one]
            all_goals grind

theorem node_step_preserves_writing_flight
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    (hnotReply :
      ∀ payload,
        event ≠ .receive .store
          (.storeReply { op, payload }))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧ (op, flight) ∈ next.flights := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hflight⟩
      · rename_i hidle
        have hnonempty : node.flights.isEmpty = false :=
          List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hflight)
        simp [hnonempty] at hidle
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hflight⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hflight⟩
        · rename_i haccept
          have hnonempty : node.flights.isEmpty = false :=
            List.isEmpty_eq_false_iff.mpr (List.ne_nil_of_mem hflight)
          simp [hnonempty] at haccept
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        by_cases hop : replyOp = op
        · subst replyOp
          exact (hnotReply payload rfl).elim
        · have hkept :
              (op, flight) ∈
                node.flights.filter (fun pair => pair.1 != replyOp) :=
            List.mem_filter.mpr ⟨hflight, by simpa [Ne.symm hop]⟩
          cases payload <;>
            simp only [Concrete.step, Concrete.Node.takeFlight] at hresult
          all_goals
            cases hlookup :
                (node.flights.find? (fun pair => pair.1 == replyOp)).map
                  (fun pair => pair.2) <;>
              rw [hlookup] at hresult
          all_goals
            simp_all [Concrete.decide, Concrete.retry,
              Concrete.Node.await, Concrete.Node.remember, Outcomes.one]
          all_goals grind

def NodeSerial (node : Concrete.Node) : Prop :=
  node.flights.length ≤ 1

theorem takeFlight_filter_empty_of_some
    {node : Concrete.Node} {op : Concrete.OpId}
    {flight : Concrete.Flight}
    (hserial : NodeSerial node)
    (hfind :
      (node.flights.find? (·.1 == op)).map (·.2) = some flight) :
    node.flights.filter (·.1 != op) = [] := by
  cases hflights : node.flights with
  | nil => simp [hflights] at hfind
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest =>
            simp [NodeSerial, hflights] at hserial
      subst tail
      obtain ⟨headOp, headFlight⟩ := head
      simp [hflights] at hfind
      simp [hflights, hfind.1]

theorem takeFlight_remaining_empty
    {node next : Concrete.Node} {op : Concrete.OpId}
    {flight : Concrete.Flight}
    (hserial : NodeSerial node)
    (h : node.takeFlight op = (some flight, next)) :
    next.flights = [] := by
  have hfilter := takeFlight_filter_empty_of_some hserial
    (congrArg Prod.fst h)
  have hsnd := congrArg
    (fun pair : Option Concrete.Flight × Concrete.Node => pair.2.flights) h
  simp [Concrete.Node.takeFlight, hfilter] at hsnd
  exact hsnd

theorem node_step_serial
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    (hserial : NodeSerial node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next, result.state = .node next ∧ NodeSerial next := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hserial⟩
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hserial⟩
            | some key =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, hserial⟩
        | cons entry rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            have hempty : node.flights = [] := by
              simp_all
            simp [NodeSerial, Concrete.Node.await, hempty]
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hserial⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hserial⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hserial⟩
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              have hempty : node.flights = [] := by
                simp_all
              simp [NodeSerial, Concrete.Node.await, hempty]
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload <;> simp only [Concrete.step] at hresult
        all_goals
          simp only [Concrete.Node.takeFlight] at hresult
          cases hlookup :
              (node.flights.find? (·.1 == op)).map (·.2) with
          | none =>
              rw [hlookup] at hresult
              simp [Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hserial⟩
          | some flight =>
              have hempty :=
                takeFlight_filter_empty_of_some hserial hlookup
              rw [hlookup] at hresult
              simp_all [hempty, NodeSerial, Concrete.Node.takeFlight,
                Concrete.decide, Concrete.retry, Concrete.Node.await,
                Concrete.Node.remember, Outcomes.one]
              all_goals
                split at hresult <;>
                  try simp_all [Outcomes.one, NodeSerial]
              all_goals
                try (split at hresult <;>
                  simp_all [Outcomes.one, NodeSerial])
              all_goals
                try (split at hresult <;>
                  simp_all [Outcomes.one, NodeSerial])
              all_goals
                try (split at hresult <;>
                  simp_all [Outcomes.one, NodeSerial])
              all_goals try (split <;> simp_all)

def NodeInternalClean (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights →
    flight.transaction.isExternal = false →
    node.pending = [] ∧ node.workflowBlocked = false

theorem node_step_internal_clean
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    (hserial : NodeSerial node)
    (hclean : NodeInternalClean node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next, result.state = .node next ∧ NodeInternalClean next := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      next hguard =>
        simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hclean⟩
      next hguard =>
        have hguard' :
            node.workflowBlocked = false ∧ node.flights = [] := by
          simp at hguard
          exact ⟨hguard.1.2, hguard.2⟩
        obtain ⟨hblocked, hflights⟩ := hguard'
        cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hclean⟩
            | some key =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, by
                  simp [NodeInternalClean, hflights]⟩
        | cons entry rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            have hempty : node.flights = [] := by simp_all
            refine ⟨_, rfl, ?_⟩
            cases entry <;>
              simp [NodeInternalClean, Concrete.Node.await, hempty,
                hblocked]
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hclean⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hclean⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hclean⟩
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              have hempty : node.flights = [] := by simp_all
              refine ⟨_, rfl, ?_⟩
              simp [NodeInternalClean, Concrete.Node.await, hempty,
                Concrete.Transaction.isExternal]
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload <;> simp only [Concrete.step] at hresult
        all_goals
          simp only [Concrete.Node.takeFlight] at hresult
          cases hlookup :
              (node.flights.find? (·.1 == op)).map (·.2) with
          | none =>
              rw [hlookup] at hresult
              simp [Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hclean⟩
          | some flight =>
              have hempty :=
                takeFlight_filter_empty_of_some hserial hlookup
              have hflightMem : (op, flight) ∈ node.flights := by
                obtain ⟨pair, hfind, hpair⟩ :=
                  Option.map_eq_some_iff.mp hlookup
                obtain ⟨foundOp, foundFlight⟩ := pair
                simp only at hpair
                subst foundFlight
                have hmem := List.mem_of_find?_eq_some hfind
                have hop : foundOp = op := by
                  simpa using List.find?_some hfind
                subst foundOp
                exact hmem
              have hcleanFlight :=
                hclean op flight hflightMem
              rw [hlookup] at hresult
              simp_all [hempty, NodeInternalClean,
                Concrete.Node.takeFlight, Concrete.decide, Concrete.retry,
                Concrete.Node.await, Concrete.Node.remember, Outcomes.one]
              all_goals
                split at hresult <;>
                  try simp_all [Outcomes.one, NodeInternalClean]
              all_goals
                try (split at hresult <;>
                  simp_all [Outcomes.one, NodeInternalClean])
              all_goals
                try (split at hresult <;>
                  simp_all [Outcomes.one, NodeInternalClean])
              all_goals
                try (split at hresult <;>
                  simp_all [Outcomes.one, NodeInternalClean])
              all_goals try (split <;> simp_all [NodeInternalClean])

def NodesSerial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧ NodeSerial node

theorem nodesSerial_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesSerial (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by simp [NodeSerial]⟩

theorem nodesSerial_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : NodesSerial world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesSerial next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress
      obtain ⟨node, hnode, hserial⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨after, hstate, hafter⟩ :=
          node_step_serial hserial (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], hserial⟩

theorem reachable_nodes_serial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesSerial world := by
  induction hreachable with
  | init hinit => exact nodesSerial_initial hinit
  | step _ hstep ih => exact nodesSerial_step ih hstep

def NodesInternalClean
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node, world.process (.node address) = .node node ∧
      NodeInternalClean node

theorem nodesInternalClean_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesInternalClean (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by
    simp [NodeInternalClean]⟩

theorem nodesInternalClean_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    (hinvariant : NodesInternalClean world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesInternalClean next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress
      obtain ⟨node, hnode, hclean⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable address haddress
        rw [hnode] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        obtain ⟨after, hstate, hafter⟩ :=
          node_step_internal_clean hserial hclean (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], hclean⟩

theorem reachable_nodes_internal_clean
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesInternalClean world := by
  induction hreachable with
  | init hinit => exact nodesInternalClean_initial hinit
  | step hreachable hstep ih =>
      exact nodesInternalClean_step hreachable ih hstep

theorem reachable_internal_flight_clean
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hinternal : flight.transaction.isExternal = false) :
    node.pending = [] ∧ node.workflowBlocked = false := by
  obtain ⟨actual, hactual, hclean⟩ :=
    reachable_nodes_internal_clean hreachable address haddress
  rw [hnode] at hactual
  cases Concrete.Local.node.inj hactual
  exact hclean op flight hflight hinternal

def WorkflowOwnsFlights
    {nodes : List Addr} {appConfig : Resonate.Config}
    (config : Concrete.Config)
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes → address ≠ config.workflowNode →
    ∃ node,
      world.process (.node address) = .node node ∧ node.flights = []

theorem node_step_nonworkflow_empty
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} (haddress : address ≠ config.workflowNode)
    {node : Concrete.Node} (hempty : node.flights = [])
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next, result.state = .node next ∧ next.flights = [] := by
  cases event with
  | timeout =>
      simp [Concrete.step, haddress, Outcomes.one] at hresult
      subst result
      exact ⟨node, rfl, hempty⟩
  | receive sender message =>
      cases sender <;> cases message <;>
        simp [Concrete.step, haddress, hempty, Outcomes.one] at hresult
      all_goals
        try
          subst result
          exact ⟨node, rfl, hempty⟩
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload <;>
          simp [Concrete.step, Concrete.Node.takeFlight, hempty,
            Outcomes.one] at hresult
        all_goals subst result
        all_goals exact ⟨node, rfl, hempty⟩

theorem workflowOwnsFlights_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    WorkflowOwnsFlights (nodes := nodes) (appConfig := appConfig) config
      (World.initial process) := by
  intro address hmem hne
  exact ⟨{}, hinit.2.2 address hmem, rfl⟩

theorem workflowOwnsFlights_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : WorkflowOwnsFlights config world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    WorkflowOwnsFlights config next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address hmem hne
      obtain ⟨node, hnode, hempty⟩ := hinvariant address hmem hne
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨after, hstate, hafter⟩ :=
          node_step_nonworkflow_empty hne hempty (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], hempty⟩

theorem reachable_workflow_owns_flights
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    WorkflowOwnsFlights (nodes := nodes) (appConfig := appConfig)
      config world := by
  induction hreachable with
  | init hinit => exact workflowOwnsFlights_initial hinit
  | step _ hstep ih => exact workflowOwnsFlights_step ih hstep

theorem reachable_flight_owner
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights) :
    address = config.workflowNode := by
  by_cases heq : address = config.workflowNode
  · exact heq
  exfalso
  obtain ⟨emptyNode, hemptyNode, hempty⟩ :=
    reachable_workflow_owns_flights hreachable address haddress heq
  rw [hnode] at hemptyNode
  cases Concrete.Local.node.inj hemptyNode
  rw [hempty] at hflight
  contradiction

theorem NodeSerial.eq_of_mem
    {node : Concrete.Node} (hserial : NodeSerial node)
    {first second : Concrete.OpId × Concrete.Flight}
    (hfirst : first ∈ node.flights) (hsecond : second ∈ node.flights) :
    first = second := by
  cases hflights : node.flights with
  | nil => simp [hflights] at hfirst
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest => simp [NodeSerial, hflights] at hserial
      subst tail
      simp [hflights] at hfirst hsecond
      exact hfirst.trans hsecond.symm

def NodesValid {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node, world.process (.node address) = .node node ∧
      NodeValid appConfig node

theorem nodesValid_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesValid (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, NodeValid.empty appConfig⟩

theorem nodesValid_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : NodesValid world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesValid next := by
  cases hstep with
  | inject =>
      intro address haddress
      simpa [World.inject] using hinvariant address haddress
  | outside =>
      intro address haddress
      simpa [World.observeOutside] using hinvariant address haddress
  | process htime hprocess hvalid hresult =>
      intro address haddress
      rename_i process now event result
      by_cases heq : Concrete.Pid.node address = process
      · subst process
        obtain ⟨node, hlocal, hnode⟩ := hinvariant address haddress
        have hvalidNext := node_step_valid hnode (hlocal ▸ hresult)
        obtain ⟨nodeNext, hstate, hnodeNext⟩ := hvalidNext
        refine ⟨nodeNext, ?_, hnodeNext⟩
        simp [World.land, hstate]
      · obtain ⟨node, hlocal, hnode⟩ := hinvariant address haddress
        refine ⟨node, ?_, hnode⟩
        simp [World.land, heq, hlocal]

theorem reachable_nodes_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesValid world := by
  induction hreachable with
  | init hinit => exact nodesValid_initial hinit
  | step _ hstep ih => exact nodesValid_step ih hstep

def StoreRequestsFresh
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address node rpc},
    address ∈ nodes →
    world.process (.node address) = .node node →
    (Concrete.Pid.node address, .store, .storeRequest rpc) ∈
      world.network →
    rpc.op < node.nextOp

def StoreRequestsUnique
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op payload₁ payload₂},
    (Concrete.Pid.node address, .store,
      .storeRequest { op, payload := payload₁ }) ∈ world.network →
    (Concrete.Pid.node address, .store,
      .storeRequest { op, payload := payload₂ }) ∈ world.network →
    payload₁ = payload₂

structure RpcIds
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop where
  fresh : StoreRequestsFresh world
  unique : StoreRequestsUnique world

theorem rpcIds_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    RpcIds
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  constructor
  · intro address node rpc haddress hnode hmem
    contradiction
  · intro address op payload₁ payload₂ hone htwo
    contradiction

theorem rpcIds_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    (hinvariant : RpcIds world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    RpcIds next := by
  cases hstep with
  | inject =>
      constructor
      · intro address node rpc haddress hnode hmem
        simp only [World.inject, List.mem_append,
          List.mem_singleton] at hmem
        rcases hmem with hold | hnew
        · exact hinvariant.fresh haddress hnode hold
        · simp at hnew
      · intro address op payload₁ payload₂ hone htwo
        simp only [World.inject, List.mem_append,
          List.mem_singleton] at hone htwo
        rcases hone with hone | hone <;>
          rcases htwo with htwo | htwo
        · exact hinvariant.unique hone htwo
        all_goals simp at *
  | outside =>
      constructor
      · intro address node rpc haddress hnode hmem
        exact hinvariant.fresh haddress hnode hmem
      · intro address op payload₁ payload₂ hone htwo
        exact hinvariant.unique hone htwo
  | @process pid now event result htime hprocess hvalid hresult =>
      constructor
      · intro address node rpc haddress hnode hmem
        simp only [World.land, List.mem_append] at hmem
        by_cases hp : pid = .node address
        · subst pid
          obtain ⟨before, hbefore, _⟩ :=
            reachable_nodes_valid hreachable address haddress
          obtain ⟨after, hstate, hmono, hsent, _⟩ :=
            node_step_ids (hbefore ▸ hresult)
          have hafter : after = node := by
            have : result.state = .node node := by
              simpa [World.land] using hnode
            rw [hstate] at this
            exact Concrete.Local.node.inj this
          subst after
          rcases hmem with hold | hnew
          · exact Nat.lt_of_lt_of_le
              (hinvariant.fresh haddress hbefore hold) hmono
          · obtain ⟨sent, hsend, heq⟩ := List.mem_map.mp hnew
            obtain ⟨recipient, message⟩ := sent
            simp only [Prod.mk.injEq] at heq
            obtain ⟨_, rfl, rfl⟩ := heq
            obtain ⟨hop, hnext⟩ := hsent _ _ hsend
            rw [hop, hnext]
            exact Nat.lt_succ_self _
        · have hbefore :
              world.process (.node address) = .node node := by
            simpa [World.land, Ne.symm hp] using hnode
          rcases hmem with hold | hnew
          · exact hinvariant.fresh haddress hbefore hold
          · obtain ⟨sent, hsend, heq⟩ := List.mem_map.mp hnew
            obtain ⟨recipient, message⟩ := sent
            simp only [Prod.mk.injEq] at heq
            exact (hp heq.1).elim
      · intro address op payload₁ payload₂ hone htwo
        simp only [World.land, List.mem_append] at hone htwo
        rcases hone with hone | hone <;>
          rcases htwo with htwo | htwo
        · exact hinvariant.unique hone htwo
        · obtain ⟨sent, hsend, heq⟩ := List.mem_map.mp htwo
          obtain ⟨recipient, message⟩ := sent
          simp only [Prod.mk.injEq] at heq
          have hp : pid = .node address := heq.1
          subst pid
          cases heq.2.1
          cases heq.2.2
          obtain ⟨before, hbefore, _⟩ :=
            reachable_nodes_valid hreachable address hprocess
          obtain ⟨after, hstate, hmono, hsent, _⟩ :=
            node_step_ids (hbefore ▸ hresult)
          have holdFresh := hinvariant.fresh hprocess hbefore hone
          have hnewOp := (hsent _ _ hsend).1
          simp only [Concrete.RpcRequest.mk.injEq] at heq
          exact (Nat.ne_of_lt holdFresh hnewOp).elim
        · obtain ⟨sent, hsend, heq⟩ := List.mem_map.mp hone
          obtain ⟨recipient, message⟩ := sent
          simp only [Prod.mk.injEq] at heq
          have hp : pid = .node address := heq.1
          subst pid
          cases heq.2.1
          cases heq.2.2
          obtain ⟨before, hbefore, _⟩ :=
            reachable_nodes_valid hreachable address hprocess
          obtain ⟨after, hstate, hmono, hsent, _⟩ :=
            node_step_ids (hbefore ▸ hresult)
          have holdFresh := hinvariant.fresh hprocess hbefore htwo
          have hnewOp := (hsent _ _ hsend).1
          simp only [Concrete.RpcRequest.mk.injEq] at heq
          exact (Nat.ne_of_lt holdFresh hnewOp).elim
        · obtain ⟨sent₁, hsend₁, heq₁⟩ := List.mem_map.mp hone
          obtain ⟨recipient₁, message₁⟩ := sent₁
          obtain ⟨sent₂, hsend₂, heq₂⟩ := List.mem_map.mp htwo
          obtain ⟨recipient₂, message₂⟩ := sent₂
          simp only [Prod.mk.injEq] at heq₁ heq₂
          have hp : pid = .node address := heq₁.1
          subst pid
          cases heq₁.2.1
          cases heq₁.2.2
          cases heq₂.2.1
          cases heq₂.2.2
          obtain ⟨before, hbefore, _⟩ :=
            reachable_nodes_valid hreachable address hprocess
          obtain ⟨after, hstate, hmono, hsent, hunique⟩ :=
            node_step_ids (hbefore ▸ hresult)
          have hrpc := hunique _ _ _ _ hsend₁ hsend₂
          exact congrArg Concrete.RpcRequest.payload hrpc

theorem reachable_rpc_ids
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    RpcIds world := by
  induction hreachable with
  | init hinit => exact rpcIds_initial _
  | step hreachable hstep ih =>
      exact rpcIds_step hreachable ih hstep

def NodeWritingPuts
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig))
    (address : Addr) (node : Concrete.Node) : Prop :=
  ∀ {op flight},
    (op, flight) ∈ node.flights →
    flight.phase = .writing →
    ∃ document,
      flight.document = some document ∧
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put flight.key document
            (flight.loaded.map (·.2))
        }) ∈ world.network

def NodeLoadingGets
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig))
    (address : Addr) (node : Concrete.Node) : Prop :=
  ∀ {op flight},
    (op, flight) ∈ node.flights →
    flight.phase = .loading →
    (Concrete.Pid.node address, .store,
      .storeRequest {
        op
        payload := .get flight.key
      }) ∈ world.network

theorem NodeLoadingGets.mono
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world next : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (h : NodeLoadingGets world address node)
    (hnetwork : ∀ message ∈ world.network, message ∈ next.network) :
    NodeLoadingGets next address node := by
  intro op flight hmem hphase
  exact hnetwork _ (h hmem hphase)

theorem NodeLoadingGets.takeFlight
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node remaining : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : NodeLoadingGets world address node)
    (htake : node.takeFlight op = (taken, remaining)) :
    NodeLoadingGets world address remaining := by
  intro currentOp flight hmem hphase
  exact h (takeFlight_remaining_mem htake hmem) hphase

theorem node_step_loading_gets
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (hinvariant : NodeLoadingGets world address node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧
      NodeLoadingGets (world.land (.node address) now result)
        address next := by
  have hold (current : Concrete.Node)
      (hcurrent : NodeLoadingGets world address current) :
      NodeLoadingGets (world.land (.node address) now result)
        address current :=
    hcurrent.mono fun message hmessage =>
      List.mem_append_left _ hmessage
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hold node hinvariant⟩
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hold node hinvariant⟩
            | some key =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, hold node hinvariant⟩
        | cons entry rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            refine ⟨_, rfl, ?_⟩
            intro op flight hmem hphase
            simp only [Concrete.Node.await, List.mem_cons] at hmem
            rcases hmem with hnew | holdMem
            · cases hnew
              simp [World.land, Concrete.Node.await]
            · exact hold node hinvariant holdMem hphase
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hold node hinvariant⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hold node hinvariant⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hold node hinvariant⟩
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              refine ⟨_, rfl, ?_⟩
              intro op flight hmem hphase
              simp only [Concrete.Node.await, List.mem_cons] at hmem
              rcases hmem with hnew | holdMem
              · cases hnew
                simp [World.land, Concrete.Node.await]
              · exact hold node hinvariant holdMem hphase
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeLoadingGets world address remaining :=
                    NodeLoadingGets.takeFlight hinvariant ht
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : taken.phase with
                    | loading =>
                        cases hs : Concrete.select appConfig taken
                            (heq ▸ loaded) with
                        | none =>
                            simp [Concrete.decide, hp, hs,
                              Outcomes.one] at hresult
                            subst result
                            exact ⟨remaining, rfl,
                              hold remaining hremaining⟩
                        | some candidate =>
                            simp [Concrete.decide, hp, hs,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro op flight hmem hphase
                            simp only [Concrete.Node.await,
                              List.mem_cons] at hmem
                            rcases hmem with hnew | holdMem
                            · cases hnew
                              cases hphase
                            · exact hold remaining hremaining holdMem hphase
                    | writing =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        exact ⟨remaining, rfl,
                          hold remaining hremaining⟩
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨remaining, rfl, hold remaining hremaining⟩
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeLoadingGets world address remaining :=
                    NodeLoadingGets.takeFlight hinvariant ht
                  cases hp : taken.phase <;>
                    simp [ht, hp, Outcomes.one] at hresult
                  · subst result
                    exact ⟨remaining, rfl, hold remaining hremaining⟩
                  · subst result
                    refine ⟨_, rfl, ?_⟩
                    intro op flight hmem hphase
                    apply hold remaining hremaining
                    · simp only [Concrete.Node.remember] at hmem
                      split at hmem <;> exact hmem
                    · exact hphase
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeLoadingGets world address remaining :=
                    NodeLoadingGets.takeFlight hinvariant ht
                  cases hp : taken.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨remaining, rfl, hold remaining hremaining⟩
                  | writing =>
                      cases hext : taken.transaction.isExternal with
                      | false =>
                          simp [ht, hp, hext, Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_⟩
                          intro op flight hmem hphase
                          exact hold remaining hremaining hmem hphase
                      | true =>
                          by_cases hattempt :
                              taken.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro op flight hmem hphase
                            simp only [Concrete.Node.await,
                              List.mem_cons] at hmem
                            rcases hmem with hnew | holdMem
                            · cases hnew
                              simp [World.land, Concrete.Node.await]
                            · exact hold remaining hremaining holdMem hphase
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            exact ⟨remaining, rfl,
                              hold remaining hremaining⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeLoadingGets world address remaining :=
                    NodeLoadingGets.takeFlight hinvariant ht
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  refine ⟨_, rfl, ?_⟩
                  intro op flight hmem hphase
                  exact hold remaining hremaining hmem hphase

theorem NodeWritingPuts.mono
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world next : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (h : NodeWritingPuts world address node)
    (hnetwork : ∀ message ∈ world.network, message ∈ next.network) :
    NodeWritingPuts next address node := by
  intro op flight hmem hphase
  obtain ⟨document, hdocument, hput⟩ := h hmem hphase
  exact ⟨document, hdocument, hnetwork _ hput⟩

theorem NodeWritingPuts.takeFlight
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node remaining : Concrete.Node}
    {op : Concrete.OpId} {taken : Option Concrete.Flight}
    (h : NodeWritingPuts world address node)
    (htake : node.takeFlight op = (taken, remaining)) :
    NodeWritingPuts world address remaining := by
  intro currentOp flight hmem hphase
  exact h (takeFlight_remaining_mem htake hmem) hphase

theorem node_step_writing_puts
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (hinvariant : NodeWritingPuts world address node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧
      NodeWritingPuts (world.land (.node address) now result)
        address next := by
  have hold (current : Concrete.Node)
      (hcurrent : NodeWritingPuts world address current) :
      NodeWritingPuts (world.land (.node address) now result)
        address current :=
    hcurrent.mono fun message hmessage =>
      List.mem_append_left _ hmessage
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hold node hinvariant⟩
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hold node hinvariant⟩
            | some key =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨{ node with pending := [.scan key now] },
                  rfl, hold node hinvariant⟩
        | cons entry rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            refine ⟨_, rfl, ?_⟩
            intro op flight hmem hphase
            simp only [Concrete.Node.await, List.mem_cons] at hmem
            rcases hmem with hnew | holdMem
            · have hp := congrArg
                (fun pair : Concrete.OpId × Concrete.Flight =>
                  pair.2.phase) hnew
              simp [hphase] at hp
            · exact hold node hinvariant holdMem hphase
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hold node hinvariant⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hold node hinvariant⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hold node hinvariant⟩
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              refine ⟨_, rfl, ?_⟩
              intro op flight hmem hphase
              simp only [Concrete.Node.await, List.mem_cons] at hmem
              rcases hmem with hnew | holdMem
              · have hp := congrArg
                  (fun pair : Concrete.OpId × Concrete.Flight =>
                    pair.2.phase) hnew
                simp [hphase] at hp
              · exact hold node hinvariant holdMem hphase
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeWritingPuts world address remaining :=
                    NodeWritingPuts.takeFlight
                      (node := node) hinvariant ht
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : taken.phase with
                    | loading =>
                        simp only [hp] at hresult
                        cases hs : Concrete.select appConfig taken
                            (heq ▸ loaded) with
                        | none =>
                            simp [Concrete.decide, hs, Outcomes.one] at hresult
                            subst result
                            exact ⟨remaining, rfl,
                              hold remaining hremaining⟩
                        | some candidate =>
                            simp [Concrete.decide, hs, Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro op flight hmem hphase
                            simp only [Concrete.Node.await,
                              List.mem_cons] at hmem
                            rcases hmem with hnew | holdMem
                            · cases hnew
                              refine ⟨candidate.document, rfl, ?_⟩
                              simp [World.land, Concrete.Node.await]
                            · exact hold remaining hremaining holdMem hphase
                    | writing =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        exact ⟨remaining, rfl,
                          hold remaining hremaining⟩
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨remaining, rfl,
                      hold remaining hremaining⟩
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeWritingPuts world address remaining :=
                    NodeWritingPuts.takeFlight
                      (node := node) hinvariant ht
                  cases hp : taken.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨remaining, rfl,
                        hold remaining hremaining⟩
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      refine ⟨_, rfl, hold _ ?_⟩
                      intro op flight hmem hphase
                      simp [Concrete.Node.remember] at hmem
                      split at hmem
                      all_goals exact hremaining hmem hphase
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeWritingPuts world address remaining :=
                    NodeWritingPuts.takeFlight
                      (node := node) hinvariant ht
                  cases hp : taken.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨remaining, rfl,
                        hold remaining hremaining⟩
                  | writing =>
                      cases hext : taken.transaction.isExternal with
                      | false =>
                          simp [ht, hp, hext, Outcomes.one] at hresult
                          subst result
                          exact ⟨_, rfl, hold _ hremaining⟩
                      | true =>
                          by_cases hattempt :
                              taken.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro op flight hmem hphase
                            simp only [Concrete.Node.await,
                              List.mem_cons] at hmem
                            rcases hmem with hnew | holdMem
                            · have hp := congrArg
                                (fun pair :
                                  Concrete.OpId × Concrete.Flight =>
                                  pair.2.phase) hnew
                              simp [hphase] at hp
                            · exact hold remaining hremaining holdMem hphase
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            exact ⟨remaining, rfl,
                              hold remaining hremaining⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hold node hinvariant⟩
              | some taken =>
                  have hremaining :
                      NodeWritingPuts world address remaining :=
                    NodeWritingPuts.takeFlight
                      (node := node) hinvariant ht
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨_, rfl, hold _ hremaining⟩

def WritingPuts
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧
      NodeWritingPuts world address node

theorem writingPuts_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    WritingPuts (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  refine ⟨{}, hinit.2.2 address haddress, ?_⟩
  intro op flight hmem
  simp at hmem

theorem writingPuts_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : WritingPuts world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    WritingPuts next := by
  cases hstep with
  | inject =>
      intro address haddress
      obtain ⟨node, hnode, hputs⟩ := hinvariant address haddress
      exact ⟨node, hnode, hputs.mono fun message hmessage =>
        List.mem_append_left _ hmessage⟩
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress
      obtain ⟨node, hnode, hputs⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨after, hstate, hafter⟩ :=
          node_step_writing_puts hputs (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode],
          hputs.mono fun message hmessage =>
            List.mem_append_left _ hmessage⟩

theorem reachable_writing_puts
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    WritingPuts world := by
  induction hreachable with
  | init hinit => exact writingPuts_initial hinit
  | step _ hstep ih => exact writingPuts_step ih hstep

def LoadingGets
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧
      NodeLoadingGets world address node

theorem loadingGets_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    LoadingGets (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  refine ⟨{}, hinit.2.2 address haddress, ?_⟩
  intro op flight hmem
  simp at hmem

theorem loadingGets_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : LoadingGets world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    LoadingGets next := by
  cases hstep with
  | inject =>
      intro address haddress
      obtain ⟨node, hnode, hgets⟩ := hinvariant address haddress
      exact ⟨node, hnode, hgets.mono fun message hmessage =>
        List.mem_append_left _ hmessage⟩
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress
      obtain ⟨node, hnode, hgets⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨after, hstate, hafter⟩ :=
          node_step_loading_gets hgets (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode],
          hgets.mono fun message hmessage =>
            List.mem_append_left _ hmessage⟩

theorem reachable_loading_gets
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    LoadingGets world := by
  induction hreachable with
  | init hinit => exact loadingGets_initial hinit
  | step _ hstep ih => exact loadingGets_step ih hstep

theorem reachable_loading_flight_request
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .loading) :
    (Concrete.Pid.node address, .store,
      .storeRequest { op, payload := .get flight.key }) ∈ world.network := by
  obtain ⟨actual, hactual, hgets⟩ :=
    reachable_loading_gets hreachable address haddress
  rw [hnode] at hactual
  cases Concrete.Local.node.inj hactual
  exact hgets hflight hphase

theorem reachable_writing_flight_provenance
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} {node : Concrete.Node}
    (haddress : address ∈ nodes)
    (hnode : world.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing) :
    ∃ document,
      flight.document = some document ∧
      ∃ provenance :
          PutProvenance appConfig flight.key document
            (flight.loaded.map (·.2)),
        provenance.transaction = flight.transaction ∧
        provenance.loaded = flight.loaded ∧
        provenance.outputs = flight.selected ∧
        provenance.continuations = flight.continuations ∧
        (Concrete.Pid.node address, .store,
          .storeRequest {
            op
            payload := .put flight.key document
              (flight.loaded.map (·.2))
          }) ∈ world.network := by
  obtain ⟨actual, hactual, hvalid⟩ :=
    reachable_nodes_valid hreachable address haddress
  rw [hnode] at hactual
  cases Concrete.Local.node.inj hactual
  obtain ⟨document, hdocument, provenance, htransaction, hloaded,
      houtputs, hcontinuations⟩ :=
    (hvalid op flight hflight).writingProvenance hphase
  obtain ⟨writingNode, hwritingNode, hwrites⟩ :=
    reachable_writing_puts hreachable address haddress
  rw [hnode] at hwritingNode
  cases Concrete.Local.node.inj hwritingNode
  obtain ⟨wireDocument, hwireDocument, hput⟩ :=
    hwrites hflight hphase
  rw [hdocument] at hwireDocument
  cases Option.some.inj hwireDocument
  exact ⟨document, hdocument, provenance, htransaction, hloaded,
    houtputs, hcontinuations, hput⟩

theorem decide_put_valid {appConfig : Resonate.Config}
    {node : Concrete.Node} {flight : Concrete.Flight}
    {loaded : Option (Document flight.key × Concrete.Version)}
    (hflight : FlightValid appConfig flight)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ (Concrete.decide appConfig node flight loaded).send) :
    ValidPut appConfig key document expectedVersion := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      simp [Concrete.decide, hselect] at hmessage
  | some candidate =>
      simp [Concrete.decide, hselect, Concrete.Node.await] at hmessage
      obtain ⟨rfl, hop, hkey, hdocument, hexpected⟩ := hmessage
      subst op
      subst key
      have : document = candidate.document := eq_of_heq hdocument
      subst document
      subst expectedVersion
      exact ⟨{
        transaction := flight.transaction
        loaded
        outputs := candidate.outputs
        continuations := candidate.continuations
        expected_eq := rfl
        selected := select_valid hflight.1 hselect
      }⟩

theorem decide_put_provenance {appConfig : Resonate.Config}
    {node : Concrete.Node} {flight : Concrete.Flight}
    {loaded : Option (Document flight.key × Concrete.Version)}
    (hflight : FlightValid appConfig flight)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ (Concrete.decide appConfig node flight loaded).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      provenance.transaction = flight.transaction ∧
      ∃ hkey : key = flight.key, hkey ▸ provenance.loaded = loaded := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      simp [Concrete.decide, hselect] at hmessage
  | some candidate =>
      simp [Concrete.decide, hselect, Concrete.Node.await] at hmessage
      obtain ⟨rfl, hop, hkey, hdocument, hexpected⟩ := hmessage
      subst op
      subst key
      have : document = candidate.document := eq_of_heq hdocument
      subst document
      subst expectedVersion
      exact ⟨{
        transaction := flight.transaction
        loaded
        outputs := candidate.outputs
        continuations := candidate.continuations
        expected_eq := rfl
        selected := select_valid hflight.1 hselect
      }, rfl, rfl, rfl⟩

theorem decide_put_provenance_complete {appConfig : Resonate.Config}
    {node : Concrete.Node} {flight : Concrete.Flight}
    {loaded : Option (Document flight.key × Concrete.Version)}
    (hflight : FlightValid appConfig flight)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ (Concrete.decide appConfig node flight loaded).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      provenance.transaction = flight.transaction ∧
      ∃ hkey : key = flight.key,
        ∃ candidate : Concrete.Candidate flight.key,
          Concrete.select appConfig flight loaded = some candidate ∧
          hkey ▸ provenance.loaded = loaded ∧
          provenance.outputs = candidate.outputs ∧
          provenance.continuations = candidate.continuations := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      simp [Concrete.decide, hselect] at hmessage
  | some candidate =>
      simp [Concrete.decide, hselect, Concrete.Node.await] at hmessage
      obtain ⟨rfl, hop, hkey, hdocument, hexpected⟩ := hmessage
      subst op
      subst key
      have : document = candidate.document := eq_of_heq hdocument
      subst document
      subst expectedVersion
      exact ⟨{
        transaction := flight.transaction
        loaded
        outputs := candidate.outputs
        continuations := candidate.continuations
        expected_eq := rfl
        selected := select_valid hflight.1 hselect
      }, rfl, rfl, candidate, rfl, rfl, rfl, rfl⟩

theorem node_step_sent_put_valid
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    (hnode : NodeValid appConfig node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val)
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    ValidPut appConfig key document expectedVersion := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        contradiction
      · cases hp : node.pending with
        | nil =>
          simp only [hp] at hresult
          cases hk : node.known.head? with
          | none =>
              simp [hk, Outcomes.one] at hresult
              subst result
              contradiction
          | some knownKey =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              contradiction
        | cons item rest =>
          simp [hp, Concrete.start, Concrete.Node.await,
            Outcomes.one] at hresult
          subst result
          contradiction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          contradiction
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          contradiction
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Concrete.sendOutputs,
                Outcomes.one] at hresult
              subst result
              simp [Concrete.sendOutputs] at hsend
          | some requestKey =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              contradiction
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                contradiction
            | some flight =>
                simp only [Prod.fst, Prod.snd] at hresult
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      have hflight :=
                        hnode replyOp flight (takeFlight_some_mem ht)
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      exact decide_put_valid hflight hsend
                  | writing =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written | conflict | failed =>
            simp_all [Concrete.Node.takeFlight, Concrete.retry,
              Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
            all_goals grind

def RawPutsValid {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op key document expectedVersion},
    (Concrete.Pid.node address, .store,
      .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ world.network →
    ValidPut appConfig key document expectedVersion

theorem step_sent_put_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {pid : Concrete.Pid} {now : Time}
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hprocess : (CModel nodes appConfig).isProcess pid)
    (hresult : result ∈
      (Concrete.step appConfig config pid (world.process pid)
        now event).val)
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    ValidPut appConfig key document expectedVersion := by
  cases pid with
  | outside => contradiction
  | node address =>
      obtain ⟨node, hlocal, hnode⟩ :=
        reachable_nodes_valid hreachable address hprocess
      exact node_step_sent_put_valid hnode (hlocal ▸ hresult) hsend
  | store =>
      cases hlocal : world.process .store <;>
        cases event with
        | timeout =>
            simp [Concrete.step, Outcomes.one, hlocal] at hresult
            subst result
            contradiction
        | receive sender message =>
            cases message with
            | request call | output output | storeReply rpc =>
                simp [Concrete.step, hlocal, Outcomes.one] at hresult
                subst result
                contradiction
            | storeRequest rpc =>
                obtain ⟨requestOp, payload⟩ := rpc
                cases payload with
                | get requestKey =>
                    simp [Concrete.step, hlocal, Outcomes.one] at hresult
                    subst result
                    contradiction
                | put requestKey requestDocument requestVersion =>
                    simp only [Concrete.step, hlocal] at hresult
                    first
                    | (simp [Outcomes.one] at hresult
                       subst result
                       contradiction)
                    | skip
                    all_goals
                      simp only [Concrete.storePut] at hresult
                      split at hresult
                      · simp [Outcomes.one] at hresult
                        subst result
                        contradiction
                      · split at hresult
                        · simp at hresult
                          rcases hresult with hresult | hresult | hresult
                          all_goals subst result
                          all_goals contradiction
                        · simp [Outcomes.one] at hresult
                          subst result
                          contradiction

theorem rawPutsValid_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    RawPutsValid
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address op key document expectedVersion h
  contradiction

theorem rawPutsValid_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    (hinvariant : RawPutsValid world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    RawPutsValid next := by
  cases hstep with
  | inject htime hprocess hinject =>
      intro address op key document expectedVersion hmem
      simp only [World.inject, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hold
      · simp at hnew
  | process htime hprocess hvalid hresult =>
      intro address op key document expectedVersion hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hold
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨recipient, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        exact step_sent_put_valid hreachable hprocess hresult hsent
  | outside =>
      exact hinvariant

theorem reachable_raw_put_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    RawPutsValid world := by
  induction hreachable with
  | init hinit => exact rawPutsValid_initial _
  | step hreach hstep ih =>
      exact rawPutsValid_step hreach ih hstep

def StoreExists {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∃ store, world.process .store = .store store

theorem storeExists_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    StoreExists (nodes := nodes) (appConfig := appConfig)
      (World.initial process) :=
  ⟨{}, hinit.2.1⟩

theorem store_step_effect
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {store : Concrete.Store} {now : Time}
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store (.store store)
          now event).val) :
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
      cases message with
      | request call | output output | storeReply rpc =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          exact ⟨store, rfl, .inl rfl⟩
      | storeRequest rpc =>
          obtain ⟨op, payload⟩ := rpc
          cases payload with
          | get key =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨store, rfl, .inl rfl⟩
          | put key document expected =>
              simp only [Concrete.step, Concrete.storePut] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact ⟨store, rfl, .inl rfl⟩
              · split at hresult
                · simp at hresult
                  rcases hresult with hresult | hresult | hresult
                  · subst result
                    exact ⟨store.commit key document, rfl,
                      .inr ⟨key, document, rfl⟩⟩
                  · subst result
                    exact ⟨store.commit key document, rfl,
                      .inr ⟨key, document, rfl⟩⟩
                  · subst result
                    exact ⟨store.fence key, rfl,
                      .inr ⟨key, store.toAbstract.read key, rfl⟩⟩
                · simp [Outcomes.one] at hresult
                  subst result
                  exact ⟨store.commit key document, rfl,
                    .inr ⟨key, document, rfl⟩⟩

theorem storeExists_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : StoreExists world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    StoreExists next := by
  obtain ⟨store, hstore⟩ := hinvariant
  cases hstep with
  | inject =>
      exact ⟨store, hstore⟩
  | outside =>
      exact ⟨store, hstore⟩
  | @process pid now event result htime hprocess hvalid hresult =>
      by_cases hp : pid = Concrete.Pid.store
      · subst pid
        rw [hstore] at hresult
        obtain ⟨nextStore, hstate, _⟩ := store_step_effect hresult
        exact ⟨nextStore, by simp [World.land, hstate]⟩
      · exact ⟨store, by simp [World.land, Ne.symm hp, hstore]⟩

theorem reachable_store_exists
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    StoreExists world := by
  induction hreachable with
  | init hinit => exact storeExists_initial hinit
  | step _ hstep ih => exact storeExists_step ih hstep

def GotSnapshots {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {store address op key loaded},
    world.process .store = .store store →
    (Concrete.Pid.store, .node address,
      .storeReply { op, payload := .got key loaded }) ∈ world.network →
    Snapshot store key loaded

theorem gotSnapshots_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    GotSnapshots
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro store address op key loaded hstore hmem
  simp [World.initial] at hmem

theorem node_step_no_store_reply
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val)
    {recipient : Concrete.Pid} {reply : Concrete.RpcReply}
    (hsend : (recipient, .storeReply reply) ∈ result.send) : False := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        contradiction
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                contradiction
            | some knownKey =>
                simp [hk, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                contradiction
        | cons item rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            contradiction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          contradiction
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          contradiction
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Concrete.sendOutputs,
                Outcomes.one] at hresult
              subst result
              simp [Concrete.sendOutputs] at hsend
          | some requestKey =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              contradiction
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                contradiction
            | some flight =>
                simp only [Prod.fst, Prod.snd] at hresult
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      simp only [hp, Concrete.decide] at hresult
                      cases hs : Concrete.select appConfig flight
                          (heq ▸ loaded) with
                      | none =>
                          simp [hs, Outcomes.one] at hresult
                          subst result
                          contradiction
                      | some candidate =>
                          simp [hs, Concrete.Node.await,
                            Outcomes.one] at hresult
                          subst result
                          contradiction
                  | writing =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written | conflict | failed =>
            simp_all [Concrete.Node.takeFlight, Concrete.retry,
              Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
            all_goals grind

theorem sent_got_origin
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {pid : Concrete.Pid} {localState : Concrete.Local} {now : Time}
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {address : Addr} {op : Concrete.OpId} {key : DocumentKey}
    {loaded : Option (Document key × Concrete.Version)}
    (hresult :
      result ∈
        (Concrete.step appConfig config pid localState now event).val)
    (hsend :
      (Concrete.Pid.node address,
        .storeReply { op, payload := .got key loaded }) ∈ result.send) :
    ∃ store,
      pid = .store ∧ localState = .store store ∧
      event = .receive (.node address)
        (.storeRequest { op, payload := .get key }) ∧
      store.read key = loaded ∧ result.state = .store store := by
  cases pid with
  | outside =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      contradiction
  | node processAddress =>
      cases localState with
      | node node =>
          exact (node_step_no_store_reply hresult hsend).elim
      | outside | store =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          contradiction
  | store =>
      cases localState with
      | outside | node =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          contradiction
      | store store =>
          cases event with
          | timeout =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              contradiction
          | receive sender message =>
              cases message with
              | request call | output output | storeReply rpc =>
                  simp [Concrete.step, Outcomes.one] at hresult
                  subst result
                  contradiction
              | storeRequest rpc =>
                  obtain ⟨requestOp, payload⟩ := rpc
                  cases payload with
                  | get requestKey =>
                      simp [Concrete.step, Outcomes.one] at hresult
                      subst result
                      grind
                  | put requestKey requestDocument requestVersion =>
                      simp only [Concrete.step, Concrete.storePut] at hresult
                      split at hresult
                      · simp [Outcomes.one] at hresult
                        subst result
                        contradiction
                      · split at hresult
                        · simp at hresult
                          rcases hresult with hresult | hresult | hresult
                          all_goals subst result
                          all_goals contradiction
                        · simp [Outcomes.one] at hresult
                          subst result
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
  | inject =>
      intro store address op key loaded hstore hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hstore hold
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro nextStore address op key loaded hnextStore hmem
      obtain ⟨store, hstore⟩ := hstoreExists
      have heffect :
          nextStore = store ∨
            ∃ writtenKey written,
              nextStore = store.commit writtenKey written := by
        by_cases hp : pid = Concrete.Pid.store
        · subst pid
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
          · exact .inl rfl
          · exact .inr ⟨writtenKey, written, rfl⟩
        · have heq : store = nextStore := by
            have hx : world.process .store = .store nextStore := by
              simpa [World.land, Ne.symm hp] using hnextStore
            rw [hstore] at hx
            exact Concrete.Local.store.inj hx
          exact .inl heq.symm
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · have hsnapshot := hinvariant hstore hold
        rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
        · exact hsnapshot
        · exact Snapshot.commit hsnapshot
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨originStore, hpid, hlocal, hevent,
            hread, hstate⟩ := sent_got_origin hresult hsent
        cases hpid
        rw [hstore] at hlocal
        cases Concrete.Local.store.inj hlocal
        cases hevent
        have hsame : nextStore = store := by
          have hx : store = nextStore := by
            simpa [World.land, hstate] using hnextStore
          exact hx.symm
        subst nextStore
        exact Snapshot.of_read hread

theorem reachable_got_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    GotSnapshots world := by
  induction hreachable with
  | init hinit => exact gotSnapshots_initial _
  | step hreachable hstep hinvariant =>
      exact gotSnapshots_step
        (reachable_store_exists hreachable) hinvariant hstep

def FlightRequestOrigins
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address node op flight call},
    address ∈ nodes →
    world.process (.node address) = .node node →
    (op, flight) ∈ node.flights →
    flight.transaction = .external call →
    (Concrete.Pid.outside, .node address, .request call) ∈ world.network

def TransactionOrigin
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) (address : Addr) :
    Concrete.Transaction → Prop
  | .external call =>
      (Concrete.Pid.outside, .node address, .request call) ∈ world.network
  | .work _ _ _ | .scan _ _ _ => True

theorem node_step_sent_put_snapshot
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (hstore : world.process .store = .store store)
    (hnode : NodeValid appConfig node)
    (hgots : GotSnapshots world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (hvalid : event.Valid world (.node address))
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val)
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        contradiction
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                contradiction
            | some knownKey =>
                simp [hk, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                contradiction
        | cons item rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            contradiction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          contradiction
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          contradiction
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Concrete.sendOutputs,
                Outcomes.one] at hresult
              subst result
              simp [Concrete.sendOutputs] at hsend
          | some requestKey =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              contradiction
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            have hsnapshot : Snapshot store loadedKey loaded :=
              hgots hstore hvalid
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                contradiction
            | some flight =>
                simp only [Prod.fst, Prod.snd] at hresult
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      have hflight :=
                        hnode replyOp flight (takeFlight_some_mem ht)
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      obtain ⟨provenance, _, hkey, hloaded⟩ :=
                        decide_put_provenance hflight hsend
                      subst key
                      subst loadedKey
                      cases hloaded
                      exact ⟨provenance, hsnapshot⟩
                  | writing =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written | conflict | failed =>
            simp_all [Concrete.Node.takeFlight, Concrete.retry,
              Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
            all_goals grind

theorem node_step_sent_put_origin
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (haddress : address ∈ nodes)
    (hnodeLocal : world.process (.node address) = .node node)
    (hnode : NodeValid appConfig node)
    (horigins : FlightRequestOrigins world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val)
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      TransactionOrigin world address provenance.transaction := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        contradiction
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                contradiction
            | some knownKey =>
                simp [hk, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                contradiction
        | cons entry rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            contradiction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          contradiction
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          contradiction
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Concrete.sendOutputs,
                Outcomes.one] at hresult
              subst result
              simp [Concrete.sendOutputs] at hsend
          | some requestKey =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              contradiction
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                contradiction
            | some flight =>
                simp only [Prod.fst, Prod.snd] at hresult
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      have hflightMem := takeFlight_some_mem ht
                      have hflight := hnode replyOp flight hflightMem
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      obtain ⟨provenance, htransaction, hkey, candidate,
                          hselect, hloaded, houtputs, hcontinuations⟩ :=
                        decide_put_provenance_complete hflight hsend
                      refine ⟨provenance, ?_⟩
                      cases ht : provenance.transaction with
                      | external call =>
                          exact horigins haddress hnodeLocal hflightMem
                            (htransaction.symm.trans ht)
                      | work item instant rest => trivial
                      | scan scanKey instant rest => trivial
                  | writing =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written | conflict | failed =>
            simp_all [Concrete.Node.takeFlight, Concrete.retry,
              Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
            all_goals grind

def OwnedPutSnapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {store address op key document expectedVersion},
    world.process .store = .store store →
    (Concrete.Pid.node address, .store,
      .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ world.network →
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded

theorem ownedPutSnapshots_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    OwnedPutSnapshots
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro store address op key document expectedVersion hstore hmem
  simp [World.initial] at hmem

theorem ownedPutSnapshots_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hstoreExists : StoreExists world)
    (hnodes : NodesValid world)
    (hgots : GotSnapshots world)
    (hinvariant : OwnedPutSnapshots world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    OwnedPutSnapshots next := by
  cases hstep with
  | inject =>
      intro store address op key document expectedVersion hstore hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · exact hinvariant hstore hold
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro nextStore address op key document expectedVersion
        hnextStore hmem
      obtain ⟨store, hstore⟩ := hstoreExists
      have heffect :
          nextStore = store ∨
            ∃ writtenKey written,
              nextStore = store.commit writtenKey written := by
        by_cases hp : pid = Concrete.Pid.store
        · subst pid
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
          · exact .inl rfl
          · exact .inr ⟨writtenKey, written, rfl⟩
        · have heq : store = nextStore := by
            have hx : world.process .store = .store nextStore := by
              simpa [World.land, Ne.symm hp] using hnextStore
            rw [hstore] at hx
            exact Concrete.Local.store.inj hx
          exact .inl heq.symm
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, hsnapshot⟩ :=
          hinvariant hstore hold
        refine ⟨provenance, ?_⟩
        rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
        · exact hsnapshot
        · exact Snapshot.commit hsnapshot
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨node, hnodeState, hnodeValid⟩ :=
          hnodes address hprocess
        have hresult' := hresult
        rw [hnodeState] at hresult'
        obtain ⟨provenance, hsnapshot⟩ :=
          node_step_sent_put_snapshot hstore hnodeValid hgots
            hvalid hresult' hsent
        have hsame : nextStore = store := by
          have hx : store = nextStore := by
            simpa [World.land, hstore] using hnextStore
          exact hx.symm
        subst nextStore
        exact ⟨provenance, hsnapshot⟩

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
        (reachable_got_snapshots hreachable)
        hinvariant hstep

def PutRepliesHaveRequest
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op reply},
    (reply = StoreReply.written ∨
      reply = .conflict ∨ reply = .failed) →
    (Concrete.Pid.store, .node address,
      .storeReply { op, payload := reply }) ∈ world.network →
    ∃ key document expectedVersion,
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ world.network

theorem sent_put_reply_origin
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {pid : Concrete.Pid} {localState : Concrete.Local} {now : Time}
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {address : Addr} {op : Concrete.OpId} {reply : StoreReply}
    (hreply : reply = StoreReply.written ∨
      reply = .conflict ∨ reply = .failed)
    (hresult :
      result ∈
        (Concrete.step appConfig config pid localState now event).val)
    (hsend :
      (Concrete.Pid.node address,
        .storeReply { op, payload := reply }) ∈ result.send) :
    ∃ key document expectedVersion,
      event = .receive (.node address)
        (.storeRequest {
          op
          payload := .put key document expectedVersion
        }) := by
  cases pid with
  | outside =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      contradiction
  | node processAddress =>
      cases localState with
      | node node =>
          exact (node_step_no_store_reply hresult hsend).elim
      | outside | store =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          contradiction
  | store =>
      cases localState with
      | outside | node =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          contradiction
      | store store =>
          cases event with
          | timeout =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              contradiction
          | receive sender message =>
              cases message with
              | request call | output output | storeReply rpc =>
                  simp [Concrete.step, Outcomes.one] at hresult
                  subst result
                  contradiction
              | storeRequest rpc =>
                  obtain ⟨requestOp, payload⟩ := rpc
                  cases payload with
                  | get requestKey =>
                      simp [Concrete.step, Outcomes.one] at hresult
                      subst result
                      rcases hreply with rfl | rfl | rfl <;>
                        contradiction
                  | put key document expected =>
                      refine ⟨key, document, expected, ?_⟩
                      simp only [Concrete.step, Concrete.storePut] at hresult
                      split at hresult
                      · simp [Outcomes.one] at hresult
                        subst result
                        grind
                      · split at hresult
                        · simp at hresult
                          rcases hresult with hresult | hresult | hresult
                          all_goals subst result
                          all_goals grind
                        · simp [Outcomes.one] at hresult
                          subst result
                          grind

theorem putRepliesHaveRequest_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    PutRepliesHaveRequest
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address op reply hreply hmem
  simp [World.initial] at hmem

theorem putRepliesHaveRequest_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : PutRepliesHaveRequest world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    PutRepliesHaveRequest next := by
  cases hstep with
  | inject =>
      intro address op reply hreply hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨key, document, expected, hput⟩ :=
          hinvariant hreply hold
        exact ⟨key, document, expected,
          List.mem_append_left _ hput⟩
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address op reply hreply hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨key, document, expected, hput⟩ :=
          hinvariant hreply hold
        exact ⟨key, document, expected,
          List.mem_append_left _ hput⟩
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨key, document, expected, horigin⟩ :=
          sent_put_reply_origin hreply hresult hsent
        cases horigin
        exact ⟨key, document, expected,
          List.mem_append_left _ hvalid⟩

theorem reachable_put_replies_have_request
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    PutRepliesHaveRequest world := by
  induction hreachable with
  | init hinit => exact putRepliesHaveRequest_initial _
  | step _ hstep ih => exact putRepliesHaveRequest_step ih hstep

def GotRepliesHaveRequest
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op key loaded},
    (Concrete.Pid.store, .node address,
      .storeReply { op, payload := .got key loaded }) ∈ world.network →
    (Concrete.Pid.node address, .store,
      .storeRequest { op, payload := .get key }) ∈ world.network

theorem gotRepliesHaveRequest_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    GotRepliesHaveRequest
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address op key loaded h
  contradiction

theorem gotRepliesHaveRequest_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : GotRepliesHaveRequest world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    GotRepliesHaveRequest next := by
  cases hstep with
  | inject =>
      intro address op key loaded hmem
      simp only [World.inject, List.mem_append, List.mem_singleton] at hmem ⊢
      rcases hmem with hold | hnew
      · exact .inl (hinvariant hold)
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address op key loaded hmem
      simp only [World.land, List.mem_append] at hmem ⊢
      rcases hmem with hold | hnew
      · exact .inl (hinvariant hold)
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨store, _, hlocal, hevent, _, _⟩ :=
          sent_got_origin hresult hsent
        cases hevent
        exact .inl hvalid

theorem reachable_got_replies_have_request
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    GotRepliesHaveRequest world := by
  induction hreachable with
  | init hinit => exact gotRepliesHaveRequest_initial _
  | step _ hstep ih => exact gotRepliesHaveRequest_step ih hstep

/-! ### Ghost request provenance for active flights

The transaction is intentionally absent from the GET/PUT wire payload.  This
reachable invariant records only the proof that an active external
continuation came from an injected request. -/

theorem flightRequestOrigins_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    FlightRequestOrigins
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address node op flight call haddress hnode hflight
  have : Concrete.Local.node node = .node {} := hnode.symm.trans
    (hinit.2.2 address haddress)
  cases this
  simp at hflight

theorem node_step_flight_request_origins
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node next : Concrete.Node}
    (haddress : address ∈ nodes)
    (hnodeLocal : world.process (.node address) = .node node)
    (hinvariant : FlightRequestOrigins world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (hvalid : event.Valid world (.node address))
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    ∀ {op flight call},
      (op, flight) ∈ next.flights →
      flight.transaction = .external call →
      (Concrete.Pid.outside, .node address, .request call) ∈
        (world.land (.node address) now result).network := by
  have hold {op flight call}
      (hmem : (op, flight) ∈ node.flights)
      (htransaction : flight.transaction = .external call) :
      (Concrete.Pid.outside, .node address, .request call) ∈
        (world.land (.node address) now result).network :=
    List.mem_append_left _
      (hinvariant haddress hnodeLocal hmem htransaction)
  intro currentOp current call hmem htransaction
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        cases Concrete.Local.node.inj hstate
        exact hold hmem htransaction
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact hold hmem htransaction
            | some key =>
                simp [hk, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                have hflights := congrArg (fun localState =>
                  match localState with
                  | .node value => value.flights
                  | _ => []) hstate
                change node.flights = next.flights at hflights
                rw [← hflights] at hmem
                exact hold hmem htransaction
        | cons entry rest =>
            cases entry with
            | scan key instant =>
                simp [hp, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                simp only [List.mem_cons] at hmem
                rcases hmem with hnew | holdMem
                · have htx := congrArg
                    (fun pair : Concrete.OpId × Concrete.Flight =>
                      pair.2.transaction) hnew
                  rw [htransaction] at htx
                  contradiction
                · exact hold holdMem htransaction
            | work item instant =>
                simp [hp, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                simp only [List.mem_cons] at hmem
                rcases hmem with hnew | holdMem
                · have htx := congrArg
                    (fun pair : Concrete.OpId × Concrete.Flight =>
                      pair.2.transaction) hnew
                  rw [htransaction] at htx
                  contradiction
                · exact hold holdMem htransaction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          cases Concrete.Local.node.inj hstate
          exact hold hmem htransaction
      case outside.request incoming =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          cases Concrete.Local.node.inj hstate
          exact hold hmem htransaction
        · cases hk : (Concrete.Transaction.external incoming).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              cases Concrete.Local.node.inj hstate
              exact hold hmem htransaction
          | some key =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              cases Concrete.Local.node.inj hstate
              simp only [List.mem_cons] at hmem
              rcases hmem with hnew | holdMem
              · cases hnew
                simp only at htransaction
                cases Concrete.Transaction.external.inj htransaction
                exact List.mem_append_left _ hvalid
              · exact hold holdMem htransaction
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk flight remaining =>
              cases flight with
            | none =>
                simp only [ht] at hresult
                simp [Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact hold hmem htransaction
            | some flight =>
                simp only [ht] at hresult
                have hremaining :
                    ∀ {op current},
                      (op, current) ∈ remaining.flights →
                      (op, current) ∈ node.flights := by
                  intro op current h
                  simp only [Concrete.Node.takeFlight] at ht
                  have hsnd := congrArg Prod.snd ht
                  simp only at hsnd
                  rw [← hsnd] at h
                  exact (List.mem_filter.mp h).1
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      simp only [hp, Outcomes.one,
                        List.mem_singleton] at hresult
                      subst result
                      cases hs : Concrete.select appConfig flight
                          (heq ▸ loaded) with
                      | none =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.decide, hs] at hflights
                          rw [← hflights] at hmem
                          exact hold (hremaining hmem) htransaction
                      | some candidate =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.decide, hs,
                            Concrete.Node.await] at hflights
                          rw [← hflights] at hmem
                          simp only [List.mem_cons] at hmem
                          rcases hmem with hnew | holdMem
                          · have htx := congrArg
                              (fun pair :
                                Concrete.OpId × Concrete.Flight =>
                                pair.2.transaction) hnew
                            apply hold (takeFlight_some_mem ht)
                            exact htx.symm.trans htransaction
                          · exact hold (hremaining holdMem) htransaction
                  | writing =>
                      simp only [hp, Outcomes.one,
                        List.mem_singleton] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      simp only at hflights
                      rw [← hflights] at hmem
                      exact hold (hremaining hmem) htransaction
                next _ =>
                  simp only [Outcomes.one, List.mem_singleton] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  simp only at hflights
                  rw [← hflights] at hmem
                  exact hold (hremaining hmem) htransaction
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change node.flights = next.flights at hflights
                  rw [← hflights] at hmem
                  exact hold hmem htransaction
              | some taken =>
                  cases hp : taken.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      change remaining.flights = next.flights at hflights
                      rw [← hflights] at hmem
                      exact hold (takeFlight_remaining_mem ht hmem)
                        htransaction
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      simp [Concrete.Node.remember] at hflights
                      split at hflights
                      all_goals
                        change remaining.flights = next.flights at hflights
                        rw [← hflights] at hmem
                        exact hold (takeFlight_remaining_mem ht hmem)
                          htransaction
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change node.flights = next.flights at hflights
                  rw [← hflights] at hmem
                  exact hold hmem htransaction
              | some taken =>
                  cases hp : taken.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      change remaining.flights = next.flights at hflights
                      rw [← hflights] at hmem
                      exact hold (takeFlight_remaining_mem ht hmem)
                        htransaction
                  | writing =>
                      by_cases hext :
                          taken.transaction.isExternal = true
                      · simp [ht, hp, hext] at hresult
                        by_cases hattempt :
                            taken.attempt < config.retries
                        · simp [Concrete.retry, hattempt, Outcomes.one] at hresult
                          subst result
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          change
                            (remaining.await {
                              taken with
                                loaded := none
                                document := none
                                selected := []
                                continuations := []
                                attempt := taken.attempt + 1
                                phase := .loading
                            } (.get taken.key)).1.flights =
                              next.flights at hflights
                          rw [← hflights] at hmem
                          simp only [Concrete.Node.await,
                            List.mem_cons] at hmem
                          rcases hmem with hnew | holdMem
                          · have htx := congrArg
                              (fun pair :
                                Concrete.OpId × Concrete.Flight =>
                                pair.2.transaction) hnew
                            apply hold (takeFlight_some_mem ht)
                            exact htx.symm.trans htransaction
                          · exact hold
                              (takeFlight_remaining_mem ht holdMem)
                              htransaction
                        · simp [Concrete.retry, hattempt, Outcomes.one] at hresult
                          subst result
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          change remaining.flights = next.flights at hflights
                          rw [← hflights] at hmem
                          exact hold (takeFlight_remaining_mem ht hmem)
                            htransaction
                      · simp [ht, hp, hext, Outcomes.one] at hresult
                        subst result
                        have hflights := congrArg (fun localState =>
                          match localState with
                          | .node value => value.flights
                          | _ => []) hstate
                        change remaining.flights = next.flights at hflights
                        rw [← hflights] at hmem
                        exact hold (takeFlight_remaining_mem ht hmem)
                          htransaction
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change node.flights = next.flights at hflights
                  rw [← hflights] at hmem
                  exact hold hmem htransaction
              | some taken =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change remaining.flights = next.flights at hflights
                  rw [← hflights] at hmem
                  exact hold (takeFlight_remaining_mem ht hmem)
                    htransaction

theorem flightRequestOrigins_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    (hinvariant : FlightRequestOrigins world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    FlightRequestOrigins next := by
  cases hstep with
  | inject =>
      intro address node op flight call haddress hnode hmem htransaction
      exact List.mem_append_left _
        (hinvariant haddress hnode hmem htransaction)
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address node op flight call haddress hnode hmem htransaction
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨before, hbefore, _⟩ :=
          reachable_nodes_valid hreachable address haddress
        have hstate : result.state = .node node := by
          simpa [World.land] using hnode
        exact node_step_flight_request_origins haddress hbefore hinvariant
          hvalid (hbefore ▸ hresult) hstate hmem htransaction
      · have hlocal :
            world.process (.node address) = .node node := by
          simpa [World.land, Ne.symm hp] using hnode
        exact List.mem_append_left _
          (hinvariant haddress hlocal hmem htransaction)

theorem reachable_flight_request_origins
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    FlightRequestOrigins world := by
  induction hreachable with
  | init hinit => exact flightRequestOrigins_initial hinit
  | step hreachable hstep ih =>
      exact flightRequestOrigins_step hreachable ih hstep

theorem TransactionOrigin.mono
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world next : World (CModel nodes appConfig)}
    {address : Addr} {transaction : Concrete.Transaction}
    (horigin : TransactionOrigin world address transaction)
    (hnetwork : ∀ message ∈ world.network, message ∈ next.network) :
    TransactionOrigin next address transaction := by
  cases transaction with
  | external call => exact hnetwork _ horigin
  | work item instant rest | scan key instant rest => trivial

def PutRequestOrigins
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address op key document expectedVersion},
    (Concrete.Pid.node address, .store,
      .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ world.network →
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      TransactionOrigin world address provenance.transaction

theorem putRequestOrigins_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    PutRequestOrigins
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address op key document expected hmem
  contradiction

theorem putRequestOrigins_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    (hinvariant : PutRequestOrigins world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    PutRequestOrigins next := by
  cases hstep with
  | inject =>
      intro address op key document expected hmem
      simp only [World.inject, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, horigin⟩ := hinvariant hold
        exact ⟨provenance, horigin.mono fun message hmessage =>
          List.mem_append_left _ hmessage⟩
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address op key document expected hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, horigin⟩ := hinvariant hold
        exact ⟨provenance, horigin.mono fun message hmessage =>
          List.mem_append_left _ hmessage⟩
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨recipient, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨node, hnodeLocal, hnode⟩ :=
          reachable_nodes_valid hreachable address hprocess
        obtain ⟨provenance, horigin⟩ :=
          node_step_sent_put_origin hprocess hnodeLocal hnode
            (reachable_flight_request_origins hreachable)
            (hnodeLocal ▸ hresult) hsent
        exact ⟨provenance, horigin.mono fun triple htriple =>
          List.mem_append_left _ htriple⟩

theorem reachable_put_request_origins
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    PutRequestOrigins world := by
  induction hreachable with
  | init hinit => exact putRequestOrigins_initial _
  | step hreachable hstep ih =>
      exact putRequestOrigins_step hreachable ih hstep

/-- A raw PUT that is still eligible to match the physical version carries
one provenance witness that is both tied to its loaded snapshot and, for an
external transaction, to the originating request.  Keeping these facts on the
same witness is what permits the store step itself to stage the abstract
transaction before the node later consumes the reply. -/
def StageablePuts
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {store address op key document expectedVersion},
    world.process .store = .store store →
    (Concrete.Pid.node address, .store,
      .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ world.network →
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded ∧
        TransactionOrigin world address provenance.transaction ∧
        (∀ node flight,
          world.process (.node address) = .node node →
          (op, flight) ∈ node.flights →
          flight.phase = .writing →
          ∃ hkey : key = flight.key,
            hkey ▸ provenance.loaded = flight.loaded ∧
            provenance.transaction = flight.transaction ∧
            provenance.outputs = flight.selected ∧
            provenance.continuations = flight.continuations) ∧
        (expectedVersion = store.version key →
          ∃ node flight,
            world.process (.node address) = .node node ∧
            (op, flight) ∈ node.flights ∧
            flight.phase = .writing ∧
            ∀ reply,
              (reply = StoreReply.written ∨
                reply = .conflict ∨ reply = .failed) →
              (Concrete.Pid.store, .node address,
                .storeReply { op, payload := reply }) ∉ world.network)

theorem node_step_sent_put_stageable
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (haddress : address ∈ nodes)
    (hnodeLocal : world.process (.node address) = .node node)
    (hstore : world.process .store = .store store)
    (hnode : NodeValid appConfig node)
    (hserial : NodeSerial node)
    (hgots : GotSnapshots world)
    (horigins : FlightRequestOrigins world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (hvalid : event.Valid world (.node address))
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val)
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, .storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded ∧
        TransactionOrigin world address provenance.transaction ∧
        (∀ next flight,
          result.state = .node next →
          (op, flight) ∈ next.flights →
          flight.phase = .writing →
          ∃ hkey : key = flight.key,
            hkey ▸ provenance.loaded = flight.loaded ∧
            provenance.transaction = flight.transaction ∧
            provenance.outputs = flight.selected ∧
            provenance.continuations = flight.continuations) ∧
        ∃ next flight,
          result.state = .node next ∧
          (op, flight) ∈ next.flights ∧
          flight.phase = .writing := by
  obtain ⟨idNode, idState, idMono, idSent, idUnique⟩ :=
    node_step_ids hresult
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        contradiction
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                contradiction
            | some knownKey =>
                simp [hk, Concrete.start, Concrete.Node.await,
                  Outcomes.one] at hresult
                subst result
                contradiction
        | cons item rest =>
            simp [hp, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            contradiction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          contradiction
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          contradiction
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Concrete.sendOutputs,
                Outcomes.one] at hresult
              subst result
              simp [Concrete.sendOutputs] at hsend
          | some requestKey =>
              simp [hk, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              contradiction
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            have hsnapshot : Snapshot store loadedKey loaded :=
              hgots hstore hvalid
            simp only [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨flight, next⟩ := taken
            cases flight with
            | none =>
                simp [Outcomes.one] at hresult
                subst result
                contradiction
            | some flight =>
                simp only [Prod.fst, Prod.snd] at hresult
                split at hresult
                next heq =>
                  cases hp : flight.phase with
                  | loading =>
                      have hflightMem := takeFlight_some_mem ht
                      have hflight := hnode replyOp flight hflightMem
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      obtain ⟨provenance, htransaction, hkey, candidate,
                          hselect, hloaded, houtputs, hcontinuations⟩ :=
                        decide_put_provenance_complete hflight hsend
                      subst key
                      subst loadedKey
                      cases hloaded
                      refine ⟨provenance, hsnapshot, ?_, ?_, ?_⟩
                      · cases hprovenance : provenance.transaction with
                        | external call =>
                            exact horigins haddress hnodeLocal hflightMem
                              (htransaction.symm.trans hprovenance)
                        | work item instant rest => trivial
                        | scan scanKey instant rest => trivial
                      · intro resultNode active hstate hactive hactivePhase
                        have hempty :
                            next.flights = [] := by
                          have hfilter :=
                            takeFlight_filter_empty_of_some hserial
                              (congrArg Prod.fst ht)
                          have hnext := congrArg
                            (fun pair :
                              Option Concrete.Flight × Concrete.Node =>
                                pair.2.flights) ht
                          simp [Concrete.Node.takeFlight, hfilter] at hnext
                          exact hnext
                        have hflights := congrArg (fun localState =>
                          match localState with
                          | .node value => value.flights
                          | _ => []) hstate
                        simp [Concrete.decide, hselect, Concrete.Node.await,
                          hempty] at hflights
                        rw [← hflights] at hactive
                        simp only [List.mem_singleton] at hactive
                        cases hactive
                        exact ⟨rfl, rfl, htransaction, houtputs,
                          hcontinuations⟩
                      · let writing : Concrete.Flight := {
                          flight with
                          loaded := provenance.loaded
                          document := some candidate.document
                          selected := candidate.outputs
                          continuations := candidate.continuations
                          phase := .writing
                        }
                        refine ⟨(next.await writing
                            (.put flight.key candidate.document
                              (provenance.loaded.map (·.2)))).1,
                          writing, ?_, ?_, rfl⟩
                        · simp [Concrete.decide, hselect, writing]
                        · simp only [Concrete.Node.await, List.mem_cons]
                          apply Or.inl
                          apply Prod.ext
                          · exact (idSent _ _ hsend).1.trans
                              (takeFlight_nextOp ht).symm
                          · rfl
                  | writing =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written | conflict | failed =>
            simp_all [Concrete.Node.takeFlight, Concrete.retry,
              Concrete.Node.await, Concrete.sendOutputs, Outcomes.one]
            all_goals grind

theorem stageablePuts_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    (process : Concrete.Pid → Concrete.Local) :
    StageablePuts
      (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro store address op key document expectedVersion hstore hmem
  contradiction

theorem stageablePuts_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    (hinvariant : StageablePuts world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    StageablePuts next := by
  cases hstep with
  | inject =>
      intro store address op key document expectedVersion hstore hmem
      simp only [World.inject, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, hsnapshot, horigin, hagreement,
          heligible⟩ :=
          hinvariant hstore hold
        refine ⟨provenance, hsnapshot,
          horigin.mono fun message hmessage =>
            List.mem_append_left _ hmessage, ?_, ?_⟩
        · intro node flight hnode hflight hphase
          exact hagreement node flight
            (by simpa [World.inject] using hnode) hflight hphase
        · intro hmatch
          obtain ⟨node, flight, hnode, hflight, hphase, hnoreply⟩ :=
            heligible hmatch
          refine ⟨node, flight, by simpa [World.inject] using hnode,
            hflight, hphase, ?_⟩
          intro reply hreply hmem
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at hmem
          rcases hmem with hold | hnew
          · exact hnoreply reply hreply hold
          · simp at hnew
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro nextStore address op key document expectedVersion
        hnextStore hmem
      obtain ⟨store, hstore⟩ := reachable_store_exists hreachable
      have heffect :
          nextStore = store ∨
            ∃ writtenKey written,
              nextStore = store.commit writtenKey written := by
        by_cases hp : pid = Concrete.Pid.store
        · subst pid
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
          · exact .inl rfl
          · exact .inr ⟨writtenKey, written, rfl⟩
        · have heq : store = nextStore := by
            have hx : world.process .store = .store nextStore := by
              simpa [World.land, Ne.symm hp] using hnextStore
            rw [hstore] at hx
            exact Concrete.Local.store.inj hx
          exact .inl heq.symm
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, hsnapshot, horigin, hagreement,
          heligible⟩ :=
          hinvariant hstore hold
        refine ⟨provenance, ?_,
          horigin.mono fun message hmessage =>
            List.mem_append_left _ hmessage, ?_, ?_⟩
        rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
        · exact hsnapshot
        · exact Snapshot.commit hsnapshot
        · intro node flight hnode hflight hphase
          by_cases hp : pid = .node address
          · subst pid
            obtain ⟨before, hbefore, _⟩ :=
              reachable_nodes_valid hreachable address hprocess
            have hstate : result.state = .node node := by
              simpa [World.land] using hnode
            have hop :=
              (reachable_rpc_ids hreachable).fresh hprocess hbefore hold
            exact hagreement before flight hbefore
              (node_step_old_flight (hbefore ▸ hresult) hstate hop hflight)
              hphase
          · exact hagreement node flight
              (by simpa [World.land, Ne.symm hp] using hnode)
              hflight hphase
        · intro hmatch
          have hmatchOld :
              expectedVersion = store.version key := by
            rcases heffect with rfl | ⟨writtenKey, written, rfl⟩
            · exact hmatch
            · by_cases hk : writtenKey = key
              · subst writtenKey
                have hbad :
                    provenance.loaded.map (·.2) =
                      (store.commit key written).version key :=
                  provenance.expected_eq.trans hmatch
                exact
                  (Snapshot.expected_ne_commit_version hsnapshot hbad).elim
              · have hv :
                    (store.commit writtenKey written).version key =
                      store.version key := by
                  simpa [Concrete.Store.version_eq_read, Ne.symm hk] using
                    Concrete.Store.read_commit_other store writtenKey key
                      written (Ne.symm hk)
                exact hmatch.trans hv
          obtain ⟨before, active, hbefore, hactive, hphase, hnoreply⟩ :=
            heligible hmatchOld
          have hnoRepliesNext :
              ∀ reply,
                (reply = StoreReply.written ∨
                  reply = .conflict ∨ reply = .failed) →
                (Concrete.Pid.store, .node address,
                  .storeReply { op, payload := reply }) ∉
                    (world.land pid now result).network := by
            intro reply hreply hreplyMem
            simp only [World.land, List.mem_append] at hreplyMem
            rcases hreplyMem with holdReply | newReply
            · exact hnoreply reply hreply holdReply
            · obtain ⟨sent, hsentReply, heq⟩ :=
                List.mem_map.mp newReply
              obtain ⟨target, message⟩ := sent
              simp only [Prod.mk.injEq] at heq
              have hpid : pid = .store := heq.1
              subst pid
              cases heq.2.1
              cases heq.2.2
              obtain ⟨replyKey, replyDocument, replyExpected, hevent⟩ :=
                sent_put_reply_origin hreply (hstore ▸ hresult)
                  hsentReply
              subst event
              have hrequest :
                  (Concrete.Pid.node address, .store,
                    .storeRequest {
                      op
                      payload := .put replyKey replyDocument replyExpected
                    }) ∈ world.network := hvalid
              have hpayload :=
                (reachable_rpc_ids hreachable).unique hold hrequest
              cases hpayload
              have hresult' := hresult
              rw [hstore] at hresult'
              simp only [Concrete.step, Concrete.storePut] at hresult'
              split at hresult'
              · simp [Outcomes.one] at hresult'
                subst result
                have hsame : store = nextStore := by
                  simpa [World.land] using hnextStore
                subst nextStore
                rename_i hmismatch
                simp only [Bool.and_eq_true, bne_iff_ne] at hmismatch
                exact hmismatch.2 hmatch
              · split at hresult'
                · simp at hresult'
                  rcases hresult' with hresult' | hresult' | hresult'
                  · subst result
                    have hsame :
                        store.commit key document = nextStore := by
                      simpa [World.land] using hnextStore
                    subst nextStore
                    exact (Snapshot.expected_ne_commit_version hsnapshot
                      (provenance.expected_eq.trans hmatch)).elim
                  · subst result
                    have hsame :
                        store.commit key document = nextStore := by
                      simpa [World.land] using hnextStore
                    subst nextStore
                    exact (Snapshot.expected_ne_commit_version hsnapshot
                      (provenance.expected_eq.trans hmatch)).elim
                  · subst result
                    have hsame :
                        store.fence key = nextStore := by
                      simpa [World.land] using hnextStore
                    subst nextStore
                    exact (Snapshot.expected_ne_commit_version
                      (document := store.toAbstract.read key) hsnapshot
                      (provenance.expected_eq.trans hmatch)).elim
                · simp [Outcomes.one] at hresult'
                  subst result
                  have hsame :
                      store.commit key document = nextStore := by
                    simpa [World.land] using hnextStore
                  subst nextStore
                  exact (Snapshot.expected_ne_commit_version hsnapshot
                    (provenance.expected_eq.trans hmatch)).elim
          by_cases hp : pid = .node address
          · subst pid
            have hnotReply
                (payload : Concrete.StoreReply) :
                event ≠ .receive .store
                  (.storeReply { op, payload }) := by
              intro hevent
              subst event
              have hreplyMem := hvalid
              cases payload with
              | got loadedKey loaded =>
                  have hget :=
                    reachable_got_replies_have_request hreachable hreplyMem
                  have heq :=
                    (reachable_rpc_ids hreachable).unique hold hget
                  contradiction
              | written =>
                  exact hnoreply .written (.inl rfl) hreplyMem
              | conflict =>
                  exact hnoreply .conflict (.inr (.inl rfl)) hreplyMem
              | failed =>
                  exact hnoreply .failed (.inr (.inr rfl)) hreplyMem
            obtain ⟨after, hafterState, hafterFlight⟩ :=
              node_step_preserves_writing_flight hactive hphase
                hnotReply (hbefore ▸ hresult)
            refine ⟨after, active,
              by simp [World.land, hafterState],
              hafterFlight, hphase, hnoRepliesNext⟩
          · refine ⟨before, active,
              by simp [World.land, Ne.symm hp, hbefore],
              hactive, hphase, hnoRepliesNext⟩
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨node, hnodeState, hnodeValid⟩ :=
          reachable_nodes_valid hreachable address hprocess
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable address hprocess
        rw [hnodeState] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        obtain ⟨provenance, hsnapshot, horigin, hagreement,
            hactiveNew⟩ :=
          node_step_sent_put_stageable hprocess hnodeState hstore
            hnodeValid hserial (reachable_got_snapshots hreachable)
            (reachable_flight_request_origins hreachable)
            hvalid (hnodeState ▸ hresult) hsent
        have hsame : nextStore = store := by
          have hx : store = nextStore := by
            simpa [World.land, hstore] using hnextStore
          exact hx.symm
        subst nextStore
        refine ⟨provenance, hsnapshot,
          horigin.mono fun message hmessage =>
            List.mem_append_left _ hmessage, ?_, ?_⟩
        intro nextNode flight hnodeNext hflight hphase
        have hstate : result.state = .node nextNode := by
          simpa [World.land] using hnodeNext
        exact hagreement nextNode flight hstate hflight hphase
        · intro hmatch
          obtain ⟨nextNode, flight, hstate, hflight, hphase⟩ :=
            hactiveNew
          refine ⟨nextNode, flight,
            by simpa [World.land] using hstate,
            hflight, hphase, ?_⟩
          intro reply hreply hmem
          simp only [World.land, List.mem_append] at hmem
          rcases hmem with hold | hnew
          · obtain ⟨replyKey, replyDocument, replyExpected, hput⟩ :=
              reachable_put_replies_have_request hreachable hreply hold
            have holdFresh :=
              (reachable_rpc_ids hreachable).fresh hprocess hnodeState hput
            have hnewOp :=
              (node_step_ids (hnodeState ▸ hresult)).choose_spec.2.2.1
                _ _ hsent |>.1
            exact (Nat.ne_of_lt holdFresh hnewOp).elim
          · obtain ⟨sent, hsentReply, heq⟩ := List.mem_map.mp hnew
            obtain ⟨target, message⟩ := sent
            simp only [Prod.mk.injEq] at heq
            obtain ⟨_, htarget, hmessage⟩ := heq
            cases htarget
            cases hmessage
            exact (node_step_no_store_reply
              (hnodeState ▸ hresult) hsentReply).elim

theorem reachable_stageable_puts
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    StageablePuts world := by
  induction hreachable with
  | init hinit => exact stageablePuts_initial _
  | step hreachable hstep ih =>
      exact stageablePuts_step hreachable ih hstep

def Covered (abstract : World AModel) (outputs : List Output) : Prop :=
  ∀ output ∈ outputs,
    (Abstract.Pid.service, .outside, Message.output output) ∈
      abstract.network

theorem Covered.mono {abstract next : World AModel}
    {outputs : List Output} (hcovered : Covered abstract outputs)
    (hnetwork : ∀ message ∈ abstract.network, message ∈ next.network) :
    Covered next outputs := by
  intro output houtput
  exact hnetwork _ (hcovered output houtput)

theorem Covered.land {abstract : World AModel} {outputs : List Output}
    (hcovered : Covered abstract outputs) {now : Time}
    (result : Result Abstract.Pid State Message) :
    Covered (abstract.land .service now result) outputs :=
  hcovered.mono fun message hmessage =>
    List.mem_append_left _ hmessage

theorem covered_sent
    (abstract : World AModel) (now : Time) (state : State)
    (outputs : List Output) :
    Covered
      (abstract.land .service now {
        state
        send := Abstract.sends outputs
      }) outputs := by
  intro output houtput
  simp only [World.land, Abstract.sends, List.mem_append, List.mem_map]
  right
  exact ⟨(.outside, Message.output output),
    ⟨output, houtput, rfl⟩, rfl⟩

def FlightWorkflowStage (flight : Concrete.Flight)
    (nodePending abstractPending : List WorkflowEntry) : Prop :=
  match flight.transaction with
  | .external _ => abstractPending = nodePending
  | .work item instant rest =>
      match flight.phase with
      | .loading => abstractPending = .work item instant :: rest
      | .writing =>
          abstractPending = .work item instant :: rest ∨
          abstractPending = flight.continuations
  | .scan key instant rest =>
      match flight.phase with
      | .loading => abstractPending = .scan key instant :: rest
      | .writing =>
          abstractPending = .scan key instant :: rest ∨
          abstractPending = flight.continuations

def TransactionPending : Concrete.Transaction → Option (List WorkflowEntry)
  | .external _ => none
  | .work item instant rest => some (.work item instant :: rest)
  | .scan key instant rest => some (.scan key instant :: rest)

def WorkflowAligned
    {nodes : List Addr} {appConfig : Resonate.Config}
    (config : Concrete.Config)
    (concrete : World (CModel nodes appConfig))
    (abstract : World AModel) : Prop :=
  if config.workflowNode ∈ nodes then
    ∃ node,
      concrete.process (.node config.workflowNode) = .node node ∧
      (node.workflowBlocked = true ∨
       (node.flights = [] ∧
          (abstract.process .service).workflow.pending = node.pending) ∨
       ∃ op flight,
         (op, flight) ∈ node.flights ∧
         FlightWorkflowStage flight node.pending
           (abstract.process .service).workflow.pending)
  else
    (abstract.process .service).workflow.pending = []

/-- The ghost invariant needed by the one-step proof. It covers raw request
provenance, outstanding local continuations, store replies, and every concrete
boundary output that may be observed later or repeatedly from Rover's
append-only network. -/
structure Related (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config)
    (concrete : World (CModel nodes appConfig))
    (abstract : World AModel) : Prop where
  time : abstract.now ≤ concrete.now
  store :
    ∃ physical : Concrete.Store,
      concrete.process .store = .store physical ∧
      StoreRep physical (abstract.process .service)
  requests :
    ∀ address call,
      (Concrete.Pid.outside, .node address, .request call) ∈
          concrete.network →
      (Abstract.Pid.outside, .service, Message.request call) ∈
          abstract.network
  outputs :
    ∀ address output,
      (Concrete.Pid.node address, .outside, .output output) ∈
          concrete.network →
      (Abstract.Pid.service, .outside, Message.output output) ∈
          abstract.network
  puts :
    ∀ address op key document expectedVersion,
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network →
      ValidPut appConfig key document expectedVersion
  gotSnapshots : GotSnapshots concrete
  ownedPutSnapshots : OwnedPutSnapshots concrete
  putReplyOrigins : PutRepliesHaveRequest concrete
  known :
    ∀ address node key,
      address ∈ nodes →
      concrete.process (.node address) = .node node →
      key ∈ node.known →
      key ∈ (abstract.process .service).store.keys
  workflow : WorkflowAligned config concrete abstract
  currentWorkflow :
    ∀ physical address node op flight pending,
      address ∈ nodes →
      concrete.process .store = .store physical →
      concrete.process (.node address) = .node node →
      (op, flight) ∈ node.flights →
      flight.phase = .writing →
      flight.loaded.map (·.2) = physical.version flight.key →
      TransactionPending flight.transaction = some pending →
      address = config.workflowNode ∧
        (abstract.process .service).workflow.pending = pending
  acknowledged :
    ∀ address op,
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .written }) ∈ concrete.network →
      ∃ key document expectedVersion,
        ∃ provenance :
            PutProvenance appConfig key document expectedVersion,
        (Concrete.Pid.node address, .store,
          .storeRequest {
            op
            payload := .put key document expectedVersion
          }) ∈ concrete.network ∧
        key ∈ (abstract.process .service).store.keys ∧
        Covered abstract provenance.outputs
  failedCovered :
    ∀ address op,
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .failed }) ∈ concrete.network →
      ∃ key document expectedVersion,
        ∃ provenance :
            PutProvenance appConfig key document expectedVersion,
        (Concrete.Pid.node address, .store,
          .storeRequest {
            op
            payload := .put key document expectedVersion
          }) ∈ concrete.network ∧
        Covered abstract
          (Concrete.failureOutputs provenance.transaction)
  activeReplies :
    ∀ address node op flight,
      address ∈ nodes →
      concrete.process (.node address) = .node node →
      (op, flight) ∈ node.flights →
      ((Concrete.Pid.store, .node address,
          .storeReply { op, payload := .written }) ∈ concrete.network →
        flight.key ∈ (abstract.process .service).store.keys ∧
          Covered abstract flight.selected ∧
          (TransactionPending flight.transaction = none ∨
            (abstract.process .service).workflow.pending =
              flight.continuations)) ∧
      ((Concrete.Pid.store, .node address,
          .storeReply { op, payload := .failed }) ∈ concrete.network →
        Covered abstract
          (Concrete.failureOutputs flight.transaction))
  flights :
    ∀ address node op flight,
      address ∈ nodes →
      concrete.process (.node address) = .node node →
      (op, flight) ∈ node.flights →
      FlightValid appConfig flight
  gotReplies :
    ∀ address op key loaded,
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .got key loaded }) ∈
          concrete.network →
      ∃ requestOp,
        requestOp = op ∧
        (Concrete.Pid.node address, .store,
          .storeRequest { op := requestOp, payload := .get key }) ∈
            concrete.network
  putReplies :
    ∀ address op reply,
      reply = StoreReply.written ∨
        reply = .conflict ∨ reply = .failed →
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := reply }) ∈ concrete.network →
      ∃ key document expectedVersion,
        (Concrete.Pid.node address, .store,
          .storeRequest {
            op
            payload := .put key document expectedVersion
          }) ∈ concrete.network ∧
        ValidPut appConfig key document expectedVersion

theorem related_after_inject
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    {address : Addr} (haddress : address ∈ nodes)
    (call : Call) {now : Time} (htime : concrete.now ≤ now) :
    Related nodes appConfig config
      (concrete.inject (.node address) (.request call) now)
      (abstract.inject .service (.request call) now) := by
  let cnext := concrete.inject (.node address) (.request call) now
  let anext := abstract.inject .service (.request call) now
  have hstep : Step (CModel nodes appConfig) config concrete
      (.input (.node address) now (.request call)) cnext :=
    Step.inject htime haddress ⟨call, rfl⟩
  have hreach := Reachable.step hreachable hstep
  refine {
    time := Nat.le_refl now
    store := ?_
    requests := ?_
    outputs := ?_
    puts := by
      intro target op key document expected hput
      exact reachable_raw_put_valid hreach hput
    gotSnapshots := reachable_got_snapshots hreach
    ownedPutSnapshots := reachable_owned_put_snapshots hreach
    putReplyOrigins := reachable_put_replies_have_request hreach
    known := ?_
    workflow := ?_
    currentWorkflow := ?_
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := ?_
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
  }
  · simpa [cnext, anext, World.inject] using related.store
  · intro target knownCall hmem
    simp only [cnext, World.inject, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with hold | hnew
    · exact List.mem_append_left _ (related.requests target knownCall hold)
    · simp only [Prod.mk.injEq] at hnew
      obtain ⟨_, _, hcall⟩ := hnew
      cases Concrete.Msg.request.inj hcall
      exact List.mem_append_right _ (by
        simp [anext, World.inject])
  · intro target output hmem
    simp only [cnext, World.inject, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with hold | hnew
    · exact List.mem_append_left _ (related.outputs target output hold)
    · simp at hnew
  · intro target node key htarget hnode hkey
    exact related.known target node key htarget
      (by simpa [cnext, World.inject] using hnode) hkey
  · simpa [WorkflowAligned, cnext, anext, World.inject] using related.workflow
  · intro physical target node op flight pending htarget hstore hnode
      hmem hphase hversion hpending
    exact related.currentWorkflow physical target node op flight pending
      htarget (by simpa [cnext, World.inject] using hstore)
      (by simpa [cnext, World.inject] using hnode) hmem hphase hversion
      hpending
  · intro target op hmem
    obtain ⟨key, document, expected, provenance, hput, hkey, hcover⟩ :=
      related.acknowledged target op
        (by simpa [cnext, World.inject] using hmem)
    exact ⟨key, document, expected, provenance,
      by simpa [cnext, World.inject] using hput,
      by simpa [anext, World.inject] using hkey,
      hcover.mono fun message hmessage =>
        List.mem_append_left _ hmessage⟩
  · intro target op hmem
    obtain ⟨key, document, expected, provenance, hput, hcover⟩ :=
      related.failedCovered target op
        (by simpa [cnext, World.inject] using hmem)
    exact ⟨key, document, expected, provenance,
      by simpa [cnext, World.inject] using hput,
      hcover.mono fun message hmessage =>
        List.mem_append_left _ hmessage⟩
  · intro target node op flight htarget hnode hflight
    have hnodeOld :
        concrete.process (.node target) = .node node := by
      simpa [cnext, World.inject] using hnode
    obtain ⟨hwritten, hfailed⟩ :=
      related.activeReplies target node op flight htarget hnodeOld hflight
    constructor
    · intro hreply
      obtain ⟨hkey, hcover, hworkflow⟩ := hwritten
        (by simpa [cnext, World.inject] using hreply)
      exact ⟨by simpa [anext, World.inject] using hkey,
        hcover.mono fun message hmessage =>
          List.mem_append_left _ hmessage,
        by simpa [anext, World.inject] using hworkflow⟩
    · intro hreply
      exact (hfailed (by simpa [cnext, World.inject] using hreply)).mono
        fun message hmessage => List.mem_append_left _ hmessage
  · intro target node op flight htarget hnode hmem
    obtain ⟨actual, hactual, hvalid⟩ :=
      reachable_nodes_valid hreach target htarget
    rw [hnode] at hactual
    cases Concrete.Local.node.inj hactual
    exact hvalid op flight hmem
  · intro target op key loaded hmem
    exact ⟨op, rfl, reachable_got_replies_have_request hreach hmem⟩
  · intro target op reply hreply hmem
    obtain ⟨key, document, expected, hput⟩ :=
      reachable_put_replies_have_request hreach hreply hmem
    exact ⟨key, document, expected, hput,
      reachable_raw_put_valid hreach hput⟩

theorem related_after_store_inject
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (call : Call) {now : Time} (htime : concrete.now ≤ now) :
    Related nodes appConfig config
      (concrete.inject .store (.request call) now)
      (abstract.inject .service (.request call) now) := by
  let cnext := concrete.inject .store (.request call) now
  let anext := abstract.inject .service (.request call) now
  have hstep : Step (CModel nodes appConfig) config concrete
      (.input .store now (.request call)) cnext :=
    Step.inject htime (by simp) ⟨call, rfl⟩
  have hreach := Reachable.step hreachable hstep
  refine {
    time := Nat.le_refl now
    store := by simpa [cnext, anext, World.inject] using related.store
    requests := ?_
    outputs := ?_
    puts := by
      intro address op key document expected hput
      exact reachable_raw_put_valid hreach hput
    gotSnapshots := reachable_got_snapshots hreach
    ownedPutSnapshots := reachable_owned_put_snapshots hreach
    putReplyOrigins := reachable_put_replies_have_request hreach
    known := ?_
    workflow := ?_
    currentWorkflow := ?_
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := ?_
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
  }
  · intro address knownCall hmem
    simp only [cnext, World.inject, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with hold | hnew
    · exact List.mem_append_left _
        (related.requests address knownCall hold)
    · simp at hnew
  · intro address output hmem
    simp only [cnext, World.inject, List.mem_append,
      List.mem_singleton] at hmem
    rcases hmem with hold | hnew
    · exact List.mem_append_left _
        (related.outputs address output hold)
    · simp at hnew
  · intro address node key haddress hnode hkey
    exact related.known address node key haddress
      (by simpa [cnext, World.inject] using hnode) hkey
  · simpa [WorkflowAligned, cnext, anext, World.inject] using
      related.workflow
  · intro physical address node op flight pending haddress hstore hnode
      hmem hphase hversion hpending
    exact related.currentWorkflow physical address node op flight pending
      haddress (by simpa [cnext, World.inject] using hstore)
      (by simpa [cnext, World.inject] using hnode) hmem hphase hversion
      hpending
  · intro address op hmem
    obtain ⟨key, document, expected, provenance, hput, hkey, hcover⟩ :=
      related.acknowledged address op
        (by simpa [cnext, World.inject] using hmem)
    exact ⟨key, document, expected, provenance,
      by simpa [cnext, World.inject] using hput,
      by simpa [anext, World.inject] using hkey,
      hcover.mono fun message hmessage =>
        List.mem_append_left _ hmessage⟩
  · intro address op hmem
    obtain ⟨key, document, expected, provenance, hput, hcover⟩ :=
      related.failedCovered address op
        (by simpa [cnext, World.inject] using hmem)
    exact ⟨key, document, expected, provenance,
      by simpa [cnext, World.inject] using hput,
      hcover.mono fun message hmessage =>
        List.mem_append_left _ hmessage⟩
  · intro address node op flight haddress hnode hflight
    have hnodeOld :
        concrete.process (.node address) = .node node := by
      simpa [cnext, World.inject] using hnode
    obtain ⟨hwritten, hfailed⟩ :=
      related.activeReplies address node op flight haddress hnodeOld hflight
    constructor
    · intro hreply
      obtain ⟨hkey, hcover, hworkflow⟩ := hwritten
        (by simpa [cnext, World.inject] using hreply)
      exact ⟨by simpa [anext, World.inject] using hkey,
        hcover.mono fun message hmessage =>
          List.mem_append_left _ hmessage,
        by simpa [anext, World.inject] using hworkflow⟩
    · intro hreply
      exact (hfailed
        (by simpa [cnext, World.inject] using hreply)).mono
          fun message hmessage => List.mem_append_left _ hmessage
  · intro address node op flight haddress hnode hmem
    obtain ⟨actual, hactual, hvalid⟩ :=
      reachable_nodes_valid hreach address haddress
    rw [hnode] at hactual
    cases Concrete.Local.node.inj hactual
    exact hvalid op flight hmem
  · intro address op key loaded hmem
    exact ⟨op, rfl, reachable_got_replies_have_request hreach hmem⟩
  · intro address op reply hreply hmem
    obtain ⟨key, document, expected, hput⟩ :=
      reachable_put_replies_have_request hreach hreply hmem
    exact ⟨key, document, expected, hput,
      reachable_raw_put_valid hreach hput⟩

theorem related_after_observe
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    {now : Time} :
    Related nodes appConfig config
      (concrete.observeOutside now) (abstract.observeOutside now) := by
  refine {
    time := Nat.le_refl now
    store := related.store
    requests := related.requests
    outputs := related.outputs
    puts := related.puts
    gotSnapshots := related.gotSnapshots
    ownedPutSnapshots := related.ownedPutSnapshots
    putReplyOrigins := related.putReplyOrigins
    known := related.known
    workflow := related.workflow
    currentWorkflow := related.currentWorkflow
    acknowledged := related.acknowledged
    failedCovered := related.failedCovered
    activeReplies := related.activeReplies
    flights := related.flights
    gotReplies := related.gotReplies
    putReplies := related.putReplies
  }

theorem related_after_concrete_observe
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    {now : Time} (htime : concrete.now ≤ now) :
    Related nodes appConfig config
      (concrete.observeOutside now) abstract := by
  refine {
    time := Nat.le_trans related.time htime
    store := related.store
    requests := related.requests
    outputs := related.outputs
    puts := related.puts
    gotSnapshots := related.gotSnapshots
    ownedPutSnapshots := related.ownedPutSnapshots
    putReplyOrigins := related.putReplyOrigins
    known := related.known
    workflow := related.workflow
    currentWorkflow := related.currentWorkflow
    acknowledged := related.acknowledged
    failedCovered := related.failedCovered
    activeReplies := related.activeReplies
    flights := related.flights
    gotReplies := related.gotReplies
    putReplies := related.putReplies
  }

theorem reachable_output_sender
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {sender : Concrete.Pid} {output : Output}
    (houtput :
      (sender, Concrete.Pid.outside, Concrete.Msg.output output) ∈
        world.network) :
    ∃ address, sender = .node address := by
  induction hreachable with
  | init hinit => contradiction
  | @step previous label next hprevious hstep ih =>
      cases hstep with
      | inject htime hprocess hinject =>
          obtain ⟨call, rfl⟩ := hinject
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at houtput
          rcases houtput with hold | hnew
          · exact ih hold
          · simp at hnew
      | outside =>
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
            | node address => exact ⟨address, rfl⟩
            | store =>
                obtain ⟨store, hstore⟩ :=
                  reachable_store_exists hprevious
                have hresult' := hresult
                rw [hstore] at hresult'
                have hresult0 :
                    result ∈
                      (Concrete.step appConfig config .store (.store store)
                        now event).val := hresult'
                cases event with
                | timeout =>
                    simp [Concrete.step, Outcomes.one] at hresult0
                    subst result
                    contradiction
                | receive process message =>
                    cases message <;>
                      simp only [Concrete.step] at hresult0
                    all_goals
                      try
                        simp [Outcomes.one] at hresult0
                        subst result
                        contradiction
                    case storeRequest rpc =>
                      obtain ⟨op, payload⟩ := rpc
                      cases payload with
                      | get key =>
                          simp [Outcomes.one] at hresult0
                          subst result
                          contradiction
                      | put key document expected =>
                          simp only [Concrete.storePut] at hresult0
                          split at hresult0
                          · simp [Outcomes.one] at hresult0
                            subst result
                            contradiction
                          · split at hresult0
                            · simp at hresult0
                              rcases hresult0 with hresult0 | hresult0 | hresult0
                              all_goals subst result
                              all_goals contradiction
                            · simp [Outcomes.one] at hresult0
                              subst result
                              contradiction

theorem reachable_node_sender
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} {recipient : Concrete.Pid} {message : Concrete.Msg}
    (hmessage : (Concrete.Pid.node address, recipient, message) ∈
      world.network) :
    address ∈ nodes := by
  induction hreachable with
  | init hinit => contradiction
  | @step previous label next hprevious hstep ih =>
      cases hstep with
      | inject =>
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at hmessage
          rcases hmessage with hold | hnew
          · exact ih hold
          · simp at hnew
      | outside =>
          exact ih hmessage
      | @process pid now event result htime hprocess hvalid hresult =>
          simp only [World.land, List.mem_append] at hmessage
          rcases hmessage with hold | hnew
          · exact ih hold
          · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
            obtain ⟨target, sentMessage⟩ := sent
            simp only [Prod.mk.injEq] at heq
            have hpid : pid = .node address := heq.1
            subst pid
            exact hprocess

theorem reachable_store_request_sender
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {sender : Concrete.Pid} {rpc : Concrete.RpcRequest}
    (hmessage :
      (sender, Concrete.Pid.store, Concrete.Msg.storeRequest rpc) ∈
        world.network) :
    ∃ address, sender = .node address := by
  induction hreachable with
  | init hinit => contradiction
  | @step previous label next hprevious hstep ih =>
      cases hstep with
      | inject htime hprocess hinject =>
          obtain ⟨call, rfl⟩ := hinject
          simp only [World.inject, List.mem_append,
            List.mem_singleton] at hmessage
          rcases hmessage with hold | hnew
          · exact ih hold
          · simp at hnew
      | outside =>
          exact ih hmessage
      | @process pid now event result htime hprocess hvalid hresult =>
          simp only [World.land, List.mem_append] at hmessage
          rcases hmessage with hold | hnew
          · exact ih hold
          · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
            obtain ⟨recipient, message⟩ := sent
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl, rfl⟩ := heq
            cases pid with
            | outside => contradiction
            | node address => exact ⟨address, rfl⟩
            | store =>
                obtain ⟨store, hstore⟩ :=
                  reachable_store_exists hprevious
                have hresult' := hresult
                rw [hstore] at hresult'
                cases event with
                | timeout =>
                    simp [Concrete.step, Outcomes.one] at hresult'
                    subst result
                    contradiction
                | receive process message =>
                    cases message <;>
                      simp only [Concrete.step] at hresult'
                    all_goals
                      try
                        simp [Outcomes.one] at hresult'
                        subst result
                        contradiction
                    case storeRequest rpc =>
                      obtain ⟨op, payload⟩ := rpc
                      cases payload with
                      | get key =>
                          simp [Outcomes.one] at hresult'
                          subst result
                          contradiction
                      | put key document expected =>
                          simp only [Concrete.storePut] at hresult'
                          split at hresult'
                          · simp [Outcomes.one] at hresult'
                            subst result
                            contradiction
                          · split at hresult'
                            · simp at hresult'
                              rcases hresult' with hresult' | hresult' | hresult'
                              all_goals subst result
                              all_goals contradiction
                            · simp [Outcomes.one] at hresult'
                              subst result
                              contradiction

theorem related_after_land
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract abstractNext : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    {pid : Concrete.Pid} {now : Time}
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hprocess : (CModel nodes appConfig).isProcess pid)
    (hstep :
      Step (CModel nodes appConfig) config concrete
        (.process pid now event result.send)
        (concrete.land pid now result))
    (htime : abstractNext.now ≤ now)
    (hnetwork :
      ∀ message ∈ abstract.network, message ∈ abstractNext.network)
    (hkeys :
      ∀ key ∈ (abstract.process .service).store.keys,
        key ∈ (abstractNext.process .service).store.keys)
    (hstore :
      ∃ physical,
        (concrete.land pid now result).process .store = .store physical ∧
        StoreRep physical (abstractNext.process .service))
    (hworkflow :
      WorkflowAligned config (concrete.land pid now result) abstractNext)
    (hcurrent :
      ∀ physical address node op flight pending,
        address ∈ nodes →
        (concrete.land pid now result).process .store = .store physical →
        (concrete.land pid now result).process (.node address) = .node node →
        (op, flight) ∈ node.flights →
        flight.phase = .writing →
        flight.loaded.map (·.2) = physical.version flight.key →
        TransactionPending flight.transaction = some pending →
        address = config.workflowNode ∧
          (abstractNext.process .service).workflow.pending = pending)
    (hknown :
      ∀ address node key,
        address ∈ nodes →
        (concrete.land pid now result).process (.node address) =
          .node node →
        key ∈ node.known →
        key ∈ (abstractNext.process .service).store.keys)
    (hnewRequest :
      ∀ {address call},
        (.node address, Concrete.Msg.request call) ∈ result.send →
        (Abstract.Pid.outside, .service, Message.request call) ∈
          abstractNext.network)
    (hnewOutput :
      ∀ {output},
        (.outside, Concrete.Msg.output output) ∈ result.send →
        (Abstract.Pid.service, .outside, Message.output output) ∈
          abstractNext.network)
    (hnewAck :
      ∀ {address op},
        (.node address,
          Concrete.Msg.storeReply { op, payload := .written }) ∈ result.send →
        ∃ key document expectedVersion,
          ∃ provenance :
              PutProvenance appConfig key document expectedVersion,
          (Concrete.Pid.node address, .store,
            .storeRequest {
              op
              payload := .put key document expectedVersion
            }) ∈ (concrete.land pid now result).network ∧
          key ∈ (abstractNext.process .service).store.keys ∧
          Covered abstractNext provenance.outputs)
    (hnewFailed :
      ∀ {address op},
        (.node address,
          Concrete.Msg.storeReply { op, payload := .failed }) ∈ result.send →
        ∃ key document expectedVersion,
          ∃ provenance :
              PutProvenance appConfig key document expectedVersion,
          (Concrete.Pid.node address, .store,
            .storeRequest {
              op
              payload := .put key document expectedVersion
            }) ∈ (concrete.land pid now result).network ∧
          Covered abstractNext
            (Concrete.failureOutputs provenance.transaction))
    (hactive :
      ∀ address node op flight,
        address ∈ nodes →
        (concrete.land pid now result).process (.node address) =
          .node node →
        (op, flight) ∈ node.flights →
        ((Concrete.Pid.store, .node address,
            .storeReply { op, payload := .written }) ∈
              (concrete.land pid now result).network →
          flight.key ∈ (abstractNext.process .service).store.keys ∧
            Covered abstractNext flight.selected ∧
            (TransactionPending flight.transaction = none ∨
              (abstractNext.process .service).workflow.pending =
                flight.continuations)) ∧
        ((Concrete.Pid.store, .node address,
            .storeReply { op, payload := .failed }) ∈
              (concrete.land pid now result).network →
          Covered abstractNext
            (Concrete.failureOutputs flight.transaction))) :
    Related nodes appConfig config (concrete.land pid now result)
      abstractNext := by
  have hreach := Reachable.step hreachable hstep
  refine {
    time := htime
    store := hstore
    requests := ?_
    outputs := ?_
    puts := by
      intro address op key document expected hput
      exact reachable_raw_put_valid hreach hput
    gotSnapshots := reachable_got_snapshots hreach
    ownedPutSnapshots := reachable_owned_put_snapshots hreach
    putReplyOrigins := reachable_put_replies_have_request hreach
    known := hknown
    workflow := hworkflow
    currentWorkflow := hcurrent
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := hactive
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
  }
  · intro address call hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · exact hnetwork _ (related.requests address call hold)
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hnewRequest hsent
  · intro address output hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · exact hnetwork _ (related.outputs address output hold)
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hnewOutput hsent
  · intro address op hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · obtain ⟨key, document, expected, provenance, hput, hkey, hcover⟩ :=
        related.acknowledged address op hold
      exact ⟨key, document, expected, provenance,
        List.mem_append_left _ hput, hkeys key hkey,
        hcover.mono hnetwork⟩
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hnewAck hsent
  · intro address op hmem
    simp only [World.land, List.mem_append] at hmem
    rcases hmem with hold | hnew
    · obtain ⟨key, document, expected, provenance, hput, hcover⟩ :=
        related.failedCovered address op hold
      exact ⟨key, document, expected, provenance,
        List.mem_append_left _ hput, hcover.mono hnetwork⟩
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact hnewFailed hsent
  · intro address node op flight haddress hnode hmem
    obtain ⟨actual, hactual, hvalid⟩ :=
      reachable_nodes_valid hreach address haddress
    rw [hnode] at hactual
    cases Concrete.Local.node.inj hactual
    exact hvalid op flight hmem
  · intro address op key loaded hmem
    exact ⟨op, rfl, reachable_got_replies_have_request hreach hmem⟩
  · intro address op reply hreply hmem
    obtain ⟨key, document, expected, hput⟩ :=
      reachable_put_replies_have_request hreach hreply hmem
    exact ⟨key, document, expected, hput,
      reachable_raw_put_valid hreach hput⟩

theorem simulate_inject
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {now : Time} (htime : concrete.now ≤ now) (call : Call) :
    let concreteNext :=
      concrete.inject (.node address) (.request call) now
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config concreteNext
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution =
        concreteObservation (nodes := nodes) (appConfig := appConfig)
          (.input (.node address) now (.request call)) := by
  let abstractNext :=
    abstract.inject .service (.request call) now
  let abstractLabel : Label AModel :=
    .input .service now (.request call)
  refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, rfl⟩
  · exact ⟨Step.inject (Nat.le_trans related.time htime) rfl
      ⟨call, rfl⟩, trivial⟩
  · simpa [endOf] using
      related_after_inject related hreachable haddress call htime

theorem simulate_outside
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {sender : Concrete.Pid} {now : Time} {message : Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hmessage : (sender, .outside, message) ∈ concrete.network) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config (concrete.observeOutside now)
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution =
        concreteObservation (nodes := nodes) (appConfig := appConfig)
          (.outside sender now message) := by
  cases message with
  | output output =>
      obtain ⟨address, rfl⟩ :=
        reachable_output_sender hreachable hmessage
      have habstractMessage := related.outputs address output hmessage
      let abstractNext := abstract.observeOutside now
      let abstractLabel : Label AModel :=
        .outside .service now (.output output)
      refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, ?_⟩
      · exact ⟨Step.outside
          (Nat.le_trans related.time htime) habstractMessage, trivial⟩
      · simpa [endOf, abstractNext] using
          (related_after_observe related :
            Related nodes appConfig config
              (concrete.observeOutside now)
              (abstract.observeOutside now))
      · cases output <;> rfl
  | request call
  | storeRequest rpc
  | storeReply rpc =>
      exact ⟨[], trivial,
        related_after_concrete_observe related htime, rfl⟩

theorem related_after_inert_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {physical : Concrete.Store} {now : Time}
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hphysical : concrete.process .store = .store physical)
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete .store)
    (hresult :
      result ∈
        (Concrete.step appConfig config .store (.store physical)
          now event).val)
    (hstate : result.state = .store physical)
    (hreplies :
      ∀ target message, (target, message) ∈ result.send →
        ∃ reply, message = Concrete.Msg.storeReply reply)
    (hnoWritten :
      ∀ address op,
        (.node address,
          Concrete.Msg.storeReply { op, payload := .written }) ∉ result.send)
    (hnoFailed :
      ∀ address op,
        (.node address,
          Concrete.Msg.storeReply { op, payload := .failed }) ∉ result.send) :
    Related nodes appConfig config
      (concrete.land .store now result) abstract := by
  have hstep :
      Step (CModel nodes appConfig) config concrete
        (.process .store now event result.send)
        (concrete.land .store now result) :=
    Step.process htime (by simp) hvalid (hphysical ▸ hresult)
  apply related_after_land related hreachable (by simp) hstep
      (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨relatedPhysical, hrelatedPhysical, hrep⟩ := related.store
    rw [hphysical] at hrelatedPhysical
    cases Concrete.Local.store.inj hrelatedPhysical
    exact ⟨physical, by simp [World.land, hstate], hrep⟩
  · simpa [WorkflowAligned, World.land] using related.workflow
  · intro store address node op flight pending haddress hstore hnode
      hmem hphase hversion hpending
    have hstoreEq : physical = store := by
      simpa [World.land, hstate] using hstore
    subst store
    exact related.currentWorkflow physical address node op flight pending
      haddress hphysical
      (by simpa [World.land] using hnode)
      hmem hphase hversion hpending
  · intro address node key haddress hnode hkey
    exact related.known address node key haddress
      (by simpa [World.land] using hnode) hkey
  · intro address call hsend
    obtain ⟨reply, heq⟩ := hreplies _ _ hsend
    contradiction
  · intro output hsend
    obtain ⟨reply, heq⟩ := hreplies _ _ hsend
    contradiction
  · intro address op hsend
    exact (hnoWritten address op hsend).elim
  · intro address op hsend
    exact (hnoFailed address op hsend).elim
  · intro address node op flight haddress hnode hflight
    have hnodeOld :
        concrete.process (.node address) = .node node := by
      simpa [World.land] using hnode
    obtain ⟨hwritten, hfailed⟩ :=
      related.activeReplies address node op flight haddress hnodeOld hflight
    constructor
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · exact hwritten hold
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨_, htarget, hmessage⟩ := heq
        cases htarget
        cases hmessage
        exact (hnoWritten address op hsent).elim
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · exact hfailed hold
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨_, htarget, hmessage⟩ := heq
        cases htarget
        cases hmessage
        exact (hnoFailed address op hsent).elim

theorem simulate_external_written_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {physical : Concrete.Store} {address : Addr} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hphysical : concrete.process .store = .store physical)
    (hconditional : config.conditional = true)
    (hrequest :
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network)
    (provenance : PutProvenance appConfig key document expectedVersion)
    (hmatch : expectedVersion = physical.version key)
    {call : Call} (htransaction : provenance.transaction = .external call)
    (hcurrent : physical.read key = provenance.loaded)
    (horigin : TransactionOrigin concrete address provenance.transaction)
    {node : Concrete.Node} {flight : Concrete.Flight}
    (haddress : address ∈ nodes)
    (hnode : concrete.process (.node address) = .node node)
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    (hkey : key = flight.key)
    (hflightTransaction : provenance.transaction = flight.transaction)
    (houtputs : provenance.outputs = flight.selected)
    {now : Time} (htime : concrete.now ≤ now) :
    let served :=
      Resonate.run { appConfig with unreliable := true } call
        (abstract.process .service)
    let abstractResult : Result Abstract.Pid State Message := {
      state := served.1
      send := Abstract.sends served.2
    }
    let concreteResult :
        Result Concrete.Pid Concrete.Local Concrete.Msg := {
      state := .store (physical.commit key document)
      send := [(.node address,
        .storeReply { op, payload := .written })]
    }
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now concreteResult)
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  dsimp
  let served :=
    Resonate.run { appConfig with unreliable := true } call
      (abstract.process .service)
  let abstractResult : Result Abstract.Pid State Message := {
    state := served.1
    send := Abstract.sends served.2
  }
  let abstractNext := abstract.land .service now abstractResult
  let concreteResult :
      Result Concrete.Pid Concrete.Local Concrete.Msg := {
    state := .store (physical.commit key document)
    send := [(.node address,
      .storeReply { op, payload := .written })]
  }
  have habstractRequest :
      (Abstract.Pid.outside, .service, Message.request call) ∈
        abstract.network := by
    rw [htransaction] at horigin
    exact related.requests address call horigin
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now
          (.receive .outside (.request call))).val := by
    simp [Abstract.step, abstractResult, served]
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now
          (.receive .outside (.request call)) abstractResult.send)
        abstractNext :=
    Step.process (Nat.le_trans related.time htime) rfl
      habstractRequest habstractResult
  have hconcreteResult :
      concreteResult ∈
        (Concrete.step appConfig config .store (.store physical) now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            }))).val := by
    simp [Concrete.step, Concrete.storePut, concreteResult]
    simp [hconditional, hmatch]
    cases config.flaky <;> simp [Outcomes.one]
  have hconcreteStep :
      Step (CModel nodes appConfig) config concrete
        (.process .store now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            })) concreteResult.send)
        (concrete.land .store now concreteResult) :=
    Step.process htime (by simp) hrequest
      (hphysical ▸ hconcreteResult)
  refine ⟨[((.process .service now
      (.receive .outside (.request call)) abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩, ?_, rfl⟩
  have htransport :=
    external_cas_transport
      (by
        obtain ⟨represented, hrepresented, hrep⟩ := related.store
        rw [hphysical] at hrepresented
        cases Concrete.Local.store.inj hrepresented
        exact hrep)
      provenance htransaction hcurrent
  have hselectedKey :
      (Concrete.Transaction.external call).key? = some key := by
    have hvalidFlight :=
      related.flights address node op flight haddress hnode hflight
    have htx := hvalidFlight.1
    rw [← hkey] at htx
    rw [← hflightTransaction, htransaction] at htx
    exact htx
  change Related nodes appConfig config
    (concrete.land .store now concreteResult) abstractNext
  apply related_after_land related hreachable (by simp) hconcreteStep
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro knownKey hknownKey
    simpa [abstractNext, World.land, abstractResult, served] using
      external_keys_mono { appConfig with unreliable := true } call
        (abstract.process .service) knownKey hknownKey
  · exact ⟨physical.commit key document,
      by simp [World.land, concreteResult],
      by simpa [abstractNext, World.land, abstractResult, served] using
        htransport.1⟩
  · simpa [WorkflowAligned, abstractNext, World.land, abstractResult,
      served, htransport.2.2] using related.workflow
  · intro nextPhysical currentAddress currentNode currentOp currentFlight
      pending hcurrentAddress hnextPhysical hcurrentNode hcurrentFlight
      hcurrentPhase hcurrentVersion hcurrentPending
    have hstoreEq :
        physical.commit key document = nextPhysical := by
      simpa [World.land, concreteResult] using hnextPhysical
    subst nextPhysical
    have hcurrentNodeOld :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNode
    have hownerCurrent :=
      reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
        hcurrentFlight
    have hownerStaged :=
      reachable_flight_owner hreachable haddress hnode hflight
    have hsameAddress : currentAddress = address :=
      hownerCurrent.trans hownerStaged.symm
    subst currentAddress
    rw [← hsameAddress] at hnode
    rw [hnode] at hcurrentNodeOld
    cases Concrete.Local.node.inj hcurrentNodeOld
    obtain ⟨serialNode, hserialNode, hserial⟩ :=
      reachable_nodes_serial hreachable config.workflowNode hcurrentAddress
    rw [hnode] at hserialNode
    cases Concrete.Local.node.inj hserialNode
    have hpairs :=
      NodeSerial.eq_of_mem hserial hcurrentFlight hflight
    cases hpairs
    rw [← hflightTransaction, htransaction] at hcurrentPending
    contradiction
  · intro knownAddress knownNode knownKey hknownAddress hknownNode hknown
    have hknownNodeOld :
        concrete.process (.node knownAddress) = .node knownNode := by
      simpa [World.land] using hknownNode
    have hmem :=
      related.known knownAddress knownNode knownKey hknownAddress
        hknownNodeOld hknown
    simpa [abstractNext, World.land, abstractResult, served] using
      external_keys_mono { appConfig with unreliable := true } call
        (abstract.process .service) knownKey hmem
  · intro sentAddress sentCall hsend
    simp [concreteResult] at hsend
  · intro output hsend
    simp [concreteResult] at hsend
  · intro ackAddress ackOp hsend
    simp [concreteResult] at hsend
    obtain ⟨rfl, rfl⟩ := hsend
    refine ⟨key, document, expectedVersion, provenance,
      List.mem_append_left _ hrequest, ?_, ?_⟩
    · simpa [abstractNext, World.land, abstractResult, served] using
        external_key_mem { appConfig with unreliable := true } call
          (abstract.process .service) key hselectedKey
    · have hcovered :=
        covered_sent abstract now served.1 served.2
      simpa [abstractNext, abstractResult, served, htransport.2.1] using
        hcovered
  · intro failedAddress failedOp hsend
    simp [concreteResult] at hsend
  · intro activeAddress activeNode activeOp activeFlight hactiveAddress
      hactiveNode hactiveFlight
    have hactiveNodeOld :
        concrete.process (.node activeAddress) = .node activeNode := by
      simpa [World.land] using hactiveNode
    obtain ⟨holdWritten, holdFailed⟩ :=
      related.activeReplies activeAddress activeNode activeOp activeFlight
        hactiveAddress hactiveNodeOld hactiveFlight
    constructor
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · obtain ⟨hknown, hcovered, hworkflow⟩ := holdWritten hold
        exact ⟨by
          simpa [abstractNext, World.land, abstractResult, served] using
            external_keys_mono { appConfig with unreliable := true } call
              (abstract.process .service) activeFlight.key hknown,
          hcovered.land abstractResult,
          by
            rcases hworkflow with hnone | hpending
            · exact .inl hnone
            · exact .inr (by
                simpa [abstractNext, World.land, abstractResult, served,
                  htransport.2.2] using hpending)⟩
      · simp [concreteResult] at hnew
        obtain ⟨rfl, rfl⟩ := hnew
        have hnodeEq : activeNode = node := by
          rw [hnode] at hactiveNodeOld
          exact (Concrete.Local.node.inj hactiveNodeOld).symm
        subst activeNode
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable activeAddress hactiveAddress
        rw [hnode] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
        cases hpairs
        refine ⟨?_, ?_, ?_⟩
        · subst key
          simpa [abstractNext, World.land, abstractResult, served] using
            external_key_mem { appConfig with unreliable := true } call
              (abstract.process .service) flight.key hselectedKey
        · have hcovered :=
            covered_sent abstract now served.1 served.2
          simpa [abstractNext, abstractResult, served, htransport.2.1,
            houtputs] using hcovered
        · left
          rw [← hflightTransaction, htransaction]
          rfl
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · exact (holdFailed hold).land abstractResult
      · simp [concreteResult] at hnew

theorem simulate_external_landed_failed_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {physical : Concrete.Store} {address : Addr} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hphysical : concrete.process .store = .store physical)
    (hconditional : config.conditional = true)
    (hflaky : config.flaky = true)
    (hrequest :
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network)
    (provenance : PutProvenance appConfig key document expectedVersion)
    (hmatch : expectedVersion = physical.version key)
    {call : Call} (htransaction : provenance.transaction = .external call)
    (hcurrent : physical.read key = provenance.loaded)
    (horigin : TransactionOrigin concrete address provenance.transaction)
    {node : Concrete.Node} {flight : Concrete.Flight}
    (haddress : address ∈ nodes)
    (hnode : concrete.process (.node address) = .node node)
    (hflight : (op, flight) ∈ node.flights)
    (hflightTransaction : provenance.transaction = flight.transaction)
    {now : Time} (htime : concrete.now ≤ now) :
    let lost :=
      Resonate.runLose { appConfig with unreliable := true } call
        (abstract.process .service)
    let abstractResult : Result Abstract.Pid State Message := {
      state := lost.1
      send := Abstract.sends lost.2
    }
    let concreteResult :
        Result Concrete.Pid Concrete.Local Concrete.Msg := {
      state := .store (physical.commit key document)
      send := [(.node address,
        .storeReply { op, payload := .failed })]
    }
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now concreteResult)
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  dsimp
  let lost :=
    Resonate.runLose { appConfig with unreliable := true } call
      (abstract.process .service)
  let abstractResult : Result Abstract.Pid State Message := {
    state := lost.1
    send := Abstract.sends lost.2
  }
  let abstractNext := abstract.land .service now abstractResult
  let concreteResult :
      Result Concrete.Pid Concrete.Local Concrete.Msg := {
    state := .store (physical.commit key document)
    send := [(.node address,
      .storeReply { op, payload := .failed })]
  }
  have habstractRequest :
      (Abstract.Pid.outside, .service, Message.request call) ∈
        abstract.network := by
    rw [htransaction] at horigin
    exact related.requests address call horigin
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now
          (.receive .outside (.request call))).val := by
    simp [Abstract.step, abstractResult, lost]
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now
          (.receive .outside (.request call)) abstractResult.send)
        abstractNext :=
    Step.process (Nat.le_trans related.time htime) rfl
      habstractRequest habstractResult
  have hconcreteResult :
      concreteResult ∈
        (Concrete.step appConfig config .store (.store physical) now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            }))).val := by
    simp [Concrete.step, Concrete.storePut, concreteResult,
      hconditional, hmatch, hflaky]
  have hconcreteStep :
      Step (CModel nodes appConfig) config concrete
        (.process .store now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            })) concreteResult.send)
        (concrete.land .store now concreteResult) :=
    Step.process htime (by simp) hrequest
      (hphysical ▸ hconcreteResult)
  refine ⟨[((.process .service now
      (.receive .outside (.request call)) abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩, ?_, rfl⟩
  have htransport :=
    external_cas_transport_lose
      (by
        obtain ⟨represented, hrepresented, hrep⟩ := related.store
        rw [hphysical] at hrepresented
        cases Concrete.Local.store.inj hrepresented
        exact hrep)
      provenance htransaction hcurrent
  change Related nodes appConfig config
    (concrete.land .store now concreteResult) abstractNext
  apply related_after_land related hreachable (by simp) hconcreteStep
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro knownKey hknownKey
    simpa [abstractNext, World.land, abstractResult, lost,
      Resonate.runLose] using
      external_keys_mono { appConfig with unreliable := true } call
        (abstract.process .service) knownKey hknownKey
  · exact ⟨physical.commit key document,
      by simp [World.land, concreteResult],
      by simpa [abstractNext, World.land, abstractResult, lost] using
        htransport.1⟩
  · simpa [WorkflowAligned, abstractNext, World.land, abstractResult,
      lost, htransport.2.2] using related.workflow
  · intro nextPhysical currentAddress currentNode currentOp currentFlight
      pending hcurrentAddress hnextPhysical hcurrentNode hcurrentFlight
      hcurrentPhase hcurrentVersion hcurrentPending
    have hstoreEq :
        physical.commit key document = nextPhysical := by
      simpa [World.land, concreteResult] using hnextPhysical
    subst nextPhysical
    have hcurrentNodeOld :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNode
    have hownerCurrent :=
      reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
        hcurrentFlight
    have hownerStaged :=
      reachable_flight_owner hreachable haddress hnode hflight
    have hsameAddress : currentAddress = address :=
      hownerCurrent.trans hownerStaged.symm
    subst currentAddress
    rw [← hsameAddress] at hnode
    rw [hnode] at hcurrentNodeOld
    cases Concrete.Local.node.inj hcurrentNodeOld
    obtain ⟨serialNode, hserialNode, hserial⟩ :=
      reachable_nodes_serial hreachable config.workflowNode hcurrentAddress
    rw [hnode] at hserialNode
    cases Concrete.Local.node.inj hserialNode
    have hpairs :=
      NodeSerial.eq_of_mem hserial hcurrentFlight hflight
    cases hpairs
    rw [← hflightTransaction, htransaction] at hcurrentPending
    contradiction
  · intro knownAddress knownNode knownKey hknownAddress hknownNode hknown
    have hknownNodeOld :
        concrete.process (.node knownAddress) = .node knownNode := by
      simpa [World.land] using hknownNode
    have hmem :=
      related.known knownAddress knownNode knownKey hknownAddress
        hknownNodeOld hknown
    simpa [abstractNext, World.land, abstractResult, lost,
      Resonate.runLose] using
      external_keys_mono { appConfig with unreliable := true } call
        (abstract.process .service) knownKey hmem
  · intro sentAddress sentCall hsend
    simp [concreteResult] at hsend
  · intro output hsend
    simp [concreteResult] at hsend
  · intro ackAddress ackOp hsend
    simp [concreteResult] at hsend
  · intro failedAddress failedOp hsend
    simp [concreteResult] at hsend
    obtain ⟨rfl, rfl⟩ := hsend
    refine ⟨key, document, expectedVersion, provenance,
      List.mem_append_left _ hrequest, ?_⟩
    have hcovered := covered_sent abstract now lost.1 lost.2
    intro output houtput
    rw [htransaction] at houtput
    simp [Concrete.failureOutputs] at houtput
    subst output
    exact hcovered _ (by simp [lost, Resonate.runLose])
  · intro activeAddress activeNode activeOp activeFlight hactiveAddress
      hactiveNode hactiveFlight
    have hactiveNodeOld :
        concrete.process (.node activeAddress) = .node activeNode := by
      simpa [World.land] using hactiveNode
    obtain ⟨holdWritten, holdFailed⟩ :=
      related.activeReplies activeAddress activeNode activeOp activeFlight
        hactiveAddress hactiveNodeOld hactiveFlight
    constructor
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · obtain ⟨hknown, hcovered, hworkflow⟩ := holdWritten hold
        exact ⟨by
          simpa [abstractNext, World.land, abstractResult, lost,
            Resonate.runLose] using
            external_keys_mono { appConfig with unreliable := true } call
              (abstract.process .service) activeFlight.key hknown,
          hcovered.land abstractResult,
          by
            rcases hworkflow with hnone | hpending
            · exact .inl hnone
            · exact .inr (by
                simpa [abstractNext, World.land, abstractResult, lost,
                  htransport.2.2] using hpending)⟩
      · simp [concreteResult] at hnew
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · exact (holdFailed hold).land abstractResult
      · simp [concreteResult] at hnew
        obtain ⟨rfl, rfl⟩ := hnew
        have hnodeEq : activeNode = node := by
          rw [hnode] at hactiveNodeOld
          exact (Concrete.Local.node.inj hactiveNodeOld).symm
        subst activeNode
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable activeAddress hactiveAddress
        rw [hnode] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
        cases hpairs
        have hcovered := covered_sent abstract now lost.1 lost.2
        intro output houtput
        rw [← hflightTransaction, htransaction] at houtput
        simp [Concrete.failureOutputs] at houtput
        subst output
        exact hcovered _ (by simp [lost, Resonate.runLose])

theorem simulate_external_not_landed_failed_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {physical : Concrete.Store} {address : Addr} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hphysical : concrete.process .store = .store physical)
    (hconditional : config.conditional = true)
    (hflaky : config.flaky = true)
    (hrequest :
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network)
    (provenance : PutProvenance appConfig key document expectedVersion)
    (hmatch : expectedVersion = physical.version key)
    {call : Call} (htransaction : provenance.transaction = .external call)
    (horigin : TransactionOrigin concrete address provenance.transaction)
    {node : Concrete.Node} {flight : Concrete.Flight}
    (haddress : address ∈ nodes)
    (hnode : concrete.process (.node address) = .node node)
    (hflight : (op, flight) ∈ node.flights)
    (hflightTransaction : provenance.transaction = flight.transaction)
    {now : Time} (htime : concrete.now ≤ now) :
    let shed := Resonate.runShed call (abstract.process .service)
    let abstractResult : Result Abstract.Pid State Message := {
      state := shed.1
      send := Abstract.sends shed.2
    }
    let concreteResult :
        Result Concrete.Pid Concrete.Local Concrete.Msg := {
      state := .store (physical.fence key)
      send := [(.node address,
        .storeReply { op, payload := .failed })]
    }
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now concreteResult)
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  dsimp
  let shed := Resonate.runShed call (abstract.process .service)
  let abstractResult : Result Abstract.Pid State Message := {
    state := shed.1
    send := Abstract.sends shed.2
  }
  let abstractNext := abstract.land .service now abstractResult
  let concreteResult :
      Result Concrete.Pid Concrete.Local Concrete.Msg := {
    state := .store (physical.fence key)
    send := [(.node address,
      .storeReply { op, payload := .failed })]
  }
  have habstractRequest :
      (Abstract.Pid.outside, .service, Message.request call) ∈
        abstract.network := by
    rw [htransaction] at horigin
    exact related.requests address call horigin
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now
          (.receive .outside (.request call))).val := by
    simp [Abstract.step, abstractResult, shed]
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now
          (.receive .outside (.request call)) abstractResult.send)
        abstractNext :=
    Step.process (Nat.le_trans related.time htime) rfl
      habstractRequest habstractResult
  have hconcreteResult :
      concreteResult ∈
        (Concrete.step appConfig config .store (.store physical) now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            }))).val := by
    simp [Concrete.step, Concrete.storePut, concreteResult,
      hconditional, hmatch, hflaky]
  have hconcreteStep :
      Step (CModel nodes appConfig) config concrete
        (.process .store now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            })) concreteResult.send)
        (concrete.land .store now concreteResult) :=
    Step.process htime (by simp) hrequest
      (hphysical ▸ hconcreteResult)
  refine ⟨[((.process .service now
      (.receive .outside (.request call)) abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩, ?_, rfl⟩
  change Related nodes appConfig config
    (concrete.land .store now concreteResult) abstractNext
  apply related_after_land related hreachable (by simp) hconcreteStep
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro knownKey hknownKey
    simpa [abstractNext, World.land, abstractResult, shed,
      Resonate.runShed] using hknownKey
  · obtain ⟨represented, hrepresented, hrep⟩ := related.store
    rw [hphysical] at hrepresented
    cases Concrete.Local.store.inj hrepresented
    exact ⟨physical.fence key,
      by simp [World.land, concreteResult],
      by simpa [abstractNext, World.land, abstractResult, shed,
        Resonate.runShed] using StoreRep.fence hrep key⟩
  · simpa [WorkflowAligned, abstractNext, World.land, abstractResult,
      shed, Resonate.runShed] using related.workflow
  · intro nextPhysical currentAddress currentNode currentOp currentFlight
      pending hcurrentAddress hnextPhysical hcurrentNode hcurrentFlight
      hcurrentPhase hcurrentVersion hcurrentPending
    have hstoreEq : physical.fence key = nextPhysical := by
      simpa [World.land, concreteResult] using hnextPhysical
    subst nextPhysical
    have hcurrentNodeOld :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNode
    have hownerCurrent :=
      reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
        hcurrentFlight
    have hownerStaged :=
      reachable_flight_owner hreachable haddress hnode hflight
    have hsameAddress : currentAddress = address :=
      hownerCurrent.trans hownerStaged.symm
    subst currentAddress
    rw [← hsameAddress] at hnode
    rw [hnode] at hcurrentNodeOld
    cases Concrete.Local.node.inj hcurrentNodeOld
    obtain ⟨serialNode, hserialNode, hserial⟩ :=
      reachable_nodes_serial hreachable config.workflowNode hcurrentAddress
    rw [hnode] at hserialNode
    cases Concrete.Local.node.inj hserialNode
    have hpairs := NodeSerial.eq_of_mem hserial hcurrentFlight hflight
    cases hpairs
    rw [← hflightTransaction, htransaction] at hcurrentPending
    contradiction
  · intro knownAddress knownNode knownKey hknownAddress hknownNode hknown
    exact related.known knownAddress knownNode knownKey hknownAddress
      (by simpa [World.land] using hknownNode) hknown
  · intro sentAddress sentCall hsend
    simp [concreteResult] at hsend
  · intro output hsend
    simp [concreteResult] at hsend
  · intro ackAddress ackOp hsend
    simp [concreteResult] at hsend
  · intro failedAddress failedOp hsend
    simp [concreteResult] at hsend
    obtain ⟨rfl, rfl⟩ := hsend
    refine ⟨key, document, expectedVersion, provenance,
      List.mem_append_left _ hrequest, ?_⟩
    have hcovered := covered_sent abstract now shed.1 shed.2
    rw [htransaction]
    intro output houtput
    simp [Concrete.failureOutputs] at houtput
    subst output
    exact hcovered _ (by simp [shed, Resonate.runShed])
  · intro activeAddress activeNode activeOp activeFlight hactiveAddress
      hactiveNode hactiveFlight
    have hactiveNodeOld :
        concrete.process (.node activeAddress) = .node activeNode := by
      simpa [World.land] using hactiveNode
    obtain ⟨holdWritten, holdFailed⟩ :=
      related.activeReplies activeAddress activeNode activeOp activeFlight
        hactiveAddress hactiveNodeOld hactiveFlight
    constructor
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · obtain ⟨hknown, hcovered, hworkflow⟩ := holdWritten hold
        exact ⟨by
          simpa [abstractNext, World.land, abstractResult, shed,
            Resonate.runShed] using hknown,
          hcovered.land abstractResult,
          by
            rcases hworkflow with hnone | hpending
            · exact .inl hnone
            · exact .inr (by
                simpa [abstractNext, World.land, abstractResult, shed,
                  Resonate.runShed] using hpending)⟩
      · simp [concreteResult] at hnew
    · intro hreply
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · exact (holdFailed hold).land abstractResult
      · simp [concreteResult] at hnew
        obtain ⟨rfl, rfl⟩ := hnew
        have hnodeEq : activeNode = node := by
          rw [hnode] at hactiveNodeOld
          exact (Concrete.Local.node.inj hactiveNodeOld).symm
        subst activeNode
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable activeAddress hactiveAddress
        rw [hnode] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
        cases hpairs
        have hcovered := covered_sent abstract now shed.1 shed.2
        rw [← hflightTransaction, htransaction]
        intro output houtput
        simp [Concrete.failureOutputs] at houtput
        subst output
        exact hcovered _ (by simp [shed, Resonate.runShed])

theorem simulate_internal_committed_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {physical : Concrete.Store} {address : Addr} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hphysical : concrete.process .store = .store physical)
    (hrequest :
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network)
    (provenance : PutProvenance appConfig key document expectedVersion)
    (hsnapshot : Snapshot physical key provenance.loaded)
    (hmatch : expectedVersion = physical.version key)
    {pendingBefore : List WorkflowEntry}
    (htransactionPending :
      TransactionPending provenance.transaction = some pendingBefore)
    (hfailure : Concrete.failureOutputs provenance.transaction = [])
    {node : Concrete.Node} {flight : Concrete.Flight}
    (haddress : address ∈ nodes)
    (hnode : concrete.process (.node address) = .node node)
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    (hkey : key = flight.key)
    (hloaded : hkey ▸ provenance.loaded = flight.loaded)
    (hflightTransaction : provenance.transaction = flight.transaction)
    (houtputs : provenance.outputs = flight.selected)
    (hcontinuations : provenance.continuations = flight.continuations)
    {now : Time}
    (lifted : State × List Output)
    (hchoice :
      lifted ∈
        (Resonate.runTimeoutChoices
          { appConfig with unreliable := true } now
          (abstract.process .service)).val)
    (htransport :
      StoreRep (physical.commit key document) lifted.1 ∧
        lifted.2 = provenance.outputs ∧
        lifted.1.workflow.pending = provenance.continuations)
    (hkeys :
      ∀ knownKey ∈ (abstract.process .service).store.keys,
        knownKey ∈ lifted.1.store.keys)
    (hkeyMem : key ∈ lifted.1.store.keys)
    {reply : StoreReply}
    (hreply : reply = .written ∨ reply = .failed)
    (htime : concrete.now ≤ now)
    (hconcreteResult :
      ({
        state := .store (physical.commit key document)
        send := [(.node address, .storeReply { op, payload := reply })]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config .store (.store physical) now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            }))).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now {
          state := .store (physical.commit key document)
          send := [(.node address,
            .storeReply { op, payload := reply })]
        })
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  let abstractResult : Result Abstract.Pid State Message := {
    state := lifted.1
    send := Abstract.sends lifted.2
  }
  let abstractNext := abstract.land .service now abstractResult
  let concreteResult :
      Result Concrete.Pid Concrete.Local Concrete.Msg := {
    state := .store (physical.commit key document)
    send := [(.node address, .storeReply { op, payload := reply })]
  }
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now .timeout).val := by
    simp only [Abstract.step]
    exact List.mem_map.mpr ⟨lifted, hchoice, by
      simp [abstractResult]⟩
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now .timeout abstractResult.send)
        abstractNext :=
    Step.process (Nat.le_trans related.time htime) rfl trivial
      habstractResult
  have hconcreteStep :
      Step (CModel nodes appConfig) config concrete
        (.process .store now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            })) concreteResult.send)
        (concrete.land .store now concreteResult) :=
    Step.process htime (by simp) hrequest
      (hphysical ▸ hconcreteResult)
  refine ⟨[((.process .service now .timeout abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩, ?_, rfl⟩
  change Related nodes appConfig config
    (concrete.land .store now concreteResult) abstractNext
  have howner :=
    reachable_flight_owner hreachable haddress hnode hflight
  have hpendingBefore :
      (abstract.process .service).workflow.pending = pendingBefore :=
    (related.currentWorkflow physical address node op flight pendingBefore
      haddress hphysical hnode hflight hphase
      (by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch)
      (by simpa [hflightTransaction] using htransactionPending)).2
  apply related_after_land related hreachable (by simp) hconcreteStep
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro knownKey hknownKey
    simpa [abstractNext, World.land, abstractResult] using
      hkeys knownKey hknownKey
  · exact ⟨physical.commit key document,
      by simp [World.land, concreteResult],
      by simpa [abstractNext, World.land, abstractResult] using
        htransport.1⟩
  · simp only [WorkflowAligned]
    split
    next hworkflowMem =>
      refine ⟨node, by
        simpa [World.land, howner] using hnode, ?_⟩
      right
      right
      exact ⟨op, flight, hflight, by
        cases ht : flight.transaction with
        | external call =>
            rw [hflightTransaction, ht] at htransactionPending
            contradiction
        | work item instant rest =>
            simp only [FlightWorkflowStage, ht, hphase]
            exact Or.inr (by
              simpa [hcontinuations, abstractNext, World.land,
                abstractResult] using htransport.2.2)
        | scan scanKey instant rest =>
            simp only [FlightWorkflowStage, ht, hphase]
            exact Or.inr (by
              simpa [hcontinuations, abstractNext, World.land,
                abstractResult] using htransport.2.2)⟩
    next hworkflowMiss =>
      exact (hworkflowMiss (howner ▸ haddress)).elim
  · intro nextPhysical currentAddress currentNode currentOp currentFlight
      pending hcurrentAddress hnextPhysical hcurrentNode hcurrentFlight
      hcurrentPhase hcurrentVersion hcurrentPending
    have hstoreEq :
        physical.commit key document = nextPhysical := by
      simpa [World.land, concreteResult] using hnextPhysical
    subst nextPhysical
    have hcurrentNodeOld :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNode
    have hcurrentOwner :=
      reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
        hcurrentFlight
    have hsameAddress : currentAddress = address :=
      hcurrentOwner.trans howner.symm
    subst currentAddress
    rw [← hsameAddress] at hnode
    rw [hnode] at hcurrentNodeOld
    cases Concrete.Local.node.inj hcurrentNodeOld
    obtain ⟨serialNode, hserialNode, hserial⟩ :=
      reachable_nodes_serial hreachable config.workflowNode hcurrentAddress
    rw [hnode] at hserialNode
    cases Concrete.Local.node.inj hserialNode
    have hpairs := NodeSerial.eq_of_mem hserial hcurrentFlight hflight
    cases hpairs
    subst key
    have hbad :
        provenance.loaded.map (·.2) =
          (physical.commit flight.key document).version flight.key := by
      simpa [hloaded] using hcurrentVersion
    exact (Snapshot.expected_ne_commit_version hsnapshot hbad).elim
  · intro knownAddress knownNode knownKey hknownAddress hknownNode hknown
    have hknownNodeOld :
        concrete.process (.node knownAddress) = .node knownNode := by
      simpa [World.land] using hknownNode
    have hmem :=
      related.known knownAddress knownNode knownKey hknownAddress
        hknownNodeOld hknown
    simpa [abstractNext, World.land, abstractResult] using
      hkeys knownKey hmem
  · intro sentAddress sentCall hsend
    simp [concreteResult] at hsend
  · intro output hsend
    simp [concreteResult] at hsend
  · intro ackAddress ackOp hsend
    rcases hreply with rfl | rfl
    · simp [concreteResult] at hsend
      obtain ⟨rfl, rfl⟩ := hsend
      refine ⟨key, document, expectedVersion, provenance,
        List.mem_append_left _ hrequest, ?_, ?_⟩
      · simpa [abstractNext, World.land, abstractResult] using hkeyMem
      · have hcovered := covered_sent abstract now lifted.1 lifted.2
        simpa [abstractNext, abstractResult, htransport.2.1] using hcovered
    · simp [concreteResult] at hsend
  · intro failedAddress failedOp hsend
    rcases hreply with rfl | rfl
    · simp [concreteResult] at hsend
    · simp [concreteResult] at hsend
      obtain ⟨rfl, rfl⟩ := hsend
      exact ⟨key, document, expectedVersion, provenance,
        List.mem_append_left _ hrequest, by
          rw [hfailure]
          simp [Covered]⟩
  · intro activeAddress activeNode activeOp activeFlight hactiveAddress
      hactiveNode hactiveFlight
    have hactiveNodeOld :
        concrete.process (.node activeAddress) = .node activeNode := by
      simpa [World.land] using hactiveNode
    obtain ⟨holdWritten, holdFailed⟩ :=
      related.activeReplies activeAddress activeNode activeOp activeFlight
        hactiveAddress hactiveNodeOld hactiveFlight
    constructor
    · intro hreplyMem
      simp only [World.land, List.mem_append] at hreplyMem
      rcases hreplyMem with hold | hnew
      · obtain ⟨hknown, hcovered, hworkflow⟩ := holdWritten hold
        have hownerActive :=
          reachable_flight_owner hreachable hactiveAddress hactiveNodeOld
            hactiveFlight
        have hownerStaged :=
          reachable_flight_owner hreachable haddress hnode hflight
        have hsameAddress : activeAddress = address :=
          hownerActive.trans hownerStaged.symm
        subst activeAddress
        rw [← hsameAddress] at hnode
        rw [hnode] at hactiveNodeOld
        cases Concrete.Local.node.inj hactiveNodeOld
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable config.workflowNode
            (hownerStaged ▸ haddress)
        rw [hnode] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
        cases hpairs
        exact ⟨by
          simpa [abstractNext, World.land, abstractResult] using
            hkeys flight.key hknown,
          hcovered.land abstractResult,
          by
            rcases hworkflow with hnone | hpending
            · exact .inl hnone
            · exact .inr (by
                simpa [abstractNext, World.land, abstractResult,
                  ← hcontinuations] using htransport.2.2)⟩
      · rcases hreply with rfl | rfl
        · simp [concreteResult] at hnew
          obtain ⟨rfl, rfl⟩ := hnew
          have hnodeEq : activeNode = node := by
            rw [hnode] at hactiveNodeOld
            exact (Concrete.Local.node.inj hactiveNodeOld).symm
          subst activeNode
          obtain ⟨serialNode, hserialNode, hserial⟩ :=
            reachable_nodes_serial hreachable activeAddress hactiveAddress
          rw [hnode] at hserialNode
          cases Concrete.Local.node.inj hserialNode
          have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
          have hactiveEq : activeFlight = flight :=
            congrArg Prod.snd hpairs
          have htxActive :
              provenance.transaction = activeFlight.transaction :=
            hflightTransaction.trans
              (congrArg (fun value : Concrete.Flight =>
                value.transaction) hactiveEq.symm)
          cases hpairs
          refine ⟨by simpa [hkey, abstractNext, World.land,
              abstractResult] using hkeyMem, ?_, ?_⟩
          ·
              have hcovered := covered_sent abstract now lifted.1 lifted.2
              simpa [abstractNext, abstractResult, htransport.2.1,
                houtputs] using hcovered
          · right
            simpa [abstractNext, World.land, abstractResult,
              ← hcontinuations] using htransport.2.2
        · simp [concreteResult] at hnew
    · intro hreplyMem
      simp only [World.land, List.mem_append] at hreplyMem
      rcases hreplyMem with hold | hnew
      · exact (holdFailed hold).land abstractResult
      · rcases hreply with rfl | rfl
        · simp [concreteResult] at hnew
        · simp [concreteResult] at hnew
          obtain ⟨rfl, rfl⟩ := hnew
          have hnodeEq : activeNode = node := by
            rw [hnode] at hactiveNodeOld
            exact (Concrete.Local.node.inj hactiveNodeOld).symm
          subst activeNode
          obtain ⟨serialNode, hserialNode, hserial⟩ :=
            reachable_nodes_serial hreachable activeAddress hactiveAddress
          rw [hnode] at hserialNode
          cases Concrete.Local.node.inj hserialNode
          have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
          have hactiveEq : activeFlight = flight :=
            congrArg Prod.snd hpairs
          rw [hactiveEq, ← hflightTransaction, hfailure]
          simp [Covered]

theorem simulate_internal_not_landed_failed_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {physical : Concrete.Store} {address : Addr} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hphysical : concrete.process .store = .store physical)
    (hrequest :
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network)
    (provenance : PutProvenance appConfig key document expectedVersion)
    (hsnapshot : Snapshot physical key provenance.loaded)
    (hfailure : Concrete.failureOutputs provenance.transaction = [])
    {node : Concrete.Node} {flight : Concrete.Flight}
    (haddress : address ∈ nodes)
    (hnode : concrete.process (.node address) = .node node)
    (hflight : (op, flight) ∈ node.flights)
    (hkey : key = flight.key)
    (hloaded : hkey ▸ provenance.loaded = flight.loaded)
    (hflightTransaction : provenance.transaction = flight.transaction)
    {now : Time}
    (htime : concrete.now ≤ now)
    (hconcreteResult :
      ({
        state := .store (physical.fence key)
        send := [(.node address,
          .storeReply { op, payload := .failed })]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config .store (.store physical) now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            }))).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now {
          state := .store (physical.fence key)
          send := [(.node address,
            .storeReply { op, payload := .failed })]
        })
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  let concreteResult :
      Result Concrete.Pid Concrete.Local Concrete.Msg := {
    state := .store (physical.fence key)
    send := [(.node address,
      .storeReply { op, payload := .failed })]
  }
  have hconcreteStep :
      Step (CModel nodes appConfig) config concrete
        (.process .store now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            })) concreteResult.send)
        (concrete.land .store now concreteResult) :=
    Step.process htime (by simp) hrequest
      (hphysical ▸ hconcreteResult)
  refine ⟨[], trivial, ?_, rfl⟩
  change Related nodes appConfig config
    (concrete.land .store now concreteResult) abstract
  apply related_after_land related hreachable (by simp) hconcreteStep
      (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨represented, hrepresented, hrep⟩ := related.store
    rw [hphysical] at hrepresented
    cases Concrete.Local.store.inj hrepresented
    exact ⟨physical.fence key,
      by simp [World.land, concreteResult],
      StoreRep.fence hrep key⟩
  · simpa [WorkflowAligned, World.land] using related.workflow
  · intro nextPhysical currentAddress currentNode currentOp currentFlight
      pending hcurrentAddress hnextPhysical hcurrentNode hcurrentFlight
      hcurrentPhase hcurrentVersion hcurrentPending
    have hstoreEq : physical.fence key = nextPhysical := by
      simpa [World.land, concreteResult] using hnextPhysical
    subst nextPhysical
    have hcurrentNodeOld :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNode
    have hownerCurrent :=
      reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
        hcurrentFlight
    have hownerStaged :=
      reachable_flight_owner hreachable haddress hnode hflight
    have hsameAddress : currentAddress = address :=
      hownerCurrent.trans hownerStaged.symm
    subst currentAddress
    rw [← hsameAddress] at hnode
    rw [hnode] at hcurrentNodeOld
    cases Concrete.Local.node.inj hcurrentNodeOld
    obtain ⟨serialNode, hserialNode, hserial⟩ :=
      reachable_nodes_serial hreachable config.workflowNode hcurrentAddress
    rw [hnode] at hserialNode
    cases Concrete.Local.node.inj hserialNode
    have hpairs := NodeSerial.eq_of_mem hserial hcurrentFlight hflight
    cases hpairs
    subst key
    have hbad :
        provenance.loaded.map (·.2) =
          (physical.fence flight.key).version flight.key := by
      simpa [hloaded] using hcurrentVersion
    exact (Snapshot.expected_ne_commit_version
      (document := physical.toAbstract.read flight.key) hsnapshot hbad).elim
  · intro knownAddress knownNode knownKey hknownAddress hknownNode hknown
    exact related.known knownAddress knownNode knownKey hknownAddress
      (by simpa [World.land] using hknownNode) hknown
  · intro sentAddress sentCall hsend
    simp [concreteResult] at hsend
  · intro output hsend
    simp [concreteResult] at hsend
  · intro ackAddress ackOp hsend
    simp [concreteResult] at hsend
  · intro failedAddress failedOp hsend
    simp [concreteResult] at hsend
    obtain ⟨rfl, rfl⟩ := hsend
    exact ⟨key, document, expectedVersion, provenance,
      List.mem_append_left _ hrequest, by
        rw [hfailure]
        simp [Covered]⟩
  · intro activeAddress activeNode activeOp activeFlight hactiveAddress
      hactiveNode hactiveFlight
    have hactiveNodeOld :
        concrete.process (.node activeAddress) = .node activeNode := by
      simpa [World.land] using hactiveNode
    obtain ⟨holdWritten, holdFailed⟩ :=
      related.activeReplies activeAddress activeNode activeOp activeFlight
        hactiveAddress hactiveNodeOld hactiveFlight
    constructor
    · intro hreplyMem
      simp only [World.land, List.mem_append] at hreplyMem
      rcases hreplyMem with hold | hnew
      · exact holdWritten hold
      · simp [concreteResult] at hnew
    · intro hreplyMem
      simp only [World.land, List.mem_append] at hreplyMem
      rcases hreplyMem with hold | hnew
      · exact holdFailed hold
      · simp [concreteResult] at hnew
        obtain ⟨rfl, rfl⟩ := hnew
        have hnodeEq : activeNode = node := by
          rw [hnode] at hactiveNodeOld
          exact (Concrete.Local.node.inj hactiveNodeOld).symm
        subst activeNode
        obtain ⟨serialNode, hserialNode, hserial⟩ :=
          reachable_nodes_serial hreachable activeAddress hactiveAddress
        rw [hnode] at hserialNode
        cases Concrete.Local.node.inj hserialNode
        have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
        cases hpairs
        rw [← hflightTransaction, hfailure]
        simp [Covered]

theorem simulate_matching_put_store
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    (hconditional : config.conditional = true)
    {physical : Concrete.Store} {address : Addr} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hphysical : concrete.process .store = .store physical)
    (hrequest :
      (Concrete.Pid.node address, .store,
        .storeRequest {
          op
          payload := .put key document expectedVersion
        }) ∈ concrete.network)
    (hmatch : expectedVersion = physical.version key)
    {now : Time}
    (htime : concrete.now ≤ now)
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config .store (.store physical) now
          (.receive (.node address)
            (.storeRequest {
              op
              payload := .put key document expectedVersion
            }))).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now result) (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  obtain ⟨provenance, hsnapshot, horigin, hagreement, heligible⟩ :=
    reachable_stageable_puts hreachable hphysical hrequest
  obtain ⟨node, flight, hnode, hflight, hphase, hnoreply⟩ :=
    heligible hmatch
  obtain ⟨hkey, hloaded, hflightTransaction, houtputs,
      hcontinuations⟩ :=
    hagreement node flight hnode hflight hphase
  have haddress : address ∈ nodes :=
    reachable_node_sender hreachable hrequest
  have hcurrent : physical.read key = provenance.loaded :=
    Snapshot.eq_of_version hsnapshot
      (provenance.expected_eq.trans hmatch)
  obtain ⟨represented, hrepresented, hrep⟩ := related.store
  rw [hphysical] at hrepresented
  cases Concrete.Local.store.inj hrepresented
  have hwork
      {item : WorkItem} {instant : Time} {rest : List WorkflowEntry}
      (htransaction :
        provenance.transaction = .work item instant rest)
      {reply : StoreReply}
      (hreply : reply = .written ∨ reply = .failed)
      (hconcreteResult :
        ({
          state := .store (physical.commit key document)
          send := [(.node address, .storeReply { op, payload := reply })]
        } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
          (Concrete.step appConfig config .store (.store physical) now
            (.receive (.node address)
              (.storeRequest {
                op
                payload := .put key document expectedVersion
              }))).val) :
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land .store now {
            state := .store (physical.commit key document)
            send := [(.node address,
              .storeReply { op, payload := reply })]
          })
          (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = [] := by
    have hitemKey : item.key = key := by
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have htx := hvalid.1
      rw [← hflightTransaction, htransaction] at htx
      simp only [Concrete.Transaction.key?, Option.some.injEq] at htx
      exact htx.trans hkey.symm
    let lifted :=
      Resonate.runWork { appConfig with unreliable := true }
        item instant rest (abstract.process .service)
    have hpendingTransaction :
        TransactionPending provenance.transaction =
          some (.work item instant :: rest) := by
      rw [htransaction]
      rfl
    have hpending :
        (abstract.process .service).workflow.pending =
          .work item instant :: rest := by
      have hversion :
          flight.loaded.map (·.2) = physical.version flight.key := by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch
      exact (related.currentWorkflow physical address node op flight
        (.work item instant :: rest) haddress hphysical hnode hflight
        hphase hversion (by
          rw [← hflightTransaction]
          exact hpendingTransaction)).2
    have hchoice :
        lifted ∈
          (Resonate.runTimeoutChoices
            { appConfig with unreliable := true } now
            (abstract.process .service)).val := by
      simp [lifted, Resonate.runTimeoutChoices, hpending,
        Resonate.runWorkflowEntry, Outcomes.one]
    have htransport :=
      work_cas_transport hrep provenance htransaction hcurrent
    have hitemMem :=
      work_key_mem { appConfig with unreliable := true }
        item instant rest (abstract.process .service)
    rw [hitemKey] at hitemMem
    exact simulate_internal_committed_store hreachable related hphysical
      hrequest provenance hsnapshot hmatch
      (htransactionPending := hpendingTransaction)
      (hfailure := by simp [htransaction, Concrete.failureOutputs])
      haddress hnode hflight hphase hkey hloaded hflightTransaction
      houtputs hcontinuations lifted hchoice htransport
      (work_keys_mono { appConfig with unreliable := true }
        item instant rest (abstract.process .service))
      (by simpa [lifted] using hitemMem)
      hreply htime hconcreteResult
  have hscan
      {scanKey : DocumentKey} {instant : Time}
      {rest : List WorkflowEntry}
      (htransaction :
        provenance.transaction = .scan scanKey instant rest)
      {reply : StoreReply}
      (hreply : reply = .written ∨ reply = .failed)
      (hconcreteResult :
        ({
          state := .store (physical.commit key document)
          send := [(.node address, .storeReply { op, payload := reply })]
        } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
          (Concrete.step appConfig config .store (.store physical) now
            (.receive (.node address)
              (.storeRequest {
                op
                payload := .put key document expectedVersion
              }))).val) :
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land .store now {
            state := .store (physical.commit key document)
            send := [(.node address,
              .storeReply { op, payload := reply })]
          })
          (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = [] := by
    have hscanKey : scanKey = key := by
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have htx := hvalid.1
      rw [← hflightTransaction, htransaction] at htx
      simp only [Concrete.Transaction.key?, Option.some.injEq] at htx
      exact htx.trans hkey.symm
    subst scanKey
    let lifted :=
      Resonate.runScan { appConfig with unreliable := true }
        key instant rest (abstract.process .service)
    have hpendingTransaction :
        TransactionPending provenance.transaction =
          some (.scan key instant :: rest) := by
      rw [htransaction]
      rfl
    have hpending :
        (abstract.process .service).workflow.pending =
          .scan key instant :: rest := by
      have hversion :
          flight.loaded.map (·.2) = physical.version flight.key := by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch
      exact (related.currentWorkflow physical address node op flight
        (.scan key instant :: rest) haddress hphysical hnode hflight
        hphase hversion (by
          rw [← hflightTransaction]
          exact hpendingTransaction)).2
    have hchoice :
        lifted ∈
          (Resonate.runTimeoutChoices
            { appConfig with unreliable := true } now
            (abstract.process .service)).val := by
      simp [lifted, Resonate.runTimeoutChoices, hpending,
        Resonate.runWorkflowEntry, Outcomes.one]
    have htransport :=
      scan_cas_transport hrep provenance htransaction hcurrent
    exact simulate_internal_committed_store hreachable related hphysical
      hrequest provenance hsnapshot hmatch
      (htransactionPending := hpendingTransaction)
      (hfailure := by simp [htransaction, Concrete.failureOutputs])
      haddress hnode hflight hphase hkey hloaded hflightTransaction
      houtputs hcontinuations lifted hchoice htransport
      (scan_keys_mono { appConfig with unreliable := true }
        key instant rest (abstract.process .service))
      (scan_key_mem { appConfig with unreliable := true }
        key instant rest (abstract.process .service))
      hreply htime hconcreteResult
  have hinternalFence
      (hfailure : Concrete.failureOutputs provenance.transaction = [])
      (hconcreteResult :
        ({
          state := .store (physical.fence key)
          send := [(.node address,
            .storeReply { op, payload := .failed })]
        } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
          (Concrete.step appConfig config .store (.store physical) now
            (.receive (.node address)
              (.storeRequest {
                op
                payload := .put key document expectedVersion
              }))).val) :
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land .store now {
            state := .store (physical.fence key)
            send := [(.node address,
              .storeReply { op, payload := .failed })]
          })
          (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = [] :=
    simulate_internal_not_landed_failed_store hreachable related hphysical
      hrequest provenance hsnapshot hfailure haddress hnode hflight hkey
      hloaded hflightTransaction htime hconcreteResult
  cases htransaction : provenance.transaction with
  | external call =>
      by_cases hflaky : config.flaky = true
      · simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
          hflaky] at hresult
        rcases hresult with rfl | rfl | rfl
        · exact simulate_external_written_store hreachable related hphysical
            hconditional hrequest provenance hmatch htransaction hcurrent
            horigin haddress hnode hflight hphase hkey hflightTransaction
            houtputs htime
        · exact simulate_external_landed_failed_store hreachable related
            hphysical hconditional hflaky hrequest provenance hmatch
            htransaction hcurrent horigin haddress hnode hflight
            hflightTransaction htime
        · exact simulate_external_not_landed_failed_store hreachable related
            hphysical hconditional hflaky hrequest provenance hmatch
            htransaction horigin haddress hnode hflight hflightTransaction
            htime
      · have hflakyFalse : config.flaky = false := by
          cases ht : config.flaky <;> simp_all
        simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
          hflakyFalse, Outcomes.one] at hresult
        subst result
        exact simulate_external_written_store hreachable related hphysical
          hconditional hrequest provenance hmatch htransaction hcurrent
          horigin haddress hnode hflight hphase hkey hflightTransaction
          houtputs htime
  | work item instant rest =>
      by_cases hflaky : config.flaky = true
      · simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
          hflaky] at hresult
        rcases hresult with rfl | rfl | rfl
        · exact hwork htransaction (.inl rfl) (by
            simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
              hflaky])
        · exact hwork htransaction (.inr rfl) (by
            simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
              hflaky])
        · exact hinternalFence
            (by simp [htransaction, Concrete.failureOutputs]) (by
              simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
                hflaky])
      · have hflakyFalse : config.flaky = false := by
          cases ht : config.flaky <;> simp_all
        simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
          hflakyFalse, Outcomes.one] at hresult
        subst result
        exact hwork htransaction (.inl rfl) (by
          simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
            hflakyFalse, Outcomes.one])
  | scan scanKey instant rest =>
      by_cases hflaky : config.flaky = true
      · simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
          hflaky] at hresult
        rcases hresult with rfl | rfl | rfl
        · exact hscan htransaction (.inl rfl) (by
            simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
              hflaky])
        · exact hscan htransaction (.inr rfl) (by
            simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
              hflaky])
        · exact hinternalFence
            (by simp [htransaction, Concrete.failureOutputs]) (by
              simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
                hflaky])
      · have hflakyFalse : config.flaky = false := by
          cases ht : config.flaky <;> simp_all
        simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
          hflakyFalse, Outcomes.one] at hresult
        subst result
        exact hscan htransaction (.inl rfl) (by
          simp [Concrete.step, Concrete.storePut, hconditional, hmatch,
            hflakyFalse, Outcomes.one])

theorem simulate_store_process
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    (hconditional : config.conditional = true)
    {physical : Concrete.Store}
    (hphysical : concrete.process .store = .store physical)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete .store)
    (hresult :
      result ∈
        (Concrete.step appConfig config .store (.store physical)
          now event).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land .store now result) (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  have hinert
      {inert : Result Concrete.Pid Concrete.Local Concrete.Msg}
      (hmember :
        inert ∈
          (Concrete.step appConfig config .store (.store physical)
            now event).val)
      (hstate : inert.state = .store physical)
      (hreplies :
        ∀ target message, (target, message) ∈ inert.send →
          ∃ reply, message = Concrete.Msg.storeReply reply)
      (hnoWritten :
        ∀ address op,
          (.node address,
            Concrete.Msg.storeReply { op, payload := .written }) ∉
              inert.send)
      (hnoFailed :
        ∀ address op,
          (.node address,
            Concrete.Msg.storeReply { op, payload := .failed }) ∉
              inert.send) :
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land .store now inert) (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = [] :=
    ⟨[], trivial,
      related_after_inert_store hreachable related hphysical htime hvalid
        hmember hstate hreplies hnoWritten hnoFailed,
      rfl⟩
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      apply hinert (by simp [Concrete.step, Outcomes.one]) <;> simp
  | receive sender message =>
      cases message with
      | request call =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          apply hinert (by simp [Concrete.step, Outcomes.one]) <;> simp
      | output output =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          apply hinert (by simp [Concrete.step, Outcomes.one]) <;> simp
      | storeReply reply =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          apply hinert (by simp [Concrete.step, Outcomes.one]) <;> simp
      | storeRequest rpc =>
          obtain ⟨op, payload⟩ := rpc
          cases payload with
          | get key =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              apply hinert (by
                simp [Concrete.step, Outcomes.one]) <;> simp
          | put key document expectedVersion =>
              obtain ⟨address, rfl⟩ :=
                reachable_store_request_sender hreachable hvalid
              by_cases hmatch :
                  expectedVersion = physical.version key
              · exact simulate_matching_put_store hreachable related
                  hconditional hphysical hvalid hmatch htime hresult
              · simp [Concrete.step, Concrete.storePut, hconditional,
                  hmatch, Outcomes.one] at hresult
                subst result
                apply hinert (by
                  simp [Concrete.step, Concrete.storePut, hconditional,
                    hmatch, Outcomes.one]) <;> simp

theorem related_after_node_land
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract abstractNext : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (habstractTime : abstractNext.now ≤ now)
    (hnetwork :
      ∀ message ∈ abstract.network, message ∈ abstractNext.network)
    (hkeys :
      ∀ key ∈ (abstract.process .service).store.keys,
        key ∈ (abstractNext.process .service).store.keys)
    (hstore :
      ∃ physical,
        concrete.process .store = .store physical ∧
        StoreRep physical (abstractNext.process .service))
    (hworkflow :
      WorkflowAligned config
        (concrete.land (.node address) now result) abstractNext)
    (hcurrent :
      ∀ physical currentAddress currentNode op flight pending,
        currentAddress ∈ nodes →
        (concrete.land (.node address) now result).process .store =
          .store physical →
        (concrete.land (.node address) now result).process
          (.node currentAddress) = .node currentNode →
        (op, flight) ∈ currentNode.flights →
        flight.phase = .writing →
        flight.loaded.map (·.2) = physical.version flight.key →
        TransactionPending flight.transaction = some pending →
        currentAddress = config.workflowNode ∧
          (abstractNext.process .service).workflow.pending = pending)
    (hknown :
      ∀ currentAddress currentNode key,
        currentAddress ∈ nodes →
        (concrete.land (.node address) now result).process
          (.node currentAddress) = .node currentNode →
        key ∈ currentNode.known →
        key ∈ (abstractNext.process .service).store.keys)
    (hnewRequest :
      ∀ {target call},
        (.node target, Concrete.Msg.request call) ∈ result.send →
        (Abstract.Pid.outside, .service, Message.request call) ∈
          abstractNext.network)
    (hnewOutput :
      ∀ {output},
        (.outside, Concrete.Msg.output output) ∈ result.send →
        (Abstract.Pid.service, .outside, Message.output output) ∈
          abstractNext.network)
    (hactive :
      ∀ currentAddress currentNode op flight,
        currentAddress ∈ nodes →
        (concrete.land (.node address) now result).process
          (.node currentAddress) = .node currentNode →
        (op, flight) ∈ currentNode.flights →
        ((Concrete.Pid.store, .node currentAddress,
            .storeReply { op, payload := .written }) ∈
              (concrete.land (.node address) now result).network →
          flight.key ∈ (abstractNext.process .service).store.keys ∧
            Covered abstractNext flight.selected ∧
            (TransactionPending flight.transaction = none ∨
              (abstractNext.process .service).workflow.pending =
                flight.continuations)) ∧
        ((Concrete.Pid.store, .node currentAddress,
            .storeReply { op, payload := .failed }) ∈
              (concrete.land (.node address) now result).network →
          Covered abstractNext
            (Concrete.failureOutputs flight.transaction))) :
    Related nodes appConfig config
      (concrete.land (.node address) now result) abstractNext := by
  have hstep :
      Step (CModel nodes appConfig) config concrete
        (.process (.node address) now event result.send)
        (concrete.land (.node address) now result) :=
    Step.process htime haddress hvalid (hnode ▸ hresult)
  apply related_after_land related hreachable haddress hstep
      habstractTime hnetwork hkeys hstore hworkflow hcurrent hknown
      hnewRequest hnewOutput
  · intro target op hsend
    exact (node_step_no_store_reply hresult hsend).elim
  · intro target op hsend
    exact (node_step_no_store_reply hresult hsend).elim
  · exact hactive

theorem related_after_inert_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      ({
        state := .node node
        send := []
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now {
        state := .node node
        send := []
      }) abstract := by
  have hprocessEq :
      (concrete.land (.node address) now {
        state := .node node
        send := []
      }).process = concrete.process := by
    funext pid
    by_cases hp : pid = .node address
    · subst pid
      simp [World.land, hnode]
    · simp [World.land, hp]
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h) related.store
  · rw [WorkflowAligned, hprocessEq]
    exact related.workflow
  · intro physical currentAddress currentNode op flight pending
      hcurrentAddress hphysical hcurrentNode hflight hphase hversion
      hpending
    rw [hprocessEq] at hphysical hcurrentNode
    exact related.currentWorkflow physical currentAddress currentNode op
      flight pending hcurrentAddress
      hphysical hcurrentNode hflight hphase hversion hpending
  · intro currentAddress currentNode key hcurrentAddress hcurrentNode hkey
    rw [hprocessEq] at hcurrentNode
    exact related.known currentAddress currentNode key hcurrentAddress
      hcurrentNode hkey
  · intro target call hsend
    contradiction
  · intro output hsend
    contradiction
  · intro currentAddress currentNode op flight hcurrentAddress hcurrentNode
      hflight
    rw [hprocessEq] at hcurrentNode
    obtain ⟨hwritten, hfailed⟩ :=
      related.activeReplies currentAddress currentNode op flight
        hcurrentAddress hcurrentNode hflight
    constructor
    · intro hreply
      exact hwritten (by simpa [World.land] using hreply)
    · intro hreply
      exact hfailed (by simpa [World.land] using hreply)

theorem simulate_pure_external_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {call : Call}
    (hkey : (Concrete.Transaction.external call).key? = none)
    {now : Time} (htime : concrete.now ≤ now)
    (hrequest :
      (Concrete.Pid.outside, .node address, .request call) ∈
        concrete.network)
    (hresult :
      (Concrete.pureExternal appConfig node call) ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .outside (.request call))).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land (.node address) now
          (Concrete.pureExternal appConfig node call))
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  let served :=
    Resonate.run { appConfig with unreliable := true } call
      (abstract.process .service)
  let abstractResult : Result Abstract.Pid State Message := {
    state := served.1
    send := Abstract.sends served.2
  }
  let abstractNext := abstract.land .service now abstractResult
  have habstractRequest :
      (Abstract.Pid.outside, .service, Message.request call) ∈
        abstract.network :=
    related.requests address call hrequest
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now
          (.receive .outside (.request call))).val := by
    simp [Abstract.step, abstractResult, served]
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now
          (.receive .outside (.request call)) abstractResult.send)
        abstractNext :=
    Step.process (Nat.le_trans related.time htime) rfl
      habstractRequest habstractResult
  refine ⟨[((.process .service now
      (.receive .outside (.request call)) abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩, ?_, rfl⟩
  have hpure :=
    external_key_none { appConfig with unreliable := true } call
      (abstract.process .service) hkey
  have hworkflowEq :
      (abstractNext.process .service).workflow =
        (abstract.process .service).workflow := by
    simpa [abstractNext, World.land, abstractResult, served] using
      hpure.2.1
  have hprocessEq :
      (concrete.land (.node address) now
        (Concrete.pureExternal appConfig node call)).process =
          concrete.process := by
    funext pid
    by_cases hp : pid = .node address
    · subst pid
      simp [World.land, Concrete.pureExternal, hnode]
    · simp [World.land, hp]
  change Related nodes appConfig config
    (concrete.land (.node address) now
      (Concrete.pureExternal appConfig node call)) abstractNext
  apply related_after_node_land hreachable related haddress hnode
      (event := .receive .outside (.request call)) htime hrequest hresult
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro knownKey hknownKey
    simpa [abstractNext, World.land, abstractResult, served] using
      external_keys_mono { appConfig with unreliable := true } call
        (abstract.process .service) knownKey hknownKey
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    refine ⟨physical, hphysical, ?_⟩
    intro other
    rw [hrep other]
    simpa [abstractNext, World.land, abstractResult, served] using
      (hpure.1 other).symm
  · rw [WorkflowAligned, hprocessEq]
    rw [hworkflowEq]
    exact related.workflow
  · intro physical currentAddress currentNode op flight pending
      hcurrentAddress hphysical hcurrentNode hflight hphase hversion
      hpending
    rw [hprocessEq] at hphysical hcurrentNode
    obtain ⟨howner, hpendingAbstract⟩ :=
      related.currentWorkflow physical currentAddress currentNode op flight
        pending hcurrentAddress hphysical hcurrentNode hflight hphase
        hversion hpending
    exact ⟨howner, by
      simpa only [hworkflowEq] using hpendingAbstract⟩
  · intro currentAddress currentNode knownKey hcurrentAddress hcurrentNode
      hknown
    rw [hprocessEq] at hcurrentNode
    have hold :=
      related.known currentAddress currentNode knownKey hcurrentAddress
        hcurrentNode hknown
    simpa [abstractNext, World.land, abstractResult, served] using
      external_keys_mono { appConfig with unreliable := true } call
        (abstract.process .service) knownKey hold
  · intro target request hsend
    simp [Concrete.pureExternal, Concrete.sendOutputs] at hsend
  · intro output hsend
    have houtput :
        output ∈
          (Resonate.run { appConfig with unreliable := true } call {}).2 := by
      simpa [Concrete.pureExternal, Concrete.sendOutputs] using hsend
    have hcovered := covered_sent abstract now served.1 served.2
    exact hcovered output (by
      simpa [served, hpure.2.2] using houtput)
  · intro currentAddress currentNode op flight hcurrentAddress hcurrentNode
      hflight
    rw [hprocessEq] at hcurrentNode
    obtain ⟨hwritten, hfailed⟩ :=
      related.activeReplies currentAddress currentNode op flight
        hcurrentAddress hcurrentNode hflight
    constructor
    · intro hreply
      obtain ⟨hknown, hcovered, hworkflow⟩ :=
        hwritten (by simpa [World.land] using hreply)
      exact ⟨by
        simpa [abstractNext, World.land, abstractResult, served] using
          external_keys_mono { appConfig with unreliable := true } call
            (abstract.process .service) flight.key hknown,
        hcovered.land abstractResult,
        by
          rcases hworkflow with hnone | hpending
          · exact .inl hnone
          · exact .inr (by
              simpa only [hworkflowEq] using hpending)⟩
    · intro hreply
      exact (hfailed (by simpa [World.land] using hreply)).land
        abstractResult

theorem simulate_idle_scan_capture
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    (howner : address = config.workflowNode)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    (hblocked : node.workflowBlocked = false)
    (hflights : node.flights = [])
    (hpendingNode : node.pending = [])
    {key : DocumentKey} (hknownHead : node.known.head? = some key)
    {now : Time} (htime : concrete.now ≤ now)
    (hresult :
      ({
        state := .node { node with pending := [.scan key now] }
        send := []
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now .timeout).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land (.node address) now {
          state := .node { node with pending := [.scan key now] }
          send := []
        })
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  subst address
  have habstractPending :
      (abstract.process .service).workflow.pending = [] := by
    simpa [WorkflowAligned, haddress, hnode, hblocked, hflights,
      hpendingNode] using related.workflow
  have hknownMem : key ∈ node.known := by
    cases hknown : node.known with
    | nil => simp [hknown] at hknownHead
    | cons first rest =>
        simp [hknown] at hknownHead
        subst first
        simp [hknown]
  have habstractKey :
      key ∈ (abstract.process .service).store.keys :=
    related.known config.workflowNode node key haddress hnode hknownMem
  let captured : State := {
    abstract.process .service with
      workflow := { pending := [.scan key now] }
  }
  let abstractResult : Result Abstract.Pid State Message := {
    state := captured
    send := []
  }
  let abstractNext := abstract.land .service now abstractResult
  have hchoice :
      (captured, []) ∈
        (Resonate.runTimeoutChoices
          { appConfig with unreliable := true } now
          (abstract.process .service)).val := by
    simp [Resonate.runTimeoutChoices, habstractPending, captured,
      habstractKey]
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now .timeout).val := by
    simp only [Abstract.step]
    exact List.mem_map.mpr ⟨(captured, []), hchoice, by
      simp [abstractResult, Abstract.sends]⟩
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now .timeout []) abstractNext :=
    Step.process (event := .timeout)
      (Nat.le_trans related.time htime) rfl trivial habstractResult
  refine ⟨[((.process .service now .timeout []), abstractNext)],
    ⟨habstractStep, trivial⟩, ?_, rfl⟩
  let nextNode : Concrete.Node :=
    { node with pending := [.scan key now] }
  have hnextFlights : nextNode.flights = [] := by
    simp [nextNode, hflights]
  have hprocessWorkflow :
      (concrete.land (.node config.workflowNode) now {
        state := .node nextNode
        send := []
      }).process (.node config.workflowNode) = .node nextNode := by
    simp [World.land]
  change Related nodes appConfig config
    (concrete.land (.node config.workflowNode) now {
      state := .node nextNode
      send := []
    }) abstractNext
  apply related_after_node_land hreachable related haddress hnode
      (event := .timeout) htime trivial hresult
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro knownKey hknown
    simpa [abstractNext, World.land, abstractResult, captured] using hknown
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    refine ⟨physical, by simpa [World.land] using hphysical, ?_⟩
    intro other
    simpa [abstractNext, World.land, abstractResult, captured] using
      hrep other
  · simp only [WorkflowAligned, haddress]
    refine ⟨nextNode, hprocessWorkflow, Or.inr (Or.inl ⟨hnextFlights, ?_⟩)⟩
    simp [abstractNext, World.land, abstractResult, captured, nextNode]
  · intro physical currentAddress currentNode op flight pending
      hcurrentAddress hphysical hcurrentNode hflight hphase hversion
      hpending
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextFlights] at hflight
      contradiction
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress
        hcurrentNodeOld hflight)).elim
  · intro currentAddress currentNode knownKey hcurrentAddress hcurrentNode
      hknown
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      have hold :=
        related.known config.workflowNode node knownKey haddress hnode hknown
      simpa [abstractNext, World.land, abstractResult, captured] using hold
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have hold :=
        related.known currentAddress currentNode knownKey hcurrentAddress
          hcurrentNodeOld hknown
      simpa [abstractNext, World.land, abstractResult, captured] using hold
  · intro target call hsend
    contradiction
  · intro output hsend
    contradiction
  · intro currentAddress currentNode op flight hcurrentAddress hcurrentNode
      hflight
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextFlights] at hflight
      contradiction
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress
        hcurrentNodeOld hflight)).elim

theorem related_after_start_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    (howner : address = config.workflowNode)
    {node base : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    (hbaseNext : base.nextOp = node.nextOp)
    (hbaseFlights : base.flights = [])
    (hbaseKnown : base.known = node.known)
    {transaction : Concrete.Transaction} {key : DocumentKey}
    (hstage :
      base.workflowBlocked = true ∨
        FlightWorkflowStage ({ key, transaction } : Concrete.Flight)
          base.pending (abstract.process .service).workflow.pending)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      Concrete.start base transaction key ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now
        (Concrete.start base transaction key)) abstract := by
  subst address
  let flight : Concrete.Flight := { key, transaction }
  let nextNode := (base.await flight (.get key)).1
  have hstartState :
      (Concrete.start base transaction key).state = .node nextNode := by
    rfl
  have hnextFlights :
      nextNode.flights = [(base.nextOp, flight)] := by
    simp [nextNode, Concrete.Node.await, hbaseFlights]
  have hnextKnown : nextNode.known = node.known := by
    simp [nextNode, Concrete.Node.await, hbaseKnown]
  have hnextPending : nextNode.pending = base.pending := by
    simp [nextNode, Concrete.Node.await]
  have hprocessWorkflow :
      (concrete.land (.node config.workflowNode) now
        (Concrete.start base transaction key)).process
          (.node config.workflowNode) = .node nextNode := by
    simp [World.land, hstartState]
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
  · simp only [WorkflowAligned, haddress]
    refine ⟨nextNode, hprocessWorkflow, ?_⟩
    rcases hstage with hblocked | hflightStage
    · left
      simpa [nextNode, Concrete.Node.await] using hblocked
    · right
      right
      refine ⟨base.nextOp, flight, by simp [hnextFlights], ?_⟩
      rw [hnextPending]
      simpa [flight] using hflightStage
  · intro physical currentAddress currentNode op currentFlight pending
      hcurrentAddress hphysical hcurrentNode hcurrentFlight hphase hversion
      hpending
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
      cases hcurrentFlight
      simp [flight] at hphase
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress
        hcurrentNodeOld hcurrentFlight)).elim
  · intro currentAddress currentNode knownKey hcurrentAddress hcurrentNode
      hknown
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextKnown] at hknown
      exact related.known config.workflowNode node knownKey haddress hnode
        hknown
    · exact related.known currentAddress currentNode knownKey
        hcurrentAddress (by simpa [World.land, heq] using hcurrentNode)
        hknown
  · intro target call hsend
    simp [Concrete.start, Concrete.Node.await] at hsend
  · intro output hsend
    simp [Concrete.start, Concrete.Node.await] at hsend
  · intro currentAddress currentNode op currentFlight hcurrentAddress
      hcurrentNode hcurrentFlight
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
      cases hcurrentFlight
      have hnoReply (reply : StoreReply)
          (hreply :
            (Concrete.Pid.store, .node config.workflowNode,
              .storeReply { op := base.nextOp, payload := reply }) ∈
                concrete.network) : False := by
        cases reply with
        | got loadedKey loaded =>
            have hget :=
              reachable_got_replies_have_request hreachable hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hget
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | written =>
            obtain ⟨putKey, document, expected, hput⟩ :=
              reachable_put_replies_have_request hreachable (.inl rfl)
                hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hput
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | conflict =>
            obtain ⟨putKey, document, expected, hput⟩ :=
              reachable_put_replies_have_request hreachable
                (.inr (.inl rfl)) hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hput
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | failed =>
            obtain ⟨putKey, document, expected, hput⟩ :=
              reachable_put_replies_have_request hreachable
                (.inr (.inr rfl)) hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hput
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
      constructor
      · intro hreply
        simp only [World.land, List.mem_append] at hreply
        rcases hreply with hold | hnew
        · exact (hnoReply .written hold).elim
        · simp [Concrete.start, Concrete.Node.await] at hnew
      · intro hreply
        simp only [World.land, List.mem_append] at hreply
        rcases hreply with hold | hnew
        · exact (hnoReply .failed hold).elim
        · simp [Concrete.start, Concrete.Node.await] at hnew
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress
        hcurrentNodeOld hcurrentFlight)).elim

theorem related_after_loading_await_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    (howner : address = config.workflowNode)
    {node base : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    (hbaseNext : base.nextOp = node.nextOp)
    (hbaseFlights : base.flights = [])
    (hbaseKnown : base.known = node.known)
    {flight : Concrete.Flight}
    (hloading : flight.phase = .loading)
    (hstage :
      base.workflowBlocked = true ∨
        FlightWorkflowStage flight base.pending
          (abstract.process .service).workflow.pending)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      ({
        state := .node (base.await flight (.get flight.key)).1
        send := [(base.await flight (.get flight.key)).2]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now {
        state := .node (base.await flight (.get flight.key)).1
        send := [(base.await flight (.get flight.key)).2]
      }) abstract := by
  subst address
  let nextNode := (base.await flight (.get flight.key)).1
  have hnextFlights :
      nextNode.flights = [(base.nextOp, flight)] := by
    simp [nextNode, Concrete.Node.await, hbaseFlights]
  have hnextKnown : nextNode.known = node.known := by
    simp [nextNode, Concrete.Node.await, hbaseKnown]
  have hnextPending : nextNode.pending = base.pending := by
    simp [nextNode, Concrete.Node.await]
  have hprocessWorkflow :
      (concrete.land (.node config.workflowNode) now {
        state := .node (base.await flight (.get flight.key)).1
        send := [(base.await flight (.get flight.key)).2]
      }).process (.node config.workflowNode) = .node nextNode := by
    simp [World.land, nextNode]
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
  · simp only [WorkflowAligned, haddress]
    refine ⟨nextNode, hprocessWorkflow, ?_⟩
    rcases hstage with hblocked | hflightStage
    · left
      simpa [nextNode, Concrete.Node.await] using hblocked
    · right
      right
      refine ⟨base.nextOp, flight, by simp [hnextFlights], ?_⟩
      rw [hnextPending]
      exact hflightStage
  · intro physical currentAddress currentNode op currentFlight pending
      hcurrentAddress hphysical hcurrentNode hcurrentFlight hphase hversion
      hpending
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
      cases hcurrentFlight
      rw [hloading] at hphase
      contradiction
    · have old :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress old
        hcurrentFlight)).elim
  · intro currentAddress currentNode knownKey hcurrentAddress hcurrentNode
      hknown
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextKnown] at hknown
      exact related.known config.workflowNode node knownKey haddress hnode
        hknown
    · exact related.known currentAddress currentNode knownKey hcurrentAddress
        (by simpa [World.land, heq] using hcurrentNode) hknown
  · intro target call hsend
    simp [Concrete.Node.await] at hsend
  · intro output hsend
    simp [Concrete.Node.await] at hsend
  · intro currentAddress currentNode op currentFlight hcurrentAddress
      hcurrentNode hcurrentFlight
    by_cases heq : currentAddress = config.workflowNode
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
      cases hcurrentFlight
      have hnoReply (reply : StoreReply)
          (hreply :
            (Concrete.Pid.store, .node config.workflowNode,
              .storeReply { op := base.nextOp, payload := reply }) ∈
                concrete.network) : False := by
        cases reply with
        | got loadedKey loaded =>
            have hget :=
              reachable_got_replies_have_request hreachable hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hget
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | written =>
            obtain ⟨putKey, document, expected, hput⟩ :=
              reachable_put_replies_have_request hreachable (.inl rfl)
                hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hput
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | conflict =>
            obtain ⟨putKey, document, expected, hput⟩ :=
              reachable_put_replies_have_request hreachable
                (.inr (.inl rfl)) hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hput
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | failed =>
            obtain ⟨putKey, document, expected, hput⟩ :=
              reachable_put_replies_have_request hreachable
                (.inr (.inr rfl)) hreply
            have hfresh :=
              (reachable_rpc_ids hreachable).fresh haddress hnode hput
            rw [← hbaseNext] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
      constructor
      · intro hreply
        simp only [World.land, List.mem_append] at hreply
        rcases hreply with hold | hnew
        · exact (hnoReply .written hold).elim
        · simp [Concrete.Node.await] at hnew
      · intro hreply
        simp only [World.land, List.mem_append] at hreply
        rcases hreply with hold | hnew
        · exact (hnoReply .failed hold).elim
        · simp [Concrete.Node.await] at hnew
    · have old :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress old
        hcurrentFlight)).elim

theorem related_after_written_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node next : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (htake : node.takeFlight op = (some flight, next))
    (hphase : flight.phase = .writing)
    {now : Time} (htime : concrete.now ≤ now)
    (hreply :
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .written }) ∈ concrete.network)
    (hresult :
      ({
        state := .node {
          next.remember flight.key with
            pending := flight.continuations ++ next.pending
        }
        send := Concrete.sendOutputs flight.selected
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .store
            (.storeReply { op, payload := .written }))).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now {
        state := .node {
          next.remember flight.key with
            pending := flight.continuations ++ next.pending
        }
        send := Concrete.sendOutputs flight.selected
      }) abstract := by
  have hflight : (op, flight) ∈ node.flights :=
    takeFlight_some_mem htake
  have howner :=
    reachable_flight_owner hreachable haddress hnode hflight
  obtain ⟨serialNode, hserialNode, hserial⟩ :=
    reachable_nodes_serial hreachable address haddress
  rw [hnode] at hserialNode
  cases Concrete.Local.node.inj hserialNode
  have hnextFlights : next.flights = [] := by
    have hfilter := takeFlight_filter_empty_of_some hserial
      (congrArg Prod.fst htake)
    have hnext := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.flights) htake
    simp [Concrete.Node.takeFlight, hfilter] at hnext
    exact hnext
  have hnextPending : next.pending = node.pending := by
    have hnext := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.pending) htake
    simpa [Concrete.Node.takeFlight] using hnext.symm
  have hnextBlocked : next.workflowBlocked = node.workflowBlocked := by
    have hnext := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.workflowBlocked) htake
    simpa [Concrete.Node.takeFlight] using hnext.symm
  have hnextKnown : next.known = node.known := by
    have hnext := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.known) htake
    simpa [Concrete.Node.takeFlight] using hnext.symm
  obtain ⟨hknownKey, hcovered, hworkflowReply⟩ :=
    (related.activeReplies address node op flight haddress hnode hflight).1
      hreply
  let nextNode : Concrete.Node := {
    next.remember flight.key with
      pending := flight.continuations ++ next.pending
  }
  have hnextNodeFlights : nextNode.flights = [] := by
    simp [nextNode, Concrete.Node.remember]
    split <;> exact hnextFlights
  have hnextNodeBlocked :
      nextNode.workflowBlocked = next.workflowBlocked := by
    simp [nextNode, Concrete.Node.remember]
    split <;> rfl
  have hprocessWorkflow :
      (concrete.land (.node address) now {
        state := .node nextNode
        send := Concrete.sendOutputs flight.selected
      }).process (.node address) = .node nextNode := by
    simp [World.land]
  have hworkflowNext :
      nextNode.workflowBlocked = true ∨
        (abstract.process .service).workflow.pending =
          nextNode.pending := by
    cases htransaction : flight.transaction with
    | external call =>
        have hvalid :=
          related.flights address node op flight haddress hnode hflight
        rw [FlightValid, hphase] at hvalid
        obtain ⟨document, hdocument, hselected⟩ := hvalid.2
        rw [htransaction] at hselected
        have hcontinuations :
            flight.continuations = [] :=
          Selected.external_continuations_nil hselected
        by_cases hblocked : node.workflowBlocked = true
        · left
          exact hnextNodeBlocked.trans (hnextBlocked.trans hblocked)
        · have hblockedFalse : node.workflowBlocked = false := by
            cases ht : node.workflowBlocked <;> simp_all
          right
          have hold := related.workflow
          simp only [WorkflowAligned, howner ▸ haddress] at hold
          obtain ⟨workflowNode, hworkflowNode, haligned⟩ := hold
          rw [← howner, hnode] at hworkflowNode
          cases Concrete.Local.node.inj hworkflowNode
          rcases haligned with hbad | hidle | hactive
          · contradiction
          · rw [hidle.1] at hflight
            contradiction
          · obtain ⟨activeOp, activeFlight, hactiveFlight, hstage⟩ :=
              hactive
            have hpairs :=
              NodeSerial.eq_of_mem hserial hactiveFlight hflight
            cases hpairs
            calc
              (abstract.process .service).workflow.pending = node.pending := by
                simpa [FlightWorkflowStage, htransaction] using hstage
              _ = nextNode.pending := by
                simp [nextNode, hcontinuations, hnextPending]
    | work item instant rest =>
        have hclean :=
          reachable_internal_flight_clean hreachable haddress hnode hflight
            (by simp [htransaction, Concrete.Transaction.isExternal])
        rcases hworkflowReply with hnone | hpending
        · simp [TransactionPending, htransaction] at hnone
        · right
          simpa [nextNode, hnextPending, hclean.1] using hpending
    | scan key instant rest =>
        have hclean :=
          reachable_internal_flight_clean hreachable haddress hnode hflight
            (by simp [htransaction, Concrete.Transaction.isExternal])
        rcases hworkflowReply with hnone | hpending
        · simp [TransactionPending, htransaction] at hnone
        · right
          simpa [nextNode, hnextPending, hclean.1] using hpending
  apply related_after_node_land hreachable related haddress hnode
      (event := .receive .store
        (.storeReply { op, payload := .written }))
      htime hreply hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
  · simp only [WorkflowAligned, howner ▸ haddress]
    refine ⟨nextNode, by
      simp [World.land, howner.symm, nextNode], ?_⟩
    rcases hworkflowNext with hblocked | hpending
    · exact .inl hblocked
    · exact .inr (.inl ⟨hnextNodeFlights, hpending⟩)
  · intro physical currentAddress currentNode currentOp currentFlight pending
      hcurrentAddress hphysical hcurrentNode hcurrentFlight hcurrentPhase
      hversion hpending
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextNodeFlights] at hcurrentFlight
      contradiction
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have hcurrentOwner :=
        reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
          hcurrentFlight
      exact (heq (hcurrentOwner.trans howner.symm)).elim
  · intro currentAddress currentNode key hcurrentAddress hcurrentNode hkey
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      simp only [nextNode, Concrete.Node.remember] at hkey
      split at hkey
      · exact related.known address node key haddress hnode
          (by simpa [hnextKnown] using hkey)
      · simp only [List.mem_append, List.mem_singleton] at hkey
        rcases hkey with hold | hnew
        · exact related.known address node key haddress hnode
            (by simpa [hnextKnown] using hold)
        · simpa [hnew] using hknownKey
    · exact related.known currentAddress currentNode key hcurrentAddress
        (by simpa [World.land, heq] using hcurrentNode) hkey
  · intro target call hsend
    simp [Concrete.sendOutputs] at hsend
  · intro output hsend
    exact hcovered output (by
      simpa [Concrete.sendOutputs] using hsend)
  · intro currentAddress currentNode currentOp currentFlight hcurrentAddress
      hcurrentNode hcurrentFlight
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessWorkflow] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextNodeFlights] at hcurrentFlight
      contradiction
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have hcurrentOwner :=
        reachable_flight_owner hreachable hcurrentAddress hcurrentNodeOld
          hcurrentFlight
      exact (heq (hcurrentOwner.trans howner.symm)).elim

theorem related_after_decide_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node remaining : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (htake : node.takeFlight op = (some flight, remaining))
    (hphase : flight.phase = .loading)
    {loaded : Option (Document flight.key × Concrete.Version)}
    {candidate : Concrete.Candidate flight.key}
    (hselect : Concrete.select appConfig flight loaded = some candidate)
    {now : Time} (htime : concrete.now ≤ now)
    (hreply :
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .got flight.key loaded }) ∈
          concrete.network)
    (hresult :
      Concrete.decide appConfig remaining flight loaded ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .store
            (.storeReply { op, payload := .got flight.key loaded }))).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now
        (Concrete.decide appConfig remaining flight loaded)) abstract := by
  have hflight : (op, flight) ∈ node.flights := takeFlight_some_mem htake
  have howner := reachable_flight_owner hreachable haddress hnode hflight
  obtain ⟨serialNode, hserialNode, hserial⟩ :=
    reachable_nodes_serial hreachable address haddress
  rw [hnode] at hserialNode
  cases Concrete.Local.node.inj hserialNode
  have hremainingFlights : remaining.flights = [] := by
    have hfilter := takeFlight_filter_empty_of_some hserial
      (congrArg Prod.fst htake)
    have hx := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.flights) htake
    simp [Concrete.Node.takeFlight, hfilter] at hx
    exact hx
  have hremainingPending : remaining.pending = node.pending := by
    have hx := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.pending) htake
    simpa [Concrete.Node.takeFlight] using hx.symm
  have hremainingKnown : remaining.known = node.known := by
    have hx := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.known) htake
    simpa [Concrete.Node.takeFlight] using hx.symm
  have hremainingBlocked :
      remaining.workflowBlocked = node.workflowBlocked := by
    have hx := congrArg
      (fun pair : Option Concrete.Flight × Concrete.Node =>
        pair.2.workflowBlocked) htake
    simpa [Concrete.Node.takeFlight] using hx.symm
  let writing : Concrete.Flight := {
    flight with
      loaded
      document := some candidate.document
      selected := candidate.outputs
      continuations := candidate.continuations
      phase := .writing
  }
  let nextNode := (remaining.await writing
    (.put flight.key candidate.document (loaded.map (·.2)))).1
  have hnextFlights :
      nextNode.flights = [(remaining.nextOp, writing)] := by
    simp [nextNode, Concrete.Node.await, hremainingFlights]
  have holdWorkflow := related.workflow
  simp only [WorkflowAligned, howner ▸ haddress] at holdWorkflow
  obtain ⟨workflowNode, hworkflowNode, haligned⟩ := holdWorkflow
  rw [← howner, hnode] at hworkflowNode
  cases Concrete.Local.node.inj hworkflowNode
  have hworkflowCase :
      node.workflowBlocked = true ∨
        FlightWorkflowStage flight node.pending
          (abstract.process .service).workflow.pending := by
    rcases haligned with hblocked | hidle | hactive
    · exact .inl hblocked
    · rw [hidle.1] at hflight
      contradiction
    · obtain ⟨activeOp, activeFlight, hactiveFlight, hactiveStage⟩ := hactive
      have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
      cases hpairs
      exact .inr hactiveStage
  apply related_after_node_land hreachable related haddress hnode
      (event := .receive .store
        (.storeReply { op, payload := .got flight.key loaded }))
      htime hreply hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
  · simp only [WorkflowAligned, howner ▸ haddress]
    refine ⟨nextNode, by
      simp [Concrete.decide, hselect, nextNode, writing, World.land,
        howner.symm], ?_⟩
    rcases hworkflowCase with hblocked | hstage
    · left
      simpa [nextNode, Concrete.Node.await, hremainingBlocked] using hblocked
    · right
      right
      refine ⟨remaining.nextOp, writing, by simp [hnextFlights], ?_⟩
      cases ht : flight.transaction with
      | external call =>
          simpa [writing, nextNode, Concrete.Node.await,
            FlightWorkflowStage, ht, hremainingPending] using hstage
      | work item instant rest =>
          simpa [writing, nextNode, Concrete.Node.await,
            FlightWorkflowStage, ht, hphase] using Or.inl hstage
      | scan key instant rest =>
          simpa [writing, nextNode, Concrete.Node.await,
            FlightWorkflowStage, ht, hphase] using Or.inl hstage
  · intro physical currentAddress currentNode currentOp currentFlight pending
      hcurrentAddress hphysical hcurrentNode hcurrentFlight hcurrentPhase
      hversion hpending
    by_cases heq : currentAddress = address
    · subst currentAddress
      have hstate : currentNode = nextNode := by
        simp [Concrete.decide, hselect, World.land, nextNode, writing]
          at hcurrentNode
        exact hcurrentNode.symm
      subst currentNode
      simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
      cases hcurrentFlight
      cases ht : flight.transaction with
      | external call => simp [writing, ht, TransactionPending] at hpending
      | work item instant rest =>
          rcases hworkflowCase with hblocked | hstage
          · have hclean := reachable_internal_flight_clean hreachable
              haddress hnode hflight (by rw [ht]; rfl)
            rw [hblocked] at hclean
            cases hclean.2
          · have : (abstract.process .service).workflow.pending =
                .work item instant :: rest := by
              simpa [FlightWorkflowStage, ht, hphase] using hstage
            have hpendingEq : pending = .work item instant :: rest := by
              symm
              simpa [writing, ht, TransactionPending] using hpending
            exact ⟨howner, by
              simpa [hpendingEq] using this⟩
      | scan key instant rest =>
          rcases hworkflowCase with hblocked | hstage
          · have hclean := reachable_internal_flight_clean hreachable
              haddress hnode hflight (by rw [ht]; rfl)
            rw [hblocked] at hclean
            cases hclean.2
          · have : (abstract.process .service).workflow.pending =
                .scan key instant :: rest := by
              simpa [FlightWorkflowStage, ht, hphase] using hstage
            have hpendingEq : pending = .scan key instant :: rest := by
              symm
              simpa [writing, ht, TransactionPending] using hpending
            exact ⟨howner, by
              simpa [hpendingEq] using this⟩
    · have old :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have owner := reachable_flight_owner hreachable hcurrentAddress old
        hcurrentFlight
      exact (heq (owner.trans howner.symm)).elim
  · intro currentAddress currentNode key hcurrentAddress hcurrentNode hkey
    by_cases heq : currentAddress = address
    · subst currentAddress
      have hstate : currentNode = nextNode := by
        simp [Concrete.decide, hselect, World.land, nextNode, writing]
          at hcurrentNode
        exact hcurrentNode.symm
      subst currentNode
      exact related.known address node key haddress hnode
        (by simpa [nextNode, Concrete.Node.await, hremainingKnown] using hkey)
    · exact related.known currentAddress currentNode key hcurrentAddress
        (by simpa [World.land, heq] using hcurrentNode) hkey
  · intro target call hsend
    simp [Concrete.decide, hselect, Concrete.Node.await] at hsend
  · intro output hsend
    simp [Concrete.decide, hselect, Concrete.Node.await] at hsend
  · intro currentAddress currentNode currentOp currentFlight hcurrentAddress
      hcurrentNode hcurrentFlight
    by_cases heq : currentAddress = address
    · subst currentAddress
      have hstate : currentNode = nextNode := by
        simp [Concrete.decide, hselect, World.land, nextNode, writing]
          at hcurrentNode
        exact hcurrentNode.symm
      subst currentNode
      simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
      cases hcurrentFlight
      have hnoReply (reply : StoreReply)
          (hterminal :
            (Concrete.Pid.store, .node address,
              .storeReply { op := remaining.nextOp, payload := reply }) ∈
                concrete.network) : False := by
        cases reply with
        | got key value =>
            have hget := reachable_got_replies_have_request hreachable
              hterminal
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hget
            have hn := takeFlight_nextOp htake
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | written =>
            have horigin := reachable_put_replies_have_request hreachable
              (.inl rfl) hterminal
            obtain ⟨putKey, document, expected, hput⟩ := horigin
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hput
            have hn := takeFlight_nextOp htake
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | conflict =>
            have horigin := reachable_put_replies_have_request hreachable
              (.inr (.inl rfl)) hterminal
            obtain ⟨putKey, document, expected, hput⟩ := horigin
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hput
            have hn := takeFlight_nextOp htake
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | failed =>
            have horigin := reachable_put_replies_have_request hreachable
              (.inr (.inr rfl)) hterminal
            obtain ⟨putKey, document, expected, hput⟩ := horigin
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hput
            have hn := takeFlight_nextOp htake
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
      constructor
      · intro hterminal
        simp only [World.land, List.mem_append] at hterminal
        rcases hterminal with hold | hnew
        · exact (hnoReply .written hold).elim
        · simp [Concrete.decide, hselect, Concrete.Node.await] at hnew
      · intro hterminal
        simp only [World.land, List.mem_append] at hterminal
        rcases hterminal with hold | hnew
        · exact (hnoReply .failed hold).elim
        · simp [Concrete.decide, hselect, Concrete.Node.await] at hnew
    · have old :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have owner := reachable_flight_owner hreachable hcurrentAddress old
        hcurrentFlight
      exact (heq (owner.trans howner.symm)).elim

theorem related_after_terminal_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node nextNode : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hnextFlights : nextNode.flights = [])
    (hnextKnown : nextNode.known = node.known)
    (hworkflow :
      nextNode.workflowBlocked = true ∨
        (abstract.process .service).workflow.pending = nextNode.pending)
    {outputs : List Output} (hcovered : Covered abstract outputs)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      ({
        state := .node nextNode
        send := Concrete.sendOutputs outputs
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now {
        state := .node nextNode
        send := Concrete.sendOutputs outputs
      }) abstract := by
  have howner :=
    reachable_flight_owner hreachable haddress hnode hflight
  have hprocessNode :
      (concrete.land (.node address) now {
        state := .node nextNode
        send := Concrete.sendOutputs outputs
      }).process (.node address) = .node nextNode := by
    simp [World.land]
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
  · simp only [WorkflowAligned, howner ▸ haddress]
    refine ⟨nextNode, by
      simpa [howner.symm] using hprocessNode, ?_⟩
    rcases hworkflow with hblocked | hpending
    · exact .inl hblocked
    · exact .inr (.inl ⟨hnextFlights, hpending⟩)
  · intro physical currentAddress currentNode currentOp currentFlight pending
      hcurrentAddress hphysical hcurrentNode hcurrentFlight hphase hversion
      hpending
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessNode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextFlights] at hcurrentFlight
      contradiction
    · have hold :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have currentOwner :=
        reachable_flight_owner hreachable hcurrentAddress hold hcurrentFlight
      exact (heq (currentOwner.trans howner.symm)).elim
  · intro currentAddress currentNode key hcurrentAddress hcurrentNode hkey
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessNode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      exact related.known address node key haddress hnode
        (by simpa [hnextKnown] using hkey)
    · exact related.known currentAddress currentNode key hcurrentAddress
        (by simpa [World.land, heq] using hcurrentNode) hkey
  · intro target call hsend
    simp [Concrete.sendOutputs] at hsend
  · intro output hsend
    exact hcovered output (by
      simpa [Concrete.sendOutputs] using hsend)
  · intro currentAddress currentNode currentOp currentFlight hcurrentAddress
      hcurrentNode hcurrentFlight
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessNode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextFlights] at hcurrentFlight
      contradiction
    · have hold :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have currentOwner :=
        reachable_flight_owner hreachable hcurrentAddress hold hcurrentFlight
      exact (heq (currentOwner.trans howner.symm)).elim

theorem workflow_after_external_flight_removed
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node remaining : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (htake : node.takeFlight op = (some flight, remaining))
    {call : Call} (htransaction : flight.transaction = .external call) :
    remaining.workflowBlocked = true ∨
      (abstract.process .service).workflow.pending = remaining.pending := by
  have hflight := takeFlight_some_mem htake
  have howner :=
    reachable_flight_owner hreachable haddress hnode hflight
  obtain ⟨serialNode, hserialNode, hserial⟩ :=
    reachable_nodes_serial hreachable address haddress
  rw [hnode] at hserialNode
  cases Concrete.Local.node.inj hserialNode
  have hold := related.workflow
  simp only [WorkflowAligned, howner ▸ haddress] at hold
  obtain ⟨workflowNode, hworkflowNode, haligned⟩ := hold
  rw [← howner, hnode] at hworkflowNode
  cases Concrete.Local.node.inj hworkflowNode
  rcases haligned with hblocked | hidle | hactive
  · left
    rw [takeFlight_blocked htake]
    exact hblocked
  · rw [hidle.1] at hflight
    contradiction
  · obtain ⟨activeOp, activeFlight, hactiveFlight, hstage⟩ := hactive
    have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
    cases hpairs
    right
    rw [takeFlight_pending htake]
    simpa [FlightWorkflowStage, htransaction] using hstage

theorem simulate_external_shed_terminal_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node nextNode : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    {call : Call} (htransaction : flight.transaction = .external call)
    (hnextFlights : nextNode.flights = [])
    (hnextKnown : nextNode.known = node.known)
    (hworkflow :
      nextNode.workflowBlocked = true ∨
        (abstract.process .service).workflow.pending = nextNode.pending)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      ({
        state := .node nextNode
        send := Concrete.sendOutputs [Resonate.unavailable call]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land (.node address) now {
          state := .node nextNode
          send := Concrete.sendOutputs [Resonate.unavailable call]
        }) (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  let shed := Resonate.runShed call (abstract.process .service)
  let abstractResult : Result Abstract.Pid State Message := {
    state := shed.1
    send := Abstract.sends shed.2
  }
  let abstractNext := abstract.land .service now abstractResult
  have hrequest :
      (Abstract.Pid.outside, .service, Message.request call) ∈
        abstract.network := by
    exact related.requests address call
      (reachable_flight_request_origins hreachable haddress hnode hflight
        htransaction)
  have habstractResult :
      abstractResult ∈
        (Abstract.step { appConfig with unreliable := true }
          .service (abstract.process .service) now
          (.receive .outside (.request call))).val := by
    simp [Abstract.step, abstractResult, shed]
  have habstractStep :
      Step AModel { appConfig with unreliable := true } abstract
        (.process .service now
          (.receive .outside (.request call)) abstractResult.send)
        abstractNext :=
    Step.process (Nat.le_trans related.time htime) rfl hrequest
      habstractResult
  refine ⟨[((.process .service now
      (.receive .outside (.request call)) abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩, ?_, rfl⟩
  change Related nodes appConfig config
    (concrete.land (.node address) now {
      state := .node nextNode
      send := Concrete.sendOutputs [Resonate.unavailable call]
    }) abstractNext
  have howner :=
    reachable_flight_owner hreachable haddress hnode hflight
  have hprocessNode :
      (concrete.land (.node address) now {
        state := .node nextNode
        send := Concrete.sendOutputs [Resonate.unavailable call]
      }).process (.node address) = .node nextNode := by
    simp [World.land]
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult
  · simp [abstractNext, World.land]
  · intro message hmessage
    exact List.mem_append_left _ hmessage
  · intro key hkey
    simpa [abstractNext, World.land, abstractResult, shed,
      Resonate.runShed] using hkey
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    refine ⟨physical, by simpa [World.land] using hphysical, ?_⟩
    simpa [abstractNext, World.land, abstractResult, shed,
      Resonate.runShed] using hrep
  · simp only [WorkflowAligned, howner ▸ haddress]
    refine ⟨nextNode, by
      simpa [howner.symm] using hprocessNode, ?_⟩
    rcases hworkflow with hblocked | hpending
    · exact .inl hblocked
    · exact .inr (.inl ⟨hnextFlights, by
        simpa [abstractNext, World.land, abstractResult, shed,
          Resonate.runShed] using hpending⟩)
  · intro physical currentAddress currentNode currentOp currentFlight pending
      hcurrentAddress hphysical hcurrentNode hcurrentFlight hphase hversion
      hpending
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessNode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextFlights] at hcurrentFlight
      contradiction
    · have hold :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have currentOwner :=
        reachable_flight_owner hreachable hcurrentAddress hold hcurrentFlight
      exact (heq (currentOwner.trans howner.symm)).elim
  · intro currentAddress currentNode key hcurrentAddress hcurrentNode hkey
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessNode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      have hknown :=
        related.known address node key haddress hnode
          (by simpa [hnextKnown] using hkey)
      simpa [abstractNext, World.land, abstractResult, shed,
        Resonate.runShed] using hknown
    · have old :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have hknown :=
        related.known currentAddress currentNode key hcurrentAddress old hkey
      simpa [abstractNext, World.land, abstractResult, shed,
        Resonate.runShed] using hknown
  · intro target request hsend
    simp [Concrete.sendOutputs] at hsend
  · intro output hsend
    simp [Concrete.sendOutputs] at hsend
    subst output
    exact covered_sent abstract now shed.1 shed.2 _ (by
      simp [shed, Resonate.runShed])
  · intro currentAddress currentNode currentOp currentFlight hcurrentAddress
      hcurrentNode hcurrentFlight
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hprocessNode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rw [hnextFlights] at hcurrentFlight
      contradiction
    · have hold :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      have currentOwner :=
        reachable_flight_owner hreachable hcurrentAddress hold hcurrentFlight
      exact (heq (currentOwner.trans howner.symm)).elim

theorem simulate_node_process
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land (.node address) now result)
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  have hinert
      (hmember :
        ({
          state := .node node
          send := []
        } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
          (Concrete.step appConfig config (.node address) (.node node)
            now event).val) :
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land (.node address) now {
            state := .node node
            send := []
          }) (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = [] :=
    ⟨[], trivial,
      related_after_inert_node hreachable related haddress hnode htime
        hvalid hmember,
      rfl⟩
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      next hguard =>
        simp [Outcomes.one] at hresult
        subst result
        exact hinert (by simp [Concrete.step, hguard, Outcomes.one])
      next hguard =>
        have hguard' :
            address = config.workflowNode ∧
              node.workflowBlocked = false ∧ node.flights = [] := by
          simp at hguard
          exact ⟨hguard.1.1, hguard.1.2, hguard.2⟩
        obtain ⟨howner, hblocked, hflights⟩ := hguard'
        cases hpending : node.pending with
        | nil =>
            simp only [hpending] at hresult
            cases hknown : node.known.head? with
            | none =>
                simp [hknown, Outcomes.one] at hresult
                subst result
                exact hinert (by
                  simp [Concrete.step, hguard, hpending, hknown,
                    Outcomes.one])
            | some key =>
                simp [hknown, Outcomes.one] at hresult
                subst result
                exact simulate_idle_scan_capture hreachable related haddress
                  howner hnode hblocked hflights hpending hknown htime
                  (by simp [Concrete.step, hguard, hpending, hknown,
                    Outcomes.one])
        | cons entry rest =>
            simp [hpending, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            have habstractPending :
                (abstract.process .service).workflow.pending =
                  entry :: rest := by
              simpa [WorkflowAligned, howner ▸ haddress, howner ▸ hnode,
                hblocked, hflights, hpending] using related.workflow
            cases entry with
            | work item instant =>
                exact ⟨[], trivial,
                  related_after_start_node hreachable related haddress howner
                    hnode (base := { node with pending := [] })
                    (by rfl) (by simp [hflights]) (by rfl)
                    (transaction := .work item instant rest)
                    (key := item.key)
                    (.inr (by
                      simpa [FlightWorkflowStage] using habstractPending))
                    (event := .timeout) htime trivial (by
                      simp [Concrete.step, hguard, hpending, Outcomes.one]
                      cases item <;> rfl),
                  rfl⟩
            | scan key instant =>
                exact ⟨[], trivial,
                  related_after_start_node hreachable related haddress howner
                    hnode (base := { node with pending := [] })
                    (by rfl) (by simp [hflights]) (by rfl)
                    (transaction := .scan key instant rest)
                    (key := key)
                    (.inr (by
                      simpa [FlightWorkflowStage] using habstractPending))
                    (event := .timeout) htime trivial (by
                      simp [Concrete.step, hguard, hpending, Outcomes.one]
                      rfl),
                  rfl⟩
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact hinert (by simp [Concrete.step, Outcomes.one])
      case outside.request call =>
        split at hresult
        next hguard =>
          simp [Outcomes.one] at hresult
          subst result
          exact hinert (by simp [Concrete.step, hguard, Outcomes.one])
        next hguard =>
          have hguard' :
              address = config.workflowNode ∧ node.flights = [] := by
            simp at hguard
            exact hguard
          obtain ⟨howner, hflights⟩ := hguard'
          cases hkey :
              (Concrete.Transaction.external call).key? with
          | none =>
              simp [hkey, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact simulate_pure_external_node hreachable related haddress
                hnode hkey htime hvalid (by
                  simp [Concrete.step, hguard, hkey,
                    Concrete.pureExternal, Outcomes.one])
          | some key =>
              simp [hkey, Concrete.start, Concrete.Node.await,
                Outcomes.one] at hresult
              subst result
              have hstage :
                  node.workflowBlocked = true ∨
                    FlightWorkflowStage
                      ({ key, transaction := .external call } :
                        Concrete.Flight)
                      node.pending
                      (abstract.process .service).workflow.pending := by
                by_cases hb : node.workflowBlocked = true
                · exact .inl hb
                · right
                  have hbfalse : node.workflowBlocked = false := by
                    cases ht : node.workflowBlocked <;> simp_all
                  have hpending :
                      (abstract.process .service).workflow.pending =
                        node.pending := by
                    simpa [WorkflowAligned, howner ▸ haddress,
                      howner ▸ hnode, hbfalse, hflights] using
                      related.workflow
                  simpa [FlightWorkflowStage] using hpending
              exact ⟨[], trivial,
                related_after_start_node hreachable related haddress howner
                  hnode rfl hflights rfl hstage htime hvalid (by
                    simp [Concrete.step, hguard, hkey, Concrete.start,
                      Concrete.Node.await, Outcomes.one]),
                rfl⟩
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        have loadingTerminalImpossible
            {flight : Concrete.Flight} {reply : StoreReply}
            (hflight : (replyOp, flight) ∈ node.flights)
            (hphase : flight.phase = .loading)
            (hterminal :
              (Concrete.Pid.store, .node address,
                .storeReply { op := replyOp, payload := reply }) ∈
                  concrete.network)
            (hreplyKind :
              reply = .written ∨ reply = .conflict ∨ reply = .failed) :
            False := by
          have hget := reachable_loading_flight_request hreachable haddress
            hnode hflight hphase
          obtain ⟨key, document, expected, hput⟩ :=
            reachable_put_replies_have_request hreachable hreplyKind
              hterminal
          have heq := (reachable_rpc_ids hreachable).unique hget hput
          contradiction
        cases payload with
        | got loadedKey loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact hinert (by
                    simp [Concrete.step, ht, Outcomes.one])
              | some flight =>
                  have hflight := takeFlight_some_mem ht
                  simp only [ht] at hresult
                  split at hresult
                  next hkey =>
                    subst loadedKey
                    cases hp : flight.phase with
                    | loading =>
                        cases hs : Concrete.select appConfig flight
                            loaded with
                        | none =>
                            have hvalidFlight :=
                              related.flights address node replyOp flight
                                haddress hnode hflight
                            exact
                              (hvalidFlight.select_ne_none loaded hs).elim
                        | some candidate =>
                            simp [ht, hp, Concrete.decide, hs,
                              Outcomes.one] at hresult
                            subst result
                            exact ⟨[], trivial,
                              by
                                simpa [endOf, Concrete.decide, hs] using
                                  related_after_decide_node hreachable related
                                    haddress hnode ht hp hs htime hvalid (by
                                      simp [Concrete.step, ht, hp,
                                        Concrete.decide, hs, Outcomes.one]),
                              rfl⟩
                    | writing =>
                        obtain ⟨document, hdocument, provenance,
                            htransaction, hloaded, houtputs,
                            hcontinuations, hput⟩ :=
                          reachable_writing_flight_provenance hreachable
                            haddress hnode hflight hp
                        have hget :=
                          reachable_got_replies_have_request hreachable hvalid
                        have heq := (reachable_rpc_ids hreachable).unique
                          hget hput
                        contradiction
                  next hkey =>
                    have hget :=
                      reachable_got_replies_have_request hreachable hvalid
                    cases hp : flight.phase with
                    | loading =>
                        have hactiveGet :=
                          reachable_loading_flight_request hreachable
                            haddress hnode hflight hp
                        have heq := (reachable_rpc_ids hreachable).unique
                          hget hactiveGet
                        simp only [Concrete.StoreRequest.get.injEq] at heq
                        exact (hkey heq).elim
                    | writing =>
                        obtain ⟨document, hdocument, provenance,
                            htransaction, hloaded, houtputs,
                            hcontinuations, hput⟩ :=
                          reachable_writing_flight_provenance hreachable
                            haddress hnode hflight hp
                        have heq := (reachable_rpc_ids hreachable).unique
                          hget hput
                        contradiction
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact hinert (by simp [Concrete.step, ht, Outcomes.one])
              | some flight =>
                  have hflight := takeFlight_some_mem ht
                  cases hp : flight.phase with
                  | loading =>
                      exact (loadingTerminalImpossible hflight hp hvalid
                        (.inl rfl)).elim
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨[], trivial,
                        related_after_written_node hreachable related
                          haddress hnode ht hp htime hvalid (by
                            simp [Concrete.step, ht, hp, Outcomes.one]),
                        rfl⟩
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact hinert (by simp [Concrete.step, ht, Outcomes.one])
              | some flight =>
                  have hflight := takeFlight_some_mem ht
                  cases hp : flight.phase with
                  | loading =>
                      exact (loadingTerminalImpossible hflight hp hvalid
                        (.inr (.inl rfl))).elim
                  | writing =>
                      obtain ⟨serialNode, hserialNode, hserial⟩ :=
                        reachable_nodes_serial hreachable address haddress
                      rw [hnode] at hserialNode
                      cases Concrete.Local.node.inj hserialNode
                      have hremainingFlights :=
                        takeFlight_remaining_empty hserial ht
                      have hremainingKnown := takeFlight_known ht
                      cases hx : flight.transaction with
                      | external call =>
                          by_cases hattempt :
                              flight.attempt < config.retries
                          · simp [ht, hp, hx,
                              Concrete.Transaction.isExternal,
                              Concrete.retry, hattempt, Outcomes.one]
                              at hresult
                            subst result
                            let loading : Concrete.Flight := {
                              flight with
                                loaded := none
                                document := none
                                selected := []
                                continuations := []
                                attempt := flight.attempt + 1
                                phase := .loading
                            }
                            have howner :=
                              reachable_flight_owner hreachable haddress
                                hnode hflight
                            have hworkflow :=
                              workflow_after_external_flight_removed hreachable
                                related haddress hnode ht hx
                            have hstage :
                                remaining.workflowBlocked = true ∨
                                  FlightWorkflowStage loading
                                    remaining.pending
                                    (abstract.process .service).workflow.pending := by
                              rcases hworkflow with hblocked | hpending
                              · exact .inl hblocked
                              · exact .inr (by
                                  simpa [loading, FlightWorkflowStage, hx]
                                    using hpending)
                            exact ⟨[], trivial,
                              by
                                simpa [endOf, hx, Concrete.retry, hattempt,
                                  loading] using
                                  related_after_loading_await_node hreachable
                                    related haddress howner hnode
                                    (takeFlight_nextOp ht)
                                    hremainingFlights hremainingKnown
                                    (flight := loading) rfl hstage htime
                                    hvalid (by
                                      simp [Concrete.step, ht, hp, hx,
                                        Concrete.Transaction.isExternal,
                                        Concrete.retry, hattempt,
                                        loading, Outcomes.one]),
                              rfl⟩
                          · simp [ht, hp, hx,
                              Concrete.Transaction.isExternal,
                              Concrete.retry, hattempt, Outcomes.one]
                              at hresult
                            subst result
                            have hworkflow :=
                              workflow_after_external_flight_removed hreachable
                                related haddress hnode ht hx
                            simpa [hx, Concrete.failureOutputs] using
                              simulate_external_shed_terminal_node hreachable
                                related haddress hnode hflight hx
                                hremainingFlights hremainingKnown hworkflow
                                htime hvalid (by
                                  simp [Concrete.step, ht, hp, hx,
                                    Concrete.Transaction.isExternal,
                                    Concrete.retry, hattempt,
                                    Concrete.failureOutputs, Outcomes.one])
                      | work item instant rest =>
                          simp [ht, hp, hx,
                            Concrete.Transaction.isExternal,
                            Outcomes.one] at hresult
                          subst result
                          exact ⟨[], trivial,
                            by
                              simpa [endOf, hx,
                                Concrete.Transaction.isExternal,
                                Concrete.sendOutputs] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    { remaining with workflowBlocked := true })
                                  (by simpa using hremainingFlights)
                                  (by simpa using hremainingKnown)
                                  (.inl rfl) (outputs := [])
                                  (by
                                    intro output houtput
                                    contradiction)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hp, hx,
                                      Concrete.Transaction.isExternal,
                                      Concrete.sendOutputs, Outcomes.one]),
                            rfl⟩
                      | scan key instant rest =>
                          simp [ht, hp, hx,
                            Concrete.Transaction.isExternal,
                            Outcomes.one] at hresult
                          subst result
                          exact ⟨[], trivial,
                            by
                              simpa [endOf, hx,
                                Concrete.Transaction.isExternal,
                                Concrete.sendOutputs] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    { remaining with workflowBlocked := true })
                                  (by simpa using hremainingFlights)
                                  (by simpa using hremainingKnown)
                                  (.inl rfl) (outputs := [])
                                  (by
                                    intro output houtput
                                    contradiction)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hp, hx,
                                      Concrete.Transaction.isExternal,
                                      Concrete.sendOutputs, Outcomes.one]),
                            rfl⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact hinert (by simp [Concrete.step, ht, Outcomes.one])
              | some flight =>
                  have hflight := takeFlight_some_mem ht
                  cases hp : flight.phase with
                  | loading =>
                      exact (loadingTerminalImpossible hflight hp hvalid
                        (.inr (.inr rfl))).elim
                  | writing =>
                      obtain ⟨serialNode, hserialNode, hserial⟩ :=
                        reachable_nodes_serial hreachable address haddress
                      rw [hnode] at hserialNode
                      cases Concrete.Local.node.inj hserialNode
                      have hremainingFlights :=
                        takeFlight_remaining_empty hserial ht
                      have hremainingKnown := takeFlight_known ht
                      have hfailed :=
                        (related.activeReplies address node replyOp flight
                          haddress hnode hflight).2 hvalid
                      cases hx : flight.transaction with
                      | external call =>
                          simp [ht, hx, Concrete.failureOutputs,
                            Concrete.Transaction.isExternal,
                            Outcomes.one] at hresult
                          subst result
                          have hworkflow :=
                            workflow_after_external_flight_removed hreachable
                              related haddress hnode ht hx
                          exact ⟨[], trivial,
                            by
                              simpa [endOf, hx,
                                Concrete.Transaction.isExternal] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight hremainingFlights
                                  hremainingKnown hworkflow
                                  (outputs := [Resonate.unavailable call])
                                  (by simpa [hx, Concrete.failureOutputs] using
                                    hfailed)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hx,
                                      Concrete.failureOutputs,
                                      Concrete.Transaction.isExternal,
                                      Outcomes.one]),
                            rfl⟩
                      | work item instant rest =>
                          simp [ht, hx, Concrete.failureOutputs,
                            Concrete.Transaction.isExternal,
                            Outcomes.one] at hresult
                          subst result
                          exact ⟨[], trivial,
                            by
                              simpa [endOf, hx,
                                Concrete.Transaction.isExternal] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    { remaining with workflowBlocked := true })
                                  (by simpa using hremainingFlights)
                                  (by simpa using hremainingKnown)
                                  (.inl rfl) (outputs := [])
                                  (by intro output houtput; contradiction)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hx,
                                      Concrete.failureOutputs,
                                      Concrete.Transaction.isExternal,
                                      Outcomes.one]),
                            rfl⟩
                      | scan key instant rest =>
                          simp [ht, hx, Concrete.failureOutputs,
                            Concrete.Transaction.isExternal,
                            Outcomes.one] at hresult
                          subst result
                          exact ⟨[], trivial,
                            by
                              simpa [endOf, hx,
                                Concrete.Transaction.isExternal] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    { remaining with workflowBlocked := true })
                                  (by simpa using hremainingFlights)
                                  (by simpa using hremainingKnown)
                                  (.inl rfl) (outputs := [])
                                  (by intro output houtput; contradiction)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hx,
                                      Concrete.failureOutputs,
                                      Concrete.Transaction.isExternal,
                                      Outcomes.one]),
                            rfl⟩

/-- One reachable concrete step is matched by zero or more abstract steps,
preserving representation and the exact boundary observation. -/
def StepSimulation (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config) : Prop :=
  ∀ {concrete next : World (CModel nodes appConfig)}
      {label : Label (CModel nodes appConfig)}
      {abstract : World AModel},
    Reachable (CModel nodes appConfig) config concrete →
    Related nodes appConfig config concrete abstract →
    Step (CModel nodes appConfig) config concrete label next →
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config next (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = concreteObservation label

def ProcessSimulation (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config) : Prop :=
  ∀ {concrete : World (CModel nodes appConfig)}
      {abstract : World AModel},
    Reachable (CModel nodes appConfig) config concrete →
    Related nodes appConfig config concrete abstract →
    ∀ {pid now event result},
      concrete.now ≤ now →
      (CModel nodes appConfig).isProcess pid →
      event.Valid concrete pid →
      result ∈
        ((CModel nodes appConfig).step config pid
          (concrete.process pid) now event).val →
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land pid now result) (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = []

def InjectSimulation (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config) : Prop :=
  ∀ {concrete : World (CModel nodes appConfig)}
      {abstract : World AModel},
    Reachable (CModel nodes appConfig) config concrete →
    Related nodes appConfig config concrete abstract →
    ∀ {to now message},
      concrete.now ≤ now →
      (CModel nodes appConfig).isProcess to →
      (CModel nodes appConfig).injectable config message →
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.inject to message now) (endOf abstract execution) ∧
        Abstract.boundaryTrace execution =
          concreteObservation (nodes := nodes) (appConfig := appConfig)
            (.input to now message)

theorem injectSimulation
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config} :
    InjectSimulation nodes appConfig config := by
  intro concrete abstract hreachable related to now message htime hprocess
    hinjectable
  obtain ⟨call, rfl⟩ := hinjectable
  cases to with
  | outside => contradiction
  | node address =>
      change address ∈ nodes at hprocess
      exact simulate_inject hreachable related hprocess htime call
  | store =>
      let abstractNext :=
        abstract.inject .service (.request call) now
      let abstractLabel : Label AModel :=
        .input .service now (.request call)
      refine ⟨[(abstractLabel, abstractNext)], ?_, ?_, rfl⟩
      · exact ⟨Step.inject (Nat.le_trans related.time htime) rfl
          ⟨call, rfl⟩, trivial⟩
      · simpa [endOf] using
          related_after_store_inject related hreachable call htime

theorem processSimulation
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    (hconditional : config.conditional = true) :
    ProcessSimulation nodes appConfig config := by
  intro concrete abstract hreachable related pid now event result htime
    hprocess hvalid hresult
  cases pid with
  | outside => contradiction
  | node address =>
      change address ∈ nodes at hprocess
      obtain ⟨node, hnode, _⟩ :=
        reachable_nodes_valid hreachable address hprocess
      rw [hnode] at hresult
      exact simulate_node_process hreachable related hprocess hnode htime
        hvalid hresult
  | store =>
      obtain ⟨physical, hphysical, _⟩ := related.store
      rw [hphysical] at hresult
      exact simulate_store_process hreachable related hconditional hphysical
        htime hvalid hresult

theorem stepSimulation_of_processSimulation
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    (hinputs : InjectSimulation nodes appConfig config)
    (hprocess : ProcessSimulation nodes appConfig config) :
    StepSimulation nodes appConfig config := by
  intro concrete next label abstract hreachable related hstep
  cases hstep with
  | @inject to now message htime htarget hinject =>
      exact hinputs hreachable related htime htarget hinject
  | @outside sender now message htime hmessage =>
      simpa using
        simulate_outside hreachable related htime hmessage
  | @process pid now event result htime hreal hvalid hresult =>
      obtain ⟨execution, hlegal, hrelated, htrace⟩ :=
        hprocess hreachable related htime hreal hvalid hresult
      exact ⟨execution, hlegal, hrelated, by
        simpa only [concreteObservation, Label.observe,
          List.filterMap_nil] using htrace⟩

theorem stepSimulation
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    (hconditional : config.conditional = true) :
    StepSimulation nodes appConfig config :=
  stepSimulation_of_processSimulation injectSimulation
    (processSimulation hconditional)

theorem legal_append {model : Model} {config : model.Config}
    {world : World model} {first second : Execution model}
    (hfirst : Legal model config world first)
    (hsecond : Legal model config (endOf world first) second) :
    Legal model config world (first ++ second) := by
  induction first generalizing world with
  | nil => exact hsecond
  | cons entry rest ih =>
      exact ⟨hfirst.1, ih hfirst.2 hsecond⟩

theorem endOf_append {model : Model} (world : World model)
    (first second : Execution model) :
    endOf world (first ++ second) =
      endOf (endOf world first) second := by
  induction first generalizing world with
  | nil => rfl
  | cons entry rest ih => exact ih entry.2

theorem abstract_boundaryTrace_append
    (first second : Execution AModel) :
    Abstract.boundaryTrace (first ++ second) =
      Abstract.boundaryTrace first ++ Abstract.boundaryTrace second := by
  simp only [Abstract.boundaryTrace]
  rw [show Rover.trace (first ++ second) =
      Rover.trace first ++ Rover.trace second by
    induction first with
    | nil => rfl
    | cons entry rest ih =>
        simp [Rover.trace, ih, List.append_assoc]]
  exact List.filterMap_append

theorem concrete_boundaryTrace_cons
    {nodes : List Addr} {appConfig : Resonate.Config}
    (label : Label (CModel nodes appConfig))
    (next : World (CModel nodes appConfig))
    (rest : Execution (CModel nodes appConfig)) :
    Concrete.boundaryTrace ((label, next) :: rest) =
      concreteObservation label ++ Concrete.boundaryTrace rest := by
  simp [Concrete.boundaryTrace, concreteObservation, Rover.trace,
    List.filterMap_append]

/-- Generic execution folding from one-step simulation to finite execution
simulation without any additional trace assumption. -/
theorem simulate_execution
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    (hsim : StepSimulation nodes appConfig config)
    {concrete : World (CModel nodes appConfig)}
    {execution : Execution (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    (legal : Legal (CModel nodes appConfig) config concrete execution) :
    ∃ abstractExecution,
      Legal AModel { appConfig with unreliable := true }
        abstract abstractExecution ∧
      Related nodes appConfig config (endOf concrete execution)
        (endOf abstract abstractExecution) ∧
      Abstract.boundaryTrace abstractExecution =
        Concrete.boundaryTrace execution := by
  induction execution generalizing concrete abstract with
  | nil => exact ⟨[], trivial, related, rfl⟩
  | cons entry rest ih =>
      obtain ⟨label, next⟩ := entry
      obtain ⟨head, hhead, hrelated, htrace⟩ :=
        hsim hreachable related legal.1
      obtain ⟨tail, htail, hfinal, httrace⟩ :=
        ih (Reachable.step hreachable legal.1) hrelated legal.2
      refine ⟨head ++ tail, legal_append hhead htail, ?_, ?_⟩
      · simpa only [endOf, endOf_append] using hfinal
      · rw [abstract_boundaryTrace_append, htrace, httrace,
          concrete_boundaryTrace_cons]

theorem initial_related
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    Related nodes appConfig config (World.initial process)
      (World.initial Abstract.initialProcess) := by
  refine {
    time := Nat.le_refl 0
    store := ⟨{}, hinit.2.1, by intro key; rfl⟩
    requests := ?_
    outputs := ?_
    puts := ?_
    gotSnapshots := gotSnapshots_initial _
    ownedPutSnapshots := ownedPutSnapshots_initial _
    putReplyOrigins := putRepliesHaveRequest_initial _
    known := ?_
    workflow := ?_
    currentWorkflow := ?_
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := ?_
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
  }
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · intro address node key haddress hnode hkey
    have : Concrete.Local.node node = .node {} := hnode.symm.trans
      (hinit.2.2 address haddress)
    cases this
    simp at hkey
  · simp only [WorkflowAligned]
    split
    next hmember =>
      refine ⟨{}, hinit.2.2 config.workflowNode hmember, ?_⟩
      right
      left
      exact ⟨rfl, rfl⟩
    next _ =>
      rfl
  · intro physical address node op flight pending haddress hstore hnode hmem
      hphase hversion hpending
    have : Concrete.Local.node node = .node {} := hnode.symm.trans
      (hinit.2.2 address haddress)
    cases this
    simp at hmem
  · intros
    contradiction
  · intros
    contradiction
  · intro address node op flight haddress hnode hflight
    have : Concrete.Local.node node = .node {} := hnode.symm.trans
      (hinit.2.2 address haddress)
    cases this
    simp at hflight
  · intro address node op flight haddress hnode hflight
    have : Concrete.Local.node node = .node {} := hnode.symm.trans
      (hinit.2.2 address haddress)
    cases this
    simp at hflight
  · intros
    contradiction
  · intros
    contradiction

/-- End-to-end trace inclusion from a protocol-specific reachable one-step
simulation, including all execution and delayed-observation plumbing. -/
theorem boundary_refinement_of_stepSimulation
    (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config)
    (hsim : StepSimulation nodes appConfig config) :
    ∀ events,
      Concrete.ValidBoundaryTrace nodes appConfig config events →
      Abstract.ValidBoundaryTrace
        { appConfig with unreliable := true } events := by
  intro events hvalid
  obtain ⟨execution, ⟨process, hinit, hlegal⟩, htrace⟩ := hvalid
  obtain ⟨abstractExecution, abstractLegal, _, abstractTrace⟩ :=
    simulate_execution hsim (Reachable.init hinit)
      (initial_related hinit) hlegal
  exact ⟨abstractExecution,
    ⟨Abstract.initialProcess,
      Abstract.initialProcess_valid
        { appConfig with unreliable := true },
      abstractLegal⟩,
    abstractTrace.trans htrace⟩

theorem boundary_refinement
    (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config)
    (hconditional : config.conditional = true) :
    ∀ events,
      Concrete.ValidBoundaryTrace nodes appConfig config events →
      Abstract.ValidBoundaryTrace
        { appConfig with unreliable := true } events :=
  boundary_refinement_of_stepSimulation nodes appConfig config
    (stepSimulation hconditional)

end Resonate.Refinement
