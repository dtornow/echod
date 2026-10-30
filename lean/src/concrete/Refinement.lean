import «concrete».Model
import «abstract».Model

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

/-- The concrete handler is independently defined, but its promise-get
decision computes the same indexed document result as the abstract handler. -/
theorem promiseGet_handler_correspondence
    (config : ServerConfig) (req : ServerModel.PromiseGetReq) (now : Time)
    (document : Document (.origin req.id.origin)) :
    Concrete.Decision.run config (Concrete.Decision.promiseGet req now) document =
      Direct.promiseGet req now { config } document := by
  rfl

theorem promiseGet_action_correspondence
    (req : ServerModel.PromiseGetReq) (now : Time) :
    Concrete.Decision.promiseGet req now = Direct.promiseGet req now := by
  rfl

theorem promiseCreate_handler_correspondence
    (req : ServerModel.PromiseCreateReq) (now : Time) :
    Concrete.Decision.promiseCreate req now = Direct.promiseCreate req now := by
  rfl

theorem promiseSettle_handler_correspondence
    (req : ServerModel.PromiseSettleReq) (now : Time) :
    Concrete.Decision.promiseSettle req now = Direct.promiseSettle req now := by
  rfl

theorem promiseRegisterCallback_handler_correspondence
    (req : ServerModel.PromiseRegisterCallbackReq) (now : Time) :
    Concrete.Decision.promiseRegisterCallback req now =
      Direct.promiseRegisterCallback req now := by
  rfl

theorem promiseRegisterListener_handler_correspondence
    (req : ServerModel.PromiseRegisterListenerReq) (now : Time) :
    Concrete.Decision.promiseRegisterListener req now =
      Direct.promiseRegisterListener req now := by
  rfl

theorem taskGet_handler_correspondence
    (req : ServerModel.TaskGetReq) (now : Time) :
    Concrete.Decision.taskGet req now = Direct.taskGet req now := by
  rfl

theorem taskCreate_handler_correspondence
    (req : ServerModel.TaskCreateReq) (now : Time) :
    Concrete.Decision.taskCreate req now = Direct.taskCreate req now := by
  rfl

theorem taskAcquire_handler_correspondence
    (req : ServerModel.TaskAcquireReq) (now : Time) :
    Concrete.Decision.taskAcquire req now = Direct.taskAcquire req now := by
  rfl

theorem taskFence_handler_correspondence
    (req : ServerModel.TaskFenceReq) (now : Time) :
    Concrete.Decision.taskFence req now = Direct.taskFence req now := by
  rfl

theorem heartbeatOne_handler_correspondence
    (origin pid : String) (ref : ServerModel.TaskRef) (now : Time) :
    (Concrete.Decision.heartbeatOne (origin := origin) pid ref now) =
      Direct.heartbeatOne (origin := origin) pid ref now := by
  rfl

theorem heartbeatAll_handler_correspondence
    (origin pid : String) (now : Time) (refs : List ServerModel.TaskRef) :
    Concrete.Decision.heartbeatAll (origin := origin) pid now refs =
      Direct.heartbeatAll (origin := origin) pid now refs := by
  induction refs with
  | nil => rfl
  | cons ref rest ih =>
      simp only [Concrete.Decision.heartbeatAll, Direct.heartbeatAll]
      rw [heartbeatOne_handler_correspondence, ih]

theorem taskHeartbeat_handler_correspondence
    (origin : String) (req : ServerModel.TaskHeartbeatReq) (now : Time) :
    Concrete.Decision.taskHeartbeat origin req now =
      Direct.taskHeartbeat origin req now := by
  unfold Concrete.Decision.taskHeartbeat Direct.taskHeartbeat
  rw [heartbeatAll_handler_correspondence]

theorem readObject_handler_correspondence
    (origin suffix : String) (now : Time) :
    Concrete.Decision.readObject (origin := origin) suffix now =
      Direct.readObject (origin := origin) suffix now := by
  rfl

theorem setPromise_handler_correspondence
    (origin suffix : String) (promise : PromiseObject) :
    Concrete.Decision.setPromise (origin := origin) suffix promise =
      Direct.setPromise (origin := origin) suffix promise := by
  rfl

theorem readTaskObject_handler_correspondence
    (origin suffix : String) (now : Time) :
    Concrete.Decision.readTaskObject (origin := origin) suffix now =
      Direct.readTaskObject (origin := origin) suffix now := by
  rfl

theorem checkAwaited_handler_correspondence
    (origin : String) (now : Time)
    (actions : List ServerModel.PromiseRegisterCallbackReq) :
    Concrete.Decision.checkAwaited (origin := origin) now actions =
      Direct.checkAwaited (origin := origin) now actions := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      simp only [Concrete.Decision.checkAwaited, Direct.checkAwaited]
      rw [readObject_handler_correspondence, ih]
      rfl

theorem registerAwaited_handler_correspondence
    (origin : String) (awaiter : ServerModel.Ident) (now : Time)
    (actions : List ServerModel.PromiseRegisterCallbackReq) :
    Concrete.Decision.registerAwaited (origin := origin) awaiter now actions =
      Direct.registerAwaited (origin := origin) awaiter now actions := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      simp only [Concrete.Decision.registerAwaited, Direct.registerAwaited]
      rw [readObject_handler_correspondence]
      simp only [Concrete.Decision.setPromise, Direct.setPromise]
      rw [ih]
      rfl

theorem taskSuspend_handler_correspondence
    (req : ServerModel.TaskSuspendReq) (now : Time) :
    Concrete.Decision.taskSuspend req now = Direct.taskSuspend req now := by
  unfold Concrete.Decision.taskSuspend Direct.taskSuspend
  rw [readTaskObject_handler_correspondence,
    checkAwaited_handler_correspondence,
    registerAwaited_handler_correspondence]
  simp only [Concrete.Decision.setTask, Direct.setTask,
    Concrete.Decision.modify, Direct.modify]
  rfl

theorem taskFulfill_handler_correspondence
    (req : ServerModel.TaskFulfillReq) (now : Time) :
    Concrete.Decision.taskFulfill req now = Direct.taskFulfill req now := by
  rfl

theorem taskRelease_handler_correspondence
    (req : ServerModel.TaskReleaseReq) (now : Time) :
    Concrete.Decision.taskRelease req now = Direct.taskRelease req now := by
  rfl

theorem taskHalt_handler_correspondence
    (req : ServerModel.TaskHaltReq) (now : Time) :
    Concrete.Decision.taskHalt req now = Direct.taskHalt req now := by
  rfl

theorem taskContinue_handler_correspondence
    (req : ServerModel.TaskContinueReq) (now : Time) :
    Concrete.Decision.taskContinue req now = Direct.taskContinue req now := by
  rfl

theorem scheduleGet_handler_correspondence
    (req : ServerModel.ScheduleGetReq) (now : Time) :
    Concrete.Decision.scheduleGet req now = Direct.scheduleGet req now := by
  rfl

theorem scheduleCreate_handler_correspondence
    (req : ServerModel.ScheduleCreateReq) (now : Time) :
    Concrete.Decision.scheduleCreate req now =
      Direct.scheduleCreate req now := by
  rfl

theorem scheduleDelete_handler_correspondence
    (req : ServerModel.ScheduleDeleteReq) (now : Time) :
    Concrete.Decision.scheduleDelete req now =
      Direct.scheduleDelete req now := by
  rfl

theorem promiseTimeout_work_correspondence
    (id : ServerModel.Ident) (now : Time) :
    Concrete.Decision.processPromiseTimeout id now =
      Direct.processPromiseTimeout id now := by
  rfl

theorem callback_work_correspondence
    (req : ServerModel.PromiseRegisterCallbackReq) (now : Time) :
    Concrete.Decision.processCallback req now =
      Direct.processCallback req now := by
  rfl

theorem listener_work_correspondence
    (req : ServerModel.PromiseRegisterListenerReq) (now : Time) :
    Concrete.Decision.processListener req now =
      Direct.processListener req now := by
  rfl

theorem leaseTimeout_work_correspondence
    (id : ServerModel.Ident) (now : Time) :
    Concrete.Decision.processLeaseTimeout id now =
      Direct.processLeaseTimeout id now := by
  rfl

theorem retryTimeout_work_correspondence
    (id : ServerModel.Ident) (now : Time) :
    Concrete.Decision.processRetryTimeout id now =
      Direct.processRetryTimeout id now := by
  rfl

theorem scheduleTimeout_work_correspondence
    (id : ServerModel.Ident) (now : Time) :
    Concrete.Decision.processSchedule id now =
      Direct.processSchedule id now := by
  rfl

theorem occurrence_work_correspondence
    (req : ServerModel.PromiseCreateReq) (instant : Time) :
    Concrete.Decision.processOccurrence req instant =
      Direct.processOccurrence req instant := by
  rfl

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

theorem originWork_correspondence
    (origin : String) (document : OriginDocument origin) (now : Time) :
    Concrete.Decision.originWork origin document now =
      Direct.originWork origin document now := by
  rfl

@[simp] theorem singleton_rewrite
    (key : DocumentKey) (before after : Document key) :
    (({} : Resonate.Store).write key before).write key after =
      ({} : Resonate.Store).write key after := by
  unfold Resonate.Store.write
  congr 1
  · simp
  · funext other
    by_cases h : other = key <;> simp [h]

theorem selectedExternal_correspondence
    (appConfig : Resonate.Config) (call : Call)
    (key : DocumentKey) (before : Document key)
    (hkey : (Concrete.Transaction.external call).key? = some key) :
    Concrete.selectedExternal appConfig call key before =
      Resonate.run { appConfig with unreliable := true } call
        (Concrete.singleState key before) := by
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
          simp [Concrete.selectedExternal,
            Concrete.selectedExternalCandidate, Concrete.externalCandidate,
            Concrete.Candidate.cast, Concrete.Decision.run,
            Resonate.run, Resonate.handleExternal, Resonate.runDocument,
            Concrete.singleState, Direct.runWith, request, tasks, hsame,
            taskHeartbeat_handler_correspondence, singleton_rewrite,
            Concrete.pendingWorkflow]
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
           simp [Concrete.selectedExternal,
             Concrete.selectedExternalCandidate, Concrete.externalCandidate,
             Concrete.Candidate.cast, Concrete.Decision.run,
             Resonate.run, Resonate.handleExternal, Resonate.runDocument,
             Concrete.singleState, Direct.runWith, request,
             taskSuspend_handler_correspondence, singleton_rewrite,
             promiseGet_action_correspondence,
             promiseCreate_handler_correspondence,
             promiseSettle_handler_correspondence,
             promiseRegisterCallback_handler_correspondence,
             promiseRegisterListener_handler_correspondence,
             taskGet_handler_correspondence,
             taskCreate_handler_correspondence,
             taskAcquire_handler_correspondence,
             taskFence_handler_correspondence,
             taskSuspend_handler_correspondence,
             taskFulfill_handler_correspondence,
             taskRelease_handler_correspondence,
             taskHalt_handler_correspondence,
             taskContinue_handler_correspondence,
             scheduleGet_handler_correspondence,
             scheduleCreate_handler_correspondence,
             scheduleDelete_handler_correspondence,
             Concrete.pendingWorkflow, *])
      | (cases hkey
         simp [Concrete.selectedExternal,
           Concrete.selectedExternalCandidate, Concrete.externalCandidate,
           Concrete.Candidate.cast, Concrete.Decision.run,
           Resonate.run, Resonate.handleExternal, Resonate.runDocument,
           Concrete.singleState, Direct.runWith, request,
           taskSuspend_handler_correspondence, singleton_rewrite,
           promiseGet_action_correspondence,
           promiseCreate_handler_correspondence,
           promiseSettle_handler_correspondence,
           promiseRegisterCallback_handler_correspondence,
           promiseRegisterListener_handler_correspondence,
           taskGet_handler_correspondence,
           taskCreate_handler_correspondence,
           taskAcquire_handler_correspondence,
           taskFence_handler_correspondence,
           taskSuspend_handler_correspondence,
           taskFulfill_handler_correspondence,
           taskRelease_handler_correspondence,
           taskHalt_handler_correspondence,
           taskContinue_handler_correspondence,
           scheduleGet_handler_correspondence,
           scheduleCreate_handler_correspondence,
           scheduleDelete_handler_correspondence,
           Concrete.pendingWorkflow, *])

@[simp] theorem pendingWorkflow_cons
    (entry : Concrete.PendingEntry) (rest : List Concrete.PendingEntry) :
    Concrete.pendingWorkflow (entry :: rest) =
      entry.toWorkflow?.toList ++ Concrete.pendingWorkflow rest := by
  rfl

@[simp] theorem pendingWorkflow_append
    (left right : List Concrete.PendingEntry) :
    Concrete.pendingWorkflow (left ++ right) =
      Concrete.pendingWorkflow left ++ Concrete.pendingWorkflow right := by
  simp [Concrete.pendingWorkflow, List.filterMap_append]

@[simp] theorem pendingWorkflow_occurrences
    (items : List WorkItem) :
    Concrete.pendingWorkflow
        (items.filterMap fun
          | .occurrence request instant =>
              some (.occurrence request instant)
          | _ => none) =
      items.filterMap Resonate.occurrenceEntry? := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      cases item <;>
        simp [Concrete.PendingEntry.toWorkflow?,
          Resonate.occurrenceEntry?, ih]

theorem selectedWork_correspondence
    (appConfig : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List Concrete.PendingEntry) (before : Document item.key) :
    Concrete.selectedWork appConfig item now rest item.key before =
      Resonate.runWork { appConfig with unreliable := true } item now
        (Concrete.pendingWorkflow rest)
        (Concrete.singleState item.key before) := by
  cases item <;>
    simp [Concrete.selectedWork, Concrete.selectedWorkCandidate,
      Concrete.workCandidate, Concrete.Candidate.cast,
      Concrete.Decision.run, Resonate.runWork, Resonate.runDocument,
      Concrete.singleState, Direct.runWith, WorkItem.key,
      singleton_rewrite,
      promiseTimeout_work_correspondence,
      callback_work_correspondence, listener_work_correspondence,
      leaseTimeout_work_correspondence,
      retryTimeout_work_correspondence,
      scheduleTimeout_work_correspondence,
      occurrence_work_correspondence]
  case scheduleTimeout =>
    exact pendingWorkflow_occurrences _

theorem selectedWork_correspondence_key
    (appConfig : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List Concrete.PendingEntry) (key : DocumentKey)
    (before : Document key) (hkey : item.key = key) :
    Concrete.selectedWork appConfig item now rest key before =
      Resonate.runWork { appConfig with unreliable := true } item now
        (Concrete.pendingWorkflow rest)
        (Concrete.singleState key before) := by
  subst key
  exact selectedWork_correspondence appConfig item now rest before

/-- Ghost meaning of a selected transaction. No field of this predicate is
serialized in `StoreRequest.put`. -/
inductive Selected (appConfig : Resonate.Config) :
    (key : DocumentKey) → Concrete.Transaction →
    Document key → Document key → List Output →
      List Concrete.PendingEntry → Prop
  | external {key call before after outputs} :
      (Concrete.Transaction.external call).key? = some key →
      Resonate.run { appConfig with unreliable := true } call
          (Concrete.singleState key before) =
        (after, outputs) →
      Selected appConfig key (.external call) before
        (after.store.read key) outputs
          (after.workflow.pending.map Concrete.PendingEntry.fromWorkflow)
  | work {item now rest before after outputs} :
      Resonate.runWork { appConfig with unreliable := true } item now
          (Concrete.pendingWorkflow rest)
          (Concrete.singleState item.key before) =
        (after, outputs) →
      Selected appConfig item.key (.work item now rest) before
        (after.store.read item.key) outputs
          (after.workflow.pending.map Concrete.PendingEntry.fromWorkflow)
  | scan {key now rest before candidate} :
      Concrete.selectScan appConfig key now rest before = some candidate →
      Selected appConfig key (.scan key now rest) before
        candidate.document candidate.outputs candidate.continuations

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
      let before :=
        (loaded.map (·.1)).getD (emptyDocument flightKey)
      let after : State := {
        store := ({} : Resonate.Store).write flightKey candidate.document
        workflow := {
          pending := Concrete.pendingWorkflow candidate.continuations }
      }
      change
        Concrete.selectedExternalCandidate appConfig call flightKey before =
          some candidate at hselect
      have hcorrespondence :=
        selectedExternal_correspondence appConfig call flightKey before hkey
      have habstract :
          Resonate.run { appConfig with unreliable := true } call
              (Concrete.singleState flightKey before) =
            (after, candidate.outputs) := by
        rw [← hcorrespondence]
        simp [Concrete.selectedExternal, hselect, after]
      simpa [after] using
        (Selected.external hkey habstract)
    case work item now rest =>
      simp only [Concrete.select] at hselect
      simp only [Concrete.Transaction.key?, Option.some.injEq] at hkey
      subst flightKey
      let before :=
        (loaded.map (·.1)).getD (emptyDocument item.key)
      let after : State := {
        store := ({} : Resonate.Store).write item.key candidate.document
        workflow := {
          pending := Concrete.pendingWorkflow candidate.continuations }
      }
      change
        Concrete.selectedWorkCandidate appConfig item now rest item.key before =
          some candidate at hselect
      have hcorrespondence :=
        selectedWork_correspondence appConfig item now rest before
      have habstract :
          Resonate.runWork { appConfig with unreliable := true } item now
              (Concrete.pendingWorkflow rest)
              (Concrete.singleState item.key before) =
            (after, candidate.outputs) := by
        rw [← hcorrespondence]
        simp [Concrete.selectedWork, hselect, after]
      simpa [after] using (Selected.work habstract)
    case scan key now rest =>
      simp only [Concrete.select] at hselect
      split at hselect
      next heq =>
        subst flightKey
        exact .scan hselect
      next _ => contradiction

/-- Reachable raw-PUT provenance. `loaded`, transaction, response/emissions,
and continuation work are ghost facts, not request payload fields. -/
structure PutProvenance (appConfig : Resonate.Config)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) where
  transaction : Concrete.Transaction
  loaded : Option (Document key × Concrete.Version)
  outputs : List Output
  continuations : List Concrete.PendingEntry
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
    {continuations : List Concrete.PendingEntry}
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

theorem pureResponse_correspondence
    (config : Resonate.Config) (call : Call)
    (hkey : (Concrete.Transaction.external call).key? = none) :
    (Resonate.run config call {}).2 =
      [.response call.client call.id
        (Concrete.pureResponse call.request)] := by
  cases request : call.request <;>
    simp only [Concrete.Transaction.key?, request] at hkey
  case promiseRegisterCallback req =>
    split at hkey
    · contradiction
    · simp [Resonate.run, Resonate.handleExternal,
        Resonate.pureRequest, Concrete.pureResponse, request, *]
  case taskHeartbeat req =>
    cases tasks : req.tasks with
    | nil =>
        simp [Resonate.run, Resonate.handleExternal,
          Resonate.pureRequest, Concrete.pureResponse, request, tasks]
    | cons first rest =>
        simp only [tasks] at hkey
        split at hkey
        · contradiction
        · simp [Resonate.run, Resonate.handleExternal,
            Resonate.pureRequest, Concrete.pureResponse, request, tasks, *]
  case taskFence req =>
    split at hkey
    · contradiction
    · rename_i hcondition
      cases hs : req.action.targetId.sameOrigin req.id with
      | false =>
          simp [Resonate.run, Resonate.handleExternal,
            Resonate.pureRequest, Concrete.pureResponse, request, hs]
      | true =>
          have hid : req.action.targetId = req.id := by
            simpa [hs] using hcondition
          have hself : req.id.sameOrigin req.id = true := by
            simpa [hid] using hs
          simp [Resonate.run, Resonate.handleExternal,
            Resonate.pureRequest, Resonate.runDocument, Direct.runWith,
            Direct.taskFence, Direct.Handler, Concrete.pureResponse,
            request, hs, hid, hself]
          have hpure (document : Document (.origin req.id.origin)) :
              (pure { status := 400 } :
                Direct.Handler (.origin req.id.origin)
                  ServerModel.TaskFenceRes)
                  { config := config.toServerConfig } document =
                ({ status := 400 }, document, []) := rfl
          rw [hpure]
          simp
  case taskSuspend req =>
    split at hkey
    · simp [Resonate.run, Resonate.handleExternal,
        Resonate.pureRequest, Concrete.pureResponse, request, *]
    · contradiction
  case promiseSearch req =>
    simp [Resonate.run, Resonate.handleExternal, Resonate.pureRequest,
      Direct.promiseSearch, Concrete.pureResponse, request]
  case scheduleSearch req =>
    simp [Resonate.run, Resonate.handleExternal, Resonate.pureRequest,
      Direct.scheduleSearch, Concrete.pureResponse, request]
  case taskSearch req =>
    simp [Resonate.run, Resonate.handleExternal, Resonate.pureRequest,
      Direct.taskSearch, Concrete.pureResponse, request]
  all_goals
    rename_i req
    first
    | contradiction
    | (split at hkey
       · contradiction
       · simp [Resonate.run, Resonate.handleExternal,
           Resonate.pureRequest, Concrete.pureResponse, request, *])
    | simp [Resonate.run, Resonate.handleExternal,
        Resonate.pureRequest, Resonate.runDocument, Direct.runWith,
        Direct.taskFence, Direct.Handler, Concrete.pureResponse,
        request, *]

theorem work_key_mem
    (config : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List WorkflowEntry) (state : State) :
    item.key ∈ (Resonate.runWork config item now rest state).1.store.keys := by
  cases item <;>
    simp [Resonate.runWork, Resonate.runDocument, Direct.runWith,
      WorkItem.key]

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
    {item : WorkItem} {now : Time} {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .work item now rest)
    (hcurrent : physical.read key = provenance.loaded) :
    let lifted := Resonate.runWork
      { appConfig with unreliable := true } item now
        (Concrete.pendingWorkflow rest) abstract
    StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 = provenance.outputs ∧
      lifted.1.workflow.pending =
        Concrete.pendingWorkflow provenance.continuations := by
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
        { appConfig with unreliable := true } item now
        (Concrete.pendingWorkflow rest) item.key
        ((loaded.map (·.1)).getD
          (emptyDocument item.key))
        abstract rfl habstract
      rw [hselected] at hlocal
      refine ⟨?_, hlocal.2.2, ?_⟩
      · intro other
        by_cases hother : other = item.key
        · subst other
          simp [hlocal.1]
        · rw [Concrete.Store.toAbstract_commit]
          simp [hother, Resonate.runWork_frame
            { appConfig with unreliable := true } item now
            (Concrete.pendingWorkflow rest)
            abstract other hother, hrep other]
      · rw [← hlocal.2.1]
        exact (Concrete.pendingWorkflow_map_fromWorkflow _).symm

theorem scan_cas_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {now : Time} {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .scan key now rest)
    (hcurrent : physical.read key = provenance.loaded)
    (hkeymem : key ∈ abstract.store.keys) :
    ∃ item,
      item.key = key ∧
      item ∈ Resonate.eligibleWorkAt abstract now ∧
      let lifted := Resonate.runWork
        { appConfig with unreliable := true } item now
          (Concrete.pendingWorkflow rest) abstract
      StoreRep (physical.commit key document) lifted.1 ∧
        lifted.2 = provenance.outputs ∧
        lifted.1.workflow.pending =
          Concrete.pendingWorkflow provenance.continuations := by
  cases provenance with
  | mk transaction loaded outputs continuations expected_eq selected =>
    simp only at htransaction
    subst transaction
    cases selected with
    | scan hselected =>
      rename_i candidate
      have hbefore := toAbstract_read_eq_loaded hcurrent
      have habstract :
          abstract.store.read key =
            (loaded.map (·.1)).getD (emptyDocument key) := by
        rw [← hrep key, hbefore]
      cases key with
      | origin origin =>
          obtain ⟨item, hitem, hdocument, houtputs, hcontinuations⟩ :=
            Concrete.selectScan_origin_some appConfig origin now rest
              ((loaded.map (·.1)).getD
                (emptyDocument (.origin origin))) _ hselected
          have hitemAbstract :
              item ∈ Direct.originWork origin
                ((loaded.map (·.1)).getD
                  (emptyDocument (.origin origin))) now := by
            rw [← originWork_correspondence]
            exact hitem
          have hitemKey : item.key = .origin origin :=
            originWork_key hitemAbstract
          have hdecision := selectedWork_correspondence_key appConfig item
            now rest (.origin origin)
            ((loaded.map (·.1)).getD
              (emptyDocument (.origin origin))) hitemKey
          have hdocument' :
              candidate.document =
                (Resonate.runWork { appConfig with unreliable := true }
                  item now (Concrete.pendingWorkflow rest)
                  (Concrete.singleState (.origin origin)
                    ((loaded.map (·.1)).getD
                      (emptyDocument (.origin origin))))).1.store.read
                    (.origin origin) := by
            rw [← hdecision]
            exact hdocument
          have houtputs' :
              candidate.outputs =
                (Resonate.runWork { appConfig with unreliable := true }
                  item now (Concrete.pendingWorkflow rest)
                  (Concrete.singleState (.origin origin)
                    ((loaded.map (·.1)).getD
                      (emptyDocument (.origin origin))))).2 := by
            rw [← hdecision]
            exact houtputs
          have hcontinuations' :
              candidate.continuations =
                (Resonate.runWork { appConfig with unreliable := true }
                  item now (Concrete.pendingWorkflow rest)
                  (Concrete.singleState (.origin origin)
                    ((loaded.map (·.1)).getD
                      (emptyDocument (.origin origin))))).1.workflow.pending.map
                    Concrete.PendingEntry.fromWorkflow := by
            rw [← hdecision]
            exact hcontinuations
          have hlocal := work_locality
            { appConfig with unreliable := true } item now
            (Concrete.pendingWorkflow rest) (.origin origin)
            ((loaded.map (·.1)).getD
              (emptyDocument (.origin origin)))
            abstract hitemKey
            habstract
          refine ⟨item, hitemKey, ?_, ?_,
            hlocal.2.2.trans houtputs'.symm, ?_⟩
          · simp only [Resonate.eligibleWorkAt, List.mem_flatMap]
            exact ⟨.origin origin, hkeymem, by
              change item ∈ Direct.originWork origin
                (abstract.store.read (.origin origin)) now
              rw [habstract]
              exact hitemAbstract⟩
          · intro other
            by_cases hother : other = .origin origin
            · subst other
              simp only [Concrete.Store.toAbstract_commit,
                Resonate.Store.read_write_same]
              exact hdocument'.trans hlocal.1.symm
            · rw [Concrete.Store.toAbstract_commit]
              simp [hother, Resonate.runWork_frame
                { appConfig with unreliable := true } item now
                (Concrete.pendingWorkflow rest) abstract other
                (by
                  intro heq
                  apply hother
                  rw [← hitemKey]
                  exact heq), hrep other]
          · rw [hlocal.2.1]
            exact (Concrete.pendingWorkflow_map_fromWorkflow _).symm.trans
              (congrArg Concrete.pendingWorkflow hcontinuations'.symm)
      | schedule id =>
          obtain ⟨schedule, hschedule, hdue, hdocument, houtputs,
              hcontinuations⟩ :=
            Concrete.selectScan_schedule_some appConfig id now rest
              ((loaded.map (·.1)).getD
                (emptyDocument (.schedule id))) _ hselected
          have hdecision := selectedWork_correspondence_key appConfig
            (.scheduleTimeout id) now rest (.schedule id)
            ((loaded.map (·.1)).getD
              (emptyDocument (.schedule id))) rfl
          have hdocument' :
              candidate.document =
                (Resonate.runWork { appConfig with unreliable := true }
                  (.scheduleTimeout id) now (Concrete.pendingWorkflow rest)
                  (Concrete.singleState (.schedule id)
                    ((loaded.map (·.1)).getD
                      (emptyDocument (.schedule id))))).1.store.read
                    (.schedule id) := by
            rw [← hdecision]
            exact hdocument
          have houtputs' :
              candidate.outputs =
                (Resonate.runWork { appConfig with unreliable := true }
                  (.scheduleTimeout id) now (Concrete.pendingWorkflow rest)
                  (Concrete.singleState (.schedule id)
                    ((loaded.map (·.1)).getD
                      (emptyDocument (.schedule id))))).2 := by
            rw [← hdecision]
            exact houtputs
          have hcontinuations' :
              candidate.continuations =
                (Resonate.runWork { appConfig with unreliable := true }
                  (.scheduleTimeout id) now (Concrete.pendingWorkflow rest)
                  (Concrete.singleState (.schedule id)
                    ((loaded.map (·.1)).getD
                      (emptyDocument (.schedule id))))).1.workflow.pending.map
                    Concrete.PendingEntry.fromWorkflow := by
            rw [← hdecision]
            exact hcontinuations
          have hlocal := work_locality
            { appConfig with unreliable := true }
            (.scheduleTimeout id) now
            (Concrete.pendingWorkflow rest) (.schedule id)
            ((loaded.map (·.1)).getD
              (emptyDocument (.schedule id)))
            abstract rfl habstract
          refine ⟨.scheduleTimeout id, rfl, ?_, ?_,
            hlocal.2.2.trans houtputs'.symm, ?_⟩
          · have habstractSchedule :
                abstract.store.read (.schedule id) = some schedule :=
              habstract.trans hschedule
            simp only [Resonate.eligibleWorkAt, List.mem_flatMap]
            exact ⟨.schedule id, hkeymem, by
              simp [habstractSchedule, hdue]⟩
          · intro other
            by_cases hother : other = .schedule id
            · subst other
              simp only [Concrete.Store.toAbstract_commit,
                Resonate.Store.read_write_same]
              exact hdocument'.trans hlocal.1.symm
            · rw [Concrete.Store.toAbstract_commit]
              simp [hother, Resonate.runWork_frame
                { appConfig with unreliable := true }
                (.scheduleTimeout id) now
                (Concrete.pendingWorkflow rest) abstract other
                hother, hrep other]
          · rw [hlocal.2.1]
            exact
              (Concrete.pendingWorkflow_map_fromWorkflow _).symm.trans
                (congrArg Concrete.pendingWorkflow hcontinuations'.symm)

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
def WorkShaped : Concrete.Transaction → Prop
  | .work item _ _ =>
      ∃ request semanticTime,
        item = .occurrence request semanticTime
  | .external _ | .scan _ _ _ => True

def FlightValid (appConfig : Resonate.Config)
    (flight : Concrete.Flight) : Prop :=
  flight.transaction.key? = some flight.key ∧
  (match flight.phase with
   | .loading => True
   | .writing =>
       ∃ document,
         flight.document = some document ∧
         Selected appConfig flight.key flight.transaction
           (flight.loaded.map (·.1) |>.getD
             (emptyDocument flight.key))
           document flight.selected flight.continuations) ∧
  WorkShaped flight.transaction

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
  obtain ⟨document, hdocument, hselected⟩ := hvalid.2.1
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
    (hnotScan :
      ∀ key instant rest,
        flight.transaction ≠ .scan key instant rest)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    Concrete.select appConfig flight loaded ≠ none := by
  cases flight with
  | mk key transaction oldLoaded document selected continuations attempt phase =>
      cases transaction with
      | external call =>
          have hkey := hvalid.1
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
                  simp [Concrete.select,
                    Concrete.selectedExternalCandidate, request, tasks]
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
                   simp [Concrete.select,
                     Concrete.selectedExternalCandidate, request])
              | (cases hkey
                 simp [Concrete.select,
                   Concrete.selectedExternalCandidate, request])
      | work item instant rest =>
          simp only [FlightValid, Concrete.Transaction.key?,
            Option.some.injEq] at hvalid
          have hkey : item.key = key := hvalid.1
          cases hkey
          cases item <;>
            simp [Concrete.select, Concrete.selectedWorkCandidate,
              WorkItem.key]
      | scan scanKey instant rest =>
          exact (hnotScan scanKey instant rest rfl).elim

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

theorem NodeValid.cachePut {appConfig : Resonate.Config}
    {node : Concrete.Node} (h : NodeValid appConfig node)
    (key : DocumentKey) (value : Concrete.Versioned key) :
    NodeValid appConfig (node.cachePut key value) := by
  exact h

theorem NodeValid.cacheInvalidate {appConfig : Resonate.Config}
    {node : Concrete.Node} (h : NodeValid appConfig node)
    (key : DocumentKey) :
    NodeValid appConfig (node.cacheInvalidate key) := by
  exact h

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
    (hkey : transaction.key? = some key)
    (hshape : WorkShaped transaction) :
    ∃ next, (Concrete.start appConfig node transaction key).state = .node next ∧
      NodeValid appConfig next := by
  let flight : Concrete.Flight := { key, transaction }
  have hflight : FlightValid appConfig flight :=
    ⟨hkey, trivial, hshape⟩
  cases hcache : node.cacheRead key with
  | none =>
      refine ⟨node.await flight (.get key) |>.1,
        by simp [Concrete.start, flight, hcache], ?_⟩
      exact NodeValid.await hnode hflight _
  | some value =>
      simp only [Concrete.start, flight, hcache]
      cases hselect :
          Concrete.select appConfig flight
            (some (value.document, value.version)) with
      | none =>
          have hselect' :
              Concrete.select appConfig { key, transaction }
                  (some (value.document, value.version)) = none := by
            simpa [flight] using hselect
          exact ⟨node, by simp [Concrete.decide, hselect'], hnode⟩
      | some candidate =>
          let writing : Concrete.Flight := {
            flight with
            loaded := some (value.document, value.version)
            document := some candidate.document
            selected := candidate.outputs
            continuations := candidate.continuations
            phase := .writing
          }
          refine ⟨(node.await writing
              (.put key candidate.document (some value.version))).1,
            ?_, ?_⟩
          · have hselect' :
                Concrete.select appConfig { key, transaction }
                    (some (value.document, value.version)) =
                  some candidate := by
              simpa [flight] using hselect
            simp [Concrete.decide, hselect', writing, flight]
          apply NodeValid.await hnode
          exact ⟨hkey, ⟨candidate.document, rfl,
            select_valid hkey hselect⟩, hshape⟩

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
      exact ⟨hflight.1, ⟨candidate.document, rfl,
        select_valid hflight.1 hselect⟩, hflight.2.2⟩

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
    simpa [FlightValid, loading] using And.intro hflight.1 hflight.2.2
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
                exact NodeValid.start hnode (.scan key now []) key rfl trivial
        | cons entry rest =>
            simp only [hp, Outcomes.one, List.mem_singleton] at hresult
            subst result
            cases entry with
            | occurrence request instant =>
                exact NodeValid.start
                  (node := { node with pending := [] }) hnode
                  (.work (.occurrence request instant) instant rest)
                  (.origin request.id.origin) rfl
                  ⟨request, instant, rfl⟩
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
              exact NodeValid.start hnode (.external call) key hk trivial
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
                      let loaded' := heq ▸ loaded
                      let cached :=
                        match loaded' with
                        | some (document, version) =>
                            next.cachePut flight.key { document, version }
                        | none => next.cacheInvalidate flight.key
                      have hcached : NodeValid appConfig cached := by
                        cases hloaded : loaded' with
                        | none =>
                            simpa [cached, hloaded] using
                              (NodeValid.cacheInvalidate hnext flight.key)
                        | some value =>
                            simpa [cached, hloaded] using
                              (NodeValid.cachePut hnext flight.key {
                                document := value.1
                                version := value.2
                              })
                      exact NodeValid.decide hcached hflight loaded'
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
                      exact NodeValid.retry
                        (NodeValid.cacheInvalidate hnext flight.key) hflight
                    · simp [Outcomes.one] at hresult
                      subst result
                      exact ⟨{
                          next.cacheInvalidate flight.key with
                          workflowBlocked := true },
                        rfl, by
                          intro currentOp current hmem
                          exact NodeValid.cacheInvalidate hnext flight.key
                            currentOp current hmem⟩
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
                exact ⟨{ next.cacheInvalidate flight.key with workflowBlocked :=
                    next.workflowBlocked ||
                      !flight.transaction.isExternal },
                  rfl, by
                    intro currentOp current hmem
                    exact NodeValid.cacheInvalidate hnext flight.key
                      currentOp current hmem⟩

theorem start_ids
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (transaction : Concrete.Transaction) (key : DocumentKey) :
    ∃ next,
      (Concrete.start appConfig node transaction key).state = .node next ∧
      node.nextOp ≤ next.nextOp ∧
      (∀ recipient rpc,
        (recipient, Concrete.Msg.storeRequest rpc) ∈
            (Concrete.start appConfig node transaction key).send →
        rpc.op = node.nextOp ∧ next.nextOp = node.nextOp + 1) ∧
      (∀ recipient₁ rpc₁ recipient₂ rpc₂,
        (recipient₁, Concrete.Msg.storeRequest rpc₁) ∈
            (Concrete.start appConfig node transaction key).send →
        (recipient₂, Concrete.Msg.storeRequest rpc₂) ∈
            (Concrete.start appConfig node transaction key).send →
        rpc₁ = rpc₂) := by
  simp only [Concrete.start]
  cases hcache : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction } (.get key)).1,
        by simp [hcache], by simp [Concrete.Node.await],
        ?_, ?_⟩
      · simp [hcache, Concrete.Node.await]
      · intros
        simp_all [hcache, Concrete.Node.await]
  | some value =>
      simp only [hcache]
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          exact ⟨node, by simp [Concrete.decide, hselect],
            Nat.le_refl _, by simp [Concrete.decide, hselect],
            by simp [Concrete.decide, hselect]⟩
      | some candidate =>
          refine ⟨(node.await {
              key
              transaction
              loaded := some (value.document, value.version)
              document := some candidate.document
              selected := candidate.outputs
              continuations := candidate.continuations
              phase := .writing
            } (.put key candidate.document (some value.version))).1,
            by simp [Concrete.decide, hselect],
            by simp [Concrete.Node.await], ?_, ?_⟩
          · simp [Concrete.decide, hselect, Concrete.Node.await]
          · intros
            simp_all [Concrete.decide, hselect, Concrete.Node.await]

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
                exact start_ids appConfig node (.scan key now []) key
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request instant =>
                simpa [Concrete.PendingEntry.key] using
                  (start_ids appConfig { node with pending := [] }
                    (.work (.occurrence request instant) instant rest)
                    (.origin request.id.origin))
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
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_ids appConfig node (.external call) key
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
                        let loaded' := heq ▸ loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut flight.key {
                                document, version }
                          | none => remaining.cacheInvalidate flight.key
                        cases hs : Concrete.select appConfig flight
                            loaded' with
                        | none =>
                            simp [loaded', cached, Concrete.decide, hs,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨cached, rfl, ?_,
                              by simp, by simp⟩
                            cases hloaded : loaded' <;>
                              simp [loaded', cached, hloaded,
                                Concrete.Node.cachePut,
                                Concrete.Node.cacheInvalidate,
                                takeFlight_nextOp ht]
                        | some candidate =>
                            simp [loaded', cached, Concrete.decide, hs,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_, ?_, ?_⟩
                            · cases hloaded : loaded' <;>
                                simp [loaded', cached, hloaded,
                                  Concrete.Node.cachePut,
                                  Concrete.Node.cacheInvalidate,
                                  Concrete.Node.await,
                                  takeFlight_nextOp ht]
                            · cases hloaded : loaded' <;>
                                simp [loaded', cached, hloaded,
                                  Concrete.Node.cachePut,
                                  Concrete.Node.cacheInvalidate,
                                  Concrete.Node.await,
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
                      cases hdocument : flight.document <;>
                        simp [hdocument, Concrete.Node.cachePut,
                          Concrete.Node.cacheInvalidate,
                          Concrete.Node.remember, takeFlight_nextOp ht] <;>
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
                          simpa [Concrete.Node.cacheInvalidate,
                            takeFlight_nextOp ht]
                      | true =>
                          by_cases hattempt :
                              flight.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_, ?_, ?_⟩
                            · simp [Concrete.Node.cacheInvalidate,
                                Concrete.Node.await,
                                takeFlight_nextOp ht]
                            · simp [Concrete.Node.cacheInvalidate,
                                Concrete.Node.await,
                                takeFlight_nextOp ht]
                            · intros
                              simp_all [Concrete.Node.await]
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨remaining.cacheInvalidate flight.key,
                              rfl, ?_,
                              by
                                intro recipient rpc h
                                simp [Concrete.sendOutputs] at h, by
                                intros
                                simp_all [Concrete.sendOutputs]⟩
                            simpa [Concrete.Node.cacheInvalidate,
                              takeFlight_nextOp ht]
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
                  simpa [Concrete.Node.cacheInvalidate,
                    takeFlight_nextOp ht]

theorem start_old_flight
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    {next : Concrete.Node} {op : Concrete.OpId} {flight : Concrete.Flight}
    (hstate :
      (Concrete.start appConfig node transaction key).state = .node next)
    (hop : op < node.nextOp) (hmem : (op, flight) ∈ next.flights) :
    (op, flight) ∈ node.flights := by
  simp only [Concrete.start] at hstate
  cases hcache : node.cacheRead key with
  | none =>
      simp [hcache, Concrete.Node.await] at hstate
      subst next
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with hnew | hold
      · exact (Nat.ne_of_lt hop hnew.1).elim
      · exact hold
  | some value =>
      simp only [hcache] at hstate
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          simp [Concrete.decide, hselect] at hstate
          subst next
          exact hmem
      | some candidate =>
          simp [Concrete.decide, hselect, Concrete.Node.await] at hstate
          subst next
          simp only [List.mem_cons, Prod.mk.injEq] at hmem
          rcases hmem with hnew | hold
          · exact (Nat.ne_of_lt hop hnew.1).elim
          · exact hold

theorem decide_old_flight
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (current : Concrete.Flight)
    (loaded : Option (Document current.key × Concrete.Version))
    {next : Concrete.Node} {op : Concrete.OpId} {flight : Concrete.Flight}
    (hstate :
      (Concrete.decide appConfig node current loaded).state = .node next)
    (hop : op < node.nextOp) (hmem : (op, flight) ∈ next.flights) :
    (op, flight) ∈ node.flights := by
  cases hselect : Concrete.select appConfig current loaded with
  | none =>
      simp [Concrete.decide, hselect] at hstate
      subst next
      exact hmem
  | some candidate =>
      simp [Concrete.decide, hselect, Concrete.Node.await] at hstate
      subst next
      simp only [List.mem_cons, Prod.mk.injEq] at hmem
      rcases hmem with hnew | hold
      · exact (Nat.ne_of_lt hop hnew.1).elim
      · exact hold

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
                exact start_old_flight appConfig node (.scan key now []) key
                  hstate hop hmem
        | cons entry rest =>
            cases entry with
            | occurrence request instant =>
                simp [hpending, Outcomes.one] at hresult
                subst result
                exact start_old_flight appConfig
                  { node with pending := [] }
                  (.work (.occurrence request instant) instant rest)
                  (.origin request.id.origin) hstate hop hmem
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
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_old_flight appConfig node (.external call) key
                hstate hop hmem
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
                    subst key
                    cases hp : taken.phase with
                    | loading =>
                        simp only [hp] at hresult
                        simp [Outcomes.one] at hresult
                        subst result
                        let loaded' := loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut taken.key {
                                document, version }
                          | none => remaining.cacheInvalidate taken.key
                        have hdecideState :
                            (Concrete.decide appConfig cached taken loaded').state =
                              .node next := by
                          exact hstate
                        have hopCached : op < cached.nextOp := by
                          cases hloaded : loaded' <;>
                            simpa [cached, hloaded,
                              Concrete.Node.cachePut,
                              Concrete.Node.cacheInvalidate,
                              takeFlight_nextOp ht] using hop
                        have hold :=
                          decide_old_flight appConfig cached taken loaded'
                            hdecideState hopCached hmem
                        apply takeFlight_remaining_mem ht
                        cases hloaded : loaded' <;>
                          simpa [cached, hloaded,
                            Concrete.Node.cachePut,
                            Concrete.Node.cacheInvalidate] using hold
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
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      have hremaining :
                          remaining.flights = next.flights := by
                        cases hdocument : taken.document <;>
                          simp [hdocument, Concrete.Node.cachePut,
                            Concrete.Node.cacheInvalidate,
                            Concrete.Node.remember] at hflights ⊢ <;>
                          split at hflights <;> simp_all
                      apply takeFlight_remaining_mem ht
                      exact hremaining ▸ hmem

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
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  change remaining.flights = next.flights at hflights
                  apply takeFlight_remaining_mem ht
                  exact hflights ▸ hmem

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
              Concrete.Node.await, Concrete.Node.remember,
              Concrete.Node.cachePut, Concrete.Node.cacheInvalidate,
              Outcomes.one]
          all_goals grind

def NodeScansValid (bound : Time) (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights →
    ∀ key instant rest,
      flight.transaction = .scan key instant rest →
      instant ≤ bound ∧ key ∈ node.known ∧ rest = []

theorem start_scan_valid
    (appConfig : Resonate.Config) {before now : Time}
    (htime : before ≤ now) (node : Concrete.Node)
    (hscan : NodeScansValid before node)
    (scanKey : DocumentKey) (hknown : scanKey ∈ node.known)
    {next : Concrete.Node}
    (hstate :
      (Concrete.start appConfig node (.scan scanKey now []) scanKey).state =
        .node next) :
    NodeScansValid now next := by
  intro op flight hflight key instant rest htransaction
  simp only [Concrete.start] at hstate
  cases hcache : node.cacheRead scanKey with
  | none =>
      simp [hcache, Concrete.Node.await] at hstate
      subst next
      simp only [List.mem_cons] at hflight
      rcases hflight with hnew | hold
      · cases hnew
        cases htransaction
        exact ⟨Nat.le_refl _, hknown, rfl⟩
      · obtain ⟨hi, hk, hr⟩ :=
          hscan op flight hold key instant rest htransaction
        exact ⟨Nat.le_trans hi htime, hk, hr⟩
  | some value =>
      simp only [hcache] at hstate
      cases hselect :
          Concrete.select appConfig
            { key := scanKey, transaction := .scan scanKey now [] }
            (some (value.document, value.version)) with
      | none =>
          simp [Concrete.decide, hselect] at hstate
          subst next
          obtain ⟨hi, hk, hr⟩ :=
            hscan op flight hflight key instant rest htransaction
          exact ⟨Nat.le_trans hi htime, hk, hr⟩
      | some candidate =>
          simp [Concrete.decide, hselect, Concrete.Node.await] at hstate
          subst next
          simp only [List.mem_cons] at hflight
          rcases hflight with hnew | hold
          · cases hnew
            cases htransaction
            exact ⟨Nat.le_refl _, hknown, rfl⟩
          · obtain ⟨hi, hk, hr⟩ :=
              hscan op flight hold key instant rest htransaction
            exact ⟨Nat.le_trans hi htime, hk, hr⟩

theorem start_non_scan_valid
    (appConfig : Resonate.Config) {before now : Time}
    (htime : before ≤ now) (node : Concrete.Node)
    (hscan : NodeScansValid before node)
    (transaction : Concrete.Transaction)
    (hnotScan :
      ∀ key instant rest, transaction ≠ .scan key instant rest)
    (transactionKey : DocumentKey) {next : Concrete.Node}
    (hstate :
      (Concrete.start appConfig node transaction transactionKey).state =
        .node next) :
    NodeScansValid now next := by
  intro op flight hflight key instant rest htransaction
  simp only [Concrete.start] at hstate
  cases hcache : node.cacheRead transactionKey with
  | none =>
      simp [hcache, Concrete.Node.await] at hstate
      subst next
      simp only [List.mem_cons] at hflight
      rcases hflight with hnew | hold
      · cases hnew
        exact (hnotScan key instant rest htransaction).elim
      · obtain ⟨hi, hk, hr⟩ :=
          hscan op flight hold key instant rest htransaction
        exact ⟨Nat.le_trans hi htime, hk, hr⟩
  | some value =>
      simp only [hcache] at hstate
      cases hselect :
          Concrete.select appConfig { key := transactionKey, transaction }
            (some (value.document, value.version)) with
      | none =>
          simp [Concrete.decide, hselect] at hstate
          subst next
          obtain ⟨hi, hk, hr⟩ :=
            hscan op flight hflight key instant rest htransaction
          exact ⟨Nat.le_trans hi htime, hk, hr⟩
      | some candidate =>
          simp [Concrete.decide, hselect, Concrete.Node.await] at hstate
          subst next
          simp only [List.mem_cons] at hflight
          rcases hflight with hnew | hold
          · cases hnew
            exact (hnotScan key instant rest htransaction).elim
          · obtain ⟨hi, hk, hr⟩ :=
              hscan op flight hold key instant rest htransaction
            exact ⟨Nat.le_trans hi htime, hk, hr⟩

theorem node_step_scans_valid
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    {before now : Time} (htime : before ≤ now)
    (hscan : NodeScansValid before node)
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    NodeScansValid now next := by
  intro op flight hflight key instant rest htransaction
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        cases Concrete.Local.node.inj hstate
        obtain ⟨hinstant, hknown, hrest⟩ :=
          hscan op flight hflight key instant rest htransaction
        exact ⟨Nat.le_trans hinstant htime, hknown, hrest⟩
      · cases hpending : node.pending with
        | nil =>
            simp only [hpending] at hresult
            cases hknown : node.known.head? with
            | none =>
                simp [hknown, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                obtain ⟨hinstant, hknown, hrest⟩ :=
                  hscan op flight hflight key instant rest htransaction
                exact ⟨Nat.le_trans hinstant htime, hknown, hrest⟩
            | some scanKey =>
                simp [hknown, Outcomes.one] at hresult
                subst result
                have hmem : scanKey ∈ node.known := by
                  obtain ⟨tail, hkeys⟩ :=
                    List.head?_eq_some_iff.mp hknown
                  rw [hkeys]
                  exact List.mem_cons_self
                exact start_scan_valid appConfig htime node hscan scanKey
                  hmem hstate op flight hflight key instant rest htransaction
        | cons entry remaining =>
            simp [hpending, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request firing =>
                exact start_non_scan_valid appConfig htime
                  { node with pending := [] }
                  (by simpa [NodeScansValid] using hscan)
                  (.work (.occurrence request firing) firing remaining)
                  (by
                    intro scanKey scanInstant scanRest h
                    cases h)
                  (.origin request.id.origin) hstate op flight hflight key
                  instant rest htransaction
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        repeat' first | split at hresult
      all_goals
        try subst result
        try cases Concrete.Local.node.inj hstate
        simp_all [NodeScansValid, Concrete.Node.takeFlight,
          Concrete.decide, Concrete.retry, Concrete.start,
          Concrete.pureExternal,
          Concrete.Node.await, Concrete.Node.remember,
          Concrete.Node.cachePut, Concrete.Node.cacheInvalidate,
          Outcomes.one]
      all_goals grind

def NodesScansValid
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧
      NodeScansValid world.now node

theorem nodesScansValid_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesScansValid (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by
    simp [NodeScansValid]⟩

theorem nodesScansValid_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hvalidNodes :
      ∀ address, address ∈ nodes → ∀ node,
        world.process (.node address) = .node node →
        NodeValid appConfig node)
    (hinvariant : NodesScansValid world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesScansValid next := by
  cases hstep with
  | inject htime _ _ =>
      intro address haddress
      obtain ⟨node, hnode, hscan⟩ := hinvariant address haddress
      refine ⟨node, by simpa [World.inject] using hnode, ?_⟩
      intro op flight hflight key instant rest htransaction
      obtain ⟨hinstant, hknown, hrest⟩ :=
        hscan op flight hflight key instant rest htransaction
      exact ⟨Nat.le_trans hinstant htime, hknown, hrest⟩
  | outside htime _ =>
      intro address haddress
      obtain ⟨node, hnode, hscan⟩ := hinvariant address haddress
      refine ⟨node, by simpa [World.observeOutside] using hnode, ?_⟩
      intro op flight hflight key instant rest htransaction
      obtain ⟨hinstant, hknown, hrest⟩ :=
        hscan op flight hflight key instant rest htransaction
      exact ⟨Nat.le_trans hinstant htime, hknown, hrest⟩
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress
      obtain ⟨node, hnode, hscan⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        have hnodeValid := hvalidNodes address haddress node hnode
        obtain ⟨after, hstate, _⟩ :=
          node_step_valid hnodeValid (hnode ▸ hresult)
        have hafter :=
          node_step_scans_valid htime hscan (hnode ▸ hresult) hstate
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · refine ⟨node, by simp [World.land, Ne.symm hp, hnode], ?_⟩
        intro op flight hflight key instant rest htransaction
        obtain ⟨hinstant, hknown, hrest⟩ :=
          hscan op flight hflight key instant rest htransaction
        exact ⟨Nat.le_trans hinstant htime, hknown, hrest⟩

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

theorem start_serial_of_empty
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    (hempty : node.flights = []) :
    ∃ next,
      (Concrete.start appConfig node transaction key).state = .node next ∧
      NodeSerial next := by
  simp only [Concrete.start]
  cases hcache : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction } (.get key)).1,
        by simp [hcache], ?_⟩
      simp [NodeSerial, Concrete.Node.await, hempty]
  | some value =>
      simp only [hcache]
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          exact ⟨node, by simp [Concrete.decide, hselect], by
            simp [NodeSerial, hempty]⟩
      | some candidate =>
          refine ⟨(node.await {
              key
              transaction
              loaded := some (value.document, value.version)
              document := some candidate.document
              selected := candidate.outputs
              continuations := candidate.continuations
              phase := .writing
            } (.put key candidate.document (some value.version))).1,
            by simp [Concrete.decide, hselect], ?_⟩
          simp [NodeSerial, Concrete.Node.await, hempty]

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
                have hempty : node.flights = [] := by simp_all
                exact start_serial_of_empty appConfig node
                  (.scan key now []) key hempty
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            have hempty : node.flights = [] := by
              simp_all
            cases entry with
            | occurrence request firing =>
                exact start_serial_of_empty appConfig
                  { node with pending := [] }
                  (.work (.occurrence request firing) firing rest)
                  (.origin request.id.origin) (by simpa using hempty)
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
              simp [hk, Outcomes.one] at hresult
              subst result
              have hempty : node.flights = [] := by
                simp_all
              exact start_serial_of_empty appConfig node (.external call)
                key hempty
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
                Concrete.Node.remember, Concrete.Node.cachePut,
                Concrete.Node.cacheInvalidate, Outcomes.one]
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

theorem start_internal_clean_of_empty
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    (hempty : node.flights = [])
    (hbase :
      transaction.isExternal = false →
        node.pending = [] ∧ node.workflowBlocked = false) :
    ∃ next,
      (Concrete.start appConfig node transaction key).state = .node next ∧
      NodeInternalClean next := by
  simp only [Concrete.start]
  cases hcache : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction } (.get key)).1,
        by simp [hcache], ?_⟩
      intro op flight hflight hinternal
      simp [Concrete.Node.await, hempty] at hflight
      rcases hflight with ⟨_, rfl⟩
      simpa [Concrete.Node.await] using hbase hinternal
  | some value =>
      simp only [hcache]
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          exact ⟨node, by simp [Concrete.decide, hselect], by
            simp [NodeInternalClean, hempty]⟩
      | some candidate =>
          refine ⟨(node.await {
              key
              transaction
              loaded := some (value.document, value.version)
              document := some candidate.document
              selected := candidate.outputs
              continuations := candidate.continuations
              phase := .writing
            } (.put key candidate.document (some value.version))).1,
            by simp [Concrete.decide, hselect], ?_⟩
          intro op flight hflight hinternal
          simp [Concrete.Node.await, hempty] at hflight
          rcases hflight with ⟨_, rfl⟩
          simpa [Concrete.Node.await] using hbase hinternal

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
                exact start_internal_clean_of_empty appConfig node
                  (.scan key now []) key hflights (by
                    intro
                    exact ⟨hp, hblocked⟩)
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            have hempty : node.flights = [] := by simp_all
            cases entry with
            | occurrence request firing =>
                exact start_internal_clean_of_empty appConfig
                  { node with pending := [] }
                  (.work (.occurrence request firing) firing rest)
                  (.origin request.id.origin) (by simpa using hempty) (by
                    intro
                    exact ⟨rfl, hblocked⟩)
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
              simp [hk, Outcomes.one] at hresult
              subst result
              have hempty : node.flights = [] := by simp_all
              exact start_internal_clean_of_empty appConfig node
                (.external call) key hempty (by
                  simp [Concrete.Transaction.isExternal])
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
                Concrete.Node.await, Concrete.Node.remember,
                Concrete.Node.cachePut, Concrete.Node.cacheInvalidate,
                Outcomes.one]
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
  | inject htime _ _ =>
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

theorem reachable_nodes_scans_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesScansValid world := by
  induction hreachable with
  | init hinit => exact nodesScansValid_initial hinit
  | step hreachable hstep ih =>
      exact nodesScansValid_step (fun address haddress node hnode =>
        by
          obtain ⟨actual, hactual, hvalid⟩ :=
            reachable_nodes_valid hreachable address haddress
          rw [hnode] at hactual
          cases Concrete.Local.node.inj hactual
          exact hvalid) ih hstep

theorem reachable_scan_flight_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    {key : DocumentKey} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .scan key instant rest) :
    instant ≤ world.now ∧ key ∈ node.known ∧ rest = [] := by
  obtain ⟨actual, hactual, hscan⟩ :=
    reachable_nodes_scans_valid hreachable address haddress
  rw [hnode] at hactual
  cases Concrete.Local.node.inj hactual
  exact hscan op flight hflight key instant rest htransaction

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
  | inject htime _ _ =>
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

theorem NodeLoadingGets.cachePut
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (h : NodeLoadingGets world address node)
    (key : DocumentKey) (value : Concrete.Versioned key) :
    NodeLoadingGets world address (node.cachePut key value) := by
  intro op flight hmem hphase
  exact h (by
    simpa [Concrete.Node.cachePut] using hmem) hphase

theorem NodeLoadingGets.cacheInvalidate
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (h : NodeLoadingGets world address node)
    (key : DocumentKey) :
    NodeLoadingGets world address (node.cacheInvalidate key) := by
  intro op flight hmem hphase
  exact h (by
    simpa [Concrete.Node.cacheInvalidate] using hmem) hphase

theorem start_loading_gets
    {nodes : List Addr} (appConfig : Resonate.Config)
    {world : World (CModel nodes appConfig)}
    (address : Addr) (node : Concrete.Node)
    (hinvariant : NodeLoadingGets world address node)
    (now : Time) (transaction : Concrete.Transaction)
    (key : DocumentKey) :
    ∃ next,
      (Concrete.start appConfig node transaction key).state = .node next ∧
      NodeLoadingGets
        (world.land (.node address) now
          (Concrete.start appConfig node transaction key))
        address next := by
  simp only [Concrete.start]
  cases hcache : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction } (.get key)).1,
        by simp [hcache], ?_⟩
      intro op flight hmem hphase
      simp only [Concrete.Node.await, List.mem_cons] at hmem
      rcases hmem with hnew | hold
      · cases hnew
        simp [World.land, hcache, Concrete.Node.await]
      · exact List.mem_append_left _
          (hinvariant hold hphase)
  | some value =>
      simp only [hcache]
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          refine ⟨node, by simp [Concrete.decide, hselect], ?_⟩
          exact hinvariant.mono fun message hmessage =>
            List.mem_append_left _ hmessage
      | some candidate =>
          refine ⟨(node.await {
              key
              transaction
              loaded := some (value.document, value.version)
              document := some candidate.document
              selected := candidate.outputs
              continuations := candidate.continuations
              phase := .writing
            } (.put key candidate.document (some value.version))).1,
            by simp [Concrete.decide, hselect], ?_⟩
          intro op flight hmem hphase
          simp only [Concrete.Node.await, List.mem_cons] at hmem
          rcases hmem with hnew | hold
          · cases hnew
            cases hphase
          · exact List.mem_append_left _
              (hinvariant hold hphase)

theorem decide_loading_gets
    {nodes : List Addr} (appConfig : Resonate.Config)
    {world : World (CModel nodes appConfig)}
    (address : Addr) (node : Concrete.Node)
    (hinvariant : NodeLoadingGets world address node)
    (now : Time) (current : Concrete.Flight)
    (loaded : Option (Document current.key × Concrete.Version)) :
    ∃ next,
      (Concrete.decide appConfig node current loaded).state = .node next ∧
      NodeLoadingGets
        (world.land (.node address) now
          (Concrete.decide appConfig node current loaded))
        address next := by
  cases hselect : Concrete.select appConfig current loaded with
  | none =>
      refine ⟨node, by simp [Concrete.decide, hselect], ?_⟩
      exact hinvariant.mono fun message hmessage =>
        List.mem_append_left _ hmessage
  | some candidate =>
      refine ⟨(node.await {
          current with
          loaded
          document := some candidate.document
          selected := candidate.outputs
          continuations := candidate.continuations
          phase := .writing
        } (.put current.key candidate.document (loaded.map (·.2)))).1,
        by simp [Concrete.decide, hselect], ?_⟩
      intro op flight hmem hphase
      simp only [Concrete.Node.await, List.mem_cons] at hmem
      rcases hmem with hnew | hold
      · cases hnew
        cases hphase
      · exact List.mem_append_left _
          (hinvariant hold hphase)

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
                exact start_loading_gets appConfig address node hinvariant
                  now (.scan key now []) key
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request firing =>
                exact start_loading_gets appConfig address
                  { node with pending := [] }
                  (by
                    intro op flight hmem hphase
                    exact hinvariant (by simpa using hmem) hphase)
                  now
                  (.work (.occurrence request firing) firing rest)
                  (.origin request.id.origin)
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
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_loading_gets appConfig address node hinvariant
                now (.external call) key
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
                        simp only [hp] at hresult
                        let loaded' := heq ▸ loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut taken.key {
                                document, version }
                          | none => remaining.cacheInvalidate taken.key
                        have hcached :
                            NodeLoadingGets world address cached := by
                          intro currentOp current hmem hphase
                          cases hloaded : loaded' with
                          | none =>
                              exact (hremaining.cacheInvalidate taken.key)
                                (by simpa [cached, hloaded] using hmem) hphase
                          | some value =>
                              obtain ⟨document, version⟩ := value
                              exact (hremaining.cachePut taken.key {
                                  document, version })
                                (by simpa [cached, hloaded] using hmem) hphase
                        simp [loaded', cached, Outcomes.one] at hresult
                        subst result
                        exact decide_loading_gets appConfig address cached
                          hcached now taken loaded'
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
                    simp [ht, hp, Concrete.Node.cachePut,
                      Concrete.Node.cacheInvalidate, Concrete.Node.remember,
                      Outcomes.one] at hresult
                  · subst result
                    exact ⟨remaining, rfl, hold remaining hremaining⟩
                  · subst result
                    cases hdocument : taken.document <;>
                      refine ⟨_, rfl, ?_⟩
                    all_goals
                      intro op flight hmem hphase
                      apply hold remaining hremaining
                      · simp only [Concrete.Node.remember] at hmem
                        split at hmem <;>
                          simpa [Concrete.Node.cachePut,
                            Concrete.Node.cacheInvalidate] using hmem
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
                      simp [ht, hp, Concrete.Node.cacheInvalidate,
                        Outcomes.one] at hresult
                      subst result
                      exact ⟨remaining, rfl, hold remaining hremaining⟩
                  | writing =>
                      cases hext : taken.transaction.isExternal with
                      | false =>
                          simp [ht, hp, hext,
                            Concrete.Node.cacheInvalidate,
                            Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_⟩
                          intro op flight hmem hphase
                          exact hold remaining hremaining hmem hphase
                      | true =>
                          by_cases hattempt :
                              taken.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Concrete.Node.cacheInvalidate,
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
                              Concrete.Node.cacheInvalidate,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro currentOp current hmem hphase
                            exact hold remaining hremaining
                              (by simpa using hmem) hphase
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
                  simp [ht, Concrete.Node.cacheInvalidate,
                    Outcomes.one] at hresult
                  subst result
                  refine ⟨_, rfl, ?_⟩
                  intro op flight hmem hphase
                  exact hold remaining hremaining (by simpa using hmem)
                    hphase

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

theorem NodeWritingPuts.cachePut
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (h : NodeWritingPuts world address node)
    (key : DocumentKey) (value : Concrete.Versioned key) :
    NodeWritingPuts world address (node.cachePut key value) := by
  intro op flight hmem hphase
  exact h (by simpa [Concrete.Node.cachePut] using hmem) hphase

theorem NodeWritingPuts.cacheInvalidate
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (h : NodeWritingPuts world address node)
    (key : DocumentKey) :
    NodeWritingPuts world address (node.cacheInvalidate key) := by
  intro op flight hmem hphase
  exact h (by simpa [Concrete.Node.cacheInvalidate] using hmem) hphase

theorem start_writing_puts
    {nodes : List Addr} (appConfig : Resonate.Config)
    {world : World (CModel nodes appConfig)}
    (address : Addr) (node : Concrete.Node)
    (hinvariant : NodeWritingPuts world address node)
    (now : Time) (transaction : Concrete.Transaction)
    (key : DocumentKey) :
    ∃ next,
      (Concrete.start appConfig node transaction key).state = .node next ∧
      NodeWritingPuts
        (world.land (.node address) now
          (Concrete.start appConfig node transaction key))
        address next := by
  simp only [Concrete.start]
  cases hcache : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction } (.get key)).1,
        by simp [hcache], ?_⟩
      intro op flight hmem hphase
      simp only [Concrete.Node.await, List.mem_cons] at hmem
      rcases hmem with hnew | hold
      · cases hnew
        cases hphase
      · obtain ⟨document, hdocument, hput⟩ :=
          hinvariant hold hphase
        exact ⟨document, hdocument,
          List.mem_append_left _ hput⟩
  | some value =>
      simp only [hcache]
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          refine ⟨node, by simp [Concrete.decide, hselect], ?_⟩
          exact hinvariant.mono fun message hmessage =>
            List.mem_append_left _ hmessage
      | some candidate =>
          refine ⟨(node.await {
              key
              transaction
              loaded := some (value.document, value.version)
              document := some candidate.document
              selected := candidate.outputs
              continuations := candidate.continuations
              phase := .writing
            } (.put key candidate.document (some value.version))).1,
            by simp [Concrete.decide, hselect], ?_⟩
          intro op flight hmem hphase
          simp only [Concrete.Node.await, List.mem_cons] at hmem
          rcases hmem with hnew | hold
          · cases hnew
            refine ⟨candidate.document, rfl, ?_⟩
            simp [World.land, Concrete.decide, hselect,
              Concrete.Node.await]
          · obtain ⟨document, hdocument, hput⟩ :=
              hinvariant hold hphase
            exact ⟨document, hdocument,
              List.mem_append_left _ hput⟩

theorem decide_writing_puts
    {nodes : List Addr} (appConfig : Resonate.Config)
    {world : World (CModel nodes appConfig)}
    (address : Addr) (node : Concrete.Node)
    (hinvariant : NodeWritingPuts world address node)
    (now : Time) (current : Concrete.Flight)
    (loaded : Option (Document current.key × Concrete.Version)) :
    ∃ next,
      (Concrete.decide appConfig node current loaded).state = .node next ∧
      NodeWritingPuts
        (world.land (.node address) now
          (Concrete.decide appConfig node current loaded))
        address next := by
  cases hselect : Concrete.select appConfig current loaded with
  | none =>
      refine ⟨node, by simp [Concrete.decide, hselect], ?_⟩
      exact hinvariant.mono fun message hmessage =>
        List.mem_append_left _ hmessage
  | some candidate =>
      refine ⟨(node.await {
          current with
          loaded
          document := some candidate.document
          selected := candidate.outputs
          continuations := candidate.continuations
          phase := .writing
        } (.put current.key candidate.document (loaded.map (·.2)))).1,
        by simp [Concrete.decide, hselect], ?_⟩
      intro op flight hmem hphase
      simp only [Concrete.Node.await, List.mem_cons] at hmem
      rcases hmem with hnew | hold
      · cases hnew
        refine ⟨candidate.document, rfl, ?_⟩
        simp [World.land, Concrete.decide, hselect,
          Concrete.Node.await]
      · obtain ⟨document, hdocument, hput⟩ :=
          hinvariant hold hphase
        exact ⟨document, hdocument,
          List.mem_append_left _ hput⟩

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
                exact start_writing_puts appConfig address node hinvariant
                  now (.scan key now []) key
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request firing =>
                exact start_writing_puts appConfig address
                  { node with pending := [] }
                  (by
                    intro op flight hmem hphase
                    exact hinvariant (by simpa using hmem) hphase)
                  now (.work (.occurrence request firing) firing rest)
                  (.origin request.id.origin)
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
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_writing_puts appConfig address node hinvariant
                now (.external call) key
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
                        let loaded' := heq ▸ loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut taken.key {
                                document, version }
                          | none => remaining.cacheInvalidate taken.key
                        have hcached :
                            NodeWritingPuts world address cached := by
                          intro currentOp current hmem hphase
                          cases hloaded : loaded' with
                          | none =>
                              exact (hremaining.cacheInvalidate taken.key)
                                (by simpa [cached, hloaded] using hmem) hphase
                          | some value =>
                              obtain ⟨document, version⟩ := value
                              exact (hremaining.cachePut taken.key {
                                  document, version })
                                (by simpa [cached, hloaded] using hmem) hphase
                        simp [loaded', cached, Outcomes.one] at hresult
                        subst result
                        exact decide_writing_puts appConfig address cached
                          hcached now taken loaded'
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
                      simp [ht, hp, Concrete.Node.cachePut,
                        Concrete.Node.cacheInvalidate, Concrete.Node.remember,
                        Outcomes.one] at hresult
                      subst result
                      cases hdocument : taken.document <;>
                        refine ⟨_, rfl, hold _ ?_⟩
                      all_goals
                        intro op flight hmem hphase
                        simp only [Concrete.Node.remember] at hmem
                        split at hmem <;>
                          exact hremaining
                            (by simpa [Concrete.Node.cachePut,
                              Concrete.Node.cacheInvalidate] using hmem)
                            hphase
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
                          simp [ht, hp, hext,
                            Concrete.Node.cacheInvalidate,
                            Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, hold _ ?_⟩
                          intro op flight hmem hphase
                          exact hremaining (by simpa using hmem) hphase
                      | true =>
                          by_cases hattempt :
                              taken.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Concrete.Node.cacheInvalidate,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro op flight hmem hphase
                            simp only [Concrete.Node.await,
                              Concrete.Node.cacheInvalidate,
                              List.mem_cons] at hmem
                            rcases hmem with hnew | holdMem
                            · have hp := congrArg
                                (fun pair :
                                  Concrete.OpId × Concrete.Flight =>
                                  pair.2.phase) hnew
                              simp [hphase] at hp
                            · exact hold remaining hremaining holdMem hphase
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Concrete.Node.cacheInvalidate,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, hold _ ?_⟩
                            intro op flight hmem hphase
                            exact hremaining (by simpa using hmem) hphase
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
                  simp [ht, Concrete.Node.cacheInvalidate,
                    Outcomes.one] at hresult
                  subst result
                  refine ⟨_, rfl, hold _ ?_⟩
                  intro op flight hmem hphase
                  exact hremaining (by simpa using hmem) hphase

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

theorem start_put_valid {appConfig : Resonate.Config}
    {node : Concrete.Node} {transaction : Concrete.Transaction}
    {transactionKey : DocumentKey}
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
    })
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey).send) :
    ValidPut appConfig key document expectedVersion := by
  simp only [Concrete.start] at hmessage
  cases hcache : node.cacheRead transactionKey with
  | none =>
      simp [hcache, Concrete.Node.await] at hmessage
  | some value =>
      simp only [hcache] at hmessage
      exact decide_put_valid hflight hmessage

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
              simp [hk, Outcomes.one] at hresult
              subst result
              apply start_put_valid
                (transaction := .scan knownKey now [])
                (transactionKey := knownKey)
              · exact ⟨rfl, trivial, trivial⟩
              · exact hsend
        | cons item rest =>
          simp [hp, Outcomes.one] at hresult
          subst result
          cases item with
          | occurrence request firing =>
              apply start_put_valid
                (transaction :=
                  .work (.occurrence request firing) firing rest)
                (transactionKey := .origin request.id.origin)
              · exact ⟨rfl, trivial,
                  ⟨request, firing, rfl⟩⟩
              · exact hsend
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
              simp [hk, Outcomes.one] at hresult
              subst result
              apply start_put_valid
                (transaction := .external call)
                (transactionKey := requestKey)
              · exact ⟨hk, trivial, trivial⟩
              · exact hsend
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

theorem start_no_store_reply
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {transaction : Concrete.Transaction} {key : DocumentKey}
    {recipient : Concrete.Pid} {reply : Concrete.RpcReply}
    (hsend :
      (recipient, Concrete.Msg.storeReply reply) ∈
        (Concrete.start appConfig node transaction key).send) : False := by
  simp only [Concrete.start] at hsend
  cases hcache : node.cacheRead key with
  | none =>
      simp [hcache, Concrete.Node.await] at hsend
  | some value =>
      simp only [hcache] at hsend
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          simp [Concrete.decide, hselect] at hsend
      | some candidate =>
          simp [Concrete.decide, hselect, Concrete.Node.await] at hsend

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
                simp [hk, Outcomes.one] at hresult
                subst result
                exact start_no_store_reply hsend
        | cons item rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            exact start_no_store_reply hsend
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
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_no_store_reply hsend
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

def TransactionOrigin
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) (address : Addr) :
    Concrete.Transaction → Prop
  | .external call =>
      (Concrete.Pid.outside, .node address, .request call) ∈ world.network
  | .work item _ _ =>
      ∃ request semanticTime,
        item = .occurrence request semanticTime
  | .scan _ instant _ => instant ≤ world.now

def FlightRequestOrigins
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ {address node op flight call},
    address ∈ nodes →
    world.process (.node address) = .node node →
    (op, flight) ∈ node.flights →
    flight.transaction = .external call →
    (Concrete.Pid.outside, .node address, .request call) ∈ world.network

def NodeCacheSnapshots (store : Concrete.Store)
    (node : Concrete.Node) : Prop :=
  ∀ key value,
    node.cacheRead key = some value →
    Snapshot store key (some (value.document, value.version))

theorem cacheRead_filter_other (entries : List Concrete.CacheEntry)
    (removed query : DocumentKey) (hne : query ≠ removed) :
    (entries.filter (·.key != removed)).findSome?
        (·.read query) =
      entries.findSome? (·.read query) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      by_cases hk : entry.key = removed
      · subst removed
        simp [Concrete.CacheEntry.read, hne, Ne.symm hne, ih]
        simpa only [Concrete.CacheEntry.read] using ih
      · have hb : (entry.key != removed) = true := by simp [hk]
        cases hread : entry.read query <;>
          simp [List.filter_cons, hb, hread, ih]

@[simp] theorem cacheRead_cachePut_same (node : Concrete.Node)
    (key : DocumentKey) (value : Concrete.Versioned key) :
    (node.cachePut key value).cacheRead key = some value := by
  simp [Concrete.Node.cachePut, Concrete.Node.cacheRead,
    Concrete.CacheEntry.read]

theorem cacheRead_cachePut_other (node : Concrete.Node)
    (key other : DocumentKey) (value : Concrete.Versioned key)
    (hne : other ≠ key) :
    (node.cachePut key value).cacheRead other = node.cacheRead other := by
  simp only [Concrete.Node.cachePut, Concrete.Node.cacheRead]
  have hhead :
      (Concrete.CacheEntry.mk key value).read other = none := by
    simp [Concrete.CacheEntry.read, Ne.symm hne]
  rw [List.findSome?_cons, hhead]
  rw [cacheRead_filter_other node.cache key other hne]

@[simp] theorem cacheRead_cacheInvalidate_same (node : Concrete.Node)
    (key : DocumentKey) :
    (node.cacheInvalidate key).cacheRead key = none := by
  unfold Concrete.Node.cacheInvalidate Concrete.Node.cacheRead
  induction node.cache with
  | nil => rfl
  | cons entry rest ih =>
      by_cases hk : entry.key = key
      · subst key
        simp [Concrete.CacheEntry.read, ih]
      · simp [Concrete.CacheEntry.read, hk, ih]

theorem cacheRead_cacheInvalidate_other (node : Concrete.Node)
    (key other : DocumentKey) (hne : other ≠ key) :
    (node.cacheInvalidate key).cacheRead other = node.cacheRead other := by
  exact cacheRead_filter_other node.cache key other hne

@[simp] theorem cacheLoaded_flights (node : Concrete.Node)
    (key : DocumentKey)
    (loaded : Option (Document key × Concrete.Version)) :
    (match loaded with
     | some (document, version) =>
         node.cachePut key { document, version }
     | none => node.cacheInvalidate key).flights = node.flights := by
  cases loaded <;> rfl

theorem NodeCacheSnapshots.cachePut
    {store : Concrete.Store} {node : Concrete.Node}
    (h : NodeCacheSnapshots store node)
    (key : DocumentKey) (value : Concrete.Versioned key)
    (hsnapshot :
      Snapshot store key (some (value.document, value.version))) :
    NodeCacheSnapshots store (node.cachePut key value) := by
  intro other cached hread
  by_cases heq : other = key
  · subst other
    rw [cacheRead_cachePut_same] at hread
    cases Option.some.inj hread
    exact hsnapshot
  · rw [cacheRead_cachePut_other node key other value heq] at hread
    exact h other cached hread

theorem NodeCacheSnapshots.cacheInvalidate
    {store : Concrete.Store} {node : Concrete.Node}
    (h : NodeCacheSnapshots store node) (key : DocumentKey) :
    NodeCacheSnapshots store (node.cacheInvalidate key) := by
  intro other cached hread
  by_cases heq : other = key
  · subst other
    rw [cacheRead_cacheInvalidate_same] at hread
    contradiction
  · rw [cacheRead_cacheInvalidate_other node key other heq] at hread
    exact h other cached hread

theorem NodeCacheSnapshots.takeFlight
    {store : Concrete.Store} {node remaining : Concrete.Node}
    (h : NodeCacheSnapshots store node) (op : Concrete.OpId)
    (htake : (node.takeFlight op).2 = remaining) :
    NodeCacheSnapshots store remaining := by
  intro key value hread
  have hcache :
      (node.takeFlight op).2.cacheRead key = node.cacheRead key := by
    simp [Concrete.Node.takeFlight, Concrete.Node.cacheRead]
  rw [htake] at hcache
  exact h key value (hcache ▸ hread)

theorem NodeCacheSnapshots.remember
    {store : Concrete.Store} {node : Concrete.Node}
    (h : NodeCacheSnapshots store node) (key : DocumentKey) :
    NodeCacheSnapshots store (node.remember key) := by
  unfold Concrete.Node.remember
  split <;> exact h

theorem decide_cache_snapshots
    (appConfig : Resonate.Config) {store : Concrete.Store}
    (node : Concrete.Node) (hcache : NodeCacheSnapshots store node)
    (current : Concrete.Flight)
    (loaded : Option (Document current.key × Concrete.Version)) :
    ∃ next,
      (Concrete.decide appConfig node current loaded).state = .node next ∧
      NodeCacheSnapshots store next := by
  cases hselect : Concrete.select appConfig current loaded with
  | none =>
      exact ⟨node, by simp [Concrete.decide, hselect], hcache⟩
  | some candidate =>
      refine ⟨(node.await {
          current with
          loaded
          document := some candidate.document
          selected := candidate.outputs
          continuations := candidate.continuations
          phase := .writing
        } (.put current.key candidate.document (loaded.map (·.2)))).1,
        by simp [Concrete.decide, hselect], ?_⟩
      intro key value hread
      change node.cacheRead key = some value at hread
      exact hcache key value hread

theorem start_cache_snapshots
    (appConfig : Resonate.Config) {store : Concrete.Store}
    (node : Concrete.Node) (hcache : NodeCacheSnapshots store node)
    (transaction : Concrete.Transaction) (key : DocumentKey) :
    ∃ next,
      (Concrete.start appConfig node transaction key).state = .node next ∧
      NodeCacheSnapshots store next := by
  simp only [Concrete.start]
  cases hread : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction } (.get key)).1,
        by simp [hread], ?_⟩
      intro other value hcached
      change node.cacheRead other = some value at hcached
      exact hcache other value hcached
  | some value =>
      simp only [hread]
      exact decide_cache_snapshots appConfig node hcache
        { key, transaction } (some (value.document, value.version))

def CacheSnapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes → ∀ {store node},
    world.process .store = .store store →
    world.process (.node address) = .node node →
    NodeCacheSnapshots store node

theorem node_step_cache_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (hstore : world.process .store = .store store)
    (hcache : NodeCacheSnapshots store node)
    (hgots : GotSnapshots world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (hvalid : event.Valid world (.node address))
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧ NodeCacheSnapshots store next := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hcache⟩
      · cases hp : node.pending with
        | nil =>
            simp only [hp] at hresult
            cases hk : node.known.head? with
            | none =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hcache⟩
            | some key =>
                simp [hk, Outcomes.one] at hresult
                subst result
                exact start_cache_snapshots appConfig node hcache
                  (.scan key now []) key
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request firing =>
                exact start_cache_snapshots appConfig
                  { node with pending := [] }
                  (by
                    intro key value hread
                    change node.cacheRead key = some value at hread
                    exact hcache key value hread)
                  (.work (.occurrence request firing) firing rest)
                  (.origin request.id.origin)
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hcache⟩
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          exact ⟨node, rfl, hcache⟩
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              exact ⟨node, rfl, hcache⟩
          | some key =>
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_cache_snapshots appConfig node hcache
                (.external call) key
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
                  exact ⟨node, rfl, hcache⟩
              | some flight =>
                  have hremaining : NodeCacheSnapshots store remaining :=
                    hcache.takeFlight replyOp
                      (by simpa [ht])
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    subst loadedKey
                    cases hp : flight.phase with
                    | loading =>
                        simp only [hp] at hresult
                        have hsnapshot : Snapshot store flight.key loaded :=
                          hgots hstore hvalid
                        cases hloaded : loaded with
                        | none =>
                            simp [hloaded, Outcomes.one] at hresult
                            subst result
                            exact decide_cache_snapshots appConfig
                              (remaining.cacheInvalidate flight.key)
                              (hremaining.cacheInvalidate flight.key)
                              flight none
                        | some value =>
                            obtain ⟨document, version⟩ := value
                            simp [hloaded, Outcomes.one] at hresult
                            subst result
                            exact decide_cache_snapshots appConfig
                              (remaining.cachePut flight.key {
                                document, version })
                              (hremaining.cachePut flight.key {
                                  document, version } (by
                                simpa [hloaded] using hsnapshot))
                              flight (some (document, version))
                    | writing =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        exact ⟨remaining, rfl, hremaining⟩
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨remaining, rfl, hremaining⟩
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hcache⟩
              | some flight =>
                  have hremaining : NodeCacheSnapshots store remaining :=
                    hcache.takeFlight replyOp (by simpa [ht])
                  cases hp : flight.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨remaining, rfl, hremaining⟩
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      refine ⟨_, rfl, ?_⟩
                      intro key value hread
                      apply hremaining key value
                      simp only [Concrete.Node.remember] at hread
                      split at hread <;>
                        exact hread
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hcache⟩
              | some flight =>
                  have hremaining : NodeCacheSnapshots store remaining :=
                    hcache.takeFlight replyOp (by simpa [ht])
                  cases hp : flight.phase with
                  | loading =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨remaining, rfl, hremaining⟩
                  | writing =>
                      cases hext : flight.transaction.isExternal with
                      | false =>
                          simp [ht, hp, hext, Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_⟩
                          intro key value hread
                          change
                            (remaining.cacheInvalidate flight.key).cacheRead
                                key = some value at hread
                          exact (hremaining.cacheInvalidate flight.key)
                            key value hread
                      | true =>
                          by_cases hattempt :
                              flight.attempt < config.retries
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            refine ⟨_, rfl, ?_⟩
                            intro key value hread
                            change
                              (remaining.cacheInvalidate flight.key).cacheRead
                                  key = some value at hread
                            exact (hremaining.cacheInvalidate flight.key)
                              key value hread
                          · simp [ht, hp, hext, Concrete.retry, hattempt,
                              Outcomes.one] at hresult
                            subst result
                            exact ⟨_, rfl,
                              hremaining.cacheInvalidate flight.key⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hcache⟩
              | some flight =>
                  have hremaining : NodeCacheSnapshots store remaining :=
                    hcache.takeFlight replyOp (by simpa [ht])
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  refine ⟨_, rfl, ?_⟩
                  intro key value hread
                  change
                    (remaining.cacheInvalidate flight.key).cacheRead key =
                      some value at hread
                  exact (hremaining.cacheInvalidate flight.key)
                    key value hread

theorem cacheSnapshots_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    CacheSnapshots (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress store node hstore hnode
  simp only [World.initial] at hstore hnode
  have hs := hinit.2.1
  rw [hs] at hstore
  cases Concrete.Local.store.inj hstore
  have hn := hinit.2.2 address haddress
  rw [hn] at hnode
  cases Concrete.Local.node.inj hnode
  intro key value hread
  simp [Concrete.Node.cacheRead] at hread

theorem cacheSnapshots_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hstoreExists : StoreExists world)
    (hnodes : NodesValid world)
    (hgots : GotSnapshots world)
    (hinvariant : CacheSnapshots world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    CacheSnapshots next := by
  cases hstep with
  | inject =>
      intro address haddress store node hstore hnode
      exact hinvariant address haddress hstore hnode
  | outside =>
      intro address haddress store node hstore hnode
      exact hinvariant address haddress hstore hnode
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress store node hstoreNext hnodeNext
      obtain ⟨beforeStore, hbeforeStore⟩ := hstoreExists
      by_cases hpStore : pid = Concrete.Pid.store
      · subst pid
        have hnodeOld :
            world.process (.node address) = .node node := by
          simpa [World.land] using hnodeNext
        have hcache :=
          hinvariant address haddress hbeforeStore hnodeOld
        have hresult' := hresult
        rw [hbeforeStore] at hresult'
        obtain ⟨afterStore, hstate, heffect⟩ :=
          store_step_effect hresult'
        have heq : afterStore = store := by
          simpa [World.land, hstate] using hstoreNext
        subst afterStore
        rcases heffect with hsame | ⟨key, document, hcommit⟩
        · subst store
          exact hcache
        · subst store
          intro key value hread
          exact Snapshot.commit (hcache key value hread)
      · have hstoreOld :
            world.process .store = .store store := by
          simpa [World.land, Ne.symm hpStore] using hstoreNext
        by_cases hpNode : pid = .node address
        · subst pid
          obtain ⟨before, hbefore, _⟩ :=
            hnodes address haddress
          have hcache :=
            hinvariant address haddress hstoreOld hbefore
          obtain ⟨after, hstate, hafter⟩ :=
            node_step_cache_snapshots hstoreOld hcache hgots hvalid
              (hbefore ▸ hresult)
          have heq : after = node := by
            have hx : result.state = .node node := by
              simpa [World.land] using hnodeNext
            rw [hstate] at hx
            exact Concrete.Local.node.inj hx
          subst after
          exact hafter
        · have hnodeOld :
              world.process (.node address) = .node node := by
            simpa [World.land, Ne.symm hpNode] using hnodeNext
          exact hinvariant address haddress hstoreOld hnodeOld

theorem reachable_cache_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    CacheSnapshots world := by
  induction hreachable with
  | init hinit => exact cacheSnapshots_initial hinit
  | step hreachable hstep ih =>
      exact cacheSnapshots_step
        (reachable_store_exists hreachable)
        (reachable_nodes_valid hreachable)
        (reachable_got_snapshots hreachable)
        ih hstep

theorem start_put_snapshot
    {appConfig : Resonate.Config} {store : Concrete.Store}
    {node : Concrete.Node} {transaction : Concrete.Transaction}
    {transactionKey : DocumentKey}
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
    })
    (hcache : NodeCacheSnapshots store node)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded := by
  simp only [Concrete.start] at hmessage
  cases hcached : node.cacheRead transactionKey with
  | none =>
      simp [hcached, Concrete.Node.await] at hmessage
  | some value =>
      simp only [hcached] at hmessage
      cases hselect :
          Concrete.select appConfig { key := transactionKey, transaction }
            (some (value.document, value.version)) with
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
            transaction
            loaded := some (value.document, value.version)
            outputs := candidate.outputs
            continuations := candidate.continuations
            expected_eq := rfl
            selected := select_valid hflight.1 hselect
          }, hcache transactionKey value hcached⟩

theorem node_step_sent_put_snapshot
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (hstore : world.process .store = .store store)
    (hnode : NodeValid appConfig node)
    (hcache : NodeCacheSnapshots store node)
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
                simp [hk, Outcomes.one] at hresult
                subst result
                apply start_put_snapshot
                  (transaction := .scan knownKey now [])
                  (transactionKey := knownKey)
                · exact ⟨rfl, trivial, trivial⟩
                · exact hcache
                · exact hsend
        | cons item rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases item with
            | occurrence request firing =>
                apply start_put_snapshot
                  (node := { node with pending := [] })
                  (transaction :=
                    .work (.occurrence request firing) firing rest)
                  (transactionKey := .origin request.id.origin)
                · exact ⟨rfl, trivial,
                    ⟨request, firing, rfl⟩⟩
                · intro cacheKey value hread
                  change node.cacheRead cacheKey = some value at hread
                  exact hcache cacheKey value hread
                · exact hsend
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
              simp [hk, Outcomes.one] at hresult
              subst result
              apply start_put_snapshot
                (transaction := .external call)
                (transactionKey := requestKey)
              · exact ⟨hk, trivial, trivial⟩
              · exact hcache
              · exact hsend
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

theorem start_put_origin
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {transaction : Concrete.Transaction}
    {transactionKey : DocumentKey}
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
    })
    (horigin :
      TransactionOrigin
        (world.land (.node address) now
          (Concrete.start appConfig node transaction transactionKey))
        address transaction)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      TransactionOrigin
        (world.land (.node address) now
          (Concrete.start appConfig node transaction transactionKey))
        address provenance.transaction := by
  simp only [Concrete.start] at hmessage ⊢
  cases hcached : node.cacheRead transactionKey with
  | none =>
      simp [hcached, Concrete.Node.await] at hmessage
  | some value =>
      simp only [hcached] at hmessage ⊢
      obtain ⟨provenance, htransaction, hkey, hloaded⟩ :=
        decide_put_provenance hflight hmessage
      refine ⟨provenance, ?_⟩
      rw [htransaction]
      simpa only [Concrete.start, hcached] using horigin

theorem node_step_sent_put_origin
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    (haddress : address ∈ nodes)
    (hnodeLocal : world.process (.node address) = .node node)
    (hnode : NodeValid appConfig node)
    (hscans : NodeScansValid world.now node)
    (horigins : FlightRequestOrigins world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : world.now ≤ now)
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
      TransactionOrigin (world.land (.node address) now result)
        address provenance.transaction := by
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
                simp [hk, Outcomes.one] at hresult
                subst result
                apply start_put_origin
                  (transaction := .scan knownKey now [])
                  (transactionKey := knownKey)
                · exact ⟨rfl, trivial, trivial⟩
                · simp [TransactionOrigin, World.land]
                · exact hsend
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request firing =>
                apply start_put_origin
                  (node := { node with pending := [] })
                  (transaction :=
                    .work (.occurrence request firing) firing rest)
                  (transactionKey := .origin request.id.origin)
                · exact ⟨rfl, trivial, ⟨request, firing, rfl⟩⟩
                · exact ⟨request, firing, rfl⟩
                · exact hsend
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
              simp [hk, Outcomes.one] at hresult
              subst result
              apply start_put_origin
                (transaction := .external call)
                (transactionKey := requestKey)
              · exact ⟨hk, trivial, trivial⟩
              · exact List.mem_append_left _ hvalid
              · exact hsend
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
                      cases hprovenance : provenance.transaction with
                      | external call =>
                          exact List.mem_append_left _
                            (horigins haddress hnodeLocal hflightMem
                              (htransaction.symm.trans hprovenance))
                      | work item instant rest =>
                          have hshape := hflight.2.2
                          rw [← htransaction, hprovenance,
                            WorkShaped] at hshape
                          exact hshape
                      | scan scanKey instant rest =>
                          exact Nat.le_trans
                            (hscans replyOp flight hflightMem scanKey instant
                              rest (htransaction.symm.trans hprovenance)).1
                            htime
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
    (hcaches : CacheSnapshots world)
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
          node_step_sent_put_snapshot hstore hnodeValid
            (hcaches address hprocess hstore hnodeState) hgots hvalid
            hresult' hsent
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
        (reachable_cache_snapshots hreachable)
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

theorem start_external_flight_provenance
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    {next : Concrete.Node} {P : Call → Prop}
    (hstate :
      (Concrete.start appConfig node transaction key).state = .node next)
    (hold :
      ∀ op flight call,
        (op, flight) ∈ node.flights →
        flight.transaction = .external call → P call)
    (fresh :
      ∀ call, transaction = .external call → P call) :
    ∀ {op flight call},
      (op, flight) ∈ next.flights →
      flight.transaction = .external call →
      P call := by
  intro op flight call hmem htransaction
  simp only [Concrete.start] at hstate
  cases hcache : node.cacheRead key with
  | none =>
      simp [hcache, Concrete.Node.await] at hstate
      subst next
      simp only [List.mem_cons] at hmem
      rcases hmem with hnew | holdMem
      · cases hnew
        exact fresh call htransaction
      · exact hold op flight call holdMem htransaction
  | some value =>
      simp only [hcache] at hstate
      cases hselect :
          Concrete.select appConfig { key, transaction }
            (some (value.document, value.version)) with
      | none =>
          simp [Concrete.decide, hselect] at hstate
          subst next
          exact hold op flight call hmem htransaction
      | some candidate =>
          simp [Concrete.decide, hselect, Concrete.Node.await] at hstate
          subst next
          simp only [List.mem_cons] at hmem
          rcases hmem with hnew | holdMem
          · cases hnew
            exact fresh call htransaction
          · exact hold op flight call holdMem htransaction

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
                simp [hk, Outcomes.one] at hresult
                subst result
                exact start_external_flight_provenance appConfig node
                  (.scan key now []) key hstate
                  (fun _ _ _ hmem htx => hold hmem htx)
                  (by intros; contradiction) hmem htransaction
        | cons entry rest =>
            cases entry with
            | occurrence request instant =>
                simp [hp, Outcomes.one] at hresult
                subst result
                exact start_external_flight_provenance appConfig
                  { node with pending := [] }
                  (.work (.occurrence request instant) instant rest)
                  (.origin request.id.origin) hstate
                  (fun _ _ _ hmem htx =>
                    hold (by simpa using hmem) htx)
                  (by intros; contradiction) hmem htransaction
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
              simp [hk, Outcomes.one] at hresult
              subst result
              exact start_external_flight_provenance appConfig node
                (.external incoming) key hstate
                (fun _ _ _ hmem htx => hold hmem htx)
                (by
                  intro call htx
                  cases Concrete.Transaction.external.inj htx
                  exact List.mem_append_left _ hvalid)
                hmem htransaction
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
                          simp [Concrete.decide, hs,
                            Concrete.Node.cachePut,
                            Concrete.Node.cacheInvalidate] at hflights
                          rw [← hflights] at hmem
                          apply hold
                            (hremaining (op := currentOp)
                              (current := current) ?_)
                            htransaction
                          cases hloaded : heq ▸ loaded <;>
                            simpa [hloaded, Concrete.Node.cachePut,
                              Concrete.Node.cacheInvalidate] using hmem
                      | some candidate =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.decide, hs,
                            Concrete.Node.await, Concrete.Node.cachePut,
                            Concrete.Node.cacheInvalidate] at hflights
                          rw [← hflights] at hmem
                          simp only [List.mem_cons] at hmem
                          rcases hmem with hnew | holdMem
                          · have htx := congrArg
                              (fun pair :
                                Concrete.OpId × Concrete.Flight =>
                                pair.2.transaction) hnew
                            apply hold (takeFlight_some_mem ht)
                            exact htx.symm.trans htransaction
                          · apply hold
                              (hremaining (op := currentOp)
                                (current := current) ?_)
                              htransaction
                            cases hloaded : heq ▸ loaded <;>
                              simpa [hloaded, Concrete.Node.cachePut,
                                Concrete.Node.cacheInvalidate] using holdMem
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
    (htime : world.now ≤ next.now)
    (hnetwork : ∀ message ∈ world.network, message ∈ next.network) :
    TransactionOrigin next address transaction := by
  cases transaction with
  | external call => exact hnetwork _ horigin
  | work item instant rest => exact horigin
  | scan key instant rest => exact Nat.le_trans horigin htime

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
  | inject htime _ _ =>
      intro address op key document expected hmem
      simp only [World.inject, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, horigin⟩ := hinvariant hold
        exact ⟨provenance, horigin.mono htime fun message hmessage =>
          List.mem_append_left _ hmessage⟩
      · simp at hnew
  | outside htime _ =>
      intro address op key document expected hmem
      obtain ⟨provenance, horigin⟩ :=
        hinvariant (by simpa [World.observeOutside] using hmem)
      exact ⟨provenance, horigin.mono htime (by
        intro message hmessage
        simpa [World.observeOutside] using hmessage)⟩
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address op key document expected hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, horigin⟩ := hinvariant hold
        exact ⟨provenance, horigin.mono htime fun message hmessage =>
          List.mem_append_left _ hmessage⟩
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨recipient, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        obtain ⟨node, hnodeLocal, hnode⟩ :=
          reachable_nodes_valid hreachable address hprocess
        obtain ⟨scanNode, hscanNode, hscans⟩ :=
          reachable_nodes_scans_valid hreachable address hprocess
        rw [hnodeLocal] at hscanNode
        cases Concrete.Local.node.inj hscanNode
        obtain ⟨provenance, horigin⟩ :=
          node_step_sent_put_origin hprocess hnodeLocal hnode hscans
            (reachable_flight_request_origins hreachable) htime
            hvalid (hnodeLocal ▸ hresult) hsent
        exact ⟨provenance, horigin⟩

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

theorem start_put_stageable
    {nodes : List Addr} (appConfig : Resonate.Config)
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} (address : Addr) (now : Time)
    (node : Concrete.Node) (transaction : Concrete.Transaction)
    (transactionKey : DocumentKey)
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
    })
    (hcache : NodeCacheSnapshots store node)
    (horigin :
      TransactionOrigin
        (world.land (.node address) now
          (Concrete.start appConfig node transaction transactionKey))
        address transaction)
    (hempty : node.flights = [])
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded ∧
        TransactionOrigin
          (world.land (.node address) now
            (Concrete.start appConfig node transaction transactionKey))
          address provenance.transaction ∧
        (∀ next flight,
          (Concrete.start appConfig node transaction transactionKey).state =
              .node next →
          (op, flight) ∈ next.flights →
          flight.phase = .writing →
          ∃ hkey : key = flight.key,
            hkey ▸ provenance.loaded = flight.loaded ∧
            provenance.transaction = flight.transaction ∧
            provenance.outputs = flight.selected ∧
            provenance.continuations = flight.continuations) ∧
        ∃ next flight,
          (Concrete.start appConfig node transaction transactionKey).state =
              .node next ∧
          (op, flight) ∈ next.flights ∧
          flight.phase = .writing := by
  simp only [Concrete.start] at hmessage ⊢
  cases hcached : node.cacheRead transactionKey with
  | none =>
      simp [hcached, Concrete.Node.await] at hmessage
  | some value =>
      simp only [hcached] at hmessage ⊢
      cases hselect :
          Concrete.select appConfig { key := transactionKey, transaction }
            (some (value.document, value.version)) with
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
          let provenance :
              PutProvenance appConfig transactionKey candidate.document
                (some value.version) := {
            transaction
            loaded := some (value.document, value.version)
            outputs := candidate.outputs
            continuations := candidate.continuations
            expected_eq := rfl
            selected := select_valid hflight.1 hselect
          }
          refine ⟨provenance, hcache transactionKey value hcached, ?_,
            ?_, ?_⟩
          · have horigin' :
                TransactionOrigin
                  (world.land (.node address) now
                    (Concrete.decide appConfig node
                      { key := transactionKey, transaction }
                      (some (value.document, value.version))))
                  address transaction := by
                simpa [Concrete.start, hcached] using horigin
            simpa [provenance] using horigin'
          · intro next flight hstate hmem hphase
            simp [Concrete.decide, hselect, Concrete.Node.await] at hstate
            subst next
            simp [Concrete.Node.await, hempty] at hmem
            rcases hmem with ⟨_, rfl⟩
            exact ⟨rfl, rfl, rfl, rfl, rfl⟩
          · let writing : Concrete.Flight := {
                key := transactionKey
                transaction
                loaded := some (value.document, value.version)
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .writing
              }
            refine ⟨(node.await writing
                (.put transactionKey candidate.document
                  (some value.version))).1, writing, ?_, ?_, rfl⟩
            · simp [Concrete.decide, hselect, writing]
            · simp [Concrete.Node.await, writing]

theorem node_step_sent_put_stageable
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (haddress : address ∈ nodes)
    (hnodeLocal : world.process (.node address) = .node node)
    (hstore : world.process .store = .store store)
    (hnode : NodeValid appConfig node)
    (hscans : NodeScansValid world.now node)
    (hserial : NodeSerial node)
    (hcache : NodeCacheSnapshots store node)
    (hgots : GotSnapshots world)
    (horigins : FlightRequestOrigins world)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (hvalid : event.Valid world (.node address))
    (htime : world.now ≤ now)
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
        TransactionOrigin (world.land (.node address) now result)
          address provenance.transaction ∧
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
                simp [hk, Outcomes.one] at hresult
                subst result
                have hempty : node.flights = [] := by simp_all
                exact start_put_stageable appConfig address now node
                  (.scan knownKey now []) knownKey
                  ⟨rfl, trivial, trivial⟩ hcache
                  (by simp [TransactionOrigin, World.land])
                  hempty hsend
        | cons item rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            have hempty : node.flights = [] := by simp_all
            cases item with
            | occurrence request firing =>
                exact start_put_stageable appConfig address now
                  { node with pending := [] }
                  (.work (.occurrence request firing) firing rest)
                  (.origin request.id.origin)
                  ⟨rfl, trivial, ⟨request, firing, rfl⟩⟩
                  (by
                    intro cacheKey value hread
                    change node.cacheRead cacheKey = some value at hread
                    exact hcache cacheKey value hread)
                  ⟨request, firing, rfl⟩
                  (by simpa using hempty) hsend
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
              simp [hk, Outcomes.one] at hresult
              subst result
              have hempty : node.flights = [] := by simp_all
              exact start_put_stageable appConfig address now node
                (.external call) requestKey
                ⟨hk, trivial, trivial⟩ hcache
                (List.mem_append_left _ hvalid) hempty hsend
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
                            exact List.mem_append_left _
                              (horigins haddress hnodeLocal hflightMem
                                (htransaction.symm.trans hprovenance))
                        | work item instant rest =>
                            have hshape := hflight.2.2
                            rw [← htransaction, hprovenance,
                              WorkShaped] at hshape
                            exact hshape
                        | scan scanKey instant rest =>
                            exact Nat.le_trans
                              (hscans replyOp flight hflightMem scanKey
                                instant rest
                                (htransaction.symm.trans hprovenance)).1
                              htime
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
                          Concrete.Node.cachePut,
                          Concrete.Node.cacheInvalidate, hempty] at hflights
                        rw [← hflights] at hactive
                        have hcachedEmpty :
                            (match provenance.loaded with
                             | some (document, version) =>
                                 next.cachePut flight.key {
                                   document, version }
                             | none =>
                                 next.cacheInvalidate flight.key).flights =
                              [] := by
                          cases hloaded : provenance.loaded with
                          | none =>
                              simpa [hloaded,
                                Concrete.Node.cacheInvalidate] using hempty
                          | some value =>
                              obtain ⟨document, version⟩ := value
                              simpa [hloaded, Concrete.Node.cachePut] using
                                hempty
                        simp [Concrete.Node.await, hcachedEmpty] at hactive
                        rcases hactive with hnew | holdActive
                        · rcases hnew with ⟨_, rfl⟩
                          exact ⟨rfl, rfl, htransaction, houtputs,
                            hcontinuations⟩
                        · exfalso
                          cases hloaded : provenance.loaded with
                          | none =>
                              have : (op, active) ∈ next.flights := by
                                simpa [hloaded,
                                  Concrete.Node.cacheInvalidate] using
                                  holdActive
                              rw [hempty] at this
                              contradiction
                          | some value =>
                              obtain ⟨document, version⟩ := value
                              have : (op, active) ∈ next.flights := by
                                simpa [hloaded, Concrete.Node.cachePut] using
                                  holdActive
                              rw [hempty] at this
                              contradiction
                      · let writing : Concrete.Flight := {
                          flight with
                          loaded := provenance.loaded
                          document := some candidate.document
                          selected := candidate.outputs
                          continuations := candidate.continuations
                          phase := .writing
                        }
                        let cached :=
                          match provenance.loaded with
                          | some (document, version) =>
                              next.cachePut flight.key {
                                document, version }
                          | none => next.cacheInvalidate flight.key
                        refine ⟨(cached.await writing
                            (.put flight.key candidate.document
                              (provenance.loaded.map (·.2)))).1,
                          writing, ?_, ?_, rfl⟩
                        · simp [Concrete.decide, hselect]
                          cases hpv : provenance.loaded <;>
                            simp [cached, writing, hpv,
                              Concrete.Node.await]
                        · simp only [Concrete.Node.await, List.mem_cons]
                          apply Or.inl
                          apply Prod.ext
                          · exact (idSent _ _ hsend).1.trans
                              (by
                                have hn := takeFlight_nextOp ht
                                cases hpv : provenance.loaded <;>
                                  simp [cached, hpv,
                                    Concrete.Node.cachePut,
                                    Concrete.Node.cacheInvalidate, hn])
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
  | inject htime _ _ =>
      intro store address op key document expectedVersion hstore hmem
      simp only [World.inject, List.mem_append,
        List.mem_singleton] at hmem
      rcases hmem with hold | hnew
      · obtain ⟨provenance, hsnapshot, horigin, hagreement,
          heligible⟩ :=
          hinvariant hstore hold
        refine ⟨provenance, hsnapshot,
          horigin.mono htime fun message hmessage =>
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
  | outside htime _ =>
      intro store address op key document expectedVersion hstore hmem
      obtain ⟨provenance, hsnapshot, horigin, hagreement, heligible⟩ :=
        hinvariant (by simpa [World.observeOutside] using hstore)
          (by simpa [World.observeOutside] using hmem)
      refine ⟨provenance, hsnapshot, horigin.mono htime (by
        intro message hmessage
        simpa [World.observeOutside] using hmessage), ?_, ?_⟩
      · intro node flight hnode hflight hphase
        exact hagreement node flight
          (by simpa [World.observeOutside] using hnode) hflight hphase
      · intro hmatch
        obtain ⟨node, flight, hnode, hflight, hphase, hnoreply⟩ :=
          heligible hmatch
        refine ⟨node, flight,
          by simpa [World.observeOutside] using hnode,
          hflight, hphase, ?_⟩
        intro reply hreply hreplyMem
        exact hnoreply reply hreply
          (by simpa [World.observeOutside] using hreplyMem)
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
          horigin.mono htime fun message hmessage =>
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
        obtain ⟨scanNode, hscanNode, hscans⟩ :=
          reachable_nodes_scans_valid hreachable address hprocess
        rw [hnodeState] at hscanNode
        cases Concrete.Local.node.inj hscanNode
        obtain ⟨provenance, hsnapshot, horigin, hagreement,
            hactiveNew⟩ :=
          node_step_sent_put_stageable hprocess hnodeState hstore
            hnodeValid hscans hserial
            (reachable_cache_snapshots hreachable address hprocess
              hstore hnodeState)
            (reachable_got_snapshots hreachable)
            (reachable_flight_request_origins hreachable)
            hvalid htime (hnodeState ▸ hresult) hsent
        have hsame : nextStore = store := by
          have hx : store = nextStore := by
            simpa [World.land, hstore] using hnextStore
          exact hx.symm
        subst nextStore
        refine ⟨provenance, hsnapshot, horigin, ?_, ?_⟩
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
    (nodePending : List Concrete.PendingEntry)
    (abstractPending : List WorkflowEntry) : Prop :=
  match flight.transaction with
  | .external _ =>
      abstractPending = Concrete.pendingWorkflow nodePending
  | .work item instant rest =>
      match flight.phase with
      | .loading =>
          abstractPending =
            (Resonate.occurrenceEntry? item).toList ++
              Concrete.pendingWorkflow rest
      | .writing =>
          abstractPending =
              (Resonate.occurrenceEntry? item).toList ++
                Concrete.pendingWorkflow rest ∨
          abstractPending =
            Concrete.pendingWorkflow flight.continuations
  | .scan key instant rest =>
      match flight.phase with
      | .loading =>
          abstractPending = Concrete.pendingWorkflow rest
      | .writing =>
          abstractPending = Concrete.pendingWorkflow rest ∨
          abstractPending =
            Concrete.pendingWorkflow flight.continuations

def TransactionPending : Concrete.Transaction → Option (List WorkflowEntry)
  | .external _ => none
  | .work item _ rest =>
      some ((Resonate.occurrenceEntry? item).toList ++
        Concrete.pendingWorkflow rest)
  | .scan _ _ rest => some (Concrete.pendingWorkflow rest)

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
          (abstract.process .service).workflow.pending =
            Concrete.pendingWorkflow node.pending) ∨
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
              Concrete.pendingWorkflow flight.continuations)) ∧
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
                Concrete.pendingWorkflow flight.continuations)) ∧
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
        lifted.1.workflow.pending =
          Concrete.pendingWorkflow provenance.continuations)
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
      {request : ServerModel.PromiseCreateReq}
      {semanticTime instant : Time}
      {rest : List Concrete.PendingEntry}
      (htransaction :
        provenance.transaction =
          .work (.occurrence request semanticTime) instant rest)
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
    let item : WorkItem := .occurrence request semanticTime
    have hitemKey : item.key = key := by
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have htx := hvalid.1
      rw [← hflightTransaction, htransaction] at htx
      simp only [Concrete.Transaction.key?, Option.some.injEq] at htx
      exact htx.trans hkey.symm
    let lifted :=
      Resonate.runWork { appConfig with unreliable := true }
        item instant (Concrete.pendingWorkflow rest)
          (abstract.process .service)
    let entry : WorkflowEntry := { request, instant := semanticTime }
    have hpendingTransaction :
        TransactionPending provenance.transaction =
          some (entry :: Concrete.pendingWorkflow rest) := by
      rw [htransaction]
      rfl
    have hpending :
        (abstract.process .service).workflow.pending =
          entry :: Concrete.pendingWorkflow rest := by
      have hversion :
          flight.loaded.map (·.2) = physical.version flight.key := by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch
      exact (related.currentWorkflow physical address node op flight
        (entry :: Concrete.pendingWorkflow rest)
        haddress hphysical hnode hflight
        hphase hversion (by
          rw [← hflightTransaction]
          exact hpendingTransaction)).2
    have hchoice :
        lifted ∈
          (Resonate.runTimeoutChoices
            { appConfig with unreliable := true } now
            (abstract.process .service)).val := by
      simp [lifted, item, entry, Resonate.runTimeoutChoices,
        Resonate.timeoutChoices, Resonate.pendingTimeoutChoices,
        hpending, Resonate.runWork, WorkflowEntry.item]
    have htransport :=
      work_cas_transport hrep provenance htransaction hcurrent
    have hitemMem :=
      work_key_mem { appConfig with unreliable := true }
        item instant (Concrete.pendingWorkflow rest)
          (abstract.process .service)
    rw [hitemKey] at hitemMem
    exact simulate_internal_committed_store hreachable related hphysical
      hrequest provenance hsnapshot hmatch
      (htransactionPending := hpendingTransaction)
      (hfailure := by simp [htransaction, Concrete.failureOutputs])
      haddress hnode hflight hphase hkey hloaded hflightTransaction
      houtputs hcontinuations lifted hchoice htransport
      (work_keys_mono { appConfig with unreliable := true }
        item instant (Concrete.pendingWorkflow rest)
          (abstract.process .service))
      (by simpa [lifted] using hitemMem)
      hreply htime hconcreteResult
  have hscan
      {scanKey : DocumentKey} {instant : Time}
      {rest : List Concrete.PendingEntry}
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
    have hpendingTransaction :
        TransactionPending provenance.transaction =
          some (Concrete.pendingWorkflow rest) := by
      rw [htransaction]
      rfl
    have hpending :
        (abstract.process .service).workflow.pending =
          Concrete.pendingWorkflow rest := by
      have hversion :
          flight.loaded.map (·.2) = physical.version flight.key := by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch
      exact (related.currentWorkflow physical address node op flight
        (Concrete.pendingWorkflow rest)
        haddress hphysical hnode hflight
        hphase hversion (by
          rw [← hflightTransaction]
          exact hpendingTransaction)).2
    have hknown :
        key ∈ node.known := by
      exact (reachable_scan_flight_valid hreachable haddress hnode hflight
        (hflightTransaction.symm.trans htransaction)).2.1
    have hkeyMem :
        key ∈ (abstract.process .service).store.keys :=
      related.known address node key haddress hnode hknown
    obtain ⟨item, hitemKey, hitem, htransport⟩ :=
      scan_cas_transport hrep provenance htransaction hcurrent hkeyMem
    let lifted :=
      Resonate.runWork { appConfig with unreliable := true }
        item instant (Concrete.pendingWorkflow rest)
          (abstract.process .service)
    have hinstant :
        instant ≤ now :=
      Nat.le_trans
        (reachable_scan_flight_valid hreachable haddress hnode hflight
          (hflightTransaction.symm.trans htransaction)).1
        htime
    have hchoice :
        lifted ∈
          (Resonate.runTimeoutChoices
            { appConfig with unreliable := true } now
            (abstract.process .service)).val := by
      simp only [Resonate.runTimeoutChoices, List.mem_cons]
      right
      simp only [Resonate.timeoutChoices, List.mem_append]
      right
      simp only [Resonate.documentTimeoutChoices, List.mem_flatMap,
        List.mem_map]
      exact ⟨instant, List.mem_range.mpr (Nat.lt_succ_iff.mpr hinstant),
        item, hitem, by simp [lifted, hpending]⟩
    have hitemKeyMem :=
      work_key_mem { appConfig with unreliable := true }
        item instant (Concrete.pendingWorkflow rest)
          (abstract.process .service)
    rw [hitemKey] at hitemKeyMem
    exact simulate_internal_committed_store hreachable related hphysical
      hrequest provenance hsnapshot hmatch
      (htransactionPending := hpendingTransaction)
      (hfailure := by simp [htransaction, Concrete.failureOutputs])
      haddress hnode hflight hphase hkey hloaded hflightTransaction
      houtputs hcontinuations lifted hchoice htransport
      (work_keys_mono { appConfig with unreliable := true }
        item instant (Concrete.pendingWorkflow rest)
          (abstract.process .service))
      (by simpa [lifted] using hitemKeyMem)
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
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have hshape := hvalid.2.2
      rw [← hflightTransaction, htransaction, WorkShaped] at hshape
      obtain ⟨request, semanticTime, hitem⟩ := hshape
      subst item
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
                Concrete.pendingWorkflow flight.continuations)) ∧
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
      rw [pureResponse_correspondence
        { appConfig with unreliable := true } call hkey]
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

theorem related_after_start_node_miss
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
    (hcache : base.cacheRead key = none)
    (hstage :
      base.workflowBlocked = true ∨
        FlightWorkflowStage ({ key, transaction } : Concrete.Flight)
          base.pending (abstract.process .service).workflow.pending)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      Concrete.start appConfig base transaction key ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now
        (Concrete.start appConfig base transaction key)) abstract := by
  subst address
  let flight : Concrete.Flight := { key, transaction }
  let nextNode := (base.await flight (.get key)).1
  have hstartState :
      (Concrete.start appConfig base transaction key).state = .node nextNode := by
    simp [Concrete.start, hcache, nextNode, flight]
  have hnextFlights :
      nextNode.flights = [(base.nextOp, flight)] := by
    simp [nextNode, Concrete.Node.await, hbaseFlights]
  have hnextKnown : nextNode.known = node.known := by
    simp [nextNode, Concrete.Node.await, hbaseKnown]
  have hnextPending : nextNode.pending = base.pending := by
    simp [nextNode, Concrete.Node.await]
  have hprocessWorkflow :
      (concrete.land (.node config.workflowNode) now
        (Concrete.start appConfig base transaction key)).process
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
    simp [Concrete.start, hcache, Concrete.Node.await] at hsend
  · intro output hsend
    simp [Concrete.start, hcache, Concrete.Node.await] at hsend
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
        · simp [Concrete.start, hcache, Concrete.Node.await] at hnew
      · intro hreply
        simp only [World.land, List.mem_append] at hreply
        rcases hreply with hold | hnew
        · exact (hnoReply .failed hold).elim
        · simp [Concrete.start, hcache, Concrete.Node.await] at hnew
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      exact (heq (reachable_flight_owner hreachable hcurrentAddress
        hcurrentNodeOld hcurrentFlight)).elim

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
    (hvalidFlight :
      FlightValid appConfig ({ key, transaction } : Concrete.Flight))
    (hinternalClean :
      transaction.isExternal = false → base.workflowBlocked = false)
    (hscanPending :
      ∀ scanKey instant rest,
        transaction = .scan scanKey instant rest → base.pending = rest)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      Concrete.start appConfig base transaction key ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now
        (Concrete.start appConfig base transaction key)) abstract := by
  cases hcache : base.cacheRead key with
  | none =>
      exact related_after_start_node_miss hreachable related haddress howner
        hnode hbaseNext hbaseFlights hbaseKnown hcache hstage htime hvalid
        hresult
  | some value =>
      let flight : Concrete.Flight := { key, transaction }
      cases hselect :
          Concrete.select appConfig flight
            (some (value.document, value.version)) with
      | none =>
          have hstart :
              Concrete.start appConfig base transaction key = {
                state := .node base
                send := []
              } := by
            simp [Concrete.start, hcache, Concrete.decide, hselect, flight]
          have hprocess :
              (concrete.land (.node address) now
                (Concrete.start appConfig base transaction key)).process
                  (.node address) = .node base := by
            simp [hstart, World.land]
          apply related_after_node_land hreachable related haddress hnode htime
              hvalid hresult (Nat.le_trans related.time htime)
              (fun _ h => h) (fun _ h => h)
          · obtain ⟨physical, hphysical, hrep⟩ := related.store
            exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
          · simp only [WorkflowAligned, howner ▸ haddress]
            refine ⟨base, by simpa [howner.symm] using hprocess, ?_⟩
            rcases hstage with hblocked | hflightStage
            · exact .inl hblocked
            · right
              left
              refine ⟨hbaseFlights, ?_⟩
              cases ht : transaction with
              | external call =>
                  have hne := hvalidFlight.select_ne_none (by
                    intro scanKey instant rest hscan
                    simp [ht] at hscan)
                    (some (value.document, value.version))
                  exact (hne (by simpa [flight] using hselect)).elim
              | work item instant rest =>
                  have hne := hvalidFlight.select_ne_none (by
                    intro scanKey scanInstant scanRest hscan
                    simp [ht] at hscan)
                    (some (value.document, value.version))
                  exact (hne (by simpa [flight] using hselect)).elim
              | scan scanKey instant rest =>
                  have hpending := hscanPending scanKey instant rest ht
                  simpa [FlightWorkflowStage, flight, ht, hpending] using
                    hflightStage
          · intro physical currentAddress currentNode op currentFlight pending
              hcurrentAddress hphysical hcurrentNode hcurrentFlight hphase
              hversion hpending
            by_cases heq : currentAddress = address
            · subst currentAddress
              rw [hprocess] at hcurrentNode
              cases Concrete.Local.node.inj hcurrentNode
              rw [hbaseFlights] at hcurrentFlight
              contradiction
            · have hold :
                  concrete.process (.node currentAddress) =
                    .node currentNode := by
                simpa [World.land, heq] using hcurrentNode
              have hflightOwner :=
                reachable_flight_owner hreachable hcurrentAddress hold
                  hcurrentFlight
              exact (heq (hflightOwner.trans howner.symm)).elim
          · intro currentAddress currentNode knownKey hcurrentAddress
              hcurrentNode hknown
            by_cases heq : currentAddress = address
            · subst currentAddress
              rw [hprocess] at hcurrentNode
              cases Concrete.Local.node.inj hcurrentNode
              exact related.known address node knownKey haddress hnode
                (by simpa [hbaseKnown] using hknown)
            · exact related.known currentAddress currentNode knownKey
                hcurrentAddress
                (by simpa [World.land, heq] using hcurrentNode) hknown
          · intro target call hsend
            simp [hstart] at hsend
          · intro output hsend
            simp [hstart] at hsend
          · intro currentAddress currentNode op currentFlight hcurrentAddress
              hcurrentNode hcurrentFlight
            by_cases heq : currentAddress = address
            · subst currentAddress
              rw [hprocess] at hcurrentNode
              cases Concrete.Local.node.inj hcurrentNode
              rw [hbaseFlights] at hcurrentFlight
              contradiction
            · have hold :
                  concrete.process (.node currentAddress) =
                    .node currentNode := by
                simpa [World.land, heq] using hcurrentNode
              obtain ⟨hwritten, hfailed⟩ :=
                related.activeReplies currentAddress currentNode op
                  currentFlight hcurrentAddress hold hcurrentFlight
              constructor
              · intro hreply
                exact hwritten (by simpa [World.land] using hreply)
              · intro hreply
                exact hfailed (by simpa [World.land] using hreply)
      | some candidate =>
          let writing : Concrete.Flight := {
            flight with
              loaded := some (value.document, value.version)
              document := some candidate.document
              selected := candidate.outputs
              continuations := candidate.continuations
              phase := .writing
          }
          let nextNode := (base.await writing
            (.put key candidate.document (some value.version))).1
          have hnextFlights :
              nextNode.flights = [(base.nextOp, writing)] := by
            simp [nextNode, Concrete.Node.await, hbaseFlights]
          have hnextKnown : nextNode.known = node.known := by
            simp [nextNode, Concrete.Node.await, hbaseKnown]
          have hprocess :
              (concrete.land (.node address) now
                (Concrete.start appConfig base transaction key)).process
                  (.node address) = .node nextNode := by
            simp [Concrete.start, hcache, Concrete.decide, hselect, flight,
              writing, nextNode, World.land]
          apply related_after_node_land hreachable related haddress hnode htime
              hvalid hresult (Nat.le_trans related.time htime)
              (fun _ h => h) (fun _ h => h)
          · obtain ⟨physical, hphysical, hrep⟩ := related.store
            exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
          · simp only [WorkflowAligned, howner ▸ haddress]
            refine ⟨nextNode, by simpa [howner.symm] using hprocess, ?_⟩
            rcases hstage with hblocked | hflightStage
            · left
              simpa [nextNode, Concrete.Node.await] using hblocked
            · right
              right
              refine ⟨base.nextOp, writing, by simp [hnextFlights], ?_⟩
              cases ht : transaction with
              | external call =>
                  simpa [writing, flight, nextNode, Concrete.Node.await,
                    FlightWorkflowStage, ht] using hflightStage
              | work item instant rest =>
                  simpa [writing, flight, nextNode, Concrete.Node.await,
                    FlightWorkflowStage, ht] using Or.inl hflightStage
              | scan scanKey instant rest =>
                  simpa [writing, flight, nextNode, Concrete.Node.await,
                    FlightWorkflowStage, ht] using Or.inl hflightStage
          · intro physical currentAddress currentNode op currentFlight pending
              hcurrentAddress hphysical hcurrentNode hcurrentFlight hphase
              hversion hpending
            by_cases heq : currentAddress = address
            · subst currentAddress
              rw [hprocess] at hcurrentNode
              cases Concrete.Local.node.inj hcurrentNode
              simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
              cases hcurrentFlight
              cases ht : transaction with
              | external call =>
                  simp [writing, flight, ht, TransactionPending] at hpending
              | work item instant rest =>
                  rcases hstage with hblocked | hflightStage
                  · have hclean := hinternalClean (by
                      simp [Concrete.Transaction.isExternal, ht])
                    rw [hclean] at hblocked
                    contradiction
                  · refine ⟨howner, ?_⟩
                    have hbefore :
                        (abstract.process .service).workflow.pending =
                          (Resonate.occurrenceEntry? item).toList ++
                            Concrete.pendingWorkflow rest := by
                      simpa [FlightWorkflowStage, flight, ht] using
                        hflightStage
                    have hpendingEq :
                        (Resonate.occurrenceEntry? item).toList ++
                            Concrete.pendingWorkflow rest = pending := by
                      simpa [writing, flight, ht, TransactionPending] using
                        hpending
                    exact hbefore.trans hpendingEq
              | scan scanKey instant rest =>
                  rcases hstage with hblocked | hflightStage
                  · have hclean := hinternalClean (by
                      simp [Concrete.Transaction.isExternal, ht])
                    rw [hclean] at hblocked
                    contradiction
                  · refine ⟨howner, ?_⟩
                    have hbefore :
                        (abstract.process .service).workflow.pending =
                          Concrete.pendingWorkflow rest := by
                      simpa [FlightWorkflowStage, flight, ht] using
                        hflightStage
                    have hpendingEq :
                        Concrete.pendingWorkflow rest = pending := by
                      simpa [writing, flight, ht, TransactionPending] using
                        hpending
                    exact hbefore.trans hpendingEq
            · have hold :
                  concrete.process (.node currentAddress) =
                    .node currentNode := by
                simpa [World.land, heq] using hcurrentNode
              have hflightOwner :=
                reachable_flight_owner hreachable hcurrentAddress hold
                  hcurrentFlight
              exact (heq (hflightOwner.trans howner.symm)).elim
          · intro currentAddress currentNode knownKey hcurrentAddress
              hcurrentNode hknown
            by_cases heq : currentAddress = address
            · subst currentAddress
              rw [hprocess] at hcurrentNode
              cases Concrete.Local.node.inj hcurrentNode
              have hknown' : knownKey ∈ nextNode.known := hknown
              rw [hnextKnown] at hknown'
              exact related.known address node knownKey haddress hnode hknown'
            · exact related.known currentAddress currentNode knownKey
                hcurrentAddress
                (by simpa [World.land, heq] using hcurrentNode) hknown
          · intro target call hsend
            simp [Concrete.start, hcache, Concrete.decide, hselect,
              Concrete.Node.await, flight] at hsend
          · intro output hsend
            simp [Concrete.start, hcache, Concrete.decide, hselect,
              Concrete.Node.await, flight] at hsend
          · intro currentAddress currentNode op currentFlight hcurrentAddress
              hcurrentNode hcurrentFlight
            by_cases heq : currentAddress = address
            · subst currentAddress
              rw [hprocess] at hcurrentNode
              cases Concrete.Local.node.inj hcurrentNode
              simp only [hnextFlights, List.mem_singleton] at hcurrentFlight
              cases hcurrentFlight
              have hnoReply (reply : StoreReply)
                  (hreply :
                    (Concrete.Pid.store, .node address,
                      .storeReply {
                        op := base.nextOp
                        payload := reply
                      }) ∈ concrete.network) : False := by
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
                · simp [Concrete.start, hcache, Concrete.decide, hselect,
                    Concrete.Node.await, flight] at hnew
              · intro hreply
                simp only [World.land, List.mem_append] at hreply
                rcases hreply with hold | hnew
                · exact (hnoReply .failed hold).elim
                · simp [Concrete.start, hcache, Concrete.decide, hselect,
                    Concrete.Node.await, flight] at hnew
            · have hold :
                  concrete.process (.node currentAddress) =
                    .node currentNode := by
                simpa [World.land, heq] using hcurrentNode
              have hflightOwner :=
                reachable_flight_owner hreachable hcurrentAddress hold
                  hcurrentFlight
              exact (heq (hflightOwner.trans howner.symm)).elim

theorem simulate_idle_scan_start
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
      Concrete.start appConfig node (.scan key now []) key ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now .timeout).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land (.node address) now
          (Concrete.start appConfig node (.scan key now []) key))
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  have habstractPending :
      (abstract.process .service).workflow.pending = [] := by
    simpa [WorkflowAligned, howner ▸ haddress, howner ▸ hnode,
      hblocked, hflights, hpendingNode, Concrete.pendingWorkflow] using
        related.workflow
  refine ⟨[], trivial, ?_, rfl⟩
  have hstage :
      node.workflowBlocked = true ∨
        FlightWorkflowStage
          ({ key, transaction := .scan key now [] } : Concrete.Flight)
          node.pending (abstract.process .service).workflow.pending := by
    right
    simp [FlightWorkflowStage, hpendingNode, habstractPending,
      Concrete.pendingWorkflow]
  apply related_after_start_node hreachable related haddress howner hnode
      (base := node) rfl hflights rfl
      (transaction := .scan key now []) (key := key) hstage
      (by simp [FlightValid, Concrete.Transaction.key?, WorkShaped])
      (by
        intro _
        simpa [Concrete.Transaction.isExternal] using hblocked)
      (by
        intro scanKey instant rest htransaction
        cases htransaction
        exact hpendingNode)
      (event := .timeout) htime trivial hresult

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
          Concrete.pendingWorkflow nextNode.pending := by
    cases htransaction : flight.transaction with
    | external call =>
        have hvalid :=
          related.flights address node op flight haddress hnode hflight
        rw [FlightValid, hphase] at hvalid
        obtain ⟨document, hdocument, hselected⟩ := hvalid.2.1
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
              (abstract.process .service).workflow.pending =
                  Concrete.pendingWorkflow node.pending := by
                simpa [FlightWorkflowStage, htransaction] using hstage
              _ = Concrete.pendingWorkflow nextNode.pending := by
                simp [nextNode, hcontinuations, hnextPending,
                  Concrete.pendingWorkflow]
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
    {node remaining base : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (htake : node.takeFlight op = (some flight, remaining))
    (hbaseNext : base.nextOp = remaining.nextOp)
    (hbaseFlights : base.flights = remaining.flights)
    (hbasePending : base.pending = remaining.pending)
    (hbaseKnown : base.known = remaining.known)
    (hbaseBlocked : base.workflowBlocked = remaining.workflowBlocked)
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
      Concrete.decide appConfig base flight loaded ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .store
            (.storeReply { op, payload := .got flight.key loaded }))).val) :
    Related nodes appConfig config
      (concrete.land (.node address) now
        (Concrete.decide appConfig base flight loaded)) abstract := by
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
  have hbaseFlightsEmpty : base.flights = [] :=
    hbaseFlights.trans hremainingFlights
  have hbasePendingNode : base.pending = node.pending :=
    hbasePending.trans hremainingPending
  have hbaseKnownNode : base.known = node.known :=
    hbaseKnown.trans hremainingKnown
  have hbaseBlockedNode :
      base.workflowBlocked = node.workflowBlocked :=
    hbaseBlocked.trans hremainingBlocked
  let writing : Concrete.Flight := {
    flight with
      loaded
      document := some candidate.document
      selected := candidate.outputs
      continuations := candidate.continuations
      phase := .writing
  }
  let nextNode := (base.await writing
    (.put flight.key candidate.document (loaded.map (·.2)))).1
  have hnextFlights :
      nextNode.flights = [(base.nextOp, writing)] := by
    simp [nextNode, Concrete.Node.await, hbaseFlightsEmpty]
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
      simpa [nextNode, Concrete.Node.await, hbaseBlockedNode] using hblocked
    · right
      right
      refine ⟨base.nextOp, writing, by simp [hnextFlights], ?_⟩
      cases ht : flight.transaction with
      | external call =>
          simpa [writing, nextNode, Concrete.Node.await,
            FlightWorkflowStage, ht, hbasePendingNode] using hstage
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
          · have hbefore :
                (abstract.process .service).workflow.pending =
                  (Resonate.occurrenceEntry? item).toList ++
                    Concrete.pendingWorkflow rest := by
              simpa [FlightWorkflowStage, ht, hphase] using hstage
            have hpendingEq :
                (Resonate.occurrenceEntry? item).toList ++
                    Concrete.pendingWorkflow rest = pending := by
              simpa [writing, ht, TransactionPending] using hpending
            exact ⟨howner, hbefore.trans hpendingEq⟩
      | scan key instant rest =>
          rcases hworkflowCase with hblocked | hstage
          · have hclean := reachable_internal_flight_clean hreachable
              haddress hnode hflight (by rw [ht]; rfl)
            rw [hblocked] at hclean
            cases hclean.2
          · have hbefore :
                (abstract.process .service).workflow.pending =
                  Concrete.pendingWorkflow rest := by
              simpa [FlightWorkflowStage, ht, hphase] using hstage
            have hpendingEq :
                Concrete.pendingWorkflow rest = pending := by
              simpa [writing, ht, TransactionPending] using hpending
            exact ⟨howner, hbefore.trans hpendingEq⟩
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
        (by simpa [nextNode, Concrete.Node.await, hbaseKnownNode] using hkey)
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
              .storeReply { op := base.nextOp, payload := reply }) ∈
                concrete.network) : False := by
        cases reply with
        | got key value =>
            have hget := reachable_got_replies_have_request hreachable
              hterminal
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hget
            have hn := hbaseNext.trans (takeFlight_nextOp htake)
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | written =>
            have horigin := reachable_put_replies_have_request hreachable
              (.inl rfl) hterminal
            obtain ⟨putKey, document, expected, hput⟩ := horigin
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hput
            have hn := hbaseNext.trans (takeFlight_nextOp htake)
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | conflict =>
            have horigin := reachable_put_replies_have_request hreachable
              (.inr (.inl rfl)) hterminal
            obtain ⟨putKey, document, expected, hput⟩ := horigin
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hput
            have hn := hbaseNext.trans (takeFlight_nextOp htake)
            rw [hn] at hfresh
            exact (Nat.lt_irrefl _ hfresh).elim
        | failed =>
            have horigin := reachable_put_replies_have_request hreachable
              (.inr (.inr rfl)) hterminal
            obtain ⟨putKey, document, expected, hput⟩ := horigin
            have hfresh := (reachable_rpc_ids hreachable).fresh haddress
              hnode hput
            have hn := hbaseNext.trans (takeFlight_nextOp htake)
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
        (abstract.process .service).workflow.pending =
          Concrete.pendingWorkflow nextNode.pending)
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
      (abstract.process .service).workflow.pending =
        Concrete.pendingWorkflow remaining.pending := by
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

theorem workflow_after_scan_flight_removed
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
    {key : DocumentKey} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .scan key instant rest) :
    remaining.workflowBlocked = true ∨
      (abstract.process .service).workflow.pending =
        Concrete.pendingWorkflow remaining.pending := by
  have hflight := takeFlight_some_mem htake
  have howner :=
    reachable_flight_owner hreachable haddress hnode hflight
  obtain ⟨serialNode, hserialNode, hserial⟩ :=
    reachable_nodes_serial hreachable address haddress
  rw [hnode] at hserialNode
  cases Concrete.Local.node.inj hserialNode
  have hclean :=
    reachable_internal_flight_clean hreachable haddress hnode hflight
      (by simp [htransaction, Concrete.Transaction.isExternal])
  have hrest :=
    (reachable_scan_flight_valid hreachable haddress hnode hflight
      htransaction).2.2
  have hold := related.workflow
  simp only [WorkflowAligned, howner ▸ haddress] at hold
  obtain ⟨workflowNode, hworkflowNode, haligned⟩ := hold
  rw [← howner, hnode] at hworkflowNode
  cases Concrete.Local.node.inj hworkflowNode
  rcases haligned with hblocked | hidle | hactive
  · rw [hblocked] at hclean
    cases hclean.2
  · rw [hidle.1] at hflight
    contradiction
  · obtain ⟨activeOp, activeFlight, hactiveFlight, hstage⟩ := hactive
    have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
    cases hpairs
    right
    rw [takeFlight_pending htake, hclean.1]
    simpa [FlightWorkflowStage, htransaction, hphase, hrest] using hstage

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
        (abstract.process .service).workflow.pending =
          Concrete.pendingWorkflow nextNode.pending)
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
                exact simulate_idle_scan_start hreachable related haddress
                  howner hnode hblocked hflights hpending hknown htime
                  (by simp [Concrete.step, hguard, hpending, hknown,
                    Outcomes.one])
        | cons entry rest =>
            simp [hpending, Concrete.start, Concrete.Node.await,
              Outcomes.one] at hresult
            subst result
            have habstractPending :
                (abstract.process .service).workflow.pending =
                  Concrete.pendingWorkflow (entry :: rest) := by
              simpa [WorkflowAligned, howner ▸ haddress, howner ▸ hnode,
                hblocked, hflights, hpending] using related.workflow
            cases entry with
            | occurrence request instant =>
                exact ⟨[], trivial,
                  related_after_start_node hreachable related haddress howner
                    hnode (base := { node with pending := [] })
                    (by rfl) (by simp [hflights]) (by rfl)
                    (transaction :=
                      .work (.occurrence request instant) instant rest)
                    (key := .origin request.id.origin)
                    (.inr (by
                      simpa [FlightWorkflowStage, Concrete.pendingWorkflow,
                        Concrete.PendingEntry.toWorkflow?,
                        Resonate.occurrenceEntry?] using habstractPending))
                    (by
                      simp [FlightValid, Concrete.Transaction.key?, WorkShaped,
                        WorkItem.key])
                    (by
                      intro _
                      simpa using hblocked)
                    (by simp)
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
                        Concrete.pendingWorkflow node.pending := by
                    simpa [WorkflowAligned, howner ▸ haddress,
                      howner ▸ hnode, hbfalse, hflights] using
                      related.workflow
                  simpa [FlightWorkflowStage] using hpending
              exact ⟨[], trivial,
                related_after_start_node hreachable related haddress howner
                  hnode rfl hflights rfl hstage
                  ⟨hkey, trivial, trivial⟩
                  (by simp [Concrete.Transaction.isExternal])
                  (by simp)
                  htime hvalid (by
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
                    let cached :=
                      match loaded with
                      | some (document, version) =>
                          remaining.cachePut flight.key { document, version }
                      | none =>
                          remaining.cacheInvalidate flight.key
                    cases hp : flight.phase with
                    | loading =>
                        cases hs : Concrete.select appConfig flight
                            loaded with
                        | none =>
                            have hvalidFlight :=
                              related.flights address node replyOp flight
                                haddress hnode hflight
                            cases htransaction : flight.transaction with
                            | external call =>
                                exact (hvalidFlight.select_ne_none
                                  (by
                                    intro key instant rest hscan
                                    simp [htransaction] at hscan)
                                  loaded hs).elim
                            | work item instant rest =>
                                exact (hvalidFlight.select_ne_none
                                  (by
                                    intro key scanInstant scanRest hscan
                                    simp [htransaction] at hscan)
                                  loaded hs).elim
                            | scan key instant rest =>
                                simp [ht, hp, Concrete.decide, hs,
                                  Outcomes.one] at hresult
                                subst result
                                obtain ⟨serialNode, hserialNode, hserial⟩ :=
                                  reachable_nodes_serial hreachable address
                                    haddress
                                rw [hnode] at hserialNode
                                cases Concrete.Local.node.inj hserialNode
                                have hremainingFlights :=
                                  takeFlight_remaining_empty hserial ht
                                have hremainingKnown := takeFlight_known ht
                                have hworkflow :=
                                  workflow_after_scan_flight_removed hreachable
                                    related haddress hnode ht hp htransaction
                                have hcachedFlights :
                                    cached.flights = [] := by
                                  cases loaded <;>
                                    simpa [cached, Concrete.Node.cachePut,
                                      Concrete.Node.cacheInvalidate] using
                                      hremainingFlights
                                have hcachedKnown :
                                    cached.known = node.known := by
                                  cases loaded <;>
                                    simpa [cached, Concrete.Node.cachePut,
                                      Concrete.Node.cacheInvalidate] using
                                      hremainingKnown
                                have hcachedWorkflow :
                                    cached.workflowBlocked = true ∨
                                      (abstract.process .service).workflow.pending =
                                        Concrete.pendingWorkflow
                                          cached.pending := by
                                  cases loaded <;>
                                    simpa [cached, Concrete.Node.cachePut,
                                      Concrete.Node.cacheInvalidate] using
                                      hworkflow
                                exact ⟨[], trivial,
                                  related_after_terminal_node hreachable related
                                    haddress hnode hflight hcachedFlights
                                    hcachedKnown hcachedWorkflow
                                    (outputs := []) (by simp [Covered])
                                    htime hvalid (by
                                      simp [Concrete.step, ht, hp,
                                        Concrete.decide, Concrete.sendOutputs,
                                        hs, Outcomes.one, cached]
                                      rfl),
                                  rfl⟩
                        | some candidate =>
                            simp [ht, hp, Concrete.decide, hs,
                              Outcomes.one] at hresult
                            subst result
                            exact ⟨[], trivial,
                              by
                                simpa [endOf, Concrete.decide, hs, cached] using
                                  related_after_decide_node hreachable related
                                    haddress hnode ht
                                    (by
                                      cases loaded <;>
                                        simp [cached, Concrete.Node.cachePut,
                                          Concrete.Node.cacheInvalidate])
                                    (by
                                      cases loaded <;>
                                        simp [cached, Concrete.Node.cachePut,
                                          Concrete.Node.cacheInvalidate])
                                    (by
                                      cases loaded <;>
                                        simp [cached, Concrete.Node.cachePut,
                                          Concrete.Node.cacheInvalidate])
                                    (by
                                      cases loaded <;>
                                        simp [cached, Concrete.Node.cachePut,
                                          Concrete.Node.cacheInvalidate])
                                    (by
                                      cases loaded <;>
                                        simp [cached, Concrete.Node.cachePut,
                                          Concrete.Node.cacheInvalidate])
                                    hp hs htime hvalid (by
                                      simp [Concrete.step, ht, hp,
                                        Concrete.decide, hs, Outcomes.one,
                                        cached]),
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
                                    (base :=
                                      remaining.cacheInvalidate flight.key)
                                    (by
                                      simpa [Concrete.Node.cacheInvalidate]
                                        using takeFlight_nextOp ht)
                                    (by
                                      simpa [Concrete.Node.cacheInvalidate]
                                        using hremainingFlights)
                                    (by
                                      simpa [Concrete.Node.cacheInvalidate]
                                        using hremainingKnown)
                                    (flight := loading) rfl
                                    (by
                                      simpa [Concrete.Node.cacheInvalidate]
                                        using hstage)
                                    htime
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
                                (nextNode :=
                                  remaining.cacheInvalidate flight.key)
                                (by
                                  simpa [Concrete.Node.cacheInvalidate] using
                                    hremainingFlights)
                                (by
                                  simpa [Concrete.Node.cacheInvalidate] using
                                    hremainingKnown)
                                (by
                                  simpa [Concrete.Node.cacheInvalidate] using
                                    hworkflow)
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
                                    { remaining.cacheInvalidate flight.key with
                                      workflowBlocked := true })
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingFlights)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingKnown)
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
                                    { remaining.cacheInvalidate flight.key with
                                      workflowBlocked := true })
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingFlights)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingKnown)
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
                                Concrete.Transaction.isExternal,
                                Concrete.Node.cacheInvalidate] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    remaining.cacheInvalidate flight.key)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingFlights)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingKnown)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hworkflow)
                                  (outputs := [Resonate.unavailable call])
                                  (by simpa [hx, Concrete.failureOutputs] using
                                    hfailed)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hx,
                                      Concrete.failureOutputs,
                                      Concrete.Transaction.isExternal,
                                      Concrete.Node.cacheInvalidate,
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
                                Concrete.Transaction.isExternal,
                                Concrete.Node.cacheInvalidate] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    { remaining.cacheInvalidate flight.key with
                                      workflowBlocked := true })
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingFlights)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingKnown)
                                  (.inl rfl) (outputs := [])
                                  (by intro output houtput; contradiction)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hx,
                                      Concrete.failureOutputs,
                                      Concrete.Transaction.isExternal,
                                      Concrete.Node.cacheInvalidate,
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
                                Concrete.Transaction.isExternal,
                                Concrete.Node.cacheInvalidate] using
                                related_after_terminal_node hreachable related
                                  haddress hnode hflight
                                  (nextNode :=
                                    { remaining.cacheInvalidate flight.key with
                                      workflowBlocked := true })
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingFlights)
                                  (by
                                    simpa [Concrete.Node.cacheInvalidate] using
                                      hremainingKnown)
                                  (.inl rfl) (outputs := [])
                                  (by intro output houtput; contradiction)
                                  htime hvalid (by
                                    simp [Concrete.step, ht, hx,
                                      Concrete.failureOutputs,
                                      Concrete.Transaction.isExternal,
                                      Concrete.Node.cacheInvalidate,
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
