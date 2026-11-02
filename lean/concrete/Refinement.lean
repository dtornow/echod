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
    (Concrete.storePut {}
      sender (({} : Concrete.Store).commit key document)
      op key document none).val =
      [({
        state := .store (({} : Concrete.Store).commit key document)
        send := [(sender, .storeReply { op, payload := .conflict })]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg)] := by
  simp [Concrete.storePut, Concrete.Store.commit,
    Concrete.Store.version, Rover.Outcomes.one]

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

/-- A document is relevant to timeout discovery exactly when it can contain
work. -/
def RelevantDocument : (key : DocumentKey) → Document key → Prop
  | .origin _, document => document ≠ []
  | .schedule _, document => document.isSome

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
  | sweep {key transaction timer now rest before}
      {candidate : Concrete.Candidate key}
      (htransaction : transaction = .sweep timer now rest)
      (hkey : timer.target.key = key) :
      (hkey ▸ Concrete.selectScan appConfig timer.target.key now rest
        (hkey.symm ▸ before)) =
        some candidate →
      Selected appConfig key transaction before
        candidate.document candidate.outputs candidate.continuations

theorem selectScanWork_relevant
    {appConfig : Resonate.Config} {key : DocumentKey} {now : Time}
    {rest : List Concrete.PendingEntry} {before : Document key}
    {candidate : Concrete.Candidate key}
    (hselect :
      Concrete.selectScanWork appConfig key now rest before = some candidate) :
    RelevantDocument key before := by
  cases key with
  | origin origin =>
      change before ≠ []
      intro hempty
      subst before
      simp [Concrete.selectScanWork, Concrete.Decision.originWork] at hselect
  | schedule id =>
      cases before with
      | none => simp [Concrete.selectScanWork] at hselect
      | some schedule => rfl

theorem deadline_relevant
    {key : DocumentKey} {before : Document key} {now : Time}
    (hdeadline :
      (Concrete.documentDeadline? key before now).isSome = true) :
    RelevantDocument key before := by
  cases key with
  | origin origin =>
      change before ≠ []
      intro hempty
      subst before
      simp [Concrete.documentDeadline?, Concrete.minimumTime?] at hdeadline
  | schedule id =>
      cases before with
      | none => simp [Concrete.documentDeadline?] at hdeadline
      | some schedule => rfl

theorem selectScan_relevant
    {appConfig : Resonate.Config} {key : DocumentKey} {now : Time}
    {rest : List Concrete.PendingEntry} {before : Document key}
    {candidate : Concrete.Candidate key}
    (hselect :
      Concrete.selectScan appConfig key now rest before = some candidate) :
    RelevantDocument key before := by
  unfold Concrete.selectScan at hselect
  cases hwork :
      Concrete.selectScanWork appConfig key now rest before with
  | some work =>
      exact selectScanWork_relevant hwork
  | none =>
      have hdeadline :
          (Concrete.documentDeadline? key before now).isSome = true := by
        cases hvalue :
            (Concrete.documentDeadline? key before now).isSome with
        | false =>
            simp [hwork, hvalue] at hselect
        | true => rfl
      exact deadline_relevant hdeadline

theorem Selected.sweep_relevant
    {appConfig : Resonate.Config} {key : DocumentKey}
    {timer : Concrete.TimerKey} {now : Time}
    {rest : List Concrete.PendingEntry}
    {before after : Document key} {outputs continuations}
    (hselected :
      Selected appConfig key (.sweep timer now rest) before after
        outputs continuations) :
    RelevantDocument key before := by
  cases hselected with
  | sweep htransaction hkey hselect =>
      cases htransaction
      cases hkey
      exact selectScan_relevant hselect

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
      flightContinuations flightAttempt flightPhase flightAddress flightArmed
      flightFired flightCleanup =>
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
    case sweep timer now rest =>
      simp only [Concrete.select] at hselect
      split at hselect
      next heq => exact .sweep rfl heq hselect
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

theorem Snapshot.sameDocuments
    {before after : Concrete.Store} {key : DocumentKey}
    {loaded : Option (Document key × Concrete.Version)}
    (hvalues : after.values = before.values)
    (h : Snapshot before key loaded) :
    Snapshot after key loaded := by
  cases loaded with
  | none => trivial
  | some value =>
      obtain ⟨document, version⟩ := value
      obtain ⟨current, currentVersion, hread, hle, heq⟩ := h
      refine ⟨current, currentVersion, ?_, hle, heq⟩
      simpa [Concrete.Store.read, hvalues] using hread

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

@[grind] theorem Selected.external_continuations_nil
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
  | sweep htransaction _ _ => contradiction

@[grind] theorem select_external_continuations_nil
    {appConfig : Resonate.Config} {key : DocumentKey} {call : Call}
    {address : Addr}
    {loaded : Option (Document key × Concrete.Version)}
    {candidate : Concrete.Candidate key}
    (hkey : (Concrete.Transaction.external call).key? = some key)
    (hselect :
      Concrete.select appConfig
          { key := key, transaction := .external call, address }
          loaded =
        some candidate) :
    candidate.continuations = [] :=
  Selected.external_continuations_nil (select_valid hkey hselect)

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

structure StoreRep (physical : Concrete.Store) (abstract : State) : Prop where
  documents :
    ∀ key, physical.toAbstract.read key = abstract.store.read key
  relevantKeys :
    ∀ key, RelevantDocument key (physical.toAbstract.read key) →
      key ∈ abstract.store.keys

instance {physical : Concrete.Store} {abstract : State} :
    CoeFun (StoreRep physical abstract) (fun _ =>
      ∀ key, physical.toAbstract.read key = abstract.store.read key) :=
  ⟨StoreRep.documents⟩

theorem StoreRep.read {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract) (key : DocumentKey) :
    physical.toAbstract.read key = abstract.store.read key :=
  hrep key

theorem StoreRep.commit {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract) (key : DocumentKey)
    (document : Document key) :
    StoreRep (physical.commit key document)
      { abstract with store := abstract.store.write key document } := by
  constructor
  · intro other
    rw [Concrete.Store.toAbstract_commit]
    by_cases h : other = key
    · subst other
      simp
    · simp [h, hrep other]
  · intro other hrelevant
    rw [Concrete.Store.toAbstract_commit] at hrelevant
    by_cases h : other = key
    · subst other
      exact Resonate.Store.key_mem_write _ _ _
    · exact Store.key_mem_write_of_mem _ _ _ _
        (hrep.relevantKeys other (by simpa [h] using hrelevant))

theorem StoreRep.fence {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract) (key : DocumentKey) :
    StoreRep (physical.fence key) abstract := by
  constructor
  · intro other
    rw [Concrete.Store.toAbstract_read_fence]
    exact hrep other
  · intro other hrelevant
    rw [Concrete.Store.toAbstract_read_fence] at hrelevant
    exact hrep.relevantKeys other hrelevant

theorem StoreRep.of_store_eq
    {physical : Concrete.Store} {left right : State}
    (hrep : StoreRep physical left) (hstore : left.store = right.store) :
    StoreRep physical right := by
  constructor
  · intro key
    rw [← hstore]
    exact hrep key
  · intro key hrelevant
    rw [← hstore]
    exact hrep.relevantKeys key hrelevant

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
      constructor
      · intro other
        by_cases hother : other = key
        · subst other
          simp [hlocal.1]
        · rw [Concrete.Store.toAbstract_commit]
          simp [hother, external_frame
            { appConfig with unreliable := true } call key other
            abstract hkey hother, hrep other]
      · intro other hrelevant
        by_cases hother : other = key
        · subst other
          exact external_key_mem
            { appConfig with unreliable := true } call abstract key hkey
        · exact external_keys_mono
            { appConfig with unreliable := true } call abstract other
              (hrep.relevantKeys other (by
                rw [Concrete.Store.toAbstract_commit] at hrelevant
                simpa [hother] using hrelevant))
    | sweep hselectedTransaction _ _ =>
      contradiction

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
      · constructor
        · intro other
          by_cases hother : other = item.key
          · subst other
            simp [hlocal.1]
          · rw [Concrete.Store.toAbstract_commit]
            simp [hother, Resonate.runWork_frame
              { appConfig with unreliable := true } item now
              (Concrete.pendingWorkflow rest)
              abstract other hother, hrep other]
        · intro other hrelevant
          by_cases hother : other = item.key
          · subst other
            exact work_key_mem { appConfig with unreliable := true } item now
              (Concrete.pendingWorkflow rest) abstract
          · exact work_keys_mono
              { appConfig with unreliable := true } item now
              (Concrete.pendingWorkflow rest) abstract other
              (hrep.relevantKeys other (by
                rw [Concrete.Store.toAbstract_commit] at hrelevant
                simpa [hother] using hrelevant))
      · rw [← hlocal.2.1]
        exact (Concrete.pendingWorkflow_map_fromWorkflow _).symm
    | sweep hselectedTransaction _ _ =>
      contradiction

theorem runWork_rest_store_outputs
    (appConfig : Resonate.Config) (item : WorkItem) (now : Time)
    (left right : List WorkflowEntry) (state : State) :
    (Resonate.runWork appConfig item now left state).1.store =
        (Resonate.runWork appConfig item now right state).1.store ∧
      (Resonate.runWork appConfig item now left state).2 =
        (Resonate.runWork appConfig item now right state).2 := by
  cases item <;> simp [Resonate.runWork]

theorem runWork_rest_pending
    (appConfig : Resonate.Config) (item : WorkItem) (now : Time)
    (left right : List WorkflowEntry) (state : State) :
    ∃ added,
      (Resonate.runWork appConfig item now left state).1.workflow.pending =
          left ++ added ∧
      (Resonate.runWork appConfig item now right state).1.workflow.pending =
          right ++ added := by
  cases item <;> simp [Resonate.runWork]

theorem work_cas_transport_rest
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {item : WorkItem} {now : Time} {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .work item now rest)
    (hcurrent : physical.read key = provenance.loaded)
    (abstractRest : List WorkflowEntry) :
    let lifted := Resonate.runWork
      { appConfig with unreliable := true } item now abstractRest abstract
    StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 = provenance.outputs := by
  have hold :=
    work_cas_transport hrep provenance htransaction hcurrent
  let concreteRest := Concrete.pendingWorkflow rest
  have hsame := runWork_rest_store_outputs
    { appConfig with unreliable := true } item now concreteRest
      abstractRest abstract
  dsimp only
  constructor
  · exact hold.1.of_store_eq hsame.1
  · rw [← hsame.2]
    exact hold.2.1

theorem sweep_cas_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey}
    {timer : Concrete.TimerKey}
    {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {now : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .sweep timer now rest)
    (htarget : timer.target.key = key)
    (hcurrent : physical.read key = provenance.loaded)
    (hwork :
      (Concrete.selectScanWork appConfig key now rest
        ((provenance.loaded.map (·.1)).getD
          (emptyDocument key))).isSome = true)
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
    rw [htransaction] at selected
    cases selected with
    | sweep hselectedTransaction hkey hselected =>
      cases hselectedTransaction
      cases hkey
      rename_i candidate
      have hselectedWork :
          Concrete.selectScanWork appConfig timer.target.key now rest
              ((loaded.map (·.1)).getD
                (emptyDocument timer.target.key)) =
            some candidate := by
        unfold Concrete.selectScan at hselected
        cases hworkResult :
            Concrete.selectScanWork appConfig timer.target.key now rest
              ((loaded.map (·.1)).getD
                (emptyDocument timer.target.key)) with
        | none =>
            simp [hworkResult] at hwork
        | some work =>
            rw [hworkResult] at hselected
            cases hselected
            rfl
      obtain ⟨deadline, target, token, armedBy⟩ := timer
      cases target with
      | origin origin =>
        simp only [Concrete.TimerTarget.key] at *
        change physical.read (.origin origin) = loaded at hcurrent
        change Concrete.selectScanWork appConfig (.origin origin) now rest
          ((loaded.map (·.1)).getD (emptyDocument (.origin origin))) =
            some candidate at hselectedWork
        have hbefore := toAbstract_read_eq_loaded hcurrent
        have habstract :
            abstract.store.read (.origin origin) =
              (loaded.map (·.1)).getD
                (emptyDocument (.origin origin)) := by
          rw [← hrep (.origin origin), hbefore]
          rfl
        obtain ⟨item, hitem, hdocument, houtputs, hcontinuations⟩ :=
          Concrete.selectScan_origin_some appConfig origin now rest
            ((loaded.map (·.1)).getD
              (emptyDocument (.origin origin))) _ hselectedWork
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
          abstract hitemKey habstract
        refine ⟨item, hitemKey, ?_, ?_,
          hlocal.2.2.trans houtputs'.symm, ?_⟩
        · simp only [Resonate.eligibleWorkAt, List.mem_flatMap]
          exact ⟨.origin origin, hkeymem, by
            change item ∈ Direct.originWork origin
              (abstract.store.read (.origin origin)) now
            rw [habstract]
            exact hitemAbstract⟩
        · constructor
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
          · intro other hrelevant
            by_cases hother : other = .origin origin
            · subst other
              simpa [hitemKey] using
                (work_key_mem { appConfig with unreliable := true } item now
                  (Concrete.pendingWorkflow rest) abstract)
            · exact work_keys_mono
                { appConfig with unreliable := true } item now
                (Concrete.pendingWorkflow rest) abstract other
                (hrep.relevantKeys other (by
                  rw [Concrete.Store.toAbstract_commit] at hrelevant
                  simpa [hother] using hrelevant))
        · rw [hlocal.2.1]
          exact (Concrete.pendingWorkflow_map_fromWorkflow _).symm.trans
            (congrArg Concrete.pendingWorkflow hcontinuations'.symm)
      | schedule id =>
        simp only [Concrete.TimerTarget.key] at *
        change physical.read (.schedule id) = loaded at hcurrent
        change Concrete.selectScanWork appConfig (.schedule id) now rest
          ((loaded.map (·.1)).getD (emptyDocument (.schedule id))) =
            some candidate at hselectedWork
        have hbefore := toAbstract_read_eq_loaded hcurrent
        have habstract :
            abstract.store.read (.schedule id) =
              (loaded.map (·.1)).getD
                (emptyDocument (.schedule id)) := by
          rw [← hrep (.schedule id), hbefore]
          rfl
        obtain ⟨schedule, hschedule, hdue, hdocument, houtputs,
            hcontinuations⟩ :=
          Concrete.selectScan_schedule_some appConfig id now rest
            ((loaded.map (·.1)).getD
              (emptyDocument (.schedule id))) _ hselectedWork
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
        · constructor
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
          · intro other hrelevant
            by_cases hother : other = .schedule id
            · subst other
              exact work_key_mem { appConfig with unreliable := true }
                (.scheduleTimeout id) now
                (Concrete.pendingWorkflow rest) abstract
            · exact work_keys_mono
                { appConfig with unreliable := true } (.scheduleTimeout id)
                now (Concrete.pendingWorkflow rest) abstract other
                (hrep.relevantKeys other (by
                  rw [Concrete.Store.toAbstract_commit] at hrelevant
                  simpa [hother] using hrelevant))
        · rw [hlocal.2.1]
          exact
            (Concrete.pendingWorkflow_map_fromWorkflow _).symm.trans
              (congrArg Concrete.pendingWorkflow hcontinuations'.symm)

theorem sweep_cas_transport_rest
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {timer : Concrete.TimerKey}
    {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {now : Time} {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .sweep timer now rest)
    (htarget : timer.target.key = key)
    (hcurrent : physical.read key = provenance.loaded)
    (hwork :
      (Concrete.selectScanWork appConfig key now rest
        ((provenance.loaded.map (·.1)).getD
          (emptyDocument key))).isSome = true)
    (hkeymem : key ∈ abstract.store.keys)
    (abstractRest : List WorkflowEntry) :
    ∃ item,
      item.key = key ∧
      item ∈ Resonate.eligibleWorkAt abstract now ∧
      let lifted := Resonate.runWork
        { appConfig with unreliable := true } item now abstractRest abstract
      StoreRep (physical.commit key document) lifted.1 ∧
        lifted.2 = provenance.outputs ∧
        (Resonate.runWork { appConfig with unreliable := true } item now
          (Concrete.pendingWorkflow rest) abstract).1.workflow.pending =
            Concrete.pendingWorkflow provenance.continuations := by
  obtain ⟨item, hitemKey, hitem, hold⟩ :=
    sweep_cas_transport hrep provenance htransaction htarget hcurrent hwork
      hkeymem
  refine ⟨item, hitemKey, hitem, ?_⟩
  have hsame := runWork_rest_store_outputs
    { appConfig with unreliable := true } item now
      (Concrete.pendingWorkflow rest) abstractRest abstract
  refine ⟨?_, ?_, hold.2.2⟩
  · exact hold.1.of_store_eq hsame.1
  · rw [← hsame.2]
    exact hold.2.1

theorem sweep_idle_cas_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {timer : Concrete.TimerKey}
    {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {now : Time} {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .sweep timer now rest)
    (hcurrent : physical.read key = provenance.loaded)
    (hwork :
      (Concrete.selectScanWork appConfig key now rest
        ((provenance.loaded.map (·.1)).getD
          (emptyDocument key))).isSome = false) :
    StoreRep (physical.commit key document) abstract ∧
      provenance.outputs = [] ∧
      Concrete.pendingWorkflow provenance.continuations =
        Concrete.pendingWorkflow rest := by
  cases provenance with
  | mk transaction loaded outputs continuations expected_eq selected =>
    simp only at htransaction hcurrent hwork ⊢
    subst transaction
    cases selected with
    | sweep hselectedTransaction hkey hselected =>
        cases hselectedTransaction
        cases hkey
        rename_i candidate
        have hworkNone :
            Concrete.selectScanWork appConfig timer.target.key now rest
                ((loaded.map (·.1)).getD
                  (emptyDocument timer.target.key)) = none := by
          cases hresult :
              Concrete.selectScanWork appConfig timer.target.key now rest
                ((loaded.map (·.1)).getD
                  (emptyDocument timer.target.key)) with
          | none => rfl
          | some candidate => simp [hresult] at hwork
        by_cases hdeadline :
            (Concrete.documentDeadline? timer.target.key
              ((loaded.map (·.1)).getD
                (emptyDocument timer.target.key)) now).isSome
        · rw [Concrete.selectScan, hworkNone, if_pos hdeadline] at hselected
          have hcandidate := Option.some.inj hselected
          cases hcandidate
          refine ⟨?_, rfl, rfl⟩
          have hdocument :
              (loaded.map (·.1)).getD (emptyDocument timer.target.key) =
                physical.toAbstract.read timer.target.key := by
            symm
            exact toAbstract_read_eq_loaded hcurrent
          rw [hdocument]
          exact StoreRep.fence hrep timer.target.key
        · rw [Concrete.selectScan, hworkNone, if_neg hdeadline] at hselected
          contradiction

theorem sweep_timeout_transport
    {appConfig : Resonate.Config}
    {physical : Concrete.Store} {abstract : State}
    (hrep : StoreRep physical abstract)
    {key : DocumentKey} {timer : Concrete.TimerKey}
    {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (provenance :
      PutProvenance appConfig key document expectedVersion)
    {instant now : Time} {rest : List Concrete.PendingEntry}
    (htransaction : provenance.transaction = .sweep timer instant rest)
    (htarget : timer.target.key = key)
    (hcurrent : physical.read key = provenance.loaded)
    (hinstant : instant ≤ now)
    (hkeyMem : key ∈ abstract.store.keys) :
    ∃ lifted added,
      lifted ∈
          (Resonate.runTimeoutChoices
            { appConfig with unreliable := true } now abstract).val ∧
      StoreRep (physical.commit key document) lifted.1 ∧
      lifted.2 = provenance.outputs ∧
      Concrete.pendingWorkflow provenance.continuations =
        Concrete.pendingWorkflow rest ++ added ∧
      lifted.1.workflow.pending = abstract.workflow.pending ++ added ∧
      (∀ knownKey ∈ abstract.store.keys,
        knownKey ∈ lifted.1.store.keys) ∧
      key ∈ lifted.1.store.keys := by
  cases hwork :
      (Concrete.selectScanWork appConfig key instant rest
        ((provenance.loaded.map (·.1)).getD
          (emptyDocument key))).isSome with
  | false =>
      have hidle :=
        sweep_idle_cas_transport hrep provenance htransaction hcurrent hwork
      refine ⟨(abstract, []), [], ?_, hidle.1, ?_, ?_, ?_, ?_, hkeyMem⟩
      · simp [Resonate.runTimeoutChoices]
      · exact hidle.2.1.symm
      · simpa using hidle.2.2
      · simp
      · intro knownKey hknown
        exact hknown
  | true =>
      obtain ⟨item, hitemKey, hitem, htransport⟩ :=
        sweep_cas_transport_rest hrep provenance htransaction htarget hcurrent
          hwork hkeyMem abstract.workflow.pending
      let lifted :=
        Resonate.runWork { appConfig with unreliable := true }
          item instant abstract.workflow.pending abstract
      obtain ⟨added, hlocalPending, habstractPending⟩ :=
        runWork_rest_pending { appConfig with unreliable := true }
          item instant (Concrete.pendingWorkflow rest)
          abstract.workflow.pending abstract
      refine ⟨lifted, added, ?_, htransport.1, htransport.2.1, ?_,
        ?_, ?_, ?_⟩
      · simp only [Resonate.runTimeoutChoices, List.mem_cons]
        right
        simp only [Resonate.timeoutChoices, List.mem_append]
        right
        simp only [Resonate.documentTimeoutChoices, List.mem_flatMap,
          List.mem_map]
        exact ⟨instant, List.mem_range.mpr (Nat.lt_succ_iff.mpr hinstant),
          item, hitem, by simp [lifted]⟩
      · rw [← htransport.2.2, hlocalPending]
      · simpa [lifted] using habstractPending
      · exact work_keys_mono { appConfig with unreliable := true }
          item instant abstract.workflow.pending abstract
      · have hitemKeyMem :=
          work_key_mem { appConfig with unreliable := true }
            item instant abstract.workflow.pending abstract
        rw [hitemKey] at hitemKeyMem
        simpa [lifted] using hitemKeyMem

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
  | .work item instant _ =>
      ∃ request, item = .occurrence request instant
  | .external _ | .sweep _ _ _ => True

def FlightValid (appConfig : Resonate.Config)
    (flight : Concrete.Flight) : Prop :=
  flight.transaction.key? = some flight.key ∧
  (match flight.phase with
   | .loading | .deleting => True
   | .arming | .writing =>
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

theorem FlightValid.putValid
    {appConfig : Resonate.Config} {flight : Concrete.Flight}
    (hvalid : FlightValid appConfig flight)
    (hphase : flight.phase = .arming ∨ flight.phase = .writing)
    {document : Document flight.key}
    (hdocument : flight.document = some document) :
    ValidPut appConfig flight.key document (flight.loaded.map (·.2)) := by
  rw [FlightValid] at hvalid
  rcases hphase with hphase | hphase <;> rw [hphase] at hvalid
  all_goals
    obtain ⟨selectedDocument, hselectedDocument, hselected⟩ := hvalid.2.1
    rw [hdocument] at hselectedDocument
    cases Option.some.inj hselectedDocument
    exact ⟨{
      transaction := flight.transaction
      loaded := flight.loaded
      outputs := flight.selected
      continuations := flight.continuations
      expected_eq := rfl
      selected := hselected
    }⟩

theorem FlightValid.select_ne_none
    {appConfig : Resonate.Config} {flight : Concrete.Flight}
    (hvalid : FlightValid appConfig flight)
    (hnotSweep :
      ∀ timer instant rest,
        flight.transaction ≠ .sweep timer instant rest)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    Concrete.select appConfig flight loaded ≠ none := by
  cases flight with
  | mk key transaction oldLoaded document selected continuations attempt phase
      address armed fired =>
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
      | sweep timer instant rest =>
          exact (hnotSweep timer instant rest rfl).elim

@[simp, grind .] theorem FlightValid.work_select_ne_none
    {appConfig : Resonate.Config} {flight : Concrete.Flight}
    (hvalid : FlightValid appConfig flight)
    {item : WorkItem} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .work item instant rest)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    Concrete.select appConfig flight loaded ≠ none := by
  apply hvalid.select_ne_none
  intro timer sweepInstant sweepRest hsweep
  rw [htransaction] at hsweep
  contradiction

def NodeValid (appConfig : Resonate.Config)
    (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights →
    FlightValid appConfig flight

structure NodeValidWitness (appConfig : Resonate.Config)
    (node : Concrete.Node) where
  value : NodeValid appConfig node

theorem NodeValid.empty (appConfig : Resonate.Config) :
    NodeValid appConfig ({} : Concrete.Node) := by
  simp [NodeValid]

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

theorem NodeValid.consFlight {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : FlightValid appConfig flight) :
    NodeValid appConfig
      { node with flights := (op, flight) :: node.flights } := by
  intro currentOp current hmem
  simp only [List.mem_cons, Prod.mk.injEq] at hmem
  rcases hmem with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    exact hflight
  · exact hnode currentOp current hold

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

theorem NodeValid.work_select_ne_none_of_find
    {appConfig : Resonate.Config} {node : Concrete.Node}
    (hvalid : NodeValid appConfig node)
    {op foundOp : Concrete.OpId} {flight : Concrete.Flight}
    (hfind : node.flights.find? (·.1 == op) = some (foundOp, flight))
    {item : WorkItem} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .work item instant rest)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    Concrete.select appConfig flight loaded ≠ none := by
  apply FlightValid.work_select_ne_none
    (hvalid foundOp flight (List.mem_of_find?_eq_some hfind))
    htransaction

theorem NodeValid.work_select_ne_none_of_find_exists
    {appConfig : Resonate.Config} {node : Concrete.Node}
    (hvalid : NodeValid appConfig node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hfind :
      ∃ foundOp, node.flights.find? (·.1 == op) = some (foundOp, flight))
    {item : WorkItem} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .work item instant rest)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    Concrete.select appConfig flight loaded ≠ none := by
  obtain ⟨foundOp, hfind⟩ := hfind
  exact hvalid.work_select_ne_none_of_find hfind htransaction loaded

theorem NodeValid.work_select_none_false
    {appConfig : Resonate.Config} {node : Concrete.Node}
    (hvalid : NodeValid appConfig node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hfind :
      ∃ foundOp, node.flights.find? (·.1 == op) = some (foundOp, flight))
    {item : WorkItem} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .work item instant rest)
    {loaded : Option (Document flight.key × Concrete.Version)}
    (hselect : Concrete.select appConfig flight loaded = none) :
    False :=
  hvalid.work_select_ne_none_of_find_exists hfind htransaction loaded hselect

theorem NodeValid.work_select_none_false_of_find
    {appConfig : Resonate.Config} {node : Concrete.Node}
    (hvalid : NodeValid appConfig node)
    {flight : Concrete.Flight}
    {loaded : Option (Document flight.key × Concrete.Version)}
    (hselect : Concrete.select appConfig flight loaded = none)
    {item : WorkItem} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .work item instant rest)
    {predicate : Concrete.OpId × Concrete.Flight → Bool}
    {foundOp : Concrete.OpId}
    (hfind : node.flights.find? predicate = some (foundOp, flight)) :
    False :=
  FlightValid.work_select_ne_none
    (hvalid foundOp flight (List.mem_of_find?_eq_some hfind))
    htransaction loaded hselect

@[simp, grind .] theorem select_pending_entry_ne_none
    (appConfig : Resonate.Config)
    (entry : Concrete.PendingEntry) (rest : List Concrete.PendingEntry)
    (address : Addr)
    (loaded : Option (Document entry.key × Concrete.Version)) :
    Concrete.select appConfig {
      key := entry.key
      transaction := .work (.occurrence entry.1 entry.2) entry.2 rest
      address
    } loaded ≠ none := by
  cases entry with
  | occurrence request instant =>
      apply FlightValid.select_ne_none
      · exact ⟨by simp [Concrete.Transaction.key?, WorkItem.key,
            Concrete.PendingEntry.key],
          trivial, ⟨request, rfl⟩⟩
      · intro timer sweepInstant sweepRest h
        contradiction

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
    (hshape : WorkShaped transaction) (address : Addr := "")
    (fired : Option Concrete.TimerKey := none) :
    ∃ next,
      (Concrete.start appConfig node transaction key address fired).state =
        .node next ∧
      NodeValid appConfig next := by
  let flight : Concrete.Flight := { key, transaction, address, fired }
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
              Concrete.select appConfig { key, transaction, address, fired }
                  (some (value.document, value.version)) = none := by
            simpa [flight] using hselect
          cases hfired : fired with
          | none =>
              have hselectNone :
                  Concrete.select appConfig { key, transaction, address }
                    (some (value.document, value.version)) = none := by
                rw [hfired] at hselect'
                exact hselect'
              exact ⟨node,
                by simp [Concrete.decide, hselectNone], hnode⟩
          | some timer =>
              have hselectSome :
                  Concrete.select appConfig
                      { key, transaction, address, fired := some timer }
                    (some (value.document, value.version)) = none := by
                rw [hfired] at hselect'
                exact hselect'
              let cleaning :=
                Concrete.cleanupFlight
                  ({ key, transaction, address, fired := some timer } :
                    Concrete.Flight) timer
              have hcleaningCleanup : cleaning.cleanup = [timer] := by
                exact Concrete.cleanupFlight_cleanup _ _
              let finished := Concrete.finishNode node cleaning
              let next :=
                (finished.awaitControl (.cleanup cleaning.selected)
                  (.deleteTimers [timer])).1
              refine ⟨next, ?_, ?_⟩
              · simp only [Concrete.decide, hselectSome, hfired]
                change (Concrete.continueCleanup node cleaning).state =
                  .node next
                rw [Concrete.continueCleanup, hcleaningCleanup]
              intro currentOp currentFlight hmem
              apply hnode currentOp currentFlight
              simpa [next, finished, Concrete.finishNode,
                Concrete.Node.awaitControl] using hmem
      | some candidate =>
          have hselect' :
              Concrete.select appConfig { key, transaction, address, fired }
                  (some (value.document, value.version)) =
                some candidate := by
            simpa [flight] using hselect
          cases htimer : Concrete.timerForDocument key candidate.document
              transaction.logicalTime node.nextTimerToken address with
          | none =>
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
              · simp [Concrete.decide, hselect', Concrete.writeCandidate,
                  htimer, writing, flight]
              · apply NodeValid.await hnode
                exact ⟨hkey, ⟨candidate.document, rfl,
                  select_valid hkey hselect⟩, hshape⟩
          | some timer =>
              let arming : Concrete.Flight := {
                flight with
                loaded := some (value.document, value.version)
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .arming
                armed := some timer
              }
              let advanced :=
                { node with nextTimerToken := node.nextTimerToken + 1 }
              refine ⟨(advanced.await arming (.armTimer timer)).1,
                ?_, ?_⟩
              · simp [Concrete.decide, hselect', htimer, arming, advanced,
                  flight]
              · have hadvanced : NodeValid appConfig advanced := hnode
                have harming : FlightValid appConfig arming := by
                  simp only [FlightValid, arming,
                    Concrete.Phase.arming]
                  exact ⟨hkey, ⟨candidate.document, rfl,
                    select_valid hkey hselect⟩, hshape⟩
                exact NodeValid.await hadvanced harming (.armTimer timer)

theorem NodeValid.decide {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {flight : Concrete.Flight} (hflight : FlightValid appConfig flight)
    (loaded : Option (Document flight.key × Concrete.Version)) :
    ∃ next, (Concrete.decide appConfig node flight loaded).state = .node next ∧
      NodeValid appConfig next := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      cases hfired : flight.fired with
      | none =>
          exact ⟨node, by simp [Concrete.decide, hselect, hfired], hnode⟩
      | some fired =>
          let cleaning := Concrete.cleanupFlight flight fired
          have hcleaningCleanup : cleaning.cleanup = [fired] := by
            exact Concrete.cleanupFlight_cleanup _ _
          let finished := Concrete.finishNode node cleaning
          let next :=
            (finished.awaitControl (.cleanup cleaning.selected)
              (.deleteTimers [fired])).1
          refine ⟨next, ?_, ?_⟩
          · simp only [Concrete.decide, hselect, hfired]
            change (Concrete.continueCleanup node cleaning).state = .node next
            rw [Concrete.continueCleanup, hcleaningCleanup]
          intro currentOp currentFlight hmem
          apply hnode currentOp currentFlight
          simpa [next, finished, Concrete.finishNode,
            Concrete.Node.awaitControl] using hmem
  | some candidate =>
      cases htimer : Concrete.timerForDocument flight.key candidate.document
          flight.transaction.logicalTime node.nextTimerToken flight.address with
      | none =>
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
            by simp [Concrete.decide, hselect, Concrete.writeCandidate,
              htimer, writing], ?_⟩
          apply NodeValid.await hnode
          exact ⟨hflight.1, ⟨candidate.document, rfl,
            select_valid hflight.1 hselect⟩, hflight.2.2⟩
      | some timer =>
          let arming : Concrete.Flight := {
            flight with
            loaded
            document := some candidate.document
            selected := candidate.outputs
            continuations := candidate.continuations
            phase := .arming
            armed := some timer
          }
          let advanced :=
            { node with nextTimerToken := node.nextTimerToken + 1 }
          refine ⟨(advanced.await arming (.armTimer timer)).1,
            by simp [Concrete.decide, hselect, htimer, arming, advanced], ?_⟩
          have hadvanced : NodeValid appConfig advanced := hnode
          have harming : FlightValid appConfig arming := by
            simp only [FlightValid, arming,
              Concrete.Phase.arming]
            exact ⟨hflight.1, ⟨candidate.document, rfl,
              select_valid hflight.1 hselect⟩, hflight.2.2⟩
          exact NodeValid.await hadvanced harming (.armTimer timer)

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
      armed := none
      attempt := flight.attempt + 1
      phase := .loading
    }
    refine ⟨(node.await loading (.get flight.key)).1,
      by simp [loading], ?_⟩
    apply NodeValid.await hnode
    simpa [FlightValid, loading] using And.intro hflight.1 hflight.2.2
  · exact ⟨node, rfl, hnode⟩

theorem NodeValid.sameFlights {appConfig : Resonate.Config}
    {before after : Concrete.Node}
    (hbefore : NodeValid appConfig before)
    (hflights : after.flights = before.flights) :
    NodeValid appConfig after := by
  intro op flight hmem
  exact hbefore op flight (hflights ▸ hmem)

@[simp] theorem noteArmed_flights
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (node.noteArmed flight).flights = node.flights := by
  unfold Concrete.Node.noteArmed
  cases flight.armed <;> rfl

@[simp] theorem noteArmed_nextOp
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (node.noteArmed flight).nextOp = node.nextOp := by
  unfold Concrete.Node.noteArmed
  cases flight.armed <;> rfl

@[simp] theorem noteArmed_cache
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (node.noteArmed flight).cache = node.cache := by
  unfold Concrete.Node.noteArmed
  cases flight.armed <;> rfl

@[simp] theorem noteArmed_pending
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (node.noteArmed flight).pending = node.pending := by
  unfold Concrete.Node.noteArmed
  cases flight.armed <;> rfl

@[simp] theorem noteArmed_wheel
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (node.noteArmed flight).wheel = node.wheel := by
  unfold Concrete.Node.noteArmed
  cases flight.armed <;> rfl

@[simp] theorem noteArmed_controls
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (node.noteArmed flight).controls = node.controls := by
  unfold Concrete.Node.noteArmed
  cases flight.armed <;> rfl

@[simp] theorem finishNode_flights
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).flights = node.flights := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_nextOp
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).nextOp = node.nextOp := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_controls
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).controls = node.controls := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_cache
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).cache = node.cache := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_membership
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).membership = node.membership := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_armed
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).armed = node.armed := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_nextHeartbeat
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).nextHeartbeat = node.nextHeartbeat := by
  simp [Concrete.finishNode]

@[simp] theorem finishNode_nextTimerToken
    (node : Concrete.Node) (flight : Concrete.Flight) :
    (Concrete.finishNode node flight).nextTimerToken = node.nextTimerToken := by
  simp [Concrete.finishNode]

@[simp] theorem awaitControl_flights
    (node : Concrete.Node) (control : Concrete.Control)
    (payload : Concrete.StoreRequest) :
    (node.awaitControl control payload).1.flights = node.flights := by
  simp [Concrete.Node.awaitControl]

@[simp] theorem awaitControl_pending
    (node : Concrete.Node) (control : Concrete.Control)
    (payload : Concrete.StoreRequest) :
    (node.awaitControl control payload).1.pending = node.pending := by
  simp [Concrete.Node.awaitControl]

@[simp] theorem takeControl_flights (node : Concrete.Node) (op : Concrete.OpId) :
    (node.takeControl op).2.flights = node.flights := by
  simp [Concrete.Node.takeControl]

@[simp] theorem takeControl_pending (node : Concrete.Node) (op : Concrete.OpId) :
    (node.takeControl op).2.pending = node.pending := by
  simp [Concrete.Node.takeControl]

theorem takeControl_cleanup_mem
    {node : Concrete.Node} {op : Concrete.OpId} {outputs : List Output}
    (h : (node.takeControl op).1 = some (.cleanup outputs)) :
    (op, .cleanup outputs) ∈ node.controls := by
  simp only [Concrete.Node.takeControl] at h
  obtain ⟨pair, hfind, hpair⟩ := Option.map_eq_some_iff.mp h
  have hfst : pair.1 = op := by
    simpa using List.find?_some hfind
  have hmem := List.mem_of_find?_eq_some hfind
  cases pair with
  | mk foundOp foundControl =>
      cases hfst
      cases hpair
      exact hmem

/-- A cleanup entry that survives `takeControl` was already on the node.
Filtering drops the completed operation and does not allocate a control. -/
theorem takeControl_cleanup_kept
    {node : Concrete.Node} {taken op : Concrete.OpId} {outputs : List Output}
    (hmem :
      (op, .cleanup outputs) ∈ (node.takeControl taken).2.controls) :
    (op, .cleanup outputs) ∈ node.controls := by
  simp only [Concrete.Node.takeControl, List.mem_filter] at hmem
  exact hmem.1

@[simp] theorem takeFlight_controls (node : Concrete.Node) (op : Concrete.OpId) :
    (node.takeFlight op).2.controls = node.controls := by
  simp [Concrete.Node.takeFlight]

@[simp] theorem await_controls
    (node : Concrete.Node) (flight : Concrete.Flight)
    (payload : Concrete.StoreRequest) :
    (node.await flight payload).1.controls = node.controls := by
  simp [Concrete.Node.await]

@[simp] theorem cachePut_controls
    (node : Concrete.Node) (key : DocumentKey)
    (value : Concrete.Versioned key) :
    (node.cachePut key value).controls = node.controls := by
  simp [Concrete.Node.cachePut]

@[simp] theorem cacheInvalidate_controls
    (node : Concrete.Node) (key : DocumentKey) :
    (node.cacheInvalidate key).controls = node.controls := by
  simp [Concrete.Node.cacheInvalidate]

@[simp] theorem cleanupFlight_selected
    (flight : Concrete.Flight) (fired : Concrete.TimerKey) :
    (Concrete.cleanupFlight flight fired).selected = flight.selected := by
  cases h : flight.transaction <;> simp [Concrete.cleanupFlight, h]

theorem awaitControl_cleanup_mem
    {node : Concrete.Node} {control : Concrete.Control}
    {payload : Concrete.StoreRequest}
    {op : Concrete.OpId} {outputs : List Output}
    (hmem :
      (op, .cleanup outputs) ∈
        (node.awaitControl control payload).1.controls) :
    (op, .cleanup outputs) ∈ node.controls ∨
      (op = node.nextOp ∧ control = .cleanup outputs) := by
  simp only [Concrete.Node.awaitControl, List.mem_cons, Prod.mk.injEq] at hmem
  rcases hmem with ⟨hop, hcontrol⟩ | htail
  · cases hcontrol
    exact Or.inr ⟨hop, rfl⟩
  · exact Or.inl htail

theorem continueCleanup_cleanup_mem
    {node next : Concrete.Node} {flight : Concrete.Flight}
    {op : Concrete.OpId} {outputs : List Output}
    (hstate : (Concrete.continueCleanup node flight).state = Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls ∨ outputs = flight.selected := by
  cases hcleanup : flight.cleanup with
  | nil =>
      have hstate' :
          Concrete.Local.node (Concrete.finishNode node flight) = Concrete.Local.node next := by
        simpa [Concrete.continueCleanup, hcleanup] using hstate
      cases Concrete.Local.node.inj hstate'
      exact Or.inl (by simpa [finishNode_controls] using hmem)
  | cons key rest =>
      have hstate' :
          Concrete.Local.node ((Concrete.finishNode node flight).awaitControl
            (.cleanup flight.selected)
            (.deleteTimers (key :: rest))).1 = Concrete.Local.node next := by
        simpa [Concrete.continueCleanup, hcleanup] using hstate
      cases Concrete.Local.node.inj hstate'
      rcases awaitControl_cleanup_mem hmem with hkept | ⟨_, hcontrol⟩
      · exact Or.inl (by simpa [finishNode_controls] using hkept)
      · cases hcontrol
        exact Or.inr rfl

theorem committedFlight_cleanup_mem
    {node next : Concrete.Node} {flight : Concrete.Flight}
    {op : Concrete.OpId} {outputs : List Output}
    (hstate : (Concrete.committedFlight node flight).state = Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls ∨ outputs = flight.selected := by
  let prepared : Concrete.Flight :=
    { flight with cleanup := Concrete.cleanupKeys node flight }
  have hstate' :
      (Concrete.continueCleanup (node.noteArmed flight) prepared).state =
        Concrete.Local.node next := by
    simpa [Concrete.committedFlight] using hstate
  rcases continueCleanup_cleanup_mem hstate' hmem with hkept | hselected
  · exact Or.inl (by simpa [noteArmed_controls] using hkept)
  · exact Or.inr hselected

theorem decide_cleanup_mem
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (flight : Concrete.Flight)
    (loaded : Option (Document flight.key × Concrete.Version))
    {next : Concrete.Node} {op : Concrete.OpId} {outputs : List Output}
    (hstate :
      (Concrete.decide appConfig node flight loaded).state = Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls ∨ outputs = flight.selected := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      cases hfired : flight.fired with
      | none =>
          have hstate' : Concrete.Local.node node = Concrete.Local.node next := by
            simpa [Concrete.decide, hselect, hfired] using hstate
          cases Concrete.Local.node.inj hstate'
          exact Or.inl hmem
      | some timer =>
          have hstate' :
              (Concrete.continueCleanup node
                (Concrete.cleanupFlight flight timer)).state = Concrete.Local.node next := by
            simpa [Concrete.decide, hselect, hfired] using hstate
          rcases continueCleanup_cleanup_mem hstate' hmem with hkept | hselected
          · exact Or.inl hkept
          · exact Or.inr (by simpa [cleanupFlight_selected] using hselected)
  | some candidate =>
      cases htimer : Concrete.timerForDocument flight.key candidate.document
          flight.transaction.logicalTime node.nextTimerToken flight.address with
      | none =>
          have hstate' :
              Concrete.Local.node (node.await {
                flight with
                loaded
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .writing
              } (.put flight.key candidate.document (loaded.map (·.2)))).1 =
                Concrete.Local.node next := by
            simpa [Concrete.decide, Concrete.writeCandidate, hselect, htimer]
              using hstate
          cases Concrete.Local.node.inj hstate'
          exact Or.inl (by simpa [await_controls] using hmem)
      | some timer =>
          have hstate' :
              Concrete.Local.node (({ node with
                  nextTimerToken := node.nextTimerToken + 1 }).await {
                flight with
                loaded
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .arming
                armed := some timer
              } (.armTimer timer)).1 = Concrete.Local.node next := by
            simpa [Concrete.decide, hselect, htimer] using hstate
          cases Concrete.Local.node.inj hstate'
          exact Or.inl (by simpa [await_controls] using hmem)

theorem start_cleanup_mem
    {appConfig : Resonate.Config} {node : Concrete.Node}
    {transaction : Concrete.Transaction} {key : DocumentKey}
    {address : Addr} {fired : Option Concrete.TimerKey}
    {next : Concrete.Node} {op : Concrete.OpId} {outputs : List Output}
    (hstate :
      (Concrete.start appConfig node transaction key address fired).state =
        Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls ∨ outputs = [] := by
  let flight : Concrete.Flight := { key, transaction, address, fired }
  cases hcache : node.cacheRead key with
  | none =>
      have hstate' :
          Concrete.Local.node (node.await flight (.get key)).1 = Concrete.Local.node next := by
        simpa [flight, Concrete.start, hcache] using hstate
      cases Concrete.Local.node.inj hstate'
      exact Or.inl (by simpa [await_controls] using hmem)
  | some value =>
      cases hselect : Concrete.select appConfig flight
          (some (value.document, value.version)) with
      | none =>
          cases fired with
          | none =>
              have hstate' : Concrete.Local.node node = Concrete.Local.node next := by
                simpa [flight, Concrete.start, hcache, hselect, Concrete.decide]
                  using hstate
              cases Concrete.Local.node.inj hstate'
              exact Or.inl hmem
          | some timer =>
              have hstate' :
                  (Concrete.continueCleanup node
                    (Concrete.cleanupFlight flight timer)).state =
                    Concrete.Local.node next := by
                simpa [flight, Concrete.start, hcache, hselect, Concrete.decide]
                  using hstate
              rcases continueCleanup_cleanup_mem hstate' hmem with
                hkept | hselected
              · exact Or.inl hkept
              · exact Or.inr (by
                  simpa [flight, cleanupFlight_selected] using hselected)
      | some candidate =>
          cases htimer : Concrete.timerForDocument key candidate.document
              transaction.logicalTime node.nextTimerToken address with
          | none =>
              have hstate' :
                  Concrete.Local.node (node.await {
                    flight with
                    loaded := some (value.document, value.version)
                    document := some candidate.document
                    selected := candidate.outputs
                    continuations := candidate.continuations
                    phase := .writing
                  } (.put key candidate.document (some value.version))).1 =
                    Concrete.Local.node next := by
                simpa [flight, Concrete.start, hcache, hselect, htimer,
                  Concrete.decide, Concrete.writeCandidate] using hstate
              cases Concrete.Local.node.inj hstate'
              exact Or.inl (by simpa [await_controls] using hmem)
          | some timer =>
              have hstate' :
                  Concrete.Local.node (({ node with
                      nextTimerToken := node.nextTimerToken + 1 }).await {
                    flight with
                    loaded := some (value.document, value.version)
                    document := some candidate.document
                    selected := candidate.outputs
                    continuations := candidate.continuations
                    phase := .arming
                    armed := some timer
                  } (.armTimer timer)).1 = Concrete.Local.node next := by
                simpa [flight, Concrete.start, hcache, hselect, htimer,
                  Concrete.decide] using hstate
              cases Concrete.Local.node.inj hstate'
              exact Or.inl (by simpa [await_controls] using hmem)

theorem beginMembershipRefresh_cleanup_mem
    (node : Concrete.Node) (address : Addr) (now : Time)
    {next : Concrete.Node} {op : Concrete.OpId} {outputs : List Output}
    (hstate :
      (Concrete.beginMembershipRefresh node address now).state = Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls := by
  simp only [Concrete.beginMembershipRefresh, Concrete.Node.awaitControl]
    at hstate
  cases Concrete.Local.node.inj hstate
  simp only [List.mem_cons, Concrete.Node.awaitControl, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, hcontrol⟩ | htail
  · cases hcontrol
  · exact htail

theorem beginTimerList_cleanup_mem
    {node : Concrete.Node} {config : Concrete.Config} {now : Time}
    {kind : Concrete.ListingKind}
    {next : Concrete.Node} {op : Concrete.OpId} {outputs : List Output}
    (hstate :
      (Concrete.beginTimerList node config now kind).state = Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls := by
  simp only [Concrete.beginTimerList, Concrete.Node.awaitControl] at hstate
  cases Concrete.Local.node.inj hstate
  simp only [List.mem_cons, Concrete.Node.awaitControl, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, hcontrol⟩ | htail
  · cases hcontrol
  · exact htail

theorem refreshEnded_cleanup_mem
    {node : Concrete.Node} {config : Concrete.Config} {now : Time}
    {next : Concrete.Node} {op : Concrete.OpId} {outputs : List Output}
    (hstate : (Concrete.refreshEnded node config now).state = Concrete.Local.node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    (op, .cleanup outputs) ∈ node.controls := by
  have hstate' :
      (Concrete.beginTimerList
        { node with nextHeartbeat := some (now + config.heartbeat) }
        config now .initial).state = Concrete.Local.node next := by
    simpa [Concrete.refreshEnded] using hstate
  exact beginTimerList_cleanup_mem
    (node := { node with nextHeartbeat := some (now + config.heartbeat) })
    hstate' hmem

@[simp] theorem cachePut_pending
    (node : Concrete.Node) (key : DocumentKey)
    (value : Concrete.Versioned key) :
    (node.cachePut key value).pending = node.pending := by
  simp [Concrete.Node.cachePut]

@[simp] theorem cacheInvalidate_pending
    (node : Concrete.Node) (key : DocumentKey) :
    (node.cacheInvalidate key).pending = node.pending := by
  simp [Concrete.Node.cacheInvalidate]

@[simp] theorem awaitControl_cache
    (node : Concrete.Node) (control : Concrete.Control)
    (payload : Concrete.StoreRequest) :
    (node.awaitControl control payload).1.cache = node.cache := by
  simp [Concrete.Node.awaitControl]

@[simp] theorem awaitControl_snd
    (node : Concrete.Node) (control : Concrete.Control)
    (payload : Concrete.StoreRequest) :
    (node.awaitControl control payload).2 =
      (.store, .storeRequest { op := node.nextOp, payload }) := by
  simp [Concrete.Node.awaitControl]

@[simp] theorem cachePut_flights
    (node : Concrete.Node) (key : DocumentKey)
    (value : Concrete.Versioned key) :
    (node.cachePut key value).flights = node.flights := by
  simp [Concrete.Node.cachePut]

@[simp] theorem cacheInvalidate_flights
    (node : Concrete.Node) (key : DocumentKey) :
    (node.cacheInvalidate key).flights = node.flights := by
  simp [Concrete.Node.cacheInvalidate]

/-- The node left by `decide` when selection fails for a flight that already
fired. Cleanup is a control continuation, so the flight list is unchanged. -/
def cleanupNext (node : Concrete.Node) (flight : Concrete.Flight)
    (timer : Concrete.TimerKey) : Concrete.Node :=
  let cleaning := Concrete.cleanupFlight flight timer
  let finished := Concrete.finishNode node cleaning
  (finished.awaitControl (.cleanup cleaning.selected)
    (.deleteTimers [timer])).1

@[simp] theorem cleanupNext_flights
    (node : Concrete.Node) (flight : Concrete.Flight)
    (timer : Concrete.TimerKey) :
    (cleanupNext node flight timer).flights = node.flights := by
  simp [cleanupNext]

@[simp] theorem cleanupNext_cache
    (node : Concrete.Node) (flight : Concrete.Flight)
    (timer : Concrete.TimerKey) :
    (cleanupNext node flight timer).cache = node.cache := by
  simp [cleanupNext]

theorem continueCleanup_state (node : Concrete.Node) (flight : Concrete.Flight) :
    ∃ next,
      (Concrete.continueCleanup node flight).state = .node next ∧
      next.flights = node.flights ∧
      next.pending = flight.continuations ++ node.pending := by
  cases hcleanup : flight.cleanup with
  | nil =>
      refine ⟨Concrete.finishNode node flight, ?_, ?_, ?_⟩
      · simp [Concrete.continueCleanup, hcleanup]
      · simp [Concrete.finishNode]
      · simp [Concrete.finishNode]
  | cons key rest =>
      let finished := Concrete.finishNode node flight
      let next :=
        finished.awaitControl (.cleanup flight.selected)
          (.deleteTimers (key :: rest))
      refine ⟨next.1, ?_, ?_, ?_⟩
      · simp [Concrete.continueCleanup, hcleanup, finished, next]
      · simp [next, finished, Concrete.Node.awaitControl, Concrete.finishNode]
      · simp [next, finished, Concrete.Node.awaitControl, Concrete.finishNode]

theorem continueCleanup_outside_mem
    {node : Concrete.Node} {flight : Concrete.Flight} {output : Output}
    (houtput :
      (.outside, Concrete.Msg.output output) ∈
        (Concrete.continueCleanup node flight).send) :
    output ∈ flight.selected ∧ flight.cleanup = [] := by
  cases hcleanup : flight.cleanup with
  | nil =>
      simp [Concrete.continueCleanup, hcleanup, Concrete.sendOutputs] at houtput
      exact ⟨houtput, rfl⟩
  | cons key rest =>
      simp [Concrete.continueCleanup, hcleanup, Concrete.Node.awaitControl]
        at houtput

theorem committedFlight_state (node : Concrete.Node) (flight : Concrete.Flight) :
    ∃ next,
      (Concrete.committedFlight node flight).state = .node next := by
  let prepared := { flight with cleanup := Concrete.cleanupKeys node flight }
  obtain ⟨next, hstate, _⟩ :=
    continueCleanup_state (node.noteArmed flight) prepared
  exact ⟨next, by simpa [Concrete.committedFlight, prepared] using hstate⟩

theorem committedFlight_outside_mem
    {node : Concrete.Node} {flight : Concrete.Flight} {output : Output}
    (houtput :
      (.outside, Concrete.Msg.output output) ∈
        (Concrete.committedFlight node flight).send) :
    output ∈ flight.selected := by
  simp only [Concrete.committedFlight, Concrete.continueCleanup] at houtput
  split at houtput
  · simp [Concrete.sendOutputs] at houtput
    exact houtput
  · simp [Concrete.Node.awaitControl] at houtput

theorem start_state
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    (address : Addr := "") (fired : Option Concrete.TimerKey := none) :
    ∃ next,
      (Concrete.start appConfig node transaction key address fired).state =
        .node next := by
  let flight : Concrete.Flight := {
    key := key
    transaction := transaction
    address := address
    fired := fired
  }
  cases hcache : node.cacheRead key with
  | none =>
      exact ⟨(node.await flight (.get key)).1,
        by simp [flight, Concrete.start, hcache, Concrete.Node.await]⟩
  | some value =>
      cases hselect :
          Concrete.select appConfig flight
            (some (value.document, value.version)) with
      | none =>
          cases fired with
          | none =>
              exact ⟨node, by simp [flight, Concrete.start, hcache, hselect,
                Concrete.decide]⟩
          | some timer =>
              obtain ⟨next, hstate, _⟩ :=
                continueCleanup_state node (Concrete.cleanupFlight flight timer)
              exact ⟨next, by
                simp [flight, Concrete.start, hcache, hselect, Concrete.decide,
                  hstate]⟩
      | some candidate =>
          cases htimer :
              Concrete.timerForDocument key candidate.document
                transaction.logicalTime node.nextTimerToken address with
          | none =>
              exact ⟨(node.await {
                flight with
                loaded := some (value.document, value.version)
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .writing
              } (.put key candidate.document (some value.version))).1, by
                simp [flight, Concrete.start, hcache, hselect, htimer,
                  Concrete.decide, Concrete.writeCandidate,
                  Concrete.Node.await]⟩
          | some timer =>
              exact ⟨({ node with
                nextTimerToken := node.nextTimerToken + 1 }.await {
                flight with
                loaded := some (value.document, value.version)
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .arming
                armed := some timer
              } (.armTimer timer)).1, by
                simp [flight, Concrete.start, hcache, hselect, htimer,
                  Concrete.decide, Concrete.Node.await]⟩

theorem decide_state_cleanup
    (appConfig : Resonate.Config) (node : Concrete.Node)
    (current : Concrete.Flight)
    (loaded : Option (Document current.key × Concrete.Version))
    (timer : Concrete.TimerKey)
    (hselect : Concrete.select appConfig current loaded = none)
    (hfired : current.fired = some timer) :
    (Concrete.decide appConfig node current loaded).state =
      .node (cleanupNext node current timer) := by
  have hcleanup :
      (Concrete.cleanupFlight current timer).cleanup = [timer] :=
    Concrete.cleanupFlight_cleanup _ _
  simp only [Concrete.decide, hselect, hfired, cleanupNext]
  rw [Concrete.continueCleanup, hcleanup]

theorem NodeValid.continueCleanup {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {flight : Concrete.Flight} (hflight : FlightValid appConfig flight) :
    ∃ next,
      (Concrete.continueCleanup node flight).state = .node next ∧
      NodeValid appConfig next := by
  let finished := Concrete.finishNode node flight
  have hfinished : NodeValid appConfig finished :=
    hnode.sameFlights (by simp [finished, Concrete.finishNode])
  cases hcleanup : flight.cleanup with
  | nil =>
      exact ⟨finished, by simp [Concrete.continueCleanup, hcleanup, finished],
        hfinished⟩
  | cons key rest =>
      let next :=
        (finished.awaitControl (.cleanup flight.selected)
          (.deleteTimers (key :: rest))).1
      refine ⟨next, by simp [Concrete.continueCleanup, hcleanup, finished,
        next], ?_⟩
      exact hfinished.sameFlights (by simp [next, Concrete.Node.awaitControl])

theorem NodeValid.committedFlight {appConfig : Resonate.Config}
    {node : Concrete.Node} (hnode : NodeValid appConfig node)
    {flight : Concrete.Flight} (hflight : FlightValid appConfig flight) :
    ∃ next,
      (Concrete.committedFlight node flight).state = .node next ∧
      NodeValid appConfig next := by
  let prepared : Concrete.Flight := {
    flight with cleanup := Concrete.cleanupKeys node flight
  }
  have hprepared : FlightValid appConfig prepared := by
    simpa [FlightValid, prepared] using hflight
  have hnoted :
      NodeValid appConfig (node.noteArmed flight) :=
    hnode.sameFlights (by
      unfold Concrete.Node.noteArmed
      cases flight.armed <;> rfl)
  simpa [Concrete.committedFlight, prepared] using
    hnoted.continueCleanup hprepared

theorem continueCleanup_sends_no_put
    {node : Concrete.Node} {flight : Concrete.Flight}
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ (Concrete.continueCleanup node flight).send) : False := by
  simp only [Concrete.continueCleanup] at hsend
  split at hsend
  · simp [Concrete.sendOutputs] at hsend
  · simp [Concrete.Node.awaitControl] at hsend

@[simp] theorem put_not_mem_sendOutputs
    (outputs : List Output) (recipient : Concrete.Pid) (op : Concrete.OpId)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) :
    (recipient, Concrete.Msg.storeRequest {
      op
      payload := .put key document expectedVersion
    }) ∉ Concrete.sendOutputs outputs := by
  simp [Concrete.sendOutputs]

@[simp] theorem put_not_mem_continueCleanup_send
    (node : Concrete.Node) (flight : Concrete.Flight)
    (recipient : Concrete.Pid) (op : Concrete.OpId)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) :
    (recipient, Concrete.Msg.storeRequest {
      op
      payload := .put key document expectedVersion
    }) ∉ (Concrete.continueCleanup node flight).send :=
  continueCleanup_sends_no_put

theorem committedFlight_sends_no_put
    {node : Concrete.Node} {flight : Concrete.Flight}
    {recipient : Concrete.Pid} {op : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hsend :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ (Concrete.committedFlight node flight).send) : False := by
  exact continueCleanup_sends_no_put hsend

@[simp] theorem put_not_mem_committedFlight_send
    (node : Concrete.Node) (flight : Concrete.Flight)
    (recipient : Concrete.Pid) (op : Concrete.OpId)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) :
    (recipient, Concrete.Msg.storeRequest {
      op
      payload := .put key document expectedVersion
    }) ∉ (Concrete.committedFlight node flight).send :=
  committedFlight_sends_no_put

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
  have sameFlights (before after : Concrete.Node)
      (hbefore : NodeValid appConfig before)
      (hflights : after.flights = before.flights) :
      NodeValid appConfig after := by
    intro op flight hmem
    exact hbefore op flight (hflights ▸ hmem)
  have controlValid (before : Concrete.Node)
      (hbefore : NodeValid appConfig before)
      (control : Concrete.Control) (payload : Concrete.StoreRequest) :
      NodeValid appConfig (before.awaitControl control payload).1 :=
    sameFlights before _ hbefore (by simp [Concrete.Node.awaitControl])
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        exact ⟨node, rfl, hnode⟩
      · cases hp : node.pending with
        | cons entry rest =>
            simp only [hp, Outcomes.one, List.mem_singleton] at hresult
            subst result
            cases entry with
            | occurrence request instant =>
                exact NodeValid.start
                  (node := { node with pending := [] })
                  (sameFlights node _ hnode (by simp))
                  (.work (.occurrence request instant) instant rest)
                  (.origin request.id.origin) rfl
                  ⟨request, rfl⟩ (address := address)
        | nil =>
            simp only [hp] at hresult
            split at hresult
            · simp [Outcomes.one] at hresult
              subst result
              refine ⟨_, rfl, ?_⟩
              exact sameFlights node _ hnode (by
                simp [Concrete.beginMembershipRefresh,
                  Concrete.Node.awaitControl])
            · let wheel := node.wheel.takeDue now config.fireConcurrency
              cases hb : wheel.beginOne with
              | some pair =>
                  obtain ⟨timer, nextWheel⟩ := pair
                  have hb' :
                      (node.wheel.takeDue now config.fireConcurrency).beginOne =
                        some (timer, nextWheel) := by
                    simpa [wheel] using hb
                  rw [hb'] at hresult
                  simp only [Option.some.injEq, Prod.mk.injEq] at *
                  subst_vars
                  split at hresult
                  · simp [wheel, hb, Outcomes.one] at hresult
                    subst result
                    simpa [hp] using
                      (NodeValid.start
                        (node := {
                          node with
                            wheel := nextWheel })
                        (sameFlights node _ hnode (by simp))
                        (.sweep timer now []) timer.target.key rfl trivial
                        (address := address) (fired := some timer))
                  · simp [wheel, hb, Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, hnode⟩
              | none =>
                  have hb' :
                      (node.wheel.takeDue now config.fireConcurrency).beginOne =
                        none := by
                    simpa [wheel] using hb
                  rw [hb'] at hresult
                  try simp at *
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    subst result
                    refine ⟨_, rfl, ?_⟩
                    exact sameFlights { node with wheel } _ hnode (by
                      simp [Concrete.beginTimerList,
                        Concrete.Node.awaitControl])
                  · split at hresult
                    · simp [Outcomes.one] at hresult
                      subst result
                      refine ⟨_, rfl, ?_⟩
                      exact sameFlights { node with wheel } _ hnode (by
                        simp [Concrete.beginTimerList,
                          Concrete.Node.awaitControl])
                    · simp [Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl, hnode⟩
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
              simp only [hk, Option.some.injEq] at hresult
              split at hresult
              · simp [hk, Outcomes.one] at hresult
                subst result
                exact NodeValid.start hnode (.external call) key hk trivial
                  (address := address)
              · simp [hk, Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload with
        | got key loaded =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hnode⟩
              | some flight =>
                  have hnext := NodeValid.takeFlight hnode op
                  rw [ht] at hnext
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : flight.phase with
                    | loading =>
                        have hflight :=
                          hnode op flight (takeFlight_some_mem ht)
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
                                  version := value.2 })
                        simp [ht, hp, loaded', cached, Outcomes.one] at hresult
                        subst result
                        exact NodeValid.decide hcached hflight loaded'
                    | arming | writing | deleting =>
                        simp [ht, hp, Outcomes.one] at hresult
                        subst result
                        exact ⟨_, rfl, hnext.consFlight
                          (hnode op flight (takeFlight_some_mem ht))⟩
                  next _ =>
                    simp [ht, Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, hnext.consFlight
                      (hnode op flight (takeFlight_some_mem ht))⟩
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hnode⟩
              | some flight =>
                  have hnext := NodeValid.takeFlight hnode op
                  rw [ht] at hnext
                  cases hp : flight.phase with
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact hnext.committedFlight
                        (hnode op flight (takeFlight_some_mem ht))
                  | loading | arming | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl, hnext.consFlight
                        (hnode op flight (takeFlight_some_mem ht))⟩
        | done =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | some flight =>
                  have hnext := NodeValid.takeFlight hnode op
                  rw [ht] at hnext
                  cases hp : flight.phase with
                  | arming =>
                      cases hd : flight.document with
                      | none =>
                          simp [ht, hp, hd, Outcomes.one] at hresult
                          subst result
                          exact ⟨next, rfl, hnext⟩
                      | some document =>
                          simp [ht, hp, hd, Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_⟩
                          apply NodeValid.await hnext
                          simpa [FlightValid, hp, hd] using
                            hnode op flight (takeFlight_some_mem ht)
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact hnext.continueCleanup
                        (hnode op flight (takeFlight_some_mem ht))
                  | loading | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl, hnext.consFlight
                        (hnode op flight (takeFlight_some_mem ht))⟩
              | none =>
                  let next := (node.takeControl op).2
                  have hnext : NodeValid appConfig next := by
                    exact sameFlights node next hnode (by
                      simp [next, Concrete.Node.takeControl])
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, next, Outcomes.one] at hresult
                      subst result
                      exact ⟨next, rfl, hnext⟩
                  | some control =>
                      cases control with
                      | announced instant =>
                          simp [ht, hc, next, Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_⟩
                          exact controlValid next hnext
                            (.announcements instant) .listAnnouncements
                      | membershipWrite instant =>
                          simp [ht, hc, next, Concrete.refreshEnded,
                            Outcomes.one] at hresult
                          subst result
                          refine ⟨_, rfl, ?_⟩
                          exact sameFlights next _ hnext (by rfl)
                      | announcements instant | membership instant live
                      | timerList instant through kind | cleanup outputs =>
                          simp [ht, hc, next, Outcomes.one] at hresult
                          subst result
                          exact ⟨next, rfl, hnext⟩
        | announcements values =>
            cases hc : (node.takeControl op).1 with
            | none =>
                simp [hc, Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, sameFlights node _ hnode (by
                  simp [Concrete.Node.takeControl])⟩
            | some control =>
                cases control <;> simp only [hc] at hresult
                all_goals try split at hresult
                all_goals simp [Outcomes.one] at hresult
                all_goals subst result
                all_goals
                  exact ⟨_, rfl, sameFlights node _ hnode (by
                    simp [Concrete.Node.takeControl,
                      Concrete.Node.awaitControl])⟩
        | membership configuration version =>
            simp only [Concrete.step] at hresult
            cases hc : (node.takeControl op).1 with
            | none =>
                simp [hc, Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, sameFlights node _ hnode (by
                  simp [Concrete.Node.takeControl])⟩
            | some control =>
                cases control <;> simp only [hc] at hresult
                all_goals try split at hresult
                all_goals simp [Outcomes.one] at hresult
                all_goals subst result
                all_goals
                  first
                  | exact ⟨_, rfl, sameFlights node _ hnode (by
                      simp [Concrete.Node.takeControl,
                        Concrete.Node.awaitControl])⟩
        | timers keys =>
            cases hc : (node.takeControl op).1 with
            | none =>
                simp [hc, Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, sameFlights node _ hnode (by
                  simp [Concrete.Node.takeControl])⟩
            | some control =>
                cases control <;> simp [hc, Outcomes.one] at hresult
                all_goals subst result
                all_goals
                  exact ⟨_, rfl, sameFlights node _ hnode (by
                    simp [Concrete.Node.takeControl])⟩
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | some flight =>
                  have hnext := NodeValid.takeFlight hnode op
                  rw [ht] at hnext
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨{
                    next with flights := (op, flight) :: next.flights
                  }, rfl, hnext.consFlight
                    (hnode op flight (takeFlight_some_mem ht))⟩
              | none =>
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl, sameFlights node _ hnode (by
                        simp [Concrete.Node.takeControl])⟩
                  | some control =>
                      cases control <;> simp [ht, hc, Concrete.refreshEnded,
                        Concrete.beginTimerList, Outcomes.one] at hresult
                      all_goals subst result
                      all_goals
                        exact ⟨_, rfl, sameFlights node _ hnode (by
                          simp [Concrete.Node.takeControl,
                            Concrete.Node.awaitControl])⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | some flight =>
                  have hnext := NodeValid.takeFlight hnode op
                  rw [ht] at hnext
                  cases hp : flight.phase with
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact hnext.continueCleanup
                        (hnode op flight (takeFlight_some_mem ht))
                  | loading | arming | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl,
                        NodeValid.cacheInvalidate hnext flight.key⟩
              | none =>
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl, sameFlights node _ hnode (by
                        simp [Concrete.Node.takeControl])⟩
                  | some control =>
                      cases control <;> simp [ht, hc, Outcomes.one] at hresult
                      all_goals subst result
                      all_goals
                        exact ⟨_, rfl, sameFlights node _ hnode (by
                          simp [Concrete.Node.takeControl])⟩

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
          cases htimer : Concrete.timerForDocument key candidate.document
              transaction.logicalTime node.nextTimerToken "" with
          | none =>
              refine ⟨(node.await {
                  key
                  transaction
                  loaded := some (value.document, value.version)
                  document := some candidate.document
                  selected := candidate.outputs
                  continuations := candidate.continuations
                  phase := .writing
                } (.put key candidate.document (some value.version))).1,
                by simp [Concrete.decide, Concrete.writeCandidate, hselect,
                  htimer],
                by simp [Concrete.Node.await], ?_, ?_⟩
              · simp [Concrete.decide, Concrete.writeCandidate, hselect,
                  htimer, Concrete.Node.await]
              · intros
                simp_all [Concrete.decide, Concrete.writeCandidate, hselect,
                  htimer, Concrete.Node.await]
          | some timer =>
              let advanced :=
                { node with nextTimerToken := node.nextTimerToken + 1 }
              refine ⟨(advanced.await {
                  key
                  transaction
                  loaded := some (value.document, value.version)
                  document := some candidate.document
                  selected := candidate.outputs
                  continuations := candidate.continuations
                  phase := .arming
                  armed := some timer
                } (.armTimer timer)).1,
                by simp [Concrete.decide, hselect, htimer, advanced],
                by simp [advanced, Concrete.Node.await], ?_, ?_⟩
              · simp [Concrete.decide, hselect, htimer, advanced,
                  Concrete.Node.await]
              · intros
                simp_all [Concrete.decide, hselect, htimer, advanced,
                  Concrete.Node.await]



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
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide, Concrete.writeCandidate,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishNode, Concrete.finishFlight,
          Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide, Concrete.writeCandidate,
          Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishNode, Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals first | contradiction | grind

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
          simp only [Concrete.decide, hselect] at hstate
          split at hstate <;>
            simp [Concrete.writeCandidate, Concrete.Node.await] at hstate
          all_goals subst next
          all_goals simp only [List.mem_cons, Prod.mk.injEq] at hmem
          all_goals rcases hmem with hnew | hold
          all_goals
            first
            | exact (Nat.ne_of_lt hop hnew.1).elim
            | exact hold

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
      cases hfired : current.fired with
      | none =>
          simp [Concrete.decide, hselect, hfired] at hstate
          subst next
          exact hmem
      | some timer =>
          rw [decide_state_cleanup appConfig node current loaded timer
            hselect hfired] at hstate
          cases hstate
          simpa using hmem
  | some candidate =>
      simp only [Concrete.decide, hselect] at hstate
      split at hstate <;>
        simp [Concrete.writeCandidate, Concrete.Node.await] at hstate
      all_goals subst next
      all_goals simp only [List.mem_cons, Prod.mk.injEq] at hmem
      all_goals rcases hmem with hnew | hold
      all_goals
        first
        | exact (Nat.ne_of_lt hop hnew.1).elim
        | exact hold



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
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide, Concrete.writeCandidate,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide, Concrete.writeCandidate,
          Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishNode,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals
        try
          subst next
          simp only [finishNode_flights, noteArmed_flights] at hmem
          exact (List.mem_filter.mp hmem).1
      all_goals first | contradiction | grind

@[grind] theorem List.eq_of_mem_of_length_le_one'
    {α : Type} {values : List α} {left right : α}
    (hleft : left ∈ values) (hright : right ∈ values)
    (hlength : values.length ≤ 1) :
    left = right := by
  cases values with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          simp at hleft hright
          exact hleft.trans hright.symm
      | cons second rest => simp at hlength

theorem node_step_preserves_writing_flight
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    (hserial : node.flights.length ≤ 1)
    (hnotWritten :
      event ≠ .receive .store
        (.storeReply { op, payload := .written }))
    (hnotConflict :
      event ≠ .receive .store
        (.storeReply { op, payload := .conflict }))
    (hnotFailed :
      event ≠ .receive .store
        (.storeReply { op, payload := .failed }))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧ (op, flight) ∈ next.flights := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.finishFlight,
          Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate,
          Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup, Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals first | contradiction | grind

def NodeSerial (node : Concrete.Node) : Prop :=
  node.flights.length ≤ 1

@[grind] theorem List.eq_of_mem_of_length_le_one
    {α : Type} {items : List α} (hlength : items.length ≤ 1)
    {first second : α} (hfirst : first ∈ items) (hsecond : second ∈ items) :
    first = second := by
  cases items with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil => simp_all
      | cons next rest => simp_all

@[grind] theorem List.snd_eq_of_find_pair_of_mem_of_length_le_one
    {α β : Type} {items : List (α × β)} (hlength : items.length ≤ 1)
    {predicate : (α × β) → Bool} {foundKey currentKey : α}
    {found current : β}
    (hfind : items.find? predicate = some (foundKey, found))
    (hmem : (currentKey, current) ∈ items) :
    current = found := by
  have hfound : (foundKey, found) ∈ items :=
    List.mem_of_find?_eq_some hfind
  exact congrArg Prod.snd
    (List.eq_of_mem_of_length_le_one hlength hmem hfound)

theorem List.filter_not_of_find_of_length_le_one
    {α : Type} {items : List α} (hlength : items.length ≤ 1)
    {predicate : α → Bool} {found : α}
    (hfind : items.find? predicate = some found) :
    items.filter (fun item => !predicate item) = [] := by
  cases items with
  | nil => simp at hfind
  | cons head tail =>
      have htail : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest => simp at hlength
      subst tail
      simp at hfind ⊢
      exact hfind.1

grind_pattern List.filter_not_of_find_of_length_le_one =>
  items.length, items.find? predicate, some found

theorem List.eq_head_of_mem_cons_filter_not_of_find_of_length_le_one
    {α : Type} {items : List α} (hlength : items.length ≤ 1)
    {predicate : α → Bool} {found new current : α}
    (hfind : items.find? predicate = some found)
    (hmem : current ∈ new :: items.filter (fun item => !predicate item)) :
    current = new := by
  rw [List.filter_not_of_find_of_length_le_one hlength hfind] at hmem
  simpa using hmem

grind_pattern
    List.eq_head_of_mem_cons_filter_not_of_find_of_length_le_one =>
  items.length, items.find? predicate, some found,
  current ∈ new :: items.filter (fun item => !predicate item)

@[simp] theorem NodeSerial.filter
    {node : Concrete.Node} (hserial : NodeSerial node)
    (predicate : Concrete.OpId × Concrete.Flight → Bool) :
    (node.flights.filter predicate).length ≤ 1 :=
  Nat.le_trans (List.length_filter_le predicate node.flights) hserial

@[grind] theorem NodeSerial.eq_of_mem
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

@[simp] theorem takeFlight_filter_empty_of_find_some
    {node : Concrete.Node} {op : Concrete.OpId}
    (hserial : NodeSerial node)
    (hfind : (node.flights.find? (·.1 == op)).isSome = true) :
    node.flights.filter (·.1 != op) = [] := by
  cases heq : node.flights.find? (·.1 == op) with
  | none => simp [heq] at hfind
  | some pair =>
      obtain ⟨found, flight⟩ := pair
      apply takeFlight_filter_empty_of_some hserial
      rw [heq]
      rfl

@[simp] theorem takeFlight_filter_empty_of_find_eq_some
    {node : Concrete.Node} {op foundOp : Concrete.OpId}
    {flight : Concrete.Flight}
    (hserial : NodeSerial node)
    (hfind : node.flights.find? (·.1 == op) = some (foundOp, flight)) :
    node.flights.filter (·.1 != op) = [] := by
  apply takeFlight_filter_empty_of_find_some hserial
  simp [hfind]

@[simp] theorem NodeSerial.filter_empty_of_find_exists
    {node : Concrete.Node} (hserial : NodeSerial node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hfind :
      ∃ foundOp, node.flights.find? (·.1 == op) = some (foundOp, flight)) :
    node.flights.filter (·.1 != op) = [] := by
  obtain ⟨foundOp, hfind⟩ := hfind
  exact takeFlight_filter_empty_of_find_eq_some hserial hfind

@[simp] theorem takeFlight_filter_empty_of_mapped_find_some
    {node : Concrete.Node} {op : Concrete.OpId}
    (hserial : NodeSerial node)
    (hfind :
      ((node.flights.find? (·.1 == op)).map (·.2)).isSome = true) :
    node.flights.filter (·.1 != op) = [] := by
  apply takeFlight_filter_empty_of_find_some hserial
  cases heq : node.flights.find? (·.1 == op) <;>
    simp_all

@[simp] theorem takeFlight_cons_filter_serial
    {node : Concrete.Node} {op : Concrete.OpId}
    (entry : Concrete.OpId × Concrete.Flight)
    (hserial : NodeSerial node)
    (hfind :
      ((node.flights.find? (·.1 == op)).map (·.2)).isSome = true) :
    (entry :: node.flights.filter (·.1 != op)).length ≤ 1 := by
  rw [takeFlight_filter_empty_of_mapped_find_some hserial hfind]
  simp

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
          simp only [Concrete.decide, hselect]
          split
          all_goals
            refine ⟨_, rfl, ?_⟩
            simp [Concrete.writeCandidate, NodeSerial, Concrete.Node.await,
              hempty]

set_option maxHeartbeats 800000 in
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
      repeat' first | split at hresult
      all_goals
        simp_all [NodeSerial, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeSerial, Concrete.Node.await,
          Concrete.Node.awaitControl]
      all_goals
        try
          obtain ⟨found, hfind⟩ := heq_3
          have hempty := takeFlight_filter_empty_of_find_some hserial (by
            simp [hfind])
          simp_all
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [NodeSerial, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeSerial, Concrete.Node.await,
          Concrete.Node.awaitControl]
      all_goals
        try
          obtain ⟨found, hfind⟩ := heq_3
          have hempty := takeFlight_filter_empty_of_find_some hserial (by
            simp [hfind])
          simp_all
      all_goals first | contradiction | grind

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

def NodeFlightsAddressed (address : Addr) (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights → flight.address = address

set_option maxHeartbeats 800000 in
theorem node_step_flights_addressed
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    (haddressed : NodeFlightsAddressed address node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val) :
    ∃ next,
      result.state = .node next ∧ NodeFlightsAddressed address next := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeFlightsAddressed, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeFlightsAddressed, Concrete.Node.await,
          Concrete.Node.awaitControl]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [NodeFlightsAddressed, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeFlightsAddressed, Concrete.Node.await,
          Concrete.Node.awaitControl]
      all_goals first | contradiction | grind

def FlightsAddressed
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧
        NodeFlightsAddressed address node

theorem flightsAddressed_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    FlightsAddressed (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address hmem
  exact ⟨{}, hinit.2.2 address hmem, by simp [NodeFlightsAddressed]⟩

theorem flightsAddressed_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hinvariant : FlightsAddressed world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    FlightsAddressed next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address hmem
      obtain ⟨node, hnode, haddressed⟩ := hinvariant address hmem
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨after, hstate, hafter⟩ :=
          node_step_flights_addressed haddressed (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], haddressed⟩

theorem reachable_flights_addressed
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    FlightsAddressed (nodes := nodes) (appConfig := appConfig) world := by
  induction hreachable with
  | init hinit => exact flightsAddressed_initial hinit
  | step _ hstep ih => exact flightsAddressed_step ih hstep

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
    address = flight.address := by
  obtain ⟨actual, hactual, haddressed⟩ :=
    reachable_flights_addressed hreachable address haddress
  rw [hnode] at hactual
  cases Concrete.Local.node.inj hactual
  exact (haddressed op flight hflight).symm

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

def NodeSweepsValid (bound : Time) (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights →
    ∀ timer instant rest,
      flight.transaction = .sweep timer instant rest →
      instant ≤ bound

set_option maxHeartbeats 800000 in
theorem node_step_sweeps_valid
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    {before now : Time} (htime : before ≤ now)
    (hsweeps : NodeSweepsValid before node)
    {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    NodeSweepsValid now next := by
  intro op flight hflight timer instant rest htransaction
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeSweepsValid, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cacheRead, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [NodeSweepsValid, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals
        try
          subst next
          simp only [finishNode_flights, noteArmed_flights] at hflight
          exact Nat.le_trans
            (hsweeps _ _ (List.mem_filter.mp hflight).1 timer instant rest
              htransaction)
            htime
      all_goals first | contradiction | grind

def NodesSweepsValid
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧
      NodeSweepsValid world.now node

theorem nodesSweepsValid_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesSweepsValid (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by
    simp [NodeSweepsValid]⟩

theorem nodesSweepsValid_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hvalidNodes :
      ∀ address, address ∈ nodes → ∀ node,
        world.process (.node address) = .node node →
        NodeValid appConfig node)
    (hinvariant : NodesSweepsValid world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesSweepsValid next := by
  cases hstep with
  | inject htime _ _ =>
      intro address haddress
      obtain ⟨node, hnode, hsweeps⟩ := hinvariant address haddress
      refine ⟨node, by simpa [World.inject] using hnode, ?_⟩
      intro op flight hflight timer instant rest htransaction
      exact Nat.le_trans
        (hsweeps op flight hflight timer instant rest htransaction) htime
  | outside htime _ =>
      intro address haddress
      obtain ⟨node, hnode, hsweeps⟩ := hinvariant address haddress
      refine ⟨node, by simpa [World.observeOutside] using hnode, ?_⟩
      intro op flight hflight timer instant rest htransaction
      exact Nat.le_trans
        (hsweeps op flight hflight timer instant rest htransaction) htime
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address haddress
      obtain ⟨node, hnode, hsweeps⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        have hnodeValid := hvalidNodes address haddress node hnode
        obtain ⟨after, hstate, _⟩ :=
          node_step_valid hnodeValid (hnode ▸ hresult)
        have hafter :=
          node_step_sweeps_valid htime hsweeps (hnode ▸ hresult) hstate
        exact ⟨after, by simp [World.land, hstate], hafter⟩
      · refine ⟨node, by simp [World.land, Ne.symm hp, hnode], ?_⟩
        intro op flight hflight timer instant rest htransaction
        exact Nat.le_trans
          (hsweeps op flight hflight timer instant rest htransaction) htime

theorem reachable_nodes_sweeps_valid
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesSweepsValid world := by
  induction hreachable with
  | init hinit => exact nodesSweepsValid_initial hinit
  | step hreachable hstep ih =>
      exact nodesSweepsValid_step (fun address haddress node hnode =>
        by
          obtain ⟨actual, hactual, hvalid⟩ :=
            reachable_nodes_valid hreachable address haddress
          rw [hnode] at hactual
          cases Concrete.Local.node.inj hactual
          exact hvalid) ih hstep

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
          simp only [Concrete.decide, hselect]
          split
          all_goals
            refine ⟨_, rfl, ?_⟩
            intro op flight hmem hphase
            simp [Concrete.writeCandidate, Concrete.Node.await] at hmem
            rcases hmem with hnew | hold
            · obtain ⟨rfl, rfl⟩ := hnew
              simp at hphase
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
      cases hfired : current.fired with
      | none =>
          refine ⟨node, by simp [Concrete.decide, hselect, hfired], ?_⟩
          exact hinvariant.mono fun message hmessage =>
            List.mem_append_left _ hmessage
      | some timer =>
          refine ⟨cleanupNext node current timer,
            decide_state_cleanup appConfig node current loaded timer
              hselect hfired, ?_⟩
          intro op flight hmem hphase
          exact List.mem_append_left _
            (hinvariant (by simpa using hmem) hphase)
  | some candidate =>
      simp only [Concrete.decide, hselect]
      split
      all_goals
        refine ⟨_, rfl, ?_⟩
        intro op flight hmem hphase
        simp [Concrete.writeCandidate, Concrete.Node.await] at hmem
        rcases hmem with hnew | hold
        · obtain ⟨rfl, rfl⟩ := hnew
          simp at hphase
        · exact List.mem_append_left _
            (hinvariant hold hphase)



set_option maxHeartbeats 800000 in
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
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight,
          World.land, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeLoadingGets, Concrete.Node.await,
          Concrete.Node.awaitControl, World.land]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs,
          World.land, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeLoadingGets, Concrete.Node.await,
          Concrete.Node.awaitControl, World.land]
      all_goals first | contradiction | grind

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
          simp only [Concrete.decide, hselect]
          split
          · refine ⟨_, rfl, ?_⟩
            intro op flight hmem hphase
            simp [Concrete.writeCandidate, Concrete.Node.await] at hmem
            rcases hmem with hnew | hold
            · obtain ⟨rfl, rfl⟩ := hnew
              refine ⟨candidate.document, rfl, ?_⟩
              simp [World.land, Concrete.writeCandidate,
                Concrete.Node.await]
            · obtain ⟨document, hdocument, hput⟩ :=
                hinvariant hold hphase
              exact ⟨document, hdocument,
                List.mem_append_left _ hput⟩
          · refine ⟨_, rfl, ?_⟩
            intro op flight hmem hphase
            simp [Concrete.Node.await] at hmem
            rcases hmem with hnew | hold
            · obtain ⟨rfl, rfl⟩ := hnew
              simp at hphase
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
      cases hfired : current.fired with
      | none =>
          refine ⟨node, by simp [Concrete.decide, hselect, hfired], ?_⟩
          exact hinvariant.mono fun message hmessage =>
            List.mem_append_left _ hmessage
      | some timer =>
          refine ⟨cleanupNext node current timer,
            decide_state_cleanup appConfig node current loaded timer
              hselect hfired, ?_⟩
          intro op flight hmem hphase
          obtain ⟨document, hdocument, hput⟩ :=
            hinvariant (by simpa using hmem) hphase
          exact ⟨document, hdocument, List.mem_append_left _ hput⟩
  | some candidate =>
      simp only [Concrete.decide, hselect]
      split
      · refine ⟨_, rfl, ?_⟩
        intro op flight hmem hphase
        simp [Concrete.writeCandidate, Concrete.Node.await] at hmem
        rcases hmem with hnew | hold
        · obtain ⟨rfl, rfl⟩ := hnew
          refine ⟨candidate.document, rfl, ?_⟩
          simp [World.land, Concrete.writeCandidate,
            Concrete.Node.await]
        · obtain ⟨document, hdocument, hput⟩ :=
            hinvariant hold hphase
          exact ⟨document, hdocument, List.mem_append_left _ hput⟩
      · refine ⟨_, rfl, ?_⟩
        intro op flight hmem hphase
        simp [Concrete.Node.await] at hmem
        rcases hmem with hnew | hold
        · obtain ⟨rfl, rfl⟩ := hnew
          simp at hphase
        · obtain ⟨document, hdocument, hput⟩ :=
            hinvariant hold hphase
          exact ⟨document, hdocument, List.mem_append_left _ hput⟩



set_option maxHeartbeats 800000 in
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
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight,
          World.land, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeWritingPuts, Concrete.Node.await,
          Concrete.Node.awaitControl, World.land]
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs,
          World.land, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeWritingPuts, Concrete.Node.await,
          Concrete.Node.awaitControl, World.land]
      all_goals first | contradiction | grind

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
      simp only [Concrete.decide, hselect] at hmessage
      split at hmessage <;>
        simp [Concrete.Node.await] at hmessage
  | some candidate =>
      simp only [Concrete.decide, hselect] at hmessage
      split at hmessage
      · simp [Concrete.writeCandidate, Concrete.Node.await] at hmessage
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
      · simp [Concrete.Node.await] at hmessage

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
      simp only [Concrete.decide, hselect] at hmessage
      split at hmessage <;>
        simp [Concrete.Node.await] at hmessage
  | some candidate =>
      simp only [Concrete.decide, hselect] at hmessage
      split at hmessage
      · simp [Concrete.writeCandidate, Concrete.Node.await] at hmessage
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
      · simp [Concrete.Node.await] at hmessage

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
          Concrete.timerForDocument flight.key candidate.document
            flight.transaction.logicalTime node.nextTimerToken
              flight.address = none ∧
          hkey ▸ provenance.loaded = loaded ∧
          provenance.outputs = candidate.outputs ∧
          provenance.continuations = candidate.continuations := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      simp only [Concrete.decide, hselect] at hmessage
      split at hmessage <;>
        simp [Concrete.Node.await] at hmessage
  | some candidate =>
      simp only [Concrete.decide, hselect] at hmessage
      cases htimer :
          Concrete.timerForDocument flight.key candidate.document
            flight.transaction.logicalTime node.nextTimerToken
              flight.address with
      | none =>
        simp [htimer, Concrete.writeCandidate,
          Concrete.Node.await] at hmessage
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
        }, rfl, rfl, candidate, rfl, htimer, rfl, rfl, rfl⟩
      | some timer =>
        simp [htimer, Concrete.Node.await] at hmessage

theorem start_put_valid {appConfig : Resonate.Config}
    {node : Concrete.Node} {transaction : Concrete.Transaction}
    {transactionKey : DocumentKey}
    {startAddress : Addr} {fired : Option Concrete.TimerKey}
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
      address := startAddress
      fired
    })
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey
          startAddress fired).send) :
    ValidPut appConfig key document expectedVersion := by
  simp only [Concrete.start] at hmessage
  cases hcache : node.cacheRead transactionKey with
  | none =>
      simp [hcache, Concrete.Node.await] at hmessage
  | some value =>
      simp only [hcache] at hmessage
      exact decide_put_valid hflight hmessage

@[simp] theorem put_not_mem_retry_send
    (config : Concrete.Config) (node : Concrete.Node)
    (flight : Concrete.Flight) (recipient : Concrete.Pid)
    (op : Concrete.OpId) (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) :
    (recipient, Concrete.Msg.storeRequest {
      op
      payload := .put key document expectedVersion
    }) ∉ (Concrete.retry config node flight).send := by
  simp only [Concrete.retry]
  split <;>
    simp [Concrete.Node.await, Concrete.sendOutputs]

@[simp] theorem put_not_mem_refreshEnded_send
    (node : Concrete.Node) (config : Concrete.Config) (now : Time)
    (recipient : Concrete.Pid) (op : Concrete.OpId)
    (key : DocumentKey) (document : Document key)
    (expectedVersion : Option Concrete.Version) :
    (recipient, Concrete.Msg.storeRequest {
      op
      payload := .put key document expectedVersion
    }) ∉ (Concrete.refreshEnded node config now).send := by
  simp [Concrete.refreshEnded, Concrete.beginTimerList,
    Concrete.Node.awaitControl]

set_option maxHeartbeats 800000 in
theorem conflict_step_sends_no_put
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node} {now : Time}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {replyOp op : Concrete.OpId} {recipient : Concrete.Pid}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .store
            (.storeReply { op := replyOp, payload := .conflict }))).val)
    (hsend :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    False := by
  simp only [Concrete.step] at hresult
  repeat' split at hresult
  all_goals
    simp_all [Concrete.Node.takeFlight, Concrete.Node.cacheInvalidate,
      Concrete.Node.await, Concrete.Node.takeControl,
      Concrete.refreshEnded, Concrete.beginTimerList,
      Concrete.Node.awaitControl, Concrete.sendOutputs,
      Outcomes.one]

theorem written_step_sends_no_put
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node} {now : Time}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {replyOp op : Concrete.OpId} {recipient : Concrete.Pid}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .store
            (.storeReply { op := replyOp, payload := .written }))).val)
    (hsend :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    False := by
  simp only [Concrete.step] at hresult
  cases ht : node.takeFlight replyOp with
  | mk taken remaining =>
      cases taken with
      | none =>
          simp [ht, Outcomes.one] at hresult
          subst result
          contradiction
      | some flight =>
          cases hp : flight.phase with
          | writing =>
              simp [ht, hp, Outcomes.one] at hresult
              subst result
              exact committedFlight_sends_no_put hsend
          | loading | arming | deleting =>
              simp [ht, hp, Outcomes.one] at hresult
              subst result
              contradiction

theorem failed_step_sends_no_put
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node} {now : Time}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {replyOp op : Concrete.OpId} {recipient : Concrete.Pid}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .store
            (.storeReply { op := replyOp, payload := .failed }))).val)
    (hsend :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈ result.send) :
    False := by
  simp only [Concrete.step] at hresult
  cases ht : node.takeFlight replyOp with
  | mk taken remaining =>
      cases taken with
      | some flight =>
          cases hp : flight.phase with
          | deleting =>
              simp [ht, hp, Outcomes.one] at hresult
              subst result
              exact continueCleanup_sends_no_put hsend
          | loading | arming | writing =>
              simp [ht, hp, Concrete.sendOutputs, Outcomes.one] at hresult
              subst result
              simp [Concrete.sendOutputs] at hsend
      | none =>
          cases hc : node.takeControl replyOp with
          | mk control next =>
              cases control with
              | none =>
                  simp [ht, hc, Outcomes.one] at hresult
                  subst result
                  contradiction
              | some control =>
                  cases control with
                  | cleanup outputs =>
                      simp [ht, hc, Outcomes.one] at hresult
                      subst result
                      simp [Concrete.sendOutputs] at hsend
                  | announced _ | announcements _ | membership _ _
                    | membershipWrite _ | timerList _ _ _ =>
                      simp [ht, hc, Concrete.refreshEnded,
                        Concrete.beginTimerList, Concrete.Node.awaitControl,
                        Outcomes.one] at hresult
                      subst result
                      contradiction

set_option maxHeartbeats 800000 in
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
        | cons item rest =>
          simp [hp, Outcomes.one] at hresult
          subst result
          cases item with
          | occurrence request firing =>
              apply start_put_valid
                (transaction :=
                  .work (.occurrence request firing) firing rest)
                (transactionKey := .origin request.id.origin)
              · exact ⟨rfl, trivial, ⟨request, rfl⟩⟩
              · exact hsend
        | nil =>
            simp only [hp] at hresult
            split at hresult
            · simp [Concrete.beginMembershipRefresh,
                Concrete.Node.awaitControl, Outcomes.one] at hresult
              subst result
              contradiction
            · cases hbegin :
                (node.wheel.takeDue now config.fireConcurrency).beginOne with
              | some pair =>
                  obtain ⟨timer, wheel⟩ := pair
                  simp only [hbegin, Option.some.injEq, Prod.mk.injEq]
                    at hresult
                  subst_vars
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    subst result
                    apply start_put_valid
                      (transaction := .sweep timer now [])
                      (transactionKey := timer.target.key)
                    · exact ⟨rfl, trivial, trivial⟩
                    · exact hsend
                  · simp [Concrete.sendOutputs, Outcomes.one] at hresult
                    subst result
                    contradiction
              | none =>
                  simp only [hbegin] at hresult
                  split at hresult
                  · simp [Concrete.beginTimerList,
                      Concrete.Node.awaitControl, Outcomes.one] at hresult
                    subst result
                    contradiction
                  · split at hresult
                    · simp [Concrete.beginTimerList,
                        Concrete.Node.awaitControl, Outcomes.one] at hresult
                      subst result
                      contradiction
                    · simp [Outcomes.one] at hresult
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                apply start_put_valid
                  (transaction := .external call)
                  (transactionKey := requestKey)
                · exact ⟨hk, trivial, trivial⟩
                · exact hsend
              · simp [Concrete.sendOutputs, Outcomes.one] at hresult
                subst result
                simp [Concrete.sendOutputs] at hsend
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload
        case got loadedKey loaded =>
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
                  | arming | writing | deleting =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        case written =>
            exact (written_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        case conflict =>
            exact (conflict_step_sends_no_put
              (appConfig := appConfig) (address := address) (now := now)
              hresult hsend).elim
        case failed =>
            exact (failed_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        case done =>
            simp [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨taken, remaining⟩ := taken
            cases taken with
            | some flight =>
                have hvalid :=
                  hnode replyOp flight (takeFlight_some_mem ht)
                cases hp : flight.phase with
                | arming =>
                    cases hd : flight.document with
                    | none =>
                        simp [ht, hp, hd, Outcomes.one] at hresult
                        subst result
                        contradiction
                    | some selectedDocument =>
                        simp [ht, hp, hd, Concrete.Node.await,
                          Outcomes.one] at hresult
                        subst result
                        simp [Concrete.Node.await] at hsend
                        obtain ⟨rfl, _, hkey, hdocument, hexpected⟩ := hsend
                        subst key
                        have : document = selectedDocument :=
                          eq_of_heq hdocument
                        subst document
                        subst expectedVersion
                        exact hvalid.putValid (.inl hp) hd
                | deleting =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    exact (continueCleanup_sends_no_put hsend).elim
                | loading | writing =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    contradiction
            | none =>
                simp only [ht] at hresult
                repeat' split at hresult
                all_goals
                  simp_all [Concrete.Node.takeControl,
                    Concrete.Node.awaitControl, Concrete.refreshEnded,
                    Concrete.beginTimerList, Outcomes.one]
        case timers _ =>
            simp [Concrete.step] at hresult
            repeat' split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]
        case announcements _ =>
            simp [Concrete.step] at hresult
            repeat' split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]
        case membership _ _ =>
            simp [Concrete.step] at hresult
            repeat' split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]

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
                    (first
                    | (simp [Outcomes.one] at hresult
                       subst result
                       contradiction)
                    | skip)
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
                | armTimer _ | deleteTimer _ | deleteTimers _ | listTimers _
                | announce _
                | listAnnouncements | getMembership | putMembership _ _ =>
                    simp only [Concrete.step, hlocal] at hresult
                    repeat' split at hresult
                    all_goals simp [Outcomes.one] at hresult
                    all_goals subst result
                    all_goals contradiction

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
        (∃ key document, nextStore = store.commit key document) ∨
        (nextStore.keys = store.keys ∧
          nextStore.values = store.values)) := by
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
                      .inr (.inl ⟨key, document, rfl⟩)⟩
                  · subst result
                    exact ⟨store.commit key document, rfl,
                      .inr (.inl ⟨key, document, rfl⟩)⟩
                  · subst result
                    exact ⟨store.fence key, rfl,
                      .inr (.inl
                        ⟨key, store.toAbstract.read key, rfl⟩)⟩
                · simp [Outcomes.one] at hresult
                  subst result
                  exact ⟨store.commit key document, rfl,
                    .inr (.inl ⟨key, document, rfl⟩)⟩
          | armTimer timer =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨_, rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
          | deleteTimer timer =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨_, rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
          | deleteTimers timers =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨_, rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
          | listTimers through =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨store, rfl, .inl rfl⟩
          | announce announcement =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨_, rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
          | listAnnouncements | getMembership =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact ⟨store, rfl, .inl rfl⟩
          | putMembership expected next =>
              simp only [Concrete.step] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, .inr (.inr ⟨rfl, rfl⟩)⟩
              · simp [Outcomes.one] at hresult
                subst result
                exact ⟨store, rfl, .inl rfl⟩

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
          simp [Concrete.decide, hselect, Concrete.Node.await] at hsend
      | some candidate =>
          simp only [Concrete.decide, hselect] at hsend
          split at hsend <;>
            simp [Concrete.writeCandidate, Concrete.Node.await] at hsend



set_option maxHeartbeats 800000 in
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
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hsend
      all_goals simp_all [Concrete.Node.await, Concrete.Node.awaitControl,
        Concrete.sendOutputs]
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs,
          Outcomes.one]
      all_goals repeat' first | split at hsend
      all_goals simp_all [Concrete.Node.await, Concrete.Node.awaitControl,
        Concrete.sendOutputs]

set_option maxHeartbeats 800000 in
theorem node_step_no_request
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult : result ∈
      (Concrete.step appConfig config (.node address) (.node node)
        now event).val)
    {recipient : Concrete.Pid} {call : Call}
    (hsend : (recipient, .request call) ∈ result.send) : False := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hsend
      all_goals simp_all [Concrete.Node.await, Concrete.Node.awaitControl,
        Concrete.sendOutputs]
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup,
          Concrete.finishFlight,
          Concrete.Node.cachePut, Concrete.Node.cacheInvalidate,
          Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hsend
      all_goals simp_all [Concrete.Node.await, Concrete.Node.awaitControl,
        Concrete.sendOutputs]

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
                  | armTimer _ | deleteTimer _ | deleteTimers _ | listTimers _
                  | announce _
                  | listAnnouncements | getMembership | putMembership _ _ =>
                      simp only [Concrete.step] at hresult
                      repeat' split at hresult
                      all_goals simp [Outcomes.one] at hresult
                      all_goals subst result
                      all_goals contradiction

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
              nextStore = store.commit writtenKey written ∨
            (nextStore.keys = store.keys ∧
              nextStore.values = store.values) := by
        by_cases hp : pid = Concrete.Pid.store
        · subst pid
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          rcases heffect with rfl | heffect
          · exact .inl rfl
          · rcases heffect with hcommit | hsame
            · obtain ⟨writtenKey, written, rfl⟩ := hcommit
              exact .inr ⟨writtenKey, written, .inl rfl⟩
            · exact .inr ⟨.origin "", emptyDocument (.origin ""),
                .inr hsame⟩
        · have heq : store = nextStore := by
            have hx : world.process .store = .store nextStore := by
              simpa [World.land, Ne.symm hp] using hnextStore
            rw [hstore] at hx
            exact Concrete.Local.store.inj hx
          exact .inl heq.symm
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · have hsnapshot := hinvariant hstore hold
        rcases heffect with rfl | heffect
        · exact hsnapshot
        · obtain ⟨writtenKey, written, heffect⟩ := heffect
          rcases heffect with rfl | hsame
          · exact Snapshot.commit hsnapshot
          · simpa [Snapshot, Concrete.Store.read, Concrete.Store.version,
              hsame.2] using hsnapshot
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
  | .work item instant _ =>
      ∃ request, item = .occurrence request instant
  | .sweep _ instant _ => instant ≤ world.now

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

theorem NodeCacheSnapshots.continueCleanup
    {store : Concrete.Store} {node : Concrete.Node}
    (hcache : NodeCacheSnapshots store node)
    (flight : Concrete.Flight) :
    ∃ next,
      (Concrete.continueCleanup node flight).state = .node next ∧
      NodeCacheSnapshots store next := by
  let finished := Concrete.finishNode node flight
  have hfinished : NodeCacheSnapshots store finished := by
    intro key value hread
    exact hcache key value (by
      simpa [finished, Concrete.finishNode, Concrete.Node.cacheRead] using hread)
  cases hcleanup : flight.cleanup with
  | nil =>
      exact ⟨finished, by simp [Concrete.continueCleanup, hcleanup, finished],
        hfinished⟩
  | cons key rest =>
      let next :=
        (finished.awaitControl (.cleanup flight.selected)
          (.deleteTimers (key :: rest))).1
      refine ⟨next, by simp [Concrete.continueCleanup, hcleanup, finished,
        next], ?_⟩
      intro query value hread
      exact hfinished query value (by
        simpa [next, Concrete.Node.awaitControl,
          Concrete.Node.cacheRead] using hread)

theorem NodeCacheSnapshots.committedFlight
    {store : Concrete.Store} {node : Concrete.Node}
    (hcache : NodeCacheSnapshots store node)
    (flight : Concrete.Flight) :
    ∃ next,
      (Concrete.committedFlight node flight).state = .node next ∧
      NodeCacheSnapshots store next := by
  apply NodeCacheSnapshots.continueCleanup
  intro key value hread
  apply hcache key value
  have hcacheEq :
      (node.noteArmed flight).cache = node.cache := by
    unfold Concrete.Node.noteArmed
    cases flight.armed <;> rfl
  change
    (node.noteArmed flight).cache.findSome? (·.read key) = some value
      at hread
  rw [hcacheEq] at hread
  exact hread

theorem NodeCacheSnapshots.retry
    {store : Concrete.Store} {node : Concrete.Node}
    (hcache : NodeCacheSnapshots store node)
    (config : Concrete.Config) (flight : Concrete.Flight) :
    ∃ next,
      (Concrete.retry config node flight).state = .node next ∧
      NodeCacheSnapshots store next := by
  unfold Concrete.retry
  split
  · let loading : Concrete.Flight := {
      flight with
      loaded := none
      document := none
      selected := []
      armed := none
      attempt := flight.attempt + 1
      phase := .loading
    }
    let next := (node.await loading (.get flight.key)).1
    refine ⟨next, by simp [loading, next], ?_⟩
    intro key value hread
    exact hcache key value hread
  · exact ⟨node, rfl, hcache⟩

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
      cases hfired : current.fired with
      | none =>
          exact ⟨node, by simp [Concrete.decide, hselect, hfired], hcache⟩
      | some timer =>
          refine ⟨cleanupNext node current timer,
            decide_state_cleanup appConfig node current loaded timer
              hselect hfired, ?_⟩
          intro key value hread
          exact hcache key value (by simpa [Concrete.Node.cacheRead] using hread)
  | some candidate =>
      simp only [Concrete.decide, hselect]
      split
      all_goals
        refine ⟨_, rfl, ?_⟩
        intro key value hread
        change node.cacheRead key = some value at hread
        exact hcache key value hread

theorem start_cache_snapshots
    (appConfig : Resonate.Config) {store : Concrete.Store}
    (node : Concrete.Node) (hcache : NodeCacheSnapshots store node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    (address : Addr := "") (fired : Option Concrete.TimerKey := none) :
    ∃ next,
      (Concrete.start appConfig node transaction key address fired).state =
        .node next ∧
      NodeCacheSnapshots store next := by
  simp only [Concrete.start]
  cases hread : node.cacheRead key with
  | none =>
      refine ⟨(node.await { key, transaction, address, fired } (.get key)).1,
        by simp [hread], ?_⟩
      intro other value hcached
      change node.cacheRead other = some value at hcached
      exact hcache other value hcached
  | some value =>
      simp only [hread]
      exact decide_cache_snapshots appConfig node hcache
        { key, transaction, address, fired }
        (some (value.document, value.version))

def CacheSnapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes → ∀ {store node},
    world.process .store = .store store →
    world.process (.node address) = .node node →
    NodeCacheSnapshots store node

set_option maxHeartbeats 800000 in
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
      repeat' first | split at hresult
      all_goals
        simp_all [NodeCacheSnapshots, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.continueCleanup, Concrete.finishNode,
          Concrete.cleanupFlight, Concrete.Node.cacheRead, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeCacheSnapshots, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.continueCleanup,
          Concrete.finishNode, Concrete.Node.cacheRead]
      all_goals first | contradiction | grind
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact start_cache_snapshots appConfig node hcache
                  (.external call) key address
              · simp [Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hcache⟩
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
                    | arming | writing | deleting =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        exact ⟨_, rfl, hremaining⟩
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, hremaining⟩
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
                      exact ⟨_, rfl, hremaining⟩
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact hremaining.committedFlight flight
                  | arming | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl, hremaining⟩
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  have hcontrol :
                      NodeCacheSnapshots store
                        (node.takeControl replyOp).2 := by
                    intro key value hread
                    apply hcache key value
                    simpa [Concrete.Node.takeControl,
                      Concrete.Node.cacheRead] using hread
                  simp only [ht] at hresult
                  split at hresult
                  · simp [Concrete.refreshEnded,
                      Concrete.beginTimerList, Concrete.Node.awaitControl,
                      Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, hcontrol⟩
                  · simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, hcontrol⟩
              | some flight =>
                  have hremaining : NodeCacheSnapshots store remaining :=
                    hcache.takeFlight replyOp (by simpa [ht])
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨{
                    remaining with
                    flights := (replyOp, flight) :: remaining.flights
                  }, rfl, by
                    intro key value hread
                    exact hremaining key value (by
                      simpa [Concrete.Node.cacheRead] using hread)⟩
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  have hcontrol :
                      NodeCacheSnapshots store
                        (node.takeControl replyOp).2 := by
                    intro key value hread
                    apply hcache key value
                    simpa [Concrete.Node.takeControl,
                      Concrete.Node.cacheRead] using hread
                  simp only [ht] at hresult
                  repeat' split at hresult
                  all_goals simp [Outcomes.one] at hresult
                  all_goals
                    subst result
                    exact ⟨_, rfl, hcontrol⟩
              | some flight =>
                  have hremaining : NodeCacheSnapshots store remaining :=
                    hcache.takeFlight replyOp (by simpa [ht])
                  cases hp : flight.phase with
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact hremaining.continueCleanup flight
                  | loading | arming | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact ⟨_, rfl,
                        hremaining.cacheInvalidate flight.key⟩
        | done | timers _ | announcements _ | membership _ _ =>
            all_goals simp only [Concrete.step] at hresult
            all_goals repeat' split at hresult
            all_goals
              simp_all [NodeCacheSnapshots, Concrete.Node.takeFlight,
                Concrete.Node.takeControl, Concrete.Node.await,
                Concrete.Node.awaitControl, Concrete.continueCleanup,
                Concrete.finishFlight,
                Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.Node.cacheRead,
                Outcomes.one]
            all_goals repeat' first | split at hresult
            all_goals
              simp_all [NodeCacheSnapshots, Concrete.Node.await,
                Concrete.Node.awaitControl, Concrete.Node.cacheRead,
                Concrete.finishFlight, Outcomes.one]
            all_goals
              intro key value hread
              apply hcache key value
              split at hread <;> exact hread

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
        rcases heffect with hsame |
          ⟨key, document, hcommit⟩ | ⟨hkeys, hvalues⟩
        · subst store
          exact hcache
        · subst store
          intro key value hread
          exact Snapshot.commit (hcache key value hread)
        · intro key value hread
          exact Snapshot.sameDocuments hvalues
            (hcache key value hread)
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

def NodeArmingSnapshots (store : Concrete.Store)
    (node : Concrete.Node) : Prop :=
  ∀ {op flight},
    (op, flight) ∈ node.flights →
    flight.phase = .arming →
    Snapshot store flight.key flight.loaded

def ArmingSnapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes → ∀ {store node},
    world.process .store = .store store →
    world.process (.node address) = .node node →
    NodeArmingSnapshots store node

theorem NodeArmingSnapshots.takeFlight
    {store : Concrete.Store} {node remaining : Concrete.Node}
    (h : NodeArmingSnapshots store node) (op : Concrete.OpId)
    (htake : (node.takeFlight op).2 = remaining) :
    NodeArmingSnapshots store remaining := by
  intro current flight hmem hphase
  have hmem' :
      (current, flight) ∈ (node.takeFlight op).2.flights := by
    simpa [htake] using hmem
  exact h (op := current) (flight := flight)
    (by simpa [Concrete.Node.takeFlight] using
      (List.mem_filter.mp hmem').1)
    hphase

theorem NodeArmingSnapshots.await
    {store : Concrete.Store} {node : Concrete.Node}
    (h : NodeArmingSnapshots store node)
    (flight : Concrete.Flight)
    (hsnapshot :
      flight.phase = .arming →
        Snapshot store flight.key flight.loaded)
    (payload : Concrete.StoreRequest) :
    NodeArmingSnapshots store (node.await flight payload).1 := by
  intro op current hmem hphase
  simp only [Concrete.Node.await, List.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · cases hmem
    exact hsnapshot hphase
  · exact h hmem hphase

theorem NodeArmingSnapshots.consFlight
    {store : Concrete.Store} {node : Concrete.Node}
    (h : NodeArmingSnapshots store node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight :
      flight.phase = .arming →
        Snapshot store flight.key flight.loaded) :
    NodeArmingSnapshots store
      { node with flights := (op, flight) :: node.flights } := by
  intro current currentFlight hmem hphase
  simp only [List.mem_cons, Prod.mk.injEq] at hmem
  rcases hmem with hnew | hold
  · rcases hnew with ⟨rfl, rfl⟩
    exact hflight hphase
  · exact h hold hphase

theorem decide_arming_snapshots
    (appConfig : Resonate.Config) {store : Concrete.Store}
    (node : Concrete.Node) (hnode : NodeArmingSnapshots store node)
    (flight : Concrete.Flight)
    (loaded : Option (Document flight.key × Concrete.Version))
    (hsnapshot : Snapshot store flight.key loaded) :
    ∃ next,
      (Concrete.decide appConfig node flight loaded).state = .node next ∧
      NodeArmingSnapshots store next := by
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      cases hfired : flight.fired with
      | none =>
          exact ⟨node, by simp [Concrete.decide, hselect, hfired], hnode⟩
      | some timer =>
          refine ⟨cleanupNext node flight timer,
            decide_state_cleanup appConfig node flight loaded timer
              hselect hfired, ?_⟩
          intro op current hmem hphase
          exact hnode (by simpa using hmem) hphase
  | some candidate =>
      simp only [Concrete.decide, hselect]
      split
      · simp only [Concrete.writeCandidate]
        refine ⟨_, rfl, hnode.await _ ?_ _⟩
        intro hphase
        contradiction
      · simp only [Concrete.Node.await]
        refine ⟨_, rfl, ?_⟩
        intro op current hmem hphase
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · cases hmem
          exact hsnapshot
        · exact hnode hmem hphase

theorem start_arming_snapshots
    (appConfig : Resonate.Config) {store : Concrete.Store}
    (node : Concrete.Node) (hnode : NodeArmingSnapshots store node)
    (hcache : NodeCacheSnapshots store node)
    (transaction : Concrete.Transaction) (key : DocumentKey)
    (address : Addr := "") (fired : Option Concrete.TimerKey := none) :
    ∃ next,
      (Concrete.start appConfig node transaction key address fired).state =
        .node next ∧
      NodeArmingSnapshots store next := by
  simp only [Concrete.start]
  cases hread : node.cacheRead key with
  | none =>
      refine ⟨_, rfl, hnode.await _ ?_ _⟩
      intro hphase
      contradiction
  | some value =>
      exact decide_arming_snapshots appConfig node hnode
        { key, transaction, address, fired }
        (some (value.document, value.version))
        (hcache key value hread)

set_option maxHeartbeats 800000 in
theorem node_step_arming_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (hstore : world.process .store = .store store)
    (hnode : NodeArmingSnapshots store node)
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
      result.state = .node next ∧ NodeArmingSnapshots store next := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeArmingSnapshots, NodeCacheSnapshots,
          Concrete.Node.cacheRead, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishFlight,
          Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeArmingSnapshots, Concrete.Node.await,
          Concrete.Node.awaitControl]
      all_goals first | contradiction | grind
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact start_arming_snapshots appConfig node hnode hcache
                  (.external call) key address
              · simp [Outcomes.one] at hresult
                subst result
                exact ⟨node, rfl, hnode⟩
      case store.storeReply rpc =>
        obtain ⟨replyOp, payload⟩ := rpc
        cases payload with
        | got loadedKey loaded =>
            have hsnapshot : Snapshot store loadedKey loaded :=
              hgots hstore hvalid
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  exact ⟨node, rfl, hnode⟩
              | some flight =>
                  have hremaining : NodeArmingSnapshots store remaining :=
                    hnode.takeFlight replyOp (by simpa [ht])
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    subst loadedKey
                    cases hp : flight.phase with
                    | loading =>
                        simp only [hp] at hresult
                        cases hloaded : loaded with
                        | none =>
                            simp [hloaded, Outcomes.one] at hresult
                            subst result
                            apply decide_arming_snapshots appConfig
                              (remaining.cacheInvalidate flight.key)
                              hremaining flight none
                            trivial
                        | some value =>
                            simp [hloaded, Outcomes.one] at hresult
                            subst result
                            apply decide_arming_snapshots appConfig
                              (remaining.cachePut flight.key {
                                document := value.1
                                version := value.2
                              })
                              hremaining flight (some value)
                            simpa [hloaded] using hsnapshot
                    | arming | writing | deleting =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        exact ⟨_, rfl, hremaining.consFlight
                          (fun hphase =>
                            hnode (takeFlight_some_mem ht) hphase)⟩
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    exact ⟨_, rfl, hremaining.consFlight
                      (fun hphase =>
                        hnode (takeFlight_some_mem ht) hphase)⟩
        | written | done | timers _ | announcements _ | membership _ _ |
            conflict | failed =>
            all_goals simp only [Concrete.step] at hresult
            all_goals repeat' first | split at hresult
            all_goals
              simp_all [NodeArmingSnapshots, Concrete.retry,
                Concrete.Node.takeFlight, Concrete.Node.takeControl,
                Concrete.Node.await, Concrete.Node.awaitControl,
                Concrete.committedFlight, Concrete.continueCleanup,
                Concrete.finishFlight,
                Concrete.Node.cacheInvalidate, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]
            all_goals repeat' first | split at hresult
            all_goals
              try simp_all [NodeArmingSnapshots, Concrete.Node.await,
                Concrete.finishFlight, Outcomes.one]
            all_goals first | contradiction | grind

theorem armingSnapshots_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    ArmingSnapshots (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress store node hstore hnodeState
  simp only [World.initial] at hstore hnodeState
  have hs := hinit.2.1
  rw [hs] at hstore
  cases Concrete.Local.store.inj hstore
  have hn := hinit.2.2 address haddress
  rw [hn] at hnodeState
  cases Concrete.Local.node.inj hnodeState
  simp [NodeArmingSnapshots]

theorem armingSnapshots_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hstoreExists : StoreExists world)
    (hnodes : NodesValid world)
    (hcaches : CacheSnapshots world)
    (hgots : GotSnapshots world)
    (hinvariant : ArmingSnapshots world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    ArmingSnapshots next := by
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
        have harming : NodeArmingSnapshots beforeStore node :=
          hinvariant address haddress hbeforeStore hnodeOld
        have hresult' := hresult
        rw [hbeforeStore] at hresult'
        obtain ⟨afterStore, hstate, heffect⟩ :=
          store_step_effect hresult'
        have heq : afterStore = store := by
          simpa [World.land, hstate] using hstoreNext
        subst afterStore
        rcases heffect with rfl |
          ⟨writtenKey, written, rfl⟩ | ⟨hkeys, hvalues⟩
        · exact harming
        · intro hmem hphase
          exact Snapshot.commit (harming hmem hphase)
        · intro hmem hphase
          exact Snapshot.sameDocuments hvalues (harming hmem hphase)
      · have hstoreOld :
            world.process .store = .store store := by
          simpa [World.land, Ne.symm hpStore] using hstoreNext
        by_cases hpNode : pid = .node address
        · subst pid
          obtain ⟨before, hbefore, _⟩ :=
            hnodes address haddress
          have harming : NodeArmingSnapshots store before :=
            hinvariant address haddress hstoreOld hbefore
          have hcache :=
            hcaches address haddress hstoreOld hbefore
          obtain ⟨after, hstate, hafter⟩ :=
            node_step_arming_snapshots hstoreOld harming hcache
              hgots hvalid (hbefore ▸ hresult)
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

theorem reachable_arming_snapshots
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    ArmingSnapshots world := by
  induction hreachable with
  | init hinit => exact armingSnapshots_initial hinit
  | step hreachable hstep ih =>
      exact armingSnapshots_step
        (reachable_store_exists hreachable)
        (reachable_nodes_valid hreachable)
        (reachable_cache_snapshots hreachable)
        (reachable_got_snapshots hreachable)
        ih hstep

theorem start_put_snapshot
    {appConfig : Resonate.Config} {store : Concrete.Store}
    {node : Concrete.Node} {transaction : Concrete.Transaction}
    {transactionKey : DocumentKey}
    (flightAddress : Addr := "") (fired : Option Concrete.TimerKey := none)
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
      address := flightAddress
      fired
    })
    (hcache : NodeCacheSnapshots store node)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey
          flightAddress fired).send) :
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
          Concrete.select appConfig {
            key := transactionKey, transaction, address := flightAddress, fired }
            (some (value.document, value.version)) with
      | none =>
          cases fired <;>
            simp [Concrete.decide, hselect,
              Concrete.Node.await] at hmessage
      | some candidate =>
          simp only [Concrete.decide, hselect] at hmessage
          cases htimer :
              Concrete.timerForDocument transactionKey candidate.document
                transaction.logicalTime node.nextTimerToken flightAddress with
          | none =>
              simp [htimer, Concrete.writeCandidate,
                Concrete.Node.await] at hmessage
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
          | some timer =>
              simp [htimer, Concrete.Node.await] at hmessage

theorem put_not_in_singleton_of_payload_ne
    {recipient otherRecipient : Concrete.Pid}
    {op otherOp : Concrete.OpId}
    {key : DocumentKey} {document : Document key}
    {expectedVersion : Option Concrete.Version}
    {payload : Concrete.StoreRequest}
    (hne : Concrete.StoreRequest.put key document expectedVersion ≠ payload)
    (hmem :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        [(otherRecipient, Concrete.Msg.storeRequest {
          op := otherOp
          payload
        })]) :
    False := by
  have hpair := List.mem_singleton.mp hmem
  have hmsg := congrArg Prod.snd hpair
  have hrpc := Concrete.Msg.storeRequest.inj hmsg
  exact hne (congrArg Concrete.RpcRequest.payload hrpc)

theorem node_step_sent_put_snapshot
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (hstore : world.process .store = .store store)
    (hnode : NodeValid appConfig node)
    (hcache : NodeCacheSnapshots store node)
    (harming : NodeArmingSnapshots store node)
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
            split at hresult
            · simp [Concrete.beginMembershipRefresh,
                Concrete.Node.awaitControl, Outcomes.one] at hresult
              cases hresult
              have hpair := List.mem_singleton.mp hsend
              have hmsg := congrArg Prod.snd hpair
              have hrpc := Concrete.Msg.storeRequest.inj hmsg
              have hpayload :=
                congrArg Concrete.RpcRequest.payload hrpc
              nomatch hpayload
            · cases hwheel :
                (node.wheel.takeDue now config.fireConcurrency).beginOne with
              | none =>
                  simp only [hwheel] at hresult
                  repeat' split at hresult
                  all_goals
                    simp [Concrete.beginTimerList,
                      Concrete.Node.awaitControl, Outcomes.one] at hresult
                  all_goals
                    rw [hresult] at hsend
                    simp at hsend
              | some timerAndWheel =>
                  obtain ⟨timer, wheel⟩ := timerAndWheel
                  simp only [hwheel] at hresult
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    rw [hresult] at hsend
                    apply start_put_snapshot
                      (node := {
                        node with pending := [], wheel := wheel })
                      (transaction := .sweep timer now [])
                      (transactionKey := timer.target.key)
                      (flightAddress := address)
                      (fired := some timer)
                    · exact ⟨rfl, trivial, trivial⟩
                    · intro cacheKey value hread
                      change node.cacheRead cacheKey = some value at hread
                      exact hcache cacheKey value hread
                    · exact hsend
                  · simp [Outcomes.one] at hresult
                    rw [hresult] at hsend
                    simp at hsend
        | cons item rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases item with
            | occurrence request firing =>
                apply start_put_snapshot
                  (node := {
                    node with pending := [] })
                  (transaction :=
                    .work (.occurrence request firing) firing rest)
                  (transactionKey := .origin request.id.origin)
                  (flightAddress := address)
                · exact ⟨rfl, trivial, ⟨request, rfl⟩⟩
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                rw [hresult] at hsend
                apply start_put_snapshot
                  (transaction := .external call)
                  (transactionKey := requestKey)
                  (flightAddress := address)
                · exact ⟨hk, trivial, trivial⟩
                · exact hcache
                · exact hsend
              · simp [Concrete.pureExternal, Concrete.sendOutputs,
                  Outcomes.one] at hresult
                rw [hresult] at hsend
                simp [Concrete.sendOutputs] at hsend
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
                  | arming | writing | deleting =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written =>
            exact (written_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        | conflict =>
            exact (conflict_step_sends_no_put
              (appConfig := appConfig) (address := address) (now := now)
              hresult hsend).elim
        | failed =>
            exact (failed_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        | done =>
            simp [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨taken, remaining⟩ := taken
            cases taken with
            | some flight =>
                have hvalid :=
                  hnode replyOp flight (takeFlight_some_mem ht)
                cases hp : flight.phase with
                | arming =>
                    have hsnapshot :
                        Snapshot store flight.key flight.loaded :=
                      harming (takeFlight_some_mem ht) hp
                    cases hd : flight.document with
                    | none =>
                        simp [ht, hp, hd, Outcomes.one] at hresult
                        subst result
                        contradiction
                    | some selectedDocument =>
                        simp [ht, hp, hd, Concrete.Node.await,
                          Outcomes.one] at hresult
                        subst result
                        simp [Concrete.Node.await] at hsend
                        obtain ⟨rfl, _, hkey, hdocument, hexpected⟩ := hsend
                        subst key
                        have : document = selectedDocument :=
                          eq_of_heq hdocument
                        subst document
                        subst expectedVersion
                        have hvalid' := hvalid
                        rw [FlightValid, hp] at hvalid'
                        obtain ⟨selectedDocument', hdocument',
                          hselected⟩ := hvalid'.2.1
                        rw [hd] at hdocument'
                        cases Option.some.inj hdocument'
                        exact ⟨{
                          transaction := flight.transaction
                          loaded := flight.loaded
                          outputs := flight.selected
                          continuations := flight.continuations
                          expected_eq := rfl
                          selected := hselected
                        }, hsnapshot⟩
                | deleting =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    exact (continueCleanup_sends_no_put hsend).elim
                | loading | writing =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    contradiction
            | none =>
                simp only [ht] at hresult
                repeat' split at hresult
                all_goals
                  simp_all [Concrete.Node.takeControl,
                    Concrete.Node.awaitControl, Concrete.refreshEnded,
                    Concrete.beginTimerList, Outcomes.one]
        | timers _ | announcements _ | membership _ _ =>
            all_goals simp [Concrete.step] at hresult
            all_goals repeat' split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]

theorem start_put_origin
    {nodes : List Addr} {appConfig : Resonate.Config}
    {world : World (CModel nodes appConfig)}
    {address : Addr} {node : Concrete.Node}
    {now : Time} {transaction : Concrete.Transaction}
    {transactionKey : DocumentKey}
    (flightAddress : Addr := "") (fired : Option Concrete.TimerKey := none)
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
      address := flightAddress
      fired
    })
    (horigin :
      TransactionOrigin
        (world.land (.node address) now
          (Concrete.start appConfig node transaction transactionKey
            flightAddress fired))
        address transaction)
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey
          flightAddress fired).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      TransactionOrigin
        (world.land (.node address) now
          (Concrete.start appConfig node transaction transactionKey
            flightAddress fired))
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
    (hsweeps : NodeSweepsValid world.now node)
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
            split at hresult
            · simp [Concrete.beginMembershipRefresh,
                Concrete.Node.awaitControl, Outcomes.one] at hresult
              cases hresult
              exact (put_not_in_singleton_of_payload_ne
                (by intro h; cases h) hsend).elim
            · cases hwheel :
                (node.wheel.takeDue now config.fireConcurrency).beginOne with
              | none =>
                  simp only [hwheel] at hresult
                  repeat' split at hresult
                  all_goals
                    simp [Concrete.beginTimerList,
                      Concrete.Node.awaitControl, Outcomes.one] at hresult
                  all_goals
                    rw [hresult] at hsend
                    first
                    | exact (put_not_in_singleton_of_payload_ne
                        (by intro h; cases h) hsend).elim
                    | simp at hsend
              | some timerAndWheel =>
                  obtain ⟨timer, wheel⟩ := timerAndWheel
                  simp only [hwheel] at hresult
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    subst result
                    apply start_put_origin
                      (node := {
                        node with pending := [], wheel := wheel })
                      (transaction := .sweep timer now [])
                      (transactionKey := timer.target.key)
                      (flightAddress := address)
                      (fired := some timer)
                    · exact ⟨rfl, trivial, trivial⟩
                    · simp [TransactionOrigin, World.land]
                    · exact hsend
                  · simp [Outcomes.one] at hresult
                    rw [hresult] at hsend
                    simp at hsend
        | cons entry rest =>
            simp [hp, Outcomes.one] at hresult
            subst result
            cases entry with
            | occurrence request firing =>
                apply start_put_origin
                  (node := {
                    node with pending := [] })
                  (transaction :=
                    .work (.occurrence request firing) firing rest)
                  (transactionKey := .origin request.id.origin)
                  (flightAddress := address)
                · exact ⟨rfl, trivial, ⟨request, rfl⟩⟩
                · exact ⟨request, rfl⟩
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                apply start_put_origin
                  (transaction := .external call)
                  (transactionKey := requestKey)
                  (flightAddress := address)
                · exact ⟨hk, trivial, trivial⟩
                · exact List.mem_append_left _ hvalid
                · exact hsend
              · simp [Concrete.pureExternal, Concrete.sendOutputs,
                  Outcomes.one] at hresult
                rw [hresult] at hsend
                simp [Concrete.sendOutputs] at hsend
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
                          hselect, htimer, hloaded, houtputs, hcontinuations⟩ :=
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
                      | sweep timer instant rest =>
                          exact Nat.le_trans
                            (hsweeps replyOp flight hflightMem timer instant
                              rest
                              (htransaction.symm.trans hprovenance))
                            htime
                  | arming | writing | deleting =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | written =>
            exact (written_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        | conflict =>
            exact (conflict_step_sends_no_put
              (appConfig := appConfig) (address := address) (now := now)
              hresult hsend).elim
        | failed =>
            exact (failed_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        | done =>
            simp [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨taken, remaining⟩ := taken
            cases taken with
            | some flight =>
                have hflightMem := takeFlight_some_mem ht
                have hflightValid := hnode replyOp flight hflightMem
                cases hp : flight.phase with
                | arming =>
                    cases hd : flight.document with
                    | none =>
                        simp [ht, hp, hd, Outcomes.one] at hresult
                        subst result
                        contradiction
                    | some selectedDocument =>
                        simp [ht, hp, hd, Concrete.Node.await,
                          Outcomes.one] at hresult
                        subst result
                        simp [Concrete.Node.await] at hsend
                        obtain ⟨rfl, _, hkey, hdocument, hexpected⟩ := hsend
                        subst key
                        have : document = selectedDocument :=
                          eq_of_heq hdocument
                        subst document
                        subst expectedVersion
                        have hvalid' := hflightValid
                        rw [FlightValid, hp] at hvalid'
                        obtain ⟨selectedDocument', hdocument',
                          hselected⟩ := hvalid'.2.1
                        rw [hd] at hdocument'
                        cases Option.some.inj hdocument'
                        have horigin :
                            TransactionOrigin
                              (world.land (.node address) now {
                                state := .node
                                  (remaining.await
                                    { flight with
                                      phase := .writing }
                                    (.put flight.key selectedDocument
                                      (flight.loaded.map (·.2)))).1
                                send := [
                                  (remaining.await
                                    { flight with
                                      phase := .writing }
                                    (.put flight.key selectedDocument
                                      (flight.loaded.map (·.2)))).2
                                ]
                              })
                              address flight.transaction := by
                          cases htransaction : flight.transaction with
                          | external call =>
                              exact List.mem_append_left _
                                (horigins haddress hnodeLocal hflightMem
                                  htransaction)
                          | work item instant rest =>
                              have hshape := hflightValid.2.2
                              rw [htransaction, WorkShaped] at hshape
                              exact hshape
                          | sweep timer instant rest =>
                              exact Nat.le_trans
                                (hsweeps replyOp flight hflightMem timer
                                  instant rest htransaction)
                                htime
                        refine ⟨{
                          transaction := flight.transaction
                          loaded := flight.loaded
                          outputs := flight.selected
                          continuations := flight.continuations
                          expected_eq := rfl
                          selected := hselected
                        }, horigin⟩
                | deleting =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    exact (continueCleanup_sends_no_put hsend).elim
                | loading | writing =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    contradiction
            | none =>
                simp only [ht] at hresult
                repeat' split at hresult
                all_goals
                  simp_all [Concrete.Node.takeControl,
                    Concrete.Node.awaitControl, Concrete.refreshEnded,
                    Concrete.beginTimerList, Outcomes.one]
        | timers _ | announcements _ | membership _ _ =>
            all_goals simp [Concrete.step] at hresult
            all_goals repeat' split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]

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
    (harmings : ArmingSnapshots world)
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
            (∃ writtenKey written,
              nextStore = store.commit writtenKey written) ∨
            nextStore.values = store.values := by
        by_cases hp : pid = Concrete.Pid.store
        · subst pid
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          rcases heffect with rfl |
            ⟨writtenKey, written, rfl⟩ | ⟨hkeys, hvalues⟩
          · exact .inl rfl
          · exact .inr (.inl ⟨writtenKey, written, rfl⟩)
          · exact .inr (.inr hvalues)
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
        rcases heffect with rfl |
          ⟨writtenKey, written, rfl⟩ | hvalues
        · exact hsnapshot
        · exact Snapshot.commit hsnapshot
        · exact Snapshot.sameDocuments hvalues hsnapshot
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
            (hcaches address hprocess hstore hnodeState)
            (harmings address hprocess hstore hnodeState)
            hgots hvalid
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
        (reachable_arming_snapshots hreachable)
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
    (∃ key document expectedVersion,
        (Concrete.Pid.node address, .store,
          .storeRequest {
            op
            payload := .put key document expectedVersion
          }) ∈ world.network) ∨
      (reply = .conflict ∧
        ∃ expected membership,
          (Concrete.Pid.node address, .store,
            .storeRequest {
              op
              payload := .putMembership expected membership
            }) ∈ world.network)

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
    (∃ key document expectedVersion,
        event = .receive (.node address)
          (.storeRequest {
            op
            payload := .put key document expectedVersion
          })) ∨
      (reply = .conflict ∧
        ∃ expected membership,
          event = .receive (.node address)
            (.storeRequest {
              op
              payload := .putMembership expected membership
            })) := by
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
                      left
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
                          all_goals first | contradiction | grind
                        · simp [Outcomes.one] at hresult
                          subst result
                          grind
                  | putMembership expected membership =>
                      simp only [Concrete.step] at hresult
                      split at hresult
                      · simp [Outcomes.one] at hresult
                        subst result
                        rcases hreply with rfl | rfl | rfl <;>
                          contradiction
                      · simp [Outcomes.one] at hresult
                        subst result
                        right
                        refine ⟨?_, expected, membership, ?_⟩ <;> grind
                  | armTimer _ | deleteTimer _ | deleteTimers _ | listTimers _
                  | announce _ | listAnnouncements | getMembership =>
                      simp [Concrete.step, Outcomes.one] at hresult
                      subst result
                      rcases hreply with rfl | rfl | rfl <;>
                        contradiction

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
      · rcases hinvariant hreply hold with hput | hcontrol
        · obtain ⟨key, document, expected, hput⟩ := hput
          exact .inl ⟨key, document, expected,
            List.mem_append_left _ hput⟩
        · obtain ⟨hconflict, expected, membership, hrequest⟩ := hcontrol
          exact .inr ⟨hconflict, expected, membership,
            List.mem_append_left _ hrequest⟩
      · simp at hnew
  | outside =>
      exact hinvariant
  | @process pid now event result htime hprocess hvalid hresult =>
      intro address op reply hreply hmem
      simp only [World.land, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · rcases hinvariant hreply hold with hput | hcontrol
        · obtain ⟨key, document, expected, hput⟩ := hput
          exact .inl ⟨key, document, expected,
            List.mem_append_left _ hput⟩
        · obtain ⟨hconflict, expected, membership, hrequest⟩ := hcontrol
          exact .inr ⟨hconflict, expected, membership,
            List.mem_append_left _ hrequest⟩
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        rcases sent_put_reply_origin hreply hresult hsent with
          horigin | horigin
        · obtain ⟨key, document, expected, horigin⟩ := horigin
          cases horigin
          exact .inl ⟨key, document, expected,
            List.mem_append_left _ hvalid⟩
        · obtain ⟨hconflict, expected, membership, horigin⟩ := horigin
          cases horigin
          exact .inr ⟨hconflict, expected, membership,
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
    (flightAddress : Addr := "")
    (fired : Option Concrete.TimerKey := none)
    {next : Concrete.Node} {P : Call → Prop}
    (hstate :
      (Concrete.start appConfig node transaction key flightAddress fired).state =
        .node next)
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
          Concrete.select appConfig {
            key
            transaction
            address := flightAddress
            fired
          }
            (some (value.document, value.version)) with
      | none =>
          cases fired with
          | none =>
              simp [Concrete.decide, hselect] at hstate
              subst next
              exact hold op flight call hmem htransaction
          | some timer =>
              have hstate' :=
                decide_state_cleanup appConfig node
                  { key, transaction, address := flightAddress,
                    fired := some timer }
                  (some (value.document, value.version)) timer hselect rfl
              rw [hstate'] at hstate
              cases hstate
              exact hold op flight call (by simpa using hmem) htransaction
      | some candidate =>
          cases htimer :
              Concrete.timerForDocument key candidate.document
                transaction.logicalTime node.nextTimerToken
                flightAddress with
          | none =>
              simp [Concrete.decide, hselect, htimer,
                Concrete.writeCandidate, Concrete.Node.await] at hstate
              subst next
              simp only [List.mem_cons] at hmem
              rcases hmem with hnew | holdMem
              · cases hnew
                exact fresh call htransaction
              · exact hold op flight call holdMem htransaction
          | some timer =>
              simp [Concrete.decide, hselect, htimer,
                Concrete.writeCandidate, Concrete.Node.await] at hstate
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
            split at hresult
            · simp [Concrete.beginMembershipRefresh,
                Concrete.Node.awaitControl, Outcomes.one] at hresult
              subst result
              cases Concrete.Local.node.inj hstate
              exact hold (by simpa using hmem) htransaction
            · cases hwheel :
                (node.wheel.takeDue now config.fireConcurrency).beginOne with
              | none =>
                  simp only [hwheel] at hresult
                  repeat' split at hresult
                  all_goals
                    simp [Concrete.beginTimerList,
                      Concrete.Node.awaitControl, Outcomes.one] at hresult
                  all_goals subst result
                  all_goals cases Concrete.Local.node.inj hstate
                  all_goals exact hold (by simpa using hmem) htransaction
              | some timerAndWheel =>
                  obtain ⟨timer, wheel⟩ := timerAndWheel
                  simp only [hwheel] at hresult
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    subst result
                    exact start_external_flight_provenance appConfig
                      {
                        node with
                        pending := []
                        wheel := wheel
                      }
                      (.sweep timer now []) timer.target.key
                      (flightAddress := address) (fired := some timer) hstate
                      (fun _ _ _ hmem htx =>
                        hold (by simpa using hmem) htx)
                      (by intros; contradiction) hmem htransaction
                  · simp [Outcomes.one] at hresult
                    subst result
                    cases Concrete.Local.node.inj hstate
                    exact hold (by simpa using hmem) htransaction
        | cons entry rest =>
            cases entry with
            | occurrence request instant =>
                simp [hp, Outcomes.one] at hresult
                subst result
                exact start_external_flight_provenance appConfig
                  { node with pending := [] }
                  (.work (.occurrence request instant) instant rest)
                  (.origin request.id.origin)
                  (flightAddress := address) (fired := none) hstate
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact start_external_flight_provenance appConfig node
                  (.external incoming) key
                  (flightAddress := address) (fired := none) hstate
                  (fun _ _ _ hmem htx => hold hmem htx)
                  (by
                    intro call htx
                    cases Concrete.Transaction.external.inj htx
                    exact List.mem_append_left _ hvalid)
                  hmem htransaction
              · simp [Concrete.pureExternal, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact hold hmem htransaction
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
                          cases hf : flight.fired with
                          | none =>
                              have hflights := congrArg (fun localState =>
                                match localState with
                                | .node value => value.flights
                                | _ => []) hstate
                              simp [Concrete.decide, hs, hf,
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
                          | some fired =>
                              have hflights : next.flights = remaining.flights := by
                                have hstate' := hstate
                                simp only [Concrete.decide, hs, hf] at hstate'
                                rw [Concrete.continueCleanup,
                                  Concrete.cleanupFlight_cleanup] at hstate'
                                cases hstate'
                                cases hloaded : heq ▸ loaded <;>
                                  simp [hloaded, Concrete.finishNode,
                                    Concrete.Node.awaitControl,
                                    Concrete.Node.cachePut,
                                    Concrete.Node.cacheInvalidate]
                              rw [hflights] at hmem
                              exact hold (hremaining hmem) htransaction
                      | some candidate =>
                          simp only [Concrete.decide, hs] at hstate
                          split at hstate
                          all_goals
                            simp [Concrete.writeCandidate, Concrete.Node.await,
                              Concrete.Node.cachePut,
                              Concrete.Node.cacheInvalidate] at hstate
                            subst next
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
                  | arming | writing | deleting =>
                      simp only [hp, Outcomes.one,
                        List.mem_singleton] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      simp only at hflights
                      rw [← hflights] at hmem
                      simp only [List.mem_cons] at hmem
                      rcases hmem with hnew | holdMem
                      · cases hnew
                        exact hold (takeFlight_some_mem ht) htransaction
                      · exact hold (hremaining holdMem) htransaction
                next _ =>
                  simp only [Outcomes.one, List.mem_singleton] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  simp only at hflights
                  rw [← hflights] at hmem
                  simp only [List.mem_cons] at hmem
                  rcases hmem with hnew | holdMem
                  · cases hnew
                    exact hold (takeFlight_some_mem ht) htransaction
                  · exact hold (hremaining holdMem) htransaction
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
                  | loading | arming | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      change
                        (replyOp, taken) :: remaining.flights =
                          next.flights at hflights
                      rw [← hflights] at hmem
                      simp only [List.mem_cons] at hmem
                      rcases hmem with hnew | holdMem
                      · cases hnew
                        exact hold (takeFlight_some_mem ht) htransaction
                      · exact hold (takeFlight_remaining_mem ht holdMem)
                          htransaction
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases hcleanup :
                          Concrete.cleanupKeys remaining taken with
                      | nil =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.committedFlight,
                            Concrete.continueCleanup, hcleanup,
                            Concrete.finishNode] at hflights
                          rw [← hflights] at hmem
                          exact hold (takeFlight_remaining_mem ht hmem)
                            htransaction
                      | cons cleanup rest =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.committedFlight,
                            Concrete.continueCleanup, hcleanup,
                            Concrete.finishNode,
                            Concrete.Node.awaitControl] at hflights
                          rw [← hflights] at hmem
                          exact hold (takeFlight_remaining_mem ht hmem)
                            htransaction
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp only [ht] at hresult
                  repeat' split at hresult
                  all_goals
                    simp [Concrete.refreshEnded, Concrete.beginTimerList,
                      Concrete.Node.awaitControl, Outcomes.one] at hresult
                    subst result
                    have hflights := congrArg (fun localState =>
                      match localState with
                      | .node value => value.flights
                      | _ => []) hstate
                    simp [Concrete.refreshEnded, Concrete.beginTimerList,
                      Concrete.Node.awaitControl] at hflights
                    rw [← hflights] at hmem
                    exact hold hmem htransaction
              | some taken =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  have hflights := congrArg (fun localState =>
                    match localState with
                    | .node value => value.flights
                    | _ => []) hstate
                  simp at hflights
                  rw [← hflights] at hmem
                  simp only [List.mem_cons, Prod.mk.injEq] at hmem
                  rcases hmem with ⟨rfl, rfl⟩ | holdMem
                  · exact hold (takeFlight_some_mem ht) htransaction
                  · exact hold (takeFlight_remaining_mem ht holdMem)
                      htransaction
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight replyOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp only [ht] at hresult
                  generalize hc : node.takeControl replyOp = controlled
                    at hresult
                  obtain ⟨control, afterControl⟩ := controlled
                  cases control with
                  | none =>
                      simp [hc, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      have hcFlights := congrArg
                        (fun pair : Option Concrete.Control × Concrete.Node =>
                          pair.2.flights) hc
                      simp [Concrete.Node.takeControl] at hcFlights
                      simp at hflights
                      rw [← hflights] at hmem
                      rw [← hcFlights] at hmem
                      exact hold hmem htransaction
                  | some control =>
                      cases control <;>
                        simp [hc, Outcomes.one] at hresult
                      all_goals
                        subst result
                        have hflights := congrArg (fun localState =>
                          match localState with
                          | .node value => value.flights
                          | _ => []) hstate
                        have hcFlights := congrArg
                          (fun pair : Option Concrete.Control × Concrete.Node =>
                            pair.2.flights) hc
                        simp [Concrete.Node.takeControl] at hcFlights
                        simp at hflights
                        rw [← hflights] at hmem
                        rw [← hcFlights] at hmem
                        exact hold hmem htransaction
              | some taken =>
                  cases hp : taken.phase with
                  | loading | arming | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      have hflights := congrArg (fun localState =>
                        match localState with
                        | .node value => value.flights
                        | _ => []) hstate
                      simp at hflights
                      rw [← hflights] at hmem
                      exact hold (takeFlight_remaining_mem ht hmem)
                        htransaction
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases hcleanup : taken.cleanup with
                      | nil =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.continueCleanup, hcleanup,
                            Concrete.finishNode] at hflights
                          rw [← hflights] at hmem
                          exact hold (takeFlight_remaining_mem ht hmem)
                            htransaction
                      | cons cleanup rest =>
                          have hflights := congrArg (fun localState =>
                            match localState with
                            | .node value => value.flights
                            | _ => []) hstate
                          simp [Concrete.continueCleanup, hcleanup,
                            Concrete.finishNode,
                            Concrete.Node.awaitControl] at hflights
                          rw [← hflights] at hmem
                          exact hold (takeFlight_remaining_mem ht hmem)
                            htransaction
        | done =>
            simp only [Concrete.step] at hresult
            repeat' first | split at hresult
            all_goals
              simp_all [Concrete.Node.takeFlight, Concrete.Node.takeControl,
                Concrete.Node.await, Concrete.Node.awaitControl,
                Concrete.continueCleanup, Concrete.finishNode,
                Concrete.refreshEnded, Concrete.beginTimerList,
                Concrete.sendOutputs, Outcomes.one]
            all_goals repeat' first | split at hresult
            all_goals try simp_all [Concrete.Node.await,
              Concrete.Node.awaitControl, Concrete.finishNode]
            all_goals
              try
                subst next
                simp only [finishNode_flights, noteArmed_flights] at hmem
                exact hold (List.mem_filter.mp hmem).1 htransaction
            all_goals first | contradiction | grind
        | timers _ | announcements _ | membership _ _ =>
            simp only [Concrete.step] at hresult
            repeat' first | split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Outcomes.one]
            all_goals first | contradiction | grind

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
  | sweep timer instant rest => exact Nat.le_trans horigin htime

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
        obtain ⟨sweepNode, hsweepNode, hsweeps⟩ :=
          reachable_nodes_sweeps_valid hreachable address hprocess
        rw [hnodeLocal] at hsweepNode
        cases Concrete.Local.node.inj hsweepNode
        obtain ⟨provenance, horigin⟩ :=
          node_step_sent_put_origin hprocess hnodeLocal hnode hsweeps
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
    (flightAddress : Addr := "")
    (fired : Option Concrete.TimerKey := none)
    (hflight : FlightValid appConfig {
      key := transactionKey
      transaction
      address := flightAddress
      fired
    })
    (hcache : NodeCacheSnapshots store node)
    (horigin :
      TransactionOrigin
        (world.land (.node address) now
          (Concrete.start appConfig node transaction transactionKey
            flightAddress fired))
        address transaction)
    (hempty : node.flights = [])
    {recipient : Concrete.Pid} {op : Concrete.OpId} {key : DocumentKey}
    {document : Document key} {expectedVersion : Option Concrete.Version}
    (hmessage :
      (recipient, Concrete.Msg.storeRequest {
        op
        payload := .put key document expectedVersion
      }) ∈
        (Concrete.start appConfig node transaction transactionKey
          flightAddress fired).send) :
    ∃ provenance :
        PutProvenance appConfig key document expectedVersion,
      Snapshot store key provenance.loaded ∧
        TransactionOrigin
          (world.land (.node address) now
            (Concrete.start appConfig node transaction transactionKey
              flightAddress fired))
          address provenance.transaction ∧
        (∀ next flight,
          (Concrete.start appConfig node transaction transactionKey
            flightAddress fired).state = .node next →
          (op, flight) ∈ next.flights →
          flight.phase = .writing →
          ∃ hkey : key = flight.key,
            hkey ▸ provenance.loaded = flight.loaded ∧
            provenance.transaction = flight.transaction ∧
            provenance.outputs = flight.selected ∧
            provenance.continuations = flight.continuations) ∧
        ∃ next flight,
          (Concrete.start appConfig node transaction transactionKey
            flightAddress fired).state = .node next ∧
          (op, flight) ∈ next.flights ∧
          flight.phase = .writing := by
  simp only [Concrete.start] at hmessage ⊢
  cases hcached : node.cacheRead transactionKey with
  | none =>
      simp [hcached, Concrete.Node.await] at hmessage
  | some value =>
      simp only [hcached] at hmessage ⊢
      cases hselect :
          Concrete.select appConfig {
            key := transactionKey
            transaction
            address := flightAddress
            fired
          }
            (some (value.document, value.version)) with
      | none =>
          cases fired <;>
            simp [Concrete.decide, hselect,
              Concrete.Node.await] at hmessage
      | some candidate =>
          cases htimer :
              Concrete.timerForDocument transactionKey candidate.document
                transaction.logicalTime node.nextTimerToken flightAddress with
          | some timer =>
              simp [Concrete.decide, hselect, htimer,
                Concrete.Node.await] at hmessage
          | none =>
              simp [Concrete.decide, hselect, htimer,
                Concrete.writeCandidate, Concrete.Node.await] at hmessage
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
                        (Concrete.decide appConfig node {
                          key := transactionKey
                          transaction
                          address := flightAddress
                          fired
                        } (some (value.document, value.version))))
                      address transaction := by
                    simpa [Concrete.start, hcached] using horigin
                simpa [provenance] using horigin'
              · intro next flight hstate hmem hphase
                simp [Concrete.decide, hselect, htimer,
                  Concrete.writeCandidate, Concrete.Node.await] at hstate
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
                    address := flightAddress
                    fired
                  }
                refine ⟨(node.await writing
                    (.put transactionKey candidate.document
                      (some value.version))).1, writing, ?_, ?_, rfl⟩
                · simp [Concrete.decide, hselect, htimer,
                    Concrete.writeCandidate, writing]
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
    (hsweeps : NodeSweepsValid world.now node)
    (hserial : NodeSerial node)
    (hcache : NodeCacheSnapshots store node)
    (harming : NodeArmingSnapshots store node)
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
            split at hresult
            · simp [Concrete.beginMembershipRefresh,
                Concrete.Node.awaitControl, Outcomes.one] at hresult
              subst result
              exact (put_not_in_singleton_of_payload_ne
                (by intro h; cases h) hsend).elim
            · cases hwheel :
                (node.wheel.takeDue now config.fireConcurrency).beginOne with
              | none =>
                  simp only [hwheel] at hresult
                  repeat' split at hresult
                  all_goals
                    simp [Concrete.beginTimerList,
                      Concrete.Node.awaitControl, Outcomes.one] at hresult
                  all_goals subst result
                  all_goals
                    first
                    | exact (put_not_in_singleton_of_payload_ne
                        (by intro h; cases h) hsend).elim
                    | contradiction
              | some timerAndWheel =>
                  obtain ⟨timer, wheel⟩ := timerAndWheel
                  simp only [hwheel] at hresult
                  split at hresult
                  · simp [Outcomes.one] at hresult
                    subst result
                    have hempty : node.flights = [] := by simp_all
                    exact start_put_stageable appConfig address now {
                        node with
                        pending := []
                        wheel := wheel
                      }
                      (.sweep timer now []) timer.target.key
                      (flightAddress := address) (fired := some timer)
                      ⟨rfl, trivial, trivial⟩
                      (by
                        intro cacheKey value hread
                        change node.cacheRead cacheKey = some value at hread
                        exact hcache cacheKey value hread)
                      (by simp [TransactionOrigin, World.land])
                      (by simpa using hempty) hsend
                  · simp [Outcomes.one] at hresult
                    subst result
                    contradiction
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
                  (flightAddress := address) (fired := none)
                  ⟨rfl, trivial, ⟨request, rfl⟩⟩
                  (by
                    intro cacheKey value hread
                    change node.cacheRead cacheKey = some value at hread
                    exact hcache cacheKey value hread)
                  ⟨request, rfl⟩
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
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                have hempty : node.flights = [] := by simp_all
                exact start_put_stageable appConfig address now node
                  (.external call) requestKey
                  (flightAddress := address) (fired := none)
                  ⟨hk, trivial, trivial⟩ hcache
                  (List.mem_append_left _ hvalid) hempty hsend
              · simp [Concrete.pureExternal, Concrete.sendOutputs,
                  Outcomes.one] at hresult
                subst result
                simp [Concrete.sendOutputs] at hsend
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
                          hselect, htimer, hloaded, houtputs, hcontinuations⟩ :=
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
                        | sweep timer instant rest =>
                            exact Nat.le_trans
                              (hsweeps replyOp flight hflightMem timer instant
                                rest
                                (htransaction.symm.trans hprovenance))
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
                        simp only [Concrete.decide, hselect] at hflights
                        rw [htimer] at hflights
                        simp [Concrete.writeCandidate, Concrete.Node.await,
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
                        try simp [Concrete.Node.await, hcachedEmpty] at hactive
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
                        · simp only [Concrete.decide, hselect]
                          rw [htimer]
                          simp [Concrete.writeCandidate]
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
                  | arming | writing | deleting =>
                      simp [hp, Outcomes.one] at hresult
                      subst result
                      contradiction
                next _ =>
                  simp [Outcomes.one] at hresult
                  subst result
                  contradiction
        | done =>
            simp [Concrete.step] at hresult
            generalize ht : node.takeFlight replyOp = taken at hresult
            obtain ⟨taken, remaining⟩ := taken
            cases taken with
            | some flight =>
                have hflightMem := takeFlight_some_mem ht
                have hflightValid := hnode replyOp flight hflightMem
                cases hp : flight.phase with
                | arming =>
                    have hsnapshot :
                        Snapshot store flight.key flight.loaded :=
                      harming hflightMem hp
                    cases hd : flight.document with
                    | none =>
                        simp [ht, hp, hd, Outcomes.one] at hresult
                        subst result
                        contradiction
                    | some selectedDocument =>
                        simp [ht, hp, hd, Concrete.Node.await,
                          Outcomes.one] at hresult
                        subst result
                        simp [Concrete.Node.await] at hsend
                        obtain ⟨rfl, _, hkey, hdocument, hexpected⟩ := hsend
                        subst key
                        have : document = selectedDocument :=
                          eq_of_heq hdocument
                        subst document
                        subst expectedVersion
                        have hvalid' := hflightValid
                        rw [FlightValid, hp] at hvalid'
                        obtain ⟨selectedDocument', hdocument',
                          hselected⟩ := hvalid'.2.1
                        rw [hd] at hdocument'
                        cases Option.some.inj hdocument'
                        let provenance :
                            PutProvenance appConfig flight.key
                              selectedDocument
                              (flight.loaded.map (·.2)) := {
                          transaction := flight.transaction
                          loaded := flight.loaded
                          outputs := flight.selected
                          continuations := flight.continuations
                          expected_eq := rfl
                          selected := hselected
                        }
                        have horigin :
                            TransactionOrigin
                              (world.land (.node address) now {
                                state := .node
                                  (remaining.await
                                    { flight with phase := .writing }
                                    (.put flight.key selectedDocument
                                      (flight.loaded.map (·.2)))).1
                                send := [
                                  (remaining.await
                                    { flight with phase := .writing }
                                    (.put flight.key selectedDocument
                                      (flight.loaded.map (·.2)))).2
                                ]
                              })
                              address flight.transaction := by
                          cases htransaction : flight.transaction with
                          | external call =>
                              exact List.mem_append_left _
                                (horigins haddress hnodeLocal hflightMem
                                  htransaction)
                          | work item instant rest =>
                              have hshape := hflightValid.2.2
                              rw [htransaction, WorkShaped] at hshape
                              exact hshape
                          | sweep timer instant rest =>
                              exact Nat.le_trans
                                (hsweeps replyOp flight hflightMem timer
                                  instant rest htransaction)
                                htime
                        have hempty : remaining.flights = [] := by
                          have hfilter :=
                            takeFlight_filter_empty_of_some hserial
                              (congrArg Prod.fst ht)
                          have hnext := congrArg
                            (fun pair :
                              Option Concrete.Flight × Concrete.Node =>
                                pair.2.flights) ht
                          simp [Concrete.Node.takeFlight, hfilter] at hnext
                          exact hnext
                        refine ⟨provenance, hsnapshot, horigin, ?_, ?_⟩
                        · intro resultNode active hstate hactive hactivePhase
                          simp [Concrete.Node.await, hd] at hstate
                          subst resultNode
                          simp [Concrete.Node.await, hempty, hd] at hactive
                          rcases hactive with ⟨_, rfl⟩
                          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
                        · let writing : Concrete.Flight :=
                            { flight with phase := .writing }
                          refine ⟨(remaining.await writing
                              (.put flight.key selectedDocument
                                (flight.loaded.map (·.2)))).1,
                            writing, by
                              simp [Concrete.Node.await, writing, hd], ?_, rfl⟩
                          simp_all [Concrete.Node.await, writing, hd]
                | deleting =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    exact (continueCleanup_sends_no_put hsend).elim
                | loading | writing =>
                    simp [ht, hp, Outcomes.one] at hresult
                    subst result
                    contradiction
            | none =>
                simp only [ht] at hresult
                repeat' split at hresult
                all_goals
                  simp_all [Concrete.Node.takeControl,
                    Concrete.Node.awaitControl, Concrete.refreshEnded,
                    Concrete.beginTimerList, Outcomes.one]
        | written =>
            exact (written_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        | conflict =>
            exact (conflict_step_sends_no_put
              (appConfig := appConfig) (address := address) (now := now)
              hresult hsend).elim
        | failed =>
            exact (failed_step_sends_no_put
              (appConfig := appConfig) (config := config)
              (address := address) (now := now) hresult hsend).elim
        | timers _ | announcements _ | membership _ _ =>
            all_goals simp [Concrete.step] at hresult
            all_goals repeat' split at hresult
            all_goals
              simp_all [Concrete.Node.takeControl,
                Concrete.Node.awaitControl, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.sendOutputs,
                Outcomes.one]

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
            (∃ writtenKey written,
              nextStore = store.commit writtenKey written) ∨
            nextStore.values = store.values := by
        by_cases hp : pid = Concrete.Pid.store
        · subst pid
          have hresult' := hresult
          rw [hstore] at hresult'
          obtain ⟨effectStore, hstate, heffect⟩ :=
            store_step_effect hresult'
          have heq : effectStore = nextStore := by
            simpa [World.land, hstate] using hnextStore
          subst effectStore
          rcases heffect with rfl |
            ⟨writtenKey, written, rfl⟩ | ⟨hkeys, hvalues⟩
          · exact .inl rfl
          · exact .inr (.inl ⟨writtenKey, written, rfl⟩)
          · exact .inr (.inr hvalues)
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
        rcases heffect with rfl |
          ⟨writtenKey, written, rfl⟩ | hvalues
        · exact hsnapshot
        · exact Snapshot.commit hsnapshot
        · exact Snapshot.sameDocuments hvalues hsnapshot
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
            rcases heffect with rfl |
              ⟨writtenKey, written, rfl⟩ | hvalues
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
            · simpa [Concrete.Store.version, Concrete.Store.read, hvalues]
                using hmatch
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
              have hputOrigin :
                  ∃ replyKey replyDocument replyExpected,
                    event = .receive (.node address)
                      (.storeRequest {
                        op
                        payload :=
                          .put replyKey replyDocument replyExpected
                      }) := by
                rcases sent_put_reply_origin hreply (hstore ▸ hresult)
                    hsentReply with hputOrigin | hcontrolOrigin
                · exact hputOrigin
                · obtain ⟨_, controlExpected, membership, hevent⟩ :=
                    hcontrolOrigin
                  subst event
                  have hrequest :
                      (Concrete.Pid.node address, .store,
                        .storeRequest {
                          op
                          payload :=
                            .putMembership controlExpected membership
                        }) ∈ world.network := hvalid
                  have hpayload :=
                    (reachable_rpc_ids hreachable).unique hold hrequest
                  cases hpayload
              obtain ⟨replyKey, replyDocument, replyExpected, hevent⟩ :=
                hputOrigin
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
                simp only [bne_iff_ne] at hmismatch
                exact hmismatch hmatch
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
            obtain ⟨serialNode, hserialNode, hserial⟩ :=
              reachable_nodes_serial hreachable address hprocess
            rw [hbefore] at hserialNode
            cases Concrete.Local.node.inj hserialNode
            have hnotWritten :
                event ≠ .receive .store
                  (.storeReply { op, payload := .written }) := by
              intro hevent
              subst event
              exact hnoreply .written (.inl rfl) hvalid
            have hnotConflict :
                event ≠ .receive .store
                  (.storeReply { op, payload := .conflict }) := by
              intro hevent
              subst event
              exact hnoreply .conflict (.inr (.inl rfl)) hvalid
            have hnotFailed :
                event ≠ .receive .store
                  (.storeReply { op, payload := .failed }) := by
              intro hevent
              subst event
              exact hnoreply .failed (.inr (.inr rfl)) hvalid
            obtain ⟨after, hafterState, hafterFlight⟩ :=
              node_step_preserves_writing_flight hactive hphase hserial
                hnotWritten hnotConflict hnotFailed
                (hbefore ▸ hresult)
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
        obtain ⟨sweepNode, hsweepNode, hsweeps⟩ :=
          reachable_nodes_sweeps_valid hreachable address hprocess
        rw [hnodeState] at hsweepNode
        cases Concrete.Local.node.inj hsweepNode
        obtain ⟨provenance, hsnapshot, horigin, hagreement,
            hactiveNew⟩ :=
          node_step_sent_put_stageable hprocess hnodeState hstore
            hnodeValid hsweeps hserial
            (reachable_cache_snapshots hreachable address hprocess
              hstore hnodeState)
            (reachable_arming_snapshots hreachable address hprocess
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
          · obtain ⟨payload, hrequest⟩ :
                ∃ payload,
                  (Concrete.Pid.node address, .store,
                    .storeRequest { op, payload }) ∈ world.network := by
              rcases reachable_put_replies_have_request hreachable hreply hold
                with hput | hcontrol
              · obtain ⟨key, document, expected, hput⟩ := hput
                exact ⟨.put key document expected, hput⟩
              · obtain ⟨_, expected, membership, hcontrol⟩ := hcontrol
                exact ⟨.putMembership expected membership, hcontrol⟩
            have holdFresh :=
              (reachable_rpc_ids hreachable).fresh hprocess hnodeState hrequest
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

theorem reachable_nodes_nodup
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    nodes.Nodup := by
  induction hreachable with
  | init hinit => exact hinit.1
  | step _ _ ih => exact ih

theorem reachable_writing_snapshot
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {store : Concrete.Store} {address : Addr} {node : Concrete.Node}
    (hstore : world.process .store = .store store)
    (haddress : address ∈ nodes)
    (hnode : world.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing) :
    Snapshot store flight.key flight.loaded := by
  obtain ⟨document, _, _, _, _, _, _, hput⟩ :=
    reachable_writing_flight_provenance hreachable haddress hnode
      hflight hphase
  obtain ⟨provenance, hsnapshot, _, hagreement, _⟩ :=
    reachable_stageable_puts hreachable hstore hput
  obtain ⟨hkey, hloaded, _, _, _⟩ :=
    hagreement node flight hnode hflight hphase
  cases hkey
  simpa [hloaded] using hsnapshot

theorem pending_work_choice_of_mem
    (appConfig : Resonate.Config) (state : State)
    (now : Time) (entry : WorkflowEntry)
    (hmem : entry ∈ state.workflow.pending) :
    ∃ rest,
      Resonate.runWork appConfig entry.item entry.instant rest state ∈
        (Resonate.runTimeoutChoices appConfig now state).val ∧
      List.Perm state.workflow.pending (entry :: rest) := by
  obtain ⟨before, after, hpending⟩ := List.append_of_mem hmem
  refine ⟨before ++ after, ?_, ?_⟩
  simp only [Resonate.runTimeoutChoices, Resonate.timeoutChoices,
    List.mem_cons, List.mem_append]
  right
  left
  simp only [Resonate.pendingTimeoutChoices, List.mem_mapIdx]
  refine ⟨before.length, by simp [hpending], ?_⟩
  · simp [hpending, List.eraseIdx_append]
  · rw [hpending]
    simpa [List.append_assoc] using
      (List.perm_middle :
        List.Perm (before ++ entry :: after) (entry :: (before ++ after)))

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
      | .loading | .arming =>
          abstractPending =
            (Resonate.occurrenceEntry? item).toList ++
              Concrete.pendingWorkflow rest
      | .writing =>
          abstractPending =
              (Resonate.occurrenceEntry? item).toList ++
                Concrete.pendingWorkflow rest ∨
          abstractPending =
            Concrete.pendingWorkflow flight.continuations
      | .deleting =>
          abstractPending =
            Concrete.pendingWorkflow flight.continuations
  | .sweep _ _ rest =>
      match flight.phase with
      | .loading | .arming =>
          abstractPending = Concrete.pendingWorkflow rest
      | .writing =>
          abstractPending = Concrete.pendingWorkflow rest ∨
          abstractPending =
            Concrete.pendingWorkflow flight.continuations
      | .deleting =>
          abstractPending =
            Concrete.pendingWorkflow flight.continuations

def TransactionPending : Concrete.Transaction → Option (List WorkflowEntry)
  | .external _ => none
  | .work item _ rest =>
      some ((Resonate.occurrenceEntry? item).toList ++
        Concrete.pendingWorkflow rest)
  | .sweep _ _ rest =>
      some (Concrete.pendingWorkflow rest)

def FlightWorkflowPart (store : Concrete.Store)
    (flight : Concrete.Flight)
    (nodePending : List Concrete.PendingEntry)
    (part : List WorkflowEntry) : Prop :=
  match flight.transaction with
  | .external _ =>
      flight.fired = none ∧
        match flight.phase with
        | .deleting =>
            flight.continuations = [] ∧
              part = Concrete.pendingWorkflow nodePending
        | .loading | .arming | .writing =>
            part = Concrete.pendingWorkflow nodePending
  | .work item _ rest =>
      flight.fired = none ∧
        nodePending = [] ∧
        let before :=
          (Resonate.occurrenceEntry? item).toList ++
            Concrete.pendingWorkflow rest
        match flight.phase with
        | .loading =>
            part = before ∨
              (0 < flight.attempt ∧
                part = Concrete.pendingWorkflow flight.continuations)
        | .arming => part = before
        | .writing =>
            part = before ∨
              (flight.loaded.map (·.2) ≠ store.version flight.key ∧
                part = Concrete.pendingWorkflow flight.continuations)
        | .deleting =>
            part = Concrete.pendingWorkflow flight.continuations
  | .sweep _ _ rest =>
      flight.fired.isSome = true ∧
        nodePending = [] ∧
        let before := Concrete.pendingWorkflow rest
        match flight.phase with
        | .loading =>
            part = before ∨
              (0 < flight.attempt ∧
                part = Concrete.pendingWorkflow flight.continuations)
        | .arming => part = before
        | .writing =>
            part = before ∨
              (flight.loaded.map (·.2) ≠ store.version flight.key ∧
                part = Concrete.pendingWorkflow flight.continuations)
        | .deleting =>
            part = Concrete.pendingWorkflow flight.continuations

def NodeWorkflowPart (store : Concrete.Store) (node : Concrete.Node)
    (part : List WorkflowEntry) : Prop :=
  (node.flights = [] →
    part = Concrete.pendingWorkflow node.pending) ∧
  ∀ op flight, (op, flight) ∈ node.flights →
    FlightWorkflowPart store flight node.pending part

structure NodeWorkflowPartWitness (store : Concrete.Store)
    (node : Concrete.Node) (part : List WorkflowEntry) where
  value : NodeWorkflowPart store node part

structure NodeWorkflowEmptyWitness (node : Concrete.Node)
    (part : List WorkflowEntry) where
  value : node.flights = [] →
    part = Concrete.pendingWorkflow node.pending

structure NodeWorkflowFlightsWitness (store : Concrete.Store)
    (node : Concrete.Node) (part : List WorkflowEntry) where
  value : ∀ op flight, (op, flight) ∈ node.flights →
    FlightWorkflowPart store flight node.pending part

@[grind] theorem FlightWorkflowPart.sweep_loading_zero
    {store : Concrete.Store} {flight : Concrete.Flight}
    {nodePending : List Concrete.PendingEntry}
    {part : List WorkflowEntry}
    {timer : Concrete.TimerKey} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (hpart : FlightWorkflowPart store flight nodePending part)
    (htransaction : flight.transaction = .sweep timer instant rest)
    (hphase : flight.phase = .loading)
    (hattempt : flight.attempt = 0) :
    part = Concrete.pendingWorkflow rest := by
  simp only [FlightWorkflowPart, htransaction, hphase] at hpart
  obtain ⟨_, _, hpart⟩ := hpart
  rcases hpart with hpart | ⟨hpositive, _⟩
  · exact hpart
  · omega

@[grind] theorem FlightWorkflowPart.work_loading_zero
    {store : Concrete.Store} {flight : Concrete.Flight}
    {nodePending : List Concrete.PendingEntry}
    {part : List WorkflowEntry}
    {item : WorkItem} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (hpart : FlightWorkflowPart store flight nodePending part)
    (htransaction : flight.transaction = .work item instant rest)
    (hphase : flight.phase = .loading)
    (hattempt : flight.attempt = 0) :
    part =
      (Resonate.occurrenceEntry? item).toList ++
        Concrete.pendingWorkflow rest := by
  simp only [FlightWorkflowPart, htransaction, hphase] at hpart
  obtain ⟨_, _, hpart⟩ := hpart
  rcases hpart with hpart | ⟨hpositive, _⟩
  · exact hpart
  · omega

theorem NodeWorkflowPartWitness.holds
    {store : Concrete.Store} {node : Concrete.Node}
    {part : List WorkflowEntry}
    (witness : NodeWorkflowPartWitness store node part) :
    NodeWorkflowPart store node part :=
  witness.value

grind_pattern NodeWorkflowPartWitness.holds =>
  NodeWorkflowPartWitness store node part

theorem NodeWorkflowEmptyWitness.holds
    {node : Concrete.Node} {part : List WorkflowEntry}
    (witness : NodeWorkflowEmptyWitness node part) :
    node.flights = [] →
      part = Concrete.pendingWorkflow node.pending :=
  witness.value

grind_pattern NodeWorkflowEmptyWitness.holds =>
  NodeWorkflowEmptyWitness node part

theorem NodeWorkflowFlightsWitness.holds
    {store : Concrete.Store} {node : Concrete.Node}
    {part : List WorkflowEntry}
    (witness : NodeWorkflowFlightsWitness store node part) :
    ∀ op flight, (op, flight) ∈ node.flights →
      FlightWorkflowPart store flight node.pending part :=
  witness.value

theorem nodeWorkflowPart_continueCleanup
    {store : Concrete.Store} {node remaining : Concrete.Node}
    {part : List WorkflowEntry} {op : Concrete.OpId}
    {flight : Concrete.Flight}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    (htake : node.takeFlight op = (some flight, remaining))
    (hphase : flight.phase = .deleting) :
    ∃ next,
      (Concrete.continueCleanup remaining flight).state = .node next ∧
      NodeWorkflowPart store next part := by
  have hflight : (op, flight) ∈ node.flights :=
    takeFlight_some_mem htake
  have hflightPart := hpart.2 op flight hflight
  have hremainingFlights : remaining.flights = [] :=
    takeFlight_remaining_empty hserial htake
  have hremainingPending : remaining.pending = node.pending :=
    takeFlight_pending (next := remaining) htake
  let finished := Concrete.finishNode remaining flight
  have hfinished : NodeWorkflowPart store finished part := by
    constructor
    · intro _
      cases ht : flight.transaction <;>
        simp [FlightWorkflowPart, ht, hphase, hremainingPending,
          finished, Concrete.finishNode,
          Concrete.pendingWorkflow] at hflightPart ⊢ <;>
        grind
    · intro currentOp currentFlight hmem
      simp [finished, Concrete.finishNode, hremainingFlights] at hmem
  cases hcleanup : flight.cleanup with
  | nil =>
      exact ⟨finished, by simp [Concrete.continueCleanup, hcleanup, finished],
        hfinished⟩
  | cons key rest =>
      let next :=
        (finished.awaitControl (.cleanup flight.selected)
          (.deleteTimers (key :: rest))).1
      refine ⟨next, by simp [Concrete.continueCleanup, hcleanup, finished,
        next], ?_⟩
      simpa [next, Concrete.Node.awaitControl, NodeWorkflowPart] using hfinished

theorem NodeWorkflowPart.copy
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    (hpart : NodeWorkflowPart store node part)
    (hflights : next.flights = node.flights)
    (hpending : next.pending = node.pending) :
    NodeWorkflowPart store next part := by
  simpa [NodeWorkflowPart, hflights, hpending] using hpart

theorem NodeWorkflowPart.restore
    {store : Concrete.Store} {node : Concrete.Node}
    {part : List WorkflowEntry}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining next : Concrete.Node}
    (htake : node.takeFlight op = (some flight, remaining))
    (hflights : next.flights = (op, flight) :: remaining.flights)
    (hpending : next.pending = node.pending) :
    NodeWorkflowPart store next part := by
  have hmem := takeFlight_some_mem htake
  have hempty := takeFlight_remaining_empty hserial htake
  have hpend := takeFlight_pending (next := remaining) htake
  constructor
  · intro hemptyNext
    simp [hflights] at hemptyNext
  · intro currentOp current hcurrent
    have hflightPart := hpart.2 op flight hmem
    simp [hflights, hempty, List.mem_cons, Prod.mk.injEq] at hcurrent
    obtain ⟨rfl, rfl⟩ := hcurrent
    simpa [FlightWorkflowPart, hpending, hpend] using hflightPart

theorem NodeWorkflowPart.drop
    {store : Concrete.Store} {node : Concrete.Node}
    {part : List WorkflowEntry}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining next : Concrete.Node}
    (htake : node.takeFlight op = (some flight, remaining))
    (hflights : next.flights = remaining.flights)
    (hpending : next.pending = node.pending)
    (hpartEq : part = Concrete.pendingWorkflow node.pending) :
    NodeWorkflowPart store next part := by
  have hempty := takeFlight_remaining_empty hserial htake
  constructor
  · intro _
    simpa [hpending] using hpartEq
  · intro currentOp current hcurrent
    simp [hflights, hempty] at hcurrent

def WorkflowAligned
    {nodes : List Addr} {appConfig : Resonate.Config}
    (_config : Concrete.Config)
    (concrete : World (CModel nodes appConfig))
    (abstract : World AModel) : Prop :=
  ∃ store parts slack,
    concrete.process .store = .store store ∧
    List.Perm (abstract.process .service).workflow.pending
      (nodes.flatMap parts ++ slack) ∧
    (∀ address, address ∈ nodes → ∀ node,
      concrete.process (.node address) = .node node →
      NodeWorkflowPart store node (parts address)) ∧
    ∀ address, address ∈ nodes → ∀ node op flight,
      concrete.process (.node address) = .node node →
      (op, flight) ∈ node.flights →
      flight.phase = .writing →
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .written }) ∈ concrete.network →
      TransactionPending flight.transaction = none ∨
        parts address = Concrete.pendingWorkflow flight.continuations

def PendingEmbedded (pending available : List WorkflowEntry) : Prop :=
  ∃ before after, List.Perm available (before ++ pending ++ after)

theorem PendingEmbedded.subset {pending available : List WorkflowEntry}
    (h : PendingEmbedded pending available) : pending ⊆ available := by
  obtain ⟨before, after, hperm⟩ := h
  intro entry hentry
  apply hperm.symm.subset
  simp [hentry]

theorem PendingEmbedded.cancel_head
    {entry : WorkflowEntry} {rest available remaining : List WorkflowEntry}
    (hembedded : PendingEmbedded (entry :: rest) available)
    (hremaining : List.Perm available (entry :: remaining)) :
    PendingEmbedded rest remaining := by
  obtain ⟨before, after, hembedded⟩ := hembedded
  refine ⟨before, after, ?_⟩
  apply List.Perm.cons_inv
  exact hremaining.symm.trans <|
    hembedded.trans <| by
      simpa [List.append_assoc] using
        (List.perm_middle :
          List.Perm (before ++ entry :: (rest ++ after))
            (entry :: (before ++ rest ++ after)))

theorem PendingEmbedded.append_same
    {pending available : List WorkflowEntry}
    (h : PendingEmbedded pending available)
    (added : List WorkflowEntry) :
    PendingEmbedded (pending ++ added) (available ++ added) := by
  obtain ⟨before, after, hperm⟩ := h
  refine ⟨before, after, (hperm.append_right added).trans ?_⟩
  have hswap : List.Perm (after ++ added) (added ++ after) :=
    List.perm_append_comm
  simpa [List.append_assoc] using
    (hswap.append_left (before ++ pending))

theorem pendingEmbedded_flatMap_part
    {parts : Addr → List WorkflowEntry} {nodes : List Addr}
    {address : Addr} (haddress : address ∈ nodes)
    (slack : List WorkflowEntry) :
    PendingEmbedded (parts address) (nodes.flatMap parts ++ slack) := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem haddress
  refine ⟨before.flatMap parts, after.flatMap parts ++ slack, ?_⟩
  apply List.Perm.of_eq
  simp [List.flatMap_append, List.append_assoc]

theorem WorkflowAligned.current
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (haligned : WorkflowAligned config concrete abstract)
    {physical : Concrete.Store} {address : Addr} {node : Concrete.Node}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {pending : List WorkflowEntry}
    (haddress : address ∈ nodes)
    (hstore : concrete.process .store = .store physical)
    (hnode : concrete.process (.node address) = .node node)
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    (hversion :
      flight.loaded.map (·.2) = physical.version flight.key)
    (hpending : TransactionPending flight.transaction = some pending) :
    PendingEmbedded pending
      (abstract.process .service).workflow.pending := by
  obtain ⟨actual, parts, slack, hactual, hperm, hparts, _⟩ := haligned
  rw [hstore] at hactual
  cases Concrete.Local.store.inj hactual
  have hpart := (hparts address haddress node hnode).2 op flight hflight
  have hpartEq : parts address = pending := by
    cases ht : flight.transaction with
    | external call =>
        simp [TransactionPending, ht] at hpending
    | work item instant rest =>
        simp only [FlightWorkflowPart, ht, hphase] at hpart
        obtain ⟨_, _, hpart⟩ := hpart
        simp only [TransactionPending, ht, Option.some.injEq] at hpending
        rcases hpart with hbefore | ⟨hstale, _⟩
        · exact hbefore.trans hpending
        · exact (hstale hversion).elim
    | sweep timer instant rest =>
        simp only [FlightWorkflowPart, ht, hphase] at hpart
        obtain ⟨_, _, hpart⟩ := hpart
        simp only [TransactionPending, ht, Option.some.injEq] at hpending
        rcases hpart with hbefore | ⟨hstale, _⟩
        · exact hbefore.trans hpending
        · exact (hstale hversion).elim
  have hembedded :=
    pendingEmbedded_flatMap_part haddress (parts := parts) slack
  rw [hpartEq] at hembedded
  obtain ⟨before, after, hpartPerm⟩ := hembedded
  exact ⟨before, after, hperm.trans hpartPerm⟩

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
      PendingEmbedded pending
        (abstract.process .service).workflow.pending
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
          (TransactionPending flight.transaction = none ∨ True)) ∧
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
  putReplies : PutRepliesHaveRequest concrete
  /-- Outputs parked on a cleanup control were covered when the control was
  created, and Rover only appends, so a later resend is not a new observation. -/
  cleanupCovered :
    ∀ address node op outputs,
      address ∈ nodes →
      concrete.process (.node address) = .node node →
      (op, Concrete.Control.cleanup outputs) ∈ node.controls →
      Covered abstract outputs

theorem Related.cleanupCovered_transport
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete concreteNext : World (CModel nodes appConfig)}
    {abstract abstractNext : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    (hprocess :
      ∀ address, concreteNext.process (.node address) =
        concrete.process (.node address))
    (hnetwork :
      ∀ message ∈ abstract.network, message ∈ abstractNext.network) :
    ∀ address node op outputs,
      address ∈ nodes →
      concreteNext.process (.node address) = .node node →
      (op, Concrete.Control.cleanup outputs) ∈ node.controls →
      Covered abstractNext outputs := by
  intro address node op outputs haddress hnode hmem
  have hnodeOld : concrete.process (.node address) = .node node := by
    rw [← hprocess address]; exact hnode
  exact (related.cleanupCovered address node op outputs haddress hnodeOld
    hmem).mono hnetwork

theorem workflowAligned_store_commit
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract nextAbstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (haligned : WorkflowAligned config concrete abstract)
    {physical : Concrete.Store}
    (hphysical : concrete.process .store = .store physical)
    {key : DocumentKey} (document : Document key)
    {now : Time}
    (result : Result Concrete.Pid Concrete.Local Concrete.Msg)
    (hstate : result.state = .store (physical.commit key document))
    (hpending :
      (nextAbstract.process .service).workflow.pending =
        (abstract.process .service).workflow.pending)
    (hnewCommitted :
      ∀ address node op flight,
        address ∈ nodes →
        concrete.process (.node address) = .node node →
        (op, flight) ∈ node.flights →
        flight.phase = .writing →
        (.node address,
          Concrete.Msg.storeReply { op, payload := .written }) ∈ result.send →
        TransactionPending flight.transaction = none) :
    WorkflowAligned config (concrete.land .store now result)
      nextAbstract := by
  obtain ⟨workflowStore, parts, slack, hworkflowStore, hperm,
      hparts, hcommitted⟩ := haligned
  rw [hphysical] at hworkflowStore
  cases Concrete.Local.store.inj hworkflowStore
  refine ⟨physical.commit key document, parts, slack,
    by simp [World.land, hstate], ?_, ?_, ?_⟩
  · rw [hpending]
    exact hperm
  · intro address haddress node hnodeNext
    have hnode :
        concrete.process (.node address) = .node node := by
      simpa [World.land] using hnodeNext
    have hold := hparts address haddress node hnode
    refine ⟨hold.1, ?_⟩
    intro op flight hflight
    have hpart := hold.2 op flight hflight
    cases ht : flight.transaction with
    | external call =>
        simpa [FlightWorkflowPart, ht] using hpart
    | work item instant rest =>
        cases hp : flight.phase with
        | loading | arming | deleting =>
            simpa [FlightWorkflowPart, ht, hp] using hpart
        | writing =>
            simp only [FlightWorkflowPart, ht, hp] at hpart ⊢
            obtain ⟨hfired, hpending, hpart⟩ := hpart
            refine ⟨hfired, hpending, ?_⟩
            rcases hpart with hbefore | ⟨hstale, hafter⟩
            · exact .inl hbefore
            · refine .inr ⟨?_, hafter⟩
              by_cases hsame : flight.key = key
              · cases hsame
                exact Snapshot.expected_ne_commit_version
                  (reachable_writing_snapshot hreachable hphysical haddress
                    hnode hflight hp)
              · simpa [Concrete.Store.version, Concrete.Store.commit,
                  hsame] using hstale
    | sweep timer instant rest =>
        cases hp : flight.phase with
        | loading | arming | deleting =>
            simpa [FlightWorkflowPart, ht, hp] using hpart
        | writing =>
            simp only [FlightWorkflowPart, ht, hp] at hpart ⊢
            obtain ⟨hfired, hpending, hpart⟩ := hpart
            refine ⟨hfired, hpending, ?_⟩
            rcases hpart with hbefore | ⟨hstale, hafter⟩
            · exact .inl hbefore
            · refine .inr ⟨?_, hafter⟩
              by_cases hsame : flight.key = key
              · cases hsame
                exact Snapshot.expected_ne_commit_version
                  (reachable_writing_snapshot hreachable hphysical haddress
                    hnode hflight hp)
              · simpa [Concrete.Store.version, Concrete.Store.commit,
                  hsame] using hstale
  · intro address haddress node op flight hnodeNext hflight hphase hreply
    have hnode :
        concrete.process (.node address) = .node node := by
      simpa [World.land] using hnodeNext
    simp only [World.land, List.mem_append] at hreply
    rcases hreply with hold | hnew
    · exact hcommitted address haddress node op flight hnode hflight hphase hold
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, rfl⟩ := heq
      exact .inl
        (hnewCommitted address node op flight haddress hnode hflight hphase
          hsent)

theorem NodeWorkflowPart.commitStore
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {physical : Concrete.Store}
    (hphysical : world.process .store = .store physical)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node)
    {part : List WorkflowEntry}
    (hpart : NodeWorkflowPart physical node part)
    {key : DocumentKey} (document : Document key) :
    NodeWorkflowPart (physical.commit key document) node part := by
  refine ⟨hpart.1, ?_⟩
  intro op flight hflight
  have hold := hpart.2 op flight hflight
  cases ht : flight.transaction with
  | external call =>
      simpa [FlightWorkflowPart, ht] using hold
  | work item instant rest =>
      cases hp : flight.phase with
      | loading | arming | deleting =>
          simpa [FlightWorkflowPart, ht, hp] using hold
      | writing =>
          simp only [FlightWorkflowPart, ht, hp] at hold ⊢
          obtain ⟨hfired, hpending, hold⟩ := hold
          refine ⟨hfired, hpending, ?_⟩
          rcases hold with hbefore | ⟨hstale, hafter⟩
          · exact .inl hbefore
          · refine .inr ⟨?_, hafter⟩
            by_cases hsame : flight.key = key
            · cases hsame
              exact Snapshot.expected_ne_commit_version
                (reachable_writing_snapshot hreachable hphysical haddress
                  hnode hflight hp)
            · simpa [Concrete.Store.version, Concrete.Store.commit,
                hsame] using hstale
  | sweep timer instant rest =>
      cases hp : flight.phase with
      | loading | arming | deleting =>
          simpa [FlightWorkflowPart, ht, hp] using hold
      | writing =>
          simp only [FlightWorkflowPart, ht, hp] at hold ⊢
          obtain ⟨hfired, hpending, hold⟩ := hold
          refine ⟨hfired, hpending, ?_⟩
          rcases hold with hbefore | ⟨hstale, hafter⟩
          · exact .inl hbefore
          · refine .inr ⟨?_, hafter⟩
            by_cases hsame : flight.key = key
            · cases hsame
              exact Snapshot.expected_ne_commit_version
                (reachable_writing_snapshot hreachable hphysical haddress
                  hnode hflight hp)
            · simpa [Concrete.Store.version, Concrete.Store.commit,
                hsame] using hstale

theorem workflowAligned_work_commit
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract nextAbstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (haligned : WorkflowAligned config concrete abstract)
    {physical : Concrete.Store}
    (hphysical : concrete.process .store = .store physical)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    {request : ServerModel.PromiseCreateReq}
    {semanticTime instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction :
      flight.transaction =
        .work (.occurrence request semanticTime) instant rest)
    (hversion :
      flight.loaded.map (·.2) = physical.version flight.key)
    (hcontinuations :
      Concrete.pendingWorkflow flight.continuations =
        Concrete.pendingWorkflow rest)
    {key : DocumentKey} (document : Document key)
    (hkey : key = flight.key)
    {now : Time}
    (result : Result Concrete.Pid Concrete.Local Concrete.Msg)
    (hstate : result.state = .store (physical.commit key document))
    (hnoWritten :
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .written }) ∉ concrete.network)
    (hnewWritten :
      ∀ replyAddress replyOp,
        (.node replyAddress,
          Concrete.Msg.storeReply {
            op := replyOp, payload := .written }) ∈ result.send →
        replyAddress = address ∧ replyOp = op)
    {nextPending : List WorkflowEntry}
    (hpendingPerm :
      List.Perm (abstract.process .service).workflow.pending
        ({ request, instant := semanticTime } :: nextPending))
    (hpending :
      (nextAbstract.process .service).workflow.pending =
        nextPending) :
    WorkflowAligned config (concrete.land .store now result)
      nextAbstract := by
  cases hkey
  let entry : WorkflowEntry := { request, instant := semanticTime }
  obtain ⟨workflowStore, parts, slack, hworkflowStore, hperm,
      hparts, hcommitted⟩ := haligned
  rw [hphysical] at hworkflowStore
  cases Concrete.Local.store.inj hworkflowStore
  have hnodePart := hparts address haddress node hnode
  have hflightPart := hnodePart.2 op flight hflight
  have hpartEq :
      parts address = entry :: Concrete.pendingWorkflow rest := by
    simp only [FlightWorkflowPart, htransaction, hphase] at hflightPart
    obtain ⟨_, _, hflightPart⟩ := hflightPart
    rcases hflightPart with hbefore | ⟨hstale, _⟩
    · simpa [entry, Resonate.occurrenceEntry?] using hbefore
    · exact (hstale hversion).elim
  let nextParts : Addr → List WorkflowEntry := fun current =>
    if current = address then Concrete.pendingWorkflow rest else parts current
  have hnodup := reachable_nodes_nodup hreachable
  obtain ⟨before, after, hnodes⟩ := List.append_of_mem haddress
  subst nodes
  simp only [List.nodup_append, List.nodup_cons] at hnodup
  have hbefore : address ∉ before := by
    intro hmem
    exact hnodup.2.2 address hmem address (by simp) rfl
  have hafter : address ∉ after := hnodup.2.1.1
  have hbeforeParts :
      before.flatMap nextParts = before.flatMap parts := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro current hcurrent
    have hne : current ≠ address := fun heq => hbefore (heq ▸ hcurrent)
    simp [nextParts, hne]
  have hafterParts :
      after.flatMap nextParts = after.flatMap parts := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro current hcurrent
    have hne : current ≠ address := fun heq => hafter (heq ▸ hcurrent)
    simp [nextParts, hne]
  have hglobal :
      List.Perm
        ((before ++ address :: after).flatMap parts ++ slack)
        (entry ::
          ((before ++ address :: after).flatMap nextParts ++ slack)) := by
    simp [List.flatMap_append, nextParts, hbeforeParts, hafterParts,
      hpartEq, List.append_assoc, List.perm_middle]
  have hnextGlobal :
      List.Perm nextPending
        ((before ++ address :: after).flatMap nextParts ++ slack) := by
    apply List.Perm.cons_inv
    exact hpendingPerm.symm.trans (hperm.trans hglobal)
  refine ⟨physical.commit flight.key document, nextParts, slack,
    by simp [World.land, hstate], ?_, ?_, ?_⟩
  · rw [hpending]
    exact hnextGlobal
  · intro currentAddress hcurrentAddress currentNode hcurrentNodeNext
    have hcurrentNode :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNodeNext
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hnode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      obtain ⟨serialNode, hserialNode, hserial⟩ :=
        reachable_nodes_serial hreachable address haddress
      rw [hnode] at hserialNode
      cases Concrete.Local.node.inj hserialNode
      refine ⟨?_, ?_⟩
      · intro hempty
        rw [hempty] at hflight
        contradiction
      · intro currentOp currentFlight hcurrentFlight
        have hpairs :=
          NodeSerial.eq_of_mem hserial hcurrentFlight hflight
        cases hpairs
        simp only [nextParts, if_pos rfl]
        simp only [FlightWorkflowPart, htransaction, hphase]
        have hold := hnodePart.2 op flight hflight
        simp only [FlightWorkflowPart, htransaction, hphase] at hold
        exact ⟨hold.1, hold.2.1, .inr ⟨
          Snapshot.expected_ne_commit_version
            (reachable_writing_snapshot hreachable hphysical haddress hnode
              hflight hphase),
          hcontinuations.symm⟩⟩
    · have hold := hparts currentAddress hcurrentAddress currentNode
          hcurrentNode
      simpa [nextParts, heq] using
        hold.commitStore hreachable hphysical hcurrentAddress hcurrentNode
          document
  · intro currentAddress hcurrentAddress currentNode currentOp currentFlight
      hcurrentNodeNext hcurrentFlight hcurrentPhase hreply
    have hcurrentNode :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNodeNext
    simp only [World.land, List.mem_append] at hreply
    rcases hreply with hold | hnew
    · rcases hcommitted currentAddress hcurrentAddress currentNode currentOp
          currentFlight hcurrentNode hcurrentFlight hcurrentPhase hold with
        hnone | hpart
      · exact .inl hnone
      · right
        by_cases heq : currentAddress = address
        · cases heq
          rw [hnode] at hcurrentNode
          cases Concrete.Local.node.inj hcurrentNode
          obtain ⟨serialNode, hserialNode, hserial⟩ :=
            reachable_nodes_serial hreachable address haddress
          rw [hnode] at hserialNode
          cases Concrete.Local.node.inj hserialNode
          have hpairs :=
            NodeSerial.eq_of_mem hserial hcurrentFlight hflight
          cases hpairs
          exact (hnoWritten hold).elim
        · simpa [nextParts, heq] using hpart
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hnewWritten _ _ hsent
      rw [hnode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      obtain ⟨serialNode, hserialNode, hserial⟩ :=
        reachable_nodes_serial hreachable currentAddress hcurrentAddress
      rw [hnode] at hserialNode
      cases Concrete.Local.node.inj hserialNode
      have hpairs := NodeSerial.eq_of_mem hserial hcurrentFlight hflight
      cases hpairs
      right
      simp [nextParts, hcontinuations]

theorem workflowAligned_document_commit
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract nextAbstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (haligned : WorkflowAligned config concrete abstract)
    {physical : Concrete.Store}
    (hphysical : concrete.process .store = .store physical)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hflight : (op, flight) ∈ node.flights)
    (hphase : flight.phase = .writing)
    {timer : Concrete.TimerKey} {instant : Time}
    {rest : List Concrete.PendingEntry}
    (htransaction : flight.transaction = .sweep timer instant rest)
    (hversion :
      flight.loaded.map (·.2) = physical.version flight.key)
    (added : List WorkflowEntry)
    (hcontinuations :
      Concrete.pendingWorkflow flight.continuations =
        Concrete.pendingWorkflow rest ++ added)
    {key : DocumentKey} (document : Document key)
    (hkey : key = flight.key)
    {now : Time}
    (result : Result Concrete.Pid Concrete.Local Concrete.Msg)
    (hstate : result.state = .store (physical.commit key document))
    (hnoWritten :
      (Concrete.Pid.store, .node address,
        .storeReply { op, payload := .written }) ∉ concrete.network)
    (hnewWritten :
      ∀ replyAddress replyOp,
        (.node replyAddress,
          Concrete.Msg.storeReply {
            op := replyOp, payload := .written }) ∈ result.send →
        replyAddress = address ∧ replyOp = op)
    (hpending :
      (nextAbstract.process .service).workflow.pending =
        (abstract.process .service).workflow.pending ++ added) :
    WorkflowAligned config (concrete.land .store now result)
      nextAbstract := by
  cases hkey
  obtain ⟨workflowStore, parts, slack, hworkflowStore, hperm,
      hparts, hcommitted⟩ := haligned
  rw [hphysical] at hworkflowStore
  cases Concrete.Local.store.inj hworkflowStore
  have hnodePart := hparts address haddress node hnode
  have hflightPart := hnodePart.2 op flight hflight
  have hpartEq :
      parts address = Concrete.pendingWorkflow rest := by
    simp only [FlightWorkflowPart, htransaction, hphase] at hflightPart
    obtain ⟨_, _, hflightPart⟩ := hflightPart
    rcases hflightPart with hbefore | ⟨hstale, _⟩
    · exact hbefore
    · exact (hstale hversion).elim
  let nextParts : Addr → List WorkflowEntry := fun current =>
    if current = address
    then Concrete.pendingWorkflow rest ++ added
    else parts current
  have hnodup := reachable_nodes_nodup hreachable
  obtain ⟨before, after, hnodes⟩ := List.append_of_mem haddress
  subst nodes
  simp only [List.nodup_append, List.nodup_cons] at hnodup
  have hbefore : address ∉ before := by
    intro hmem
    exact hnodup.2.2 address hmem address (by simp) rfl
  have hafter : address ∉ after := hnodup.2.1.1
  have hbeforeParts :
      before.flatMap nextParts = before.flatMap parts := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro current hcurrent
    have hne : current ≠ address := fun heq => hbefore (heq ▸ hcurrent)
    simp [nextParts, hne]
  have hafterParts :
      after.flatMap nextParts = after.flatMap parts := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro current hcurrent
    have hne : current ≠ address := fun heq => hafter (heq ▸ hcurrent)
    simp [nextParts, hne]
  have hglobal :
      List.Perm
        (((before ++ address :: after).flatMap parts ++ slack) ++ added)
        ((before ++ address :: after).flatMap nextParts ++ slack) := by
    have hswap :
        List.Perm ((after.flatMap parts ++ slack) ++ added)
          (added ++ (after.flatMap parts ++ slack)) :=
      List.perm_append_comm
    simpa [List.flatMap_append, nextParts, hbeforeParts, hafterParts,
      hpartEq, List.append_assoc] using
        hswap.append_left (before.flatMap parts ++
          Concrete.pendingWorkflow rest)
  refine ⟨physical.commit flight.key document, nextParts, slack,
    by simp [World.land, hstate], ?_, ?_, ?_⟩
  · rw [hpending]
    exact (hperm.append_right added).trans hglobal
  · intro currentAddress hcurrentAddress currentNode hcurrentNodeNext
    have hcurrentNode :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNodeNext
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [hnode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      obtain ⟨serialNode, hserialNode, hserial⟩ :=
        reachable_nodes_serial hreachable address haddress
      rw [hnode] at hserialNode
      cases Concrete.Local.node.inj hserialNode
      refine ⟨?_, ?_⟩
      · intro hempty
        rw [hempty] at hflight
        contradiction
      · intro currentOp currentFlight hcurrentFlight
        have hpairs :=
          NodeSerial.eq_of_mem hserial hcurrentFlight hflight
        cases hpairs
        simp only [nextParts, if_pos rfl]
        simp only [FlightWorkflowPart, htransaction, hphase]
        have hold := hnodePart.2 op flight hflight
        simp only [FlightWorkflowPart, htransaction, hphase] at hold
        exact ⟨hold.1, hold.2.1, .inr ⟨Snapshot.expected_ne_commit_version
          (reachable_writing_snapshot hreachable hphysical haddress hnode
            hflight hphase), hcontinuations.symm⟩⟩
    · have hold := hparts currentAddress hcurrentAddress currentNode
          hcurrentNode
      simpa [nextParts, heq] using
        hold.commitStore hreachable hphysical hcurrentAddress hcurrentNode
          document
  · intro currentAddress hcurrentAddress currentNode currentOp currentFlight
      hcurrentNodeNext hcurrentFlight hcurrentPhase hreply
    have hcurrentNode :
        concrete.process (.node currentAddress) = .node currentNode := by
      simpa [World.land] using hcurrentNodeNext
    simp only [World.land, List.mem_append] at hreply
    rcases hreply with hold | hnew
    · rcases hcommitted currentAddress hcurrentAddress currentNode currentOp
          currentFlight hcurrentNode hcurrentFlight hcurrentPhase hold with
        hnone | hpart
      · exact .inl hnone
      · right
        by_cases heq : currentAddress = address
        · cases heq
          rw [hnode] at hcurrentNode
          cases Concrete.Local.node.inj hcurrentNode
          obtain ⟨serialNode, hserialNode, hserial⟩ :=
            reachable_nodes_serial hreachable address haddress
          rw [hnode] at hserialNode
          cases Concrete.Local.node.inj hserialNode
          have hpairs :=
            NodeSerial.eq_of_mem hserial hcurrentFlight hflight
          cases hpairs
          exact (hnoWritten hold).elim
        · simpa [nextParts, heq] using hpart
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := hnewWritten _ _ hsent
      rw [hnode] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      obtain ⟨serialNode, hserialNode, hserial⟩ :=
        reachable_nodes_serial hreachable currentAddress hcurrentAddress
      rw [hnode] at hserialNode
      cases Concrete.Local.node.inj hserialNode
      have hpairs := NodeSerial.eq_of_mem hserial hcurrentFlight hflight
      cases hpairs
      right
      simp [nextParts, hcontinuations]

theorem workflowAligned_node_land
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (haligned : WorkflowAligned config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node nextNode : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {now : Time}
    (result : Result Concrete.Pid Concrete.Local Concrete.Msg)
    (hstate : result.state = .node nextNode)
    (hpreserve :
      ∀ store part,
        NodeWorkflowPart store node part →
        NodeWorkflowPart store nextNode part)
    (hcommittedNext :
      ∀ (parts : Addr → List WorkflowEntry),
        (∀ current, current ∈ nodes → ∀ currentNode op flight,
          concrete.process (.node current) = .node currentNode →
          (op, flight) ∈ currentNode.flights →
          flight.phase = .writing →
          (Concrete.Pid.store, .node current,
            .storeReply { op, payload := .written }) ∈ concrete.network →
          TransactionPending flight.transaction = none ∨
            parts current =
              Concrete.pendingWorkflow flight.continuations) →
        ∀ op flight,
        (op, flight) ∈ nextNode.flights →
        flight.phase = .writing →
        (Concrete.Pid.store, .node address,
          .storeReply { op, payload := .written }) ∈ concrete.network →
        TransactionPending flight.transaction = none ∨
          parts address = Concrete.pendingWorkflow flight.continuations)
    (hnoWritten :
      ∀ target op,
        (target, Concrete.Msg.storeReply {
          op, payload := .written }) ∉ result.send) :
    WorkflowAligned config
      (concrete.land (.node address) now result) abstract := by
  obtain ⟨store, parts, slack, hstore, hpending, hparts, hcommitted⟩ :=
    haligned
  refine ⟨store, parts, slack, by simpa [World.land] using hstore,
    hpending, ?_, ?_⟩
  · intro current hcurrent currentNode hcurrentNode
    by_cases heq : current = address
    · subst current
      rw [show
        (concrete.land (.node address) now result).process (.node address) =
          result.state by simp [World.land],
        hstate] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      exact hpreserve store (parts address)
        (hparts address haddress node hnode)
    · exact hparts current hcurrent currentNode
        (by simpa [World.land, heq] using hcurrentNode)
  · intro current hcurrent currentNode op flight hcurrentNode hflight hphase
      hreply
    simp only [World.land, List.mem_append] at hreply
    rcases hreply with hold | hnew
    · by_cases heq : current = address
      · subst current
        rw [show
          (concrete.land (.node address) now result).process (.node address) =
            result.state by simp [World.land],
          hstate] at hcurrentNode
        cases Concrete.Local.node.inj hcurrentNode
        exact hcommittedNext parts hcommitted op flight hflight hphase hold
      · exact hcommitted current hcurrent currentNode op flight
          (by simpa [World.land, heq] using hcurrentNode)
          hflight hphase hold
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, rfl⟩ := heq
      exact (hnoWritten _ _ hsent).elim




def NodeAttempts (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights → flight.attempt = 0

@[grind] theorem NodeAttempts.mem
    {node : Concrete.Node} (hattempts : NodeAttempts node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    (hmem : (op, flight) ∈ node.flights) :
    flight.attempt = 0 :=
  hattempts op flight hmem

/-- A node step keeps the represented workflow, or releases a suffix into the
alignment slack when the flight is dropped. A flight that stays keeps the part. -/
abbrev WorkflowStep (store : Concrete.Store) (node next : Concrete.Node)
    (part : List WorkflowEntry) : Prop :=
  ∃ part' released,
    NodeWorkflowPart store next part' ∧
    part = part' ++ released ∧
    ∀ keptOp keptFlight,
      (keptOp, keptFlight) ∈ next.flights →
      (keptOp, keptFlight) ∈ node.flights →
      part' = part

theorem NodeWorkflowPart.kept
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    (hnext : NodeWorkflowPart store next part) :
    WorkflowStep store node next part :=
  ⟨part, [], hnext, by simp, fun _ _ _ _ => rfl⟩

theorem NodeWorkflowPart.singleton
    {store : Concrete.Store} {next : Concrete.Node}
    {flight : Concrete.Flight} {op : Concrete.OpId}
    {pending : List Concrete.PendingEntry} {part : List WorkflowEntry}
    (hflight : FlightWorkflowPart store flight pending part)
    (hflights : next.flights = [(op, flight)])
    (hpending : next.pending = pending) :
    NodeWorkflowPart store next part := by
  constructor
  · intro hempty
    simp [hflights] at hempty
  · intro currentOp current hmem
    simp only [hflights, List.mem_singleton, Prod.mk.injEq] at hmem
    obtain ⟨rfl, rfl⟩ := hmem
    rw [hpending]
    exact hflight

theorem flights_empty_of_ready {node : Concrete.Node}
    (hready : ¬ (!node.flights.isEmpty || !node.controls.isEmpty) = true) :
    node.flights = [] := by
  cases h : node.flights.isEmpty with
  | false =>
      exact False.elim (hready (by simp [h]))
  | true =>
      cases hflights : node.flights with
      | nil => rfl
      | cons head tail => simp [List.isEmpty_cons, hflights] at h

theorem Result.state_node_inj
    {a b : Concrete.Node}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (h : result.state = .node a) (h' : result.state = .node b) : a = b :=
  Concrete.Local.node.inj (h.symm.trans h')

theorem flightWorkflowPart_external
    {store : Concrete.Store} {flight : Concrete.Flight}
    {pending : List Concrete.PendingEntry} {part : List WorkflowEntry}
    {call : Call}
    (htransaction : flight.transaction = .external call)
    (hfired : flight.fired = none)
    (hphase :
      flight.phase = .loading ∨ flight.phase = .arming ∨
        flight.phase = .writing)
    (hpart : part = Concrete.pendingWorkflow pending) :
    FlightWorkflowPart store flight pending part := by
  rcases hphase with hphase | hphase | hphase <;>
    simp [FlightWorkflowPart, htransaction, hfired, hphase, hpart]

theorem flightWorkflowPart_after_decide
    {store : Concrete.Store} {flight promoted : Concrete.Flight}
    {nodePending : List Concrete.PendingEntry} {part : List WorkflowEntry}
    (hflight : FlightWorkflowPart store flight nodePending part)
    (hphase : flight.phase = .loading)
    (hattempt : flight.attempt = 0)
    (htransaction : promoted.transaction = flight.transaction)
    (hfired : promoted.fired = flight.fired)
    (hpromoted : promoted.phase = .arming ∨ promoted.phase = .writing) :
    FlightWorkflowPart store promoted nodePending part := by
  cases ht : flight.transaction with
  | external call =>
      have htx : promoted.transaction = .external call := by
        rw [htransaction, ht]
      simp only [FlightWorkflowPart, ht, hphase] at hflight
      obtain ⟨hfiredNone, hpartEq⟩ := hflight
      rcases hpromoted with hpromoted | hpromoted <;>
        simp only [FlightWorkflowPart, htx, hpromoted] <;>
        exact ⟨by rw [hfired]; exact hfiredNone, hpartEq⟩
  | work item instant rest =>
      have htx : promoted.transaction = .work item instant rest := by
        rw [htransaction, ht]
      have hpartEq :=
        FlightWorkflowPart.work_loading_zero hflight ht hphase hattempt
      simp only [FlightWorkflowPart, ht] at hflight
      obtain ⟨hfiredNone, hemptyPending, _⟩ := hflight
      rcases hpromoted with hpromoted | hpromoted
      · simp only [FlightWorkflowPart, htx, hpromoted]
        exact ⟨by rw [hfired]; exact hfiredNone, hemptyPending, hpartEq⟩
      · simp only [FlightWorkflowPart, htx, hpromoted]
        exact ⟨by rw [hfired]; exact hfiredNone, hemptyPending, Or.inl hpartEq⟩
  | sweep sweepTimer instant rest =>
      have htx : promoted.transaction = .sweep sweepTimer instant rest := by
        rw [htransaction, ht]
      have hpartEq :=
        FlightWorkflowPart.sweep_loading_zero hflight ht hphase hattempt
      simp only [FlightWorkflowPart, ht] at hflight
      obtain ⟨hfiredSome, hemptyPending, _⟩ := hflight
      rcases hpromoted with hpromoted | hpromoted
      · simp only [FlightWorkflowPart, htx, hpromoted]
        exact ⟨by simpa [hfired] using hfiredSome, hemptyPending, hpartEq⟩
      · simp only [FlightWorkflowPart, htx, hpromoted]
        exact ⟨by simpa [hfired] using hfiredSome, hemptyPending,
          Or.inl hpartEq⟩

theorem flightWorkflowPart_promote_writing
    {store : Concrete.Store} {flight promoted : Concrete.Flight}
    {nodePending : List Concrete.PendingEntry} {part : List WorkflowEntry}
    (hflight : FlightWorkflowPart store flight nodePending part)
    (hphase : flight.phase = .arming)
    (hpromoted : promoted = { flight with phase := .writing }) :
    FlightWorkflowPart store promoted nodePending part := by
  cases ht : flight.transaction with
  | external call =>
      simp only [FlightWorkflowPart, ht, hphase] at hflight
      obtain ⟨hfiredNone, hpartEq⟩ := hflight
      simp only [hpromoted, FlightWorkflowPart, ht]
      exact ⟨hfiredNone, hpartEq⟩
  | work item instant rest =>
      simp only [FlightWorkflowPart, ht, hphase] at hflight
      obtain ⟨hfiredNone, hemptyPending, hpartEq⟩ := hflight
      simp only [hpromoted, FlightWorkflowPart, ht]
      exact ⟨hfiredNone, hemptyPending, Or.inl hpartEq⟩
  | sweep sweepTimer instant rest =>
      simp only [FlightWorkflowPart, ht, hphase] at hflight
      obtain ⟨hfiredSome, hemptyPending, hpartEq⟩ := hflight
      simp only [hpromoted, FlightWorkflowPart, ht]
      exact ⟨hfiredSome, hemptyPending, Or.inl hpartEq⟩

theorem NodeWorkflowPart.kept_restore
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining : Concrete.Node}
    (htake : node.takeFlight op = (some flight, remaining))
    (hflights : next.flights = (op, flight) :: remaining.flights)
    (hpending : next.pending = node.pending) :
    WorkflowStep store node next part :=
  (hpart.restore hserial htake hflights hpending).kept

theorem NodeWorkflowPart.releaseTaken
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining : Concrete.Node}
    (htake : node.takeFlight op = (some flight, remaining))
    (hflights : next.flights = remaining.flights)
    (hpending : next.pending = node.pending) :
    WorkflowStep store node next part := by
  have hempty := takeFlight_remaining_empty hserial htake
  have hmem := takeFlight_some_mem htake
  have hflightPart := hpart.2 op flight hmem
  have hnextEmpty : next.flights = [] := by
    rw [hflights, hempty]
  cases htransaction : flight.transaction with
  | external _ =>
      have hpartEq : part = Concrete.pendingWorkflow node.pending := by
        cases hphase : flight.phase with
        | deleting =>
            simp only [FlightWorkflowPart, htransaction, hphase] at hflightPart
            exact hflightPart.2.2
        | loading | arming | writing =>
            simp only [FlightWorkflowPart, htransaction, hphase] at hflightPart
            exact hflightPart.2
      refine ⟨Concrete.pendingWorkflow node.pending, [], ?_, ?_, ?_⟩
      · constructor
        · intro _
          simp [hpending]
        · intro _ _ hcurrent
          simp [hnextEmpty] at hcurrent
      · simpa using hpartEq
      · intro _ _ hkept _
        simp [hnextEmpty] at hkept
  | work _ _ _ =>
      simp only [FlightWorkflowPart, htransaction] at hflightPart
      obtain ⟨_, hemptyPending, _⟩ := hflightPart
      refine ⟨[], part, ?_, by simp, ?_⟩
      · constructor
        · intro _
          simp [Concrete.pendingWorkflow, hpending, hemptyPending]
        · intro _ _ hcurrent
          simp [hnextEmpty] at hcurrent
      · intro _ _ hkept _
        simp [hnextEmpty] at hkept
  | sweep _ _ _ =>
      simp only [FlightWorkflowPart, htransaction] at hflightPart
      obtain ⟨_, hemptyPending, _⟩ := hflightPart
      refine ⟨[], part, ?_, by simp, ?_⟩
      · constructor
        · intro _
          simp [Concrete.pendingWorkflow, hpending, hemptyPending]
        · intro _ _ hcurrent
          simp [hnextEmpty] at hcurrent
      · intro _ _ hkept _
        simp [hnextEmpty] at hkept

theorem NodeWorkflowPart.promoteWriting
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining : Concrete.Node} {document : Document flight.key}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    (htake : node.takeFlight op = (some flight, remaining))
    (hphase : flight.phase = .arming)
    (hdocument : flight.document = some document)
    (hnext :
      next = (remaining.await
        { key := flight.key
          transaction := flight.transaction
          loaded := flight.loaded
          document := some document
          selected := flight.selected
          continuations := flight.continuations
          attempt := flight.attempt
          phase := .writing
          address := flight.address
          armed := flight.armed
          fired := flight.fired
          cleanup := flight.cleanup }
        (.put flight.key document (flight.loaded.map (·.2)))).1) :
    WorkflowStep store node next part := by
  have hempty := takeFlight_remaining_empty hserial htake
  have hpending := takeFlight_pending (next := remaining) htake
  let writing : Concrete.Flight := { flight with phase := .writing }
  have hwriting :
      writing = {
        key := flight.key
        transaction := flight.transaction
        loaded := flight.loaded
        document := some document
        selected := flight.selected
        continuations := flight.continuations
        attempt := flight.attempt
        phase := .writing
        address := flight.address
        armed := flight.armed
        fired := flight.fired
        cleanup := flight.cleanup
      } := by
    simp [writing, hdocument]
  have hsingle : next.flights = [(remaining.nextOp, writing)] := by
    simp [hnext, hwriting, Concrete.Node.await, hempty]
  have hpend : next.pending = node.pending := by
    simp [hnext, Concrete.Node.await, hpending]
  have hwf :=
    flightWorkflowPart_promote_writing
      (hpart.2 op flight (takeFlight_some_mem htake)) hphase rfl
  exact (NodeWorkflowPart.singleton hwf hsingle hpend).kept

theorem nodeWorkflowPart_loading_decide
    {appConfig : Resonate.Config}
    {store : Concrete.Store} {node cached next : Concrete.Node}
    {part : List WorkflowEntry}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining : Concrete.Node}
    {loaded : Option (Document flight.key × Concrete.Version)}
    (hnodeValid : NodeValid appConfig node)
    (hserial : NodeSerial node)
    (hpart : NodeWorkflowPart store node part)
    (hattempt : flight.attempt = 0)
    (htake : node.takeFlight op = (some flight, remaining))
    (hphase : flight.phase = .loading)
    (hcachedFlights : cached.flights = remaining.flights)
    (hcachedPending : cached.pending = remaining.pending)
    (hstate :
      (Concrete.decide appConfig cached flight loaded).state = .node next) :
    WorkflowStep store node next part := by
  have hemptyRemaining := takeFlight_remaining_empty hserial htake
  have hpendingRemaining := takeFlight_pending (next := remaining) htake
  have hmem := takeFlight_some_mem htake
  have hflightPart := hpart.2 op flight hmem
  have hcachedEmpty : cached.flights = [] := by
    rw [hcachedFlights, hemptyRemaining]
  have hcachedPending' : cached.pending = node.pending := by
    rw [hcachedPending, hpendingRemaining]
  cases hselect : Concrete.select appConfig flight loaded with
  | none =>
      cases hfired : flight.fired with
      | none =>
          have hnext : next = cached := by
            apply Result.state_node_inj hstate
            simp [Concrete.decide, hselect, hfired]
          subst hnext
          exact NodeWorkflowPart.releaseTaken hpart hserial htake
            hcachedFlights hcachedPending'
      | some firedTimer =>
          cases ht : flight.transaction with
          | external _ =>
              have hfiredNone : flight.fired = none := by
                simp only [FlightWorkflowPart, ht, hphase] at hflightPart
                exact hflightPart.1
              rw [hfired] at hfiredNone
              cases hfiredNone
          | work _ _ _ =>
              have hfiredNone : flight.fired = none := by
                simp only [FlightWorkflowPart, ht, hphase] at hflightPart
                exact hflightPart.1
              rw [hfired] at hfiredNone
              cases hfiredNone
          | sweep _ instant rest =>
              have hpartEq :=
                FlightWorkflowPart.sweep_loading_zero hflightPart ht hphase
                  hattempt
              have hemptyPending : node.pending = [] := by
                simp only [FlightWorkflowPart, ht] at hflightPart
                exact hflightPart.2.1
              obtain ⟨cleaned, hcleaned, hflights, hpendingClean⟩ :=
                continueCleanup_state cached
                  (Concrete.cleanupFlight flight firedTimer)
              have hdecide :
                  (Concrete.decide appConfig cached flight loaded).state =
                    (Concrete.continueCleanup cached
                      (Concrete.cleanupFlight flight firedTimer)).state := by
                simp [Concrete.decide, hselect, hfired]
              have hnext : next = cleaned :=
                Concrete.Local.node.inj
                  (hstate.symm.trans (hdecide.trans hcleaned))
              rw [hnext]
              have hcont :
                  (Concrete.cleanupFlight flight firedTimer).continuations =
                    rest := by
                simp [Concrete.cleanupFlight, ht, hattempt]
              refine ⟨part, [], ?_, by simp, fun _ _ _ _ => rfl⟩
              constructor
              · intro _
                have hpendingNext : cleaned.pending = rest := by
                  simpa [hcont, hcachedPending', hemptyPending] using
                    hpendingClean
                simpa [hpendingNext] using hpartEq
              · intro _ _ hcurrent
                have hemptyNext : cleaned.flights = [] := by
                  simpa [hcachedEmpty] using hflights
                simp [hemptyNext] at hcurrent
  | some candidate =>
      have hbase : FlightWorkflowPart store flight node.pending part :=
        hflightPart
      cases htimer : Concrete.timerForDocument flight.key candidate.document
          flight.transaction.logicalTime cached.nextTimerToken
          flight.address with
      | none =>
          let writing : Concrete.Flight := {
            flight with
            loaded
            document := some candidate.document
            selected := candidate.outputs
            continuations := candidate.continuations
            phase := .writing
          }
          have hnext :
              next = (cached.await writing
                (.put flight.key candidate.document (loaded.map (·.2)))).1 := by
            apply Result.state_node_inj hstate
            simp [Concrete.decide, Concrete.writeCandidate, hselect, htimer,
              writing]
          have hsingle : next.flights = [(cached.nextOp, writing)] := by
            simp [hnext, Concrete.Node.await, hcachedEmpty]
          have hpend : next.pending = node.pending := by
            simp [hnext, Concrete.Node.await, hcachedPending']
          have hwf :=
            flightWorkflowPart_after_decide (promoted := writing) hbase hphase
              hattempt rfl rfl (Or.inr rfl)
          exact (NodeWorkflowPart.singleton hwf hsingle hpend).kept
      | some timer =>
          let arming : Concrete.Flight := {
            flight with
            loaded
            document := some candidate.document
            selected := candidate.outputs
            continuations := candidate.continuations
            phase := .arming
            armed := some timer
          }
          let prepared :=
            { cached with nextTimerToken := cached.nextTimerToken + 1 }
          have hnext :
              next = (prepared.await arming (.armTimer timer)).1 := by
            apply Result.state_node_inj hstate
            simp [Concrete.decide, hselect, htimer, arming, prepared]
          have hsingle : next.flights = [(prepared.nextOp, arming)] := by
            simp [hnext, Concrete.Node.await, prepared, hcachedEmpty]
          have hpend : next.pending = node.pending := by
            simp [hnext, Concrete.Node.await, prepared, hcachedPending']
          have hwf :=
            flightWorkflowPart_after_decide (promoted := arming) hbase hphase
              hattempt rfl rfl (Or.inl rfl)
          exact (NodeWorkflowPart.singleton hwf hsingle hpend).kept

theorem nodeWorkflowPart_external_start
    {appConfig : Resonate.Config}
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    {call : Call} {key : DocumentKey} {address : Addr}
    (hpart : NodeWorkflowPart store node part)
    (hempty : node.flights = [])
    (hstate :
      (Concrete.start appConfig node (.external call) key address).state =
        .node next) :
    WorkflowStep store node next part := by
  have hpartEq : part = Concrete.pendingWorkflow node.pending :=
    hpart.1 hempty
  let flight : Concrete.Flight := {
    key := key
    transaction := .external call
    address := address
    fired := none
  }
  cases hcache : node.cacheRead key with
  | none =>
      have hnext : next = (node.await flight (.get key)).1 := by
        apply Result.state_node_inj hstate
        simp [Concrete.start, flight, hcache]
      have hsingle : next.flights = [(node.nextOp, flight)] := by
        simp [hnext, Concrete.Node.await, hempty]
      have hpend : next.pending = node.pending := by
        simp [hnext, Concrete.Node.await]
      have hwf :=
        flightWorkflowPart_external (store := store) (flight := flight) rfl rfl
          (Or.inl rfl) (by simpa [hpend] using hpartEq)
      exact (NodeWorkflowPart.singleton hwf hsingle hpend).kept
  | some value =>
      cases hselect : Concrete.select appConfig flight
          (some (value.document, value.version)) with
      | none =>
          have hnext : next = node := by
            apply Result.state_node_inj hstate
            simp [Concrete.start, Concrete.decide, flight, hcache, hselect]
          subst hnext
          exact hpart.kept
      | some candidate =>
          cases htimer : Concrete.timerForDocument key candidate.document
              (Concrete.Transaction.external call).logicalTime node.nextTimerToken
              address with
          | none =>
              let writing : Concrete.Flight := {
                flight with
                loaded := some (value.document, value.version)
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .writing
              }
              have hnext :
                  next = (node.await writing
                    (.put key candidate.document (some value.version))).1 := by
                apply Result.state_node_inj hstate
                simp [Concrete.start, Concrete.decide, Concrete.writeCandidate,
                  flight, hcache, hselect, htimer, writing]
              have hsingle : next.flights = [(node.nextOp, writing)] := by
                simp [hnext, Concrete.Node.await, hempty]
              have hpend : next.pending = node.pending := by
                simp [hnext, Concrete.Node.await]
              have hwf :=
                flightWorkflowPart_external (store := store) (flight := writing)
                  rfl rfl (Or.inr (Or.inr rfl))
                  (by simpa [hpend] using hpartEq)
              exact (NodeWorkflowPart.singleton hwf hsingle hpend).kept
          | some timer =>
              let arming : Concrete.Flight := {
                flight with
                loaded := some (value.document, value.version)
                document := some candidate.document
                selected := candidate.outputs
                continuations := candidate.continuations
                phase := .arming
                armed := some timer
              }
              let prepared :=
                { node with nextTimerToken := node.nextTimerToken + 1 }
              have hnext :
                  next = (prepared.await arming (.armTimer timer)).1 := by
                apply Result.state_node_inj hstate
                simp [Concrete.start, Concrete.decide, flight, hcache, hselect,
                  htimer, arming, prepared]
              have hsingle : next.flights = [(prepared.nextOp, arming)] := by
                simp [hnext, Concrete.Node.await, prepared, hempty]
              have hpend : next.pending = node.pending := by
                simp [hnext, Concrete.Node.await, prepared]
              have hwf :=
                flightWorkflowPart_external (store := store) (flight := arming)
                  rfl rfl (Or.inr (Or.inl rfl))
                  (by simpa [hpend] using hpartEq)
              exact (NodeWorkflowPart.singleton hwf hsingle hpend).kept

theorem nodeWorkflowPart_written
    {appConfig : Resonate.Config}
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining : Concrete.Node}
    (hnodeValid : NodeValid appConfig node)
    (hserial : NodeSerial node)
    (hpart : NodeWorkflowPart store node part)
    (hcommitted :
      TransactionPending flight.transaction = none ∨
        part = Concrete.pendingWorkflow flight.continuations)
    (htake : node.takeFlight op = (some flight, remaining))
    (hphase : flight.phase = .writing)
    (hstate :
      (Concrete.committedFlight remaining flight).state = .node next) :
    WorkflowStep store node next part := by
  have hmem := takeFlight_some_mem htake
  have hempty := takeFlight_remaining_empty hserial htake
  have hpending0 := takeFlight_pending (next := remaining) htake
  have hflightPart := hpart.2 op flight hmem
  let prepared : Concrete.Flight :=
    { flight with cleanup := Concrete.cleanupKeys remaining flight }
  obtain ⟨cleaned, hcleaned, hflights, hpending⟩ :=
    continueCleanup_state (remaining.noteArmed flight) prepared
  have hcommit :
      (Concrete.committedFlight remaining flight).state =
        (Concrete.continueCleanup (remaining.noteArmed flight) prepared).state := by
    simp [Concrete.committedFlight, prepared]
  have hnext : next = cleaned :=
    Concrete.Local.node.inj (hstate.symm.trans (hcommit.trans hcleaned))
  have hflightsEmpty : cleaned.flights = [] := by
    simpa [noteArmed_flights, hempty] using hflights
  have hpendingClean :
      cleaned.pending = flight.continuations ++ node.pending := by
    simpa [prepared, noteArmed_pending, hpending0] using hpending
  rw [hnext]
  cases ht : flight.transaction with
  | external call =>
      have hvalid := hnodeValid op flight hmem
      simp only [FlightValid, hphase, ht] at hvalid
      obtain ⟨_, _, hselected⟩ := hvalid.2.1
      have hcont := Selected.external_continuations_nil hselected
      have hpartEq : part = Concrete.pendingWorkflow node.pending := by
        simp only [FlightWorkflowPart, ht, hphase] at hflightPart
        exact hflightPart.2
      have hpendEq : cleaned.pending = node.pending := by
        simpa [hcont] using hpendingClean
      refine ⟨part, [], ?_, by simp, fun _ _ _ _ => rfl⟩
      constructor
      · intro _
        rw [hpendEq]
        exact hpartEq
      · intro _ _ hcurrent
        simp [hflightsEmpty] at hcurrent
  | work item instant rest =>
      have hpartEq : part = Concrete.pendingWorkflow flight.continuations := by
        cases hcommitted with
        | inl hnone => simp [TransactionPending, ht] at hnone
        | inr hpartEq => exact hpartEq
      have hemptyPending : node.pending = [] := by
        simp only [FlightWorkflowPart, ht] at hflightPart
        exact hflightPart.2.1
      have hpendEq : cleaned.pending = flight.continuations := by
        simpa [hemptyPending] using hpendingClean
      refine ⟨part, [], ?_, by simp, fun _ _ _ _ => rfl⟩
      constructor
      · intro _
        rw [hpendEq]
        exact hpartEq
      · intro _ _ hcurrent
        simp [hflightsEmpty] at hcurrent
  | sweep sweepTimer instant rest =>
      have hpartEq : part = Concrete.pendingWorkflow flight.continuations := by
        cases hcommitted with
        | inl hnone => simp [TransactionPending, ht] at hnone
        | inr hpartEq => exact hpartEq
      have hemptyPending : node.pending = [] := by
        simp only [FlightWorkflowPart, ht] at hflightPart
        exact hflightPart.2.1
      have hpendEq : cleaned.pending = flight.continuations := by
        simpa [hemptyPending] using hpendingClean
      refine ⟨part, [], ?_, by simp, fun _ _ _ _ => rfl⟩
      constructor
      · intro _
        rw [hpendEq]
        exact hpartEq
      · intro _ _ hcurrent
        simp [hflightsEmpty] at hcurrent

theorem nodeWorkflowPart_deleting
    {store : Concrete.Store} {node next : Concrete.Node}
    {part : List WorkflowEntry}
    {op : Concrete.OpId} {flight : Concrete.Flight}
    {remaining : Concrete.Node}
    (hpart : NodeWorkflowPart store node part)
    (hserial : NodeSerial node)
    (htake : node.takeFlight op = (some flight, remaining))
    (hphase : flight.phase = .deleting)
    (hstate :
      (Concrete.continueCleanup remaining flight).state = .node next) :
    WorkflowStep store node next part := by
  obtain ⟨cleaned, hcleaned, hcleanedPart⟩ :=
    nodeWorkflowPart_continueCleanup hpart hserial htake hphase
  cases Concrete.Local.node.inj (hstate.symm.trans hcleaned)
  exact hcleanedPart.kept


set_option maxHeartbeats 8000000 in
theorem nodeWorkflowPart_step
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    {store : Concrete.Store} {part : List WorkflowEntry}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hnodeValid : NodeValid appConfig node)
    (hserial : NodeSerial node)
    (hpart : NodeWorkflowPart store node part)
    (hattempts : NodeAttempts node)
    (hcommitted :
      ∀ op flight,
        (op, flight) ∈ node.flights →
        flight.phase = .writing →
        event = .receive .store
          (.storeReply { op, payload := .written }) →
        TransactionPending flight.transaction = none ∨
          part = Concrete.pendingWorkflow flight.continuations)
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    WorkflowStep store node next part := by
  have workSelect
      (request : ServerModel.PromiseCreateReq) (instant : Time)
      (rest : List Concrete.PendingEntry) (flightAddress : Addr)
      (loaded : Option
        (Document (DocumentKey.origin request.id.origin) ×
          Concrete.Version)) :
      Concrete.select appConfig {
        key := .origin request.id.origin
        transaction := .work (.occurrence request instant) instant rest
        address := flightAddress
      } loaded ≠ none := by
    apply FlightValid.select_ne_none
    · exact ⟨by simp [Concrete.Transaction.key?, WorkItem.key],
        trivial, ⟨request, rfl⟩⟩
    · intro timer sweepInstant sweepRest h
      contradiction
  have workSelectEntry
      (entry : Concrete.PendingEntry) (rest : List Concrete.PendingEntry)
      (flightAddress : Addr)
      (loaded : Option (Document entry.key × Concrete.Version)) :
      Concrete.select appConfig {
        key := entry.key
        transaction := .work (.occurrence entry.1 entry.2) entry.2 rest
        address := flightAddress
      } loaded ≠ none := by
    cases entry with
    | occurrence request instant =>
        exact workSelect request instant rest flightAddress loaded
  have activeWorkSelect
      (op : Concrete.OpId) (flight : Concrete.Flight)
      (hfind :
        ∃ foundOp, node.flights.find? (·.1 == op) =
          some (foundOp, flight))
      (item : WorkItem) (instant : Time)
      (rest : List Concrete.PendingEntry)
      (htransaction : flight.transaction = .work item instant rest)
      (loaded : Option (Document flight.key × Concrete.Version)) :
      Concrete.select appConfig flight loaded ≠ none := by
    obtain ⟨foundOp, hfind⟩ := hfind
    exact hnodeValid.work_select_ne_none_of_find hfind htransaction loaded
  have nodeValidWitness : NodeValidWitness appConfig node :=
    ⟨hnodeValid⟩
  have nodeWorkflowPartWitness : NodeWorkflowPartWitness store node part :=
    ⟨hpart⟩
  have nodeWorkflowEmptyWitness : NodeWorkflowEmptyWitness node part :=
    ⟨hpart.1⟩
  have nodeWorkflowFlightsWitness :
      NodeWorkflowFlightsWitness store node part :=
    ⟨hpart.2⟩
  cases event with
  | timeout =>
      refine ⟨part, [], ?_, by simp, fun _ _ _ _ => rfl⟩
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeWorkflowPart, FlightWorkflowPart,
          TransactionPending, NodeValid, FlightValid, WorkShaped,
          Concrete.start, Concrete.decide, Concrete.writeCandidate,
          Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup, Concrete.finishNode,
          Concrete.cleanupFlight,
          Concrete.Node.cachePut, Concrete.Node.cacheInvalidate,
          Concrete.pendingWorkflow, Concrete.PendingEntry.toWorkflow?,
          Resonate.occurrenceEntry?, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals
        try simp_all [NodeWorkflowPart, FlightWorkflowPart, NodeSerial,
          TransactionPending, NodeValid, FlightValid, WorkShaped,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.pendingWorkflow, Concrete.PendingEntry.toWorkflow?,
          Resonate.occurrenceEntry?]
      all_goals subst_vars
      all_goals try rcases entry with ⟨request, instant⟩
      all_goals try assumption
      all_goals try exact (workSelectEntry entry rest address _ heq_1).elim
      all_goals try exact (workSelect request instant rest address _ heq_1).elim
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          cases Concrete.Local.node.inj hstate
          exact hpart.kept
      case outside.request call =>
        split at hresult
        next _ =>
          simp [Outcomes.one] at hresult
          subst result
          cases Concrete.Local.node.inj hstate
          exact hpart.kept
        next hready =>
          cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              cases Concrete.Local.node.inj hstate
              exact hpart.kept
          | some key =>
              simp only [hk] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact nodeWorkflowPart_external_start hpart
                  (flights_empty_of_ready hready) hstate
              · simp [Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact hpart.kept
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
                  cases Concrete.Local.node.inj hstate
                  exact hpart.kept
              | some flight =>
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : flight.phase with
                    | loading =>
                        let loaded' := heq ▸ loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut flight.key
                                { document, version }
                          | none => remaining.cacheInvalidate flight.key
                        have hcachedFlights :
                            cached.flights = remaining.flights := by
                          cases hloaded : loaded' with
                          | none => simp [cached, hloaded]
                          | some value => simp [cached, hloaded]
                        have hcachedPending :
                            cached.pending = remaining.pending := by
                          cases hloaded : loaded' with
                          | none => simp [cached, hloaded]
                          | some value => simp [cached, hloaded]
                        simp [hp, loaded', cached, Outcomes.one] at hresult
                        subst result
                        exact nodeWorkflowPart_loading_decide hnodeValid
                          hserial hpart
                          (hattempts op flight (takeFlight_some_mem ht))
                          ht hp hcachedFlights hcachedPending hstate
                    | arming | writing | deleting =>
                        simp [hp, Outcomes.one] at hresult
                        subst result
                        cases Concrete.Local.node.inj hstate
                        exact hpart.kept_restore hserial ht rfl
                          (takeFlight_pending (next := remaining) ht)
                  next _ =>
                    simp [Outcomes.one] at hresult
                    subst result
                    cases Concrete.Local.node.inj hstate
                    exact hpart.kept_restore hserial ht rfl
                      (takeFlight_pending (next := remaining) ht)
        | written =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact hpart.kept
              | some flight =>
                  cases hp : flight.phase with
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact nodeWorkflowPart_written hnodeValid hserial hpart
                        (hcommitted op flight (takeFlight_some_mem ht) hp rfl)
                        ht hp hstate
                  | loading | arming | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact hpart.kept_restore hserial ht rfl
                        (takeFlight_pending (next := remaining) ht)
        | done =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  cases hp : flight.phase with
                  | arming =>
                      cases hd : flight.document with
                      | none =>
                          have hvalid :=
                            hnodeValid op flight (takeFlight_some_mem ht)
                          simp only [FlightValid, hp] at hvalid
                          obtain ⟨_, hdocument, _⟩ := hvalid.2.1
                          rw [hd] at hdocument
                          cases hdocument
                      | some document =>
                          simp [ht, hp, hd, Outcomes.one] at hresult
                          subst result
                          exact NodeWorkflowPart.promoteWriting hpart hserial
                            ht hp hd (Concrete.Local.node.inj hstate).symm
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact nodeWorkflowPart_deleting hpart hserial ht hp hstate
                  | loading | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact hpart.kept_restore hserial ht rfl
                        (takeFlight_pending (next := remaining) ht)
              | none =>
                  let controlled := (node.takeControl op).2
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, controlled, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact (hpart.copy (by rfl) (by rfl)).kept
                  | some control =>
                      cases control with
                      | announced instant =>
                          simp [ht, hc, controlled, Outcomes.one] at hresult
                          subst result
                          cases Concrete.Local.node.inj hstate
                          exact (hpart.copy (by rfl) (by rfl)).kept
                      | membershipWrite instant =>
                          simp [ht, hc, controlled, Concrete.refreshEnded,
                            Concrete.beginTimerList, Outcomes.one] at hresult
                          subst result
                          cases Concrete.Local.node.inj hstate
                          exact (hpart.copy (by rfl) (by rfl)).kept
                      | announcements instant | membership instant live
                      | timerList instant through kind | cleanup outputs =>
                          simp [ht, hc, controlled, Outcomes.one] at hresult
                          subst result
                          cases Concrete.Local.node.inj hstate
                          exact (hpart.copy (by rfl) (by rfl)).kept
        | announcements values =>
            cases hc : (node.takeControl op).1 with
            | none =>
                simp [hc, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact (hpart.copy (by rfl) (by rfl)).kept
            | some control =>
                cases control <;> simp only [hc] at hresult
                all_goals try split at hresult
                all_goals simp [Outcomes.one] at hresult
                all_goals subst result
                all_goals cases Concrete.Local.node.inj hstate
                all_goals exact (hpart.copy (by rfl) (by rfl)).kept
        | membership configuration version =>
            simp only [Concrete.step] at hresult
            cases hc : (node.takeControl op).1 with
            | none =>
                simp [hc, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact (hpart.copy (by rfl) (by rfl)).kept
            | some control =>
                cases control <;> simp only [hc] at hresult
                all_goals try split at hresult
                all_goals simp [Outcomes.one, Concrete.refreshEnded,
                  Concrete.beginTimerList, Concrete.Node.awaitControl] at hresult
                all_goals subst result
                all_goals cases Concrete.Local.node.inj hstate
                all_goals exact (hpart.copy (by rfl) (by rfl)).kept
        | timers keys =>
            cases hc : (node.takeControl op).1 with
            | none =>
                simp [hc, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact (hpart.copy (by rfl) (by rfl)).kept
            | some control =>
                cases control <;> simp [hc, Outcomes.one] at hresult
                all_goals subst result
                all_goals cases Concrete.Local.node.inj hstate
                all_goals exact (hpart.copy (by rfl) (by rfl)).kept
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact hpart.kept_restore hserial ht rfl
                    (takeFlight_pending (next := remaining) ht)
              | none =>
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact (hpart.copy (by rfl) (by rfl)).kept
                  | some control =>
                      cases control <;>
                        simp [ht, hc, Concrete.refreshEnded,
                          Concrete.beginTimerList, Outcomes.one] at hresult
                      all_goals subst result
                      all_goals cases Concrete.Local.node.inj hstate
                      all_goals exact (hpart.copy (by rfl) (by rfl)).kept
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  cases hp : flight.phase with
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      exact nodeWorkflowPart_deleting hpart hserial ht hp hstate
                  | loading | arming | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact NodeWorkflowPart.releaseTaken hpart hserial ht
                        (by simp [cacheInvalidate_flights])
                        (by simp [cacheInvalidate_pending, takeFlight_pending (next := remaining) ht])
              | none =>
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact (hpart.copy (by rfl) (by rfl)).kept
                  | some control =>
                      cases control <;> simp [ht, hc, Outcomes.one] at hresult
                      all_goals subst result
                      all_goals cases Concrete.Local.node.inj hstate
                      all_goals exact (hpart.copy (by rfl) (by rfl)).kept

theorem committedFlight_mem
    {node : Concrete.Node} {flight : Concrete.Flight} {next : Concrete.Node}
    {op : Concrete.OpId} {kept : Concrete.Flight}
    (hstate : (Concrete.committedFlight node flight).state = .node next)
    (hmem : (op, kept) ∈ next.flights) :
    (op, kept) ∈ node.flights := by
  let prepared : Concrete.Flight :=
    { flight with cleanup := Concrete.cleanupKeys node flight }
  obtain ⟨cleaned, hcleaned, hflights, _⟩ :=
    continueCleanup_state (node.noteArmed flight) prepared
  have hcommit :
      (Concrete.committedFlight node flight).state =
        (Concrete.continueCleanup (node.noteArmed flight) prepared).state := by
    simp [Concrete.committedFlight, prepared]
  have hsame : next = cleaned :=
    Concrete.Local.node.inj (hstate.symm.trans (hcommit.trans hcleaned))
  have hflightsEq : cleaned.flights = node.flights := by
    simpa [noteArmed_flights, prepared] using hflights
  simpa [hsame, hflightsEq] using hmem

theorem continueCleanup_mem
    {node : Concrete.Node} {flight : Concrete.Flight} {next : Concrete.Node}
    {op : Concrete.OpId} {kept : Concrete.Flight}
    (hstate : (Concrete.continueCleanup node flight).state = .node next)
    (hmem : (op, kept) ∈ next.flights) :
    (op, kept) ∈ node.flights := by
  obtain ⟨cleaned, hcleaned, hflights, _⟩ := continueCleanup_state node flight
  have hsame : next = cleaned :=
    Concrete.Local.node.inj (hstate.symm.trans hcleaned)
  simpa [hsame, hflights] using hmem

set_option maxHeartbeats 4000000 in
theorem node_step_flight_origin
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
    (hflight : (op, flight) ∈ next.flights) :
    (op, flight) ∈ node.flights ∨ op = node.nextOp := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.finishNode, Concrete.continueCleanup, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals
        try
          subst next
          simp only [finishNode_flights, noteArmed_flights] at hflight
          exact Or.inl (List.mem_filter.mp hflight).1
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.finishNode,
          Concrete.Node.cachePut, Concrete.Node.cacheInvalidate,
          Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals
        try
          subst result
          simp only [Concrete.continueCleanup, Concrete.cleanupFlight_cleanup,
            Concrete.finishNode, Concrete.Node.awaitControl,
            Concrete.Node.cachePut, Concrete.Node.cacheInvalidate] at hstate
          cases hstate
          simp only [finishNode_flights, awaitControl_flights,
            cachePut_flights, cacheInvalidate_flights, noteArmed_flights,
            List.mem_filter] at hflight
          first
          | exact Or.inl hflight
          | exact Or.inl hflight.1
      all_goals
        try
          subst next
          simp only [finishNode_flights, noteArmed_flights,
            awaitControl_flights, cachePut_flights,
            cacheInvalidate_flights] at hflight
          first
          | exact Or.inl hflight
          | exact Or.inl (List.mem_filter.mp hflight).1
      all_goals try
        have hmem := (List.mem_filter.mp (committedFlight_mem hstate hflight)).1
        first | exact Or.inl hmem | subst_vars; exact Or.inl hmem
      all_goals try
        have hmem := (List.mem_filter.mp (continueCleanup_mem hstate hflight)).1
        first | exact Or.inl hmem | subst_vars; exact Or.inl hmem
      all_goals first | contradiction | grind

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
    workflow := ?_
    currentWorkflow := ?_
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := ?_
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
    cleanupCovered := ?_
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
  · exact reachable_put_replies_have_request hreach
  · exact related.cleanupCovered_transport
      (fun address => by simp [cnext, World.inject])
      (fun message hmessage => List.mem_append_left _ hmessage)

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
    workflow := ?_
    currentWorkflow := ?_
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := ?_
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
    cleanupCovered := ?_
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
  · exact reachable_put_replies_have_request hreach
  · exact related.cleanupCovered_transport
      (fun address => by simp [cnext, World.inject])
      (fun message hmessage => List.mem_append_left _ hmessage)

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
    workflow := by
      simpa [WorkflowAligned, World.observeOutside] using related.workflow
    currentWorkflow := related.currentWorkflow
    acknowledged := related.acknowledged
    failedCovered := related.failedCovered
    activeReplies := related.activeReplies
    flights := related.flights
    gotReplies := related.gotReplies
    putReplies := related.putReplies
    cleanupCovered := related.cleanupCovered
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
    workflow := by
      simpa [WorkflowAligned, World.observeOutside] using related.workflow
    currentWorkflow := related.currentWorkflow
    acknowledged := related.acknowledged
    failedCovered := related.failedCovered
    activeReplies := related.activeReplies
    flights := related.flights
    gotReplies := related.gotReplies
    putReplies := related.putReplies
    cleanupCovered := related.cleanupCovered
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
                      | armTimer _ | deleteTimer _ | deleteTimers _
                      | listTimers _
                      | announce _ | listAnnouncements | getMembership =>
                          simp [Outcomes.one] at hresult0
                          subst result
                          contradiction
                      | putMembership expected next =>
                          simp only [Concrete.step] at hresult0
                          split at hresult0 <;>
                            simp [Outcomes.one] at hresult0
                          all_goals subst result
                          all_goals contradiction

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
                      | armTimer _ | deleteTimer _ | deleteTimers _
                      | listTimers _
                      | announce _ | listAnnouncements | getMembership =>
                          simp [Outcomes.one] at hresult'
                          subst result
                          contradiction
                      | putMembership expected next =>
                          simp only [Concrete.step] at hresult'
                          split at hresult' <;>
                            simp [Outcomes.one] at hresult'
                          all_goals subst result
                          all_goals contradiction

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
    (_hcurrent : True)
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
            (TransactionPending flight.transaction = none ∨ True)) ∧
        ((Concrete.Pid.store, .node address,
            .storeReply { op, payload := .failed }) ∈
              (concrete.land pid now result).network →
          Covered abstractNext
            (Concrete.failureOutputs flight.transaction)))
    (hcleanup :
      ∀ address node op outputs,
        address ∈ nodes →
        (concrete.land pid now result).process (.node address) =
          .node node →
        (op, Concrete.Control.cleanup outputs) ∈ node.controls →
        Covered abstractNext outputs) :
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
    workflow := hworkflow
    currentWorkflow := by
      intro physical address node op flight pending haddress hstore hnode
        hflight hphase hversion hpending
      exact hworkflow.current haddress hstore hnode hflight hphase
        hversion hpending
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := hactive
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
    cleanupCovered := hcleanup
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
  · exact reachable_put_replies_have_request hreach

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
    {nextPhysical : Concrete.Store}
    (hstate : result.state = .store nextPhysical)
    (hvalues : nextPhysical.values = physical.values)
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
    refine ⟨nextPhysical, by simp [World.land, hstate], ?_⟩
    constructor
    · intro key
      simpa [Concrete.Store.toAbstract, Resonate.Store.read, hvalues] using
        hrep key
    · intro key hrelevant
      apply hrep.relevantKeys key
      simpa [Concrete.Store.toAbstract, Resonate.Store.read, hvalues] using
        hrelevant
  · obtain ⟨workflowStore, parts, slack, hworkflowStore, hpending,
        hparts, hcommitted⟩ := related.workflow
    rw [hphysical] at hworkflowStore
    cases Concrete.Local.store.inj hworkflowStore
    refine ⟨nextPhysical, parts, slack, by simp [World.land, hstate],
      hpending, ?_, ?_⟩
    · intro workflowAddress hworkflowAddress workflowState hworkflowState
      have hold := hparts workflowAddress hworkflowAddress workflowState
        (by simpa [World.land] using hworkflowState)
      simpa [NodeWorkflowPart, FlightWorkflowPart, Concrete.Store.version,
        hvalues] using hold
    · intro address haddress node op flight hnodeNext hflight hphase hreply
      have hnode :
          concrete.process (.node address) = .node node := by
        simpa [World.land] using hnodeNext
      simp only [World.land, List.mem_append] at hreply
      rcases hreply with hold | hnew
      · exact hcommitted address haddress node op flight hnode hflight
          hphase hold
      · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
        obtain ⟨target, message⟩ := sent
        simp only [Prod.mk.injEq] at heq
        obtain ⟨_, htarget, hmessage⟩ := heq
        cases htarget
        cases hmessage
        exact (hnoWritten address op hsent).elim
  · trivial
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
  · exact related.cleanupCovered_transport
      (fun address => by simp [World.land])
      (fun message hmessage => hmessage)

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
    simp [hmatch]
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
  · apply workflowAligned_store_commit hreachable related.workflow hphysical
      document concreteResult rfl
    · simp [abstractNext, World.land, abstractResult, served,
        htransport.2.2]
    · intro activeAddress activeNode activeOp activeFlight hactiveAddress
        hactiveNode hactiveFlight hactivePhase hsend
      simp [concreteResult] at hsend
      obtain ⟨rfl, rfl⟩ := hsend
      rw [hnode] at hactiveNode
      cases Concrete.Local.node.inj hactiveNode
      obtain ⟨serialNode, hserialNode, hserial⟩ :=
        reachable_nodes_serial hreachable activeAddress hactiveAddress
      rw [hnode] at hserialNode
      cases Concrete.Local.node.inj hserialNode
      have hpairs := NodeSerial.eq_of_mem hserial hactiveFlight hflight
      cases hpairs
      simp [TransactionPending, ← hflightTransaction, htransaction]
  · trivial
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
  · exact related.cleanupCovered_transport
      (fun _ => by simp [World.land])
      (fun message hmessage => List.mem_append_left _ hmessage)

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
      hmatch, hflaky]
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
  · apply workflowAligned_store_commit hreachable related.workflow hphysical
      document concreteResult rfl
    · simp [abstractNext, World.land, abstractResult, lost,
        htransport.2.2]
    · intro activeAddress activeNode activeOp activeFlight hactiveAddress
        hactiveNode hactiveFlight hactivePhase hsend
      simp [concreteResult] at hsend
  · trivial
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
  · exact related.cleanupCovered_transport
      (fun _ => by simp [World.land])
      (fun message hmessage => List.mem_append_left _ hmessage)

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
      hmatch, hflaky]
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
  · apply workflowAligned_store_commit hreachable related.workflow hphysical
      (physical.toAbstract.read key) concreteResult
      (by simp [concreteResult, Concrete.Store.fence])
    · simp [abstractNext, World.land, abstractResult, shed,
        Resonate.runShed]
    · intro activeAddress activeNode activeOp activeFlight hactiveAddress
        hactiveNode hactiveFlight hactivePhase hsend
      simp [concreteResult] at hsend
  · trivial
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
  · exact related.cleanupCovered_transport
      (fun _ => by simp [World.land])
      (fun message hmessage => List.mem_append_left _ hmessage)

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
        lifted.2 = provenance.outputs)
    (hcontinuationsEmbedded :
      PendingEmbedded (Concrete.pendingWorkflow provenance.continuations)
        lifted.1.workflow.pending)
    {reply : StoreReply}
    (hworkflowNext :
      WorkflowAligned config
        (concrete.land .store now {
          state := .store (physical.commit key document)
          send := [(.node address,
            .storeReply { op, payload := reply })]
        })
        (abstract.land .service now {
          state := lifted.1
          send := Abstract.sends lifted.2
        }))
    (hkeys :
      ∀ knownKey ∈ (abstract.process .service).store.keys,
        knownKey ∈ lifted.1.store.keys)
    (hkeyMem : key ∈ lifted.1.store.keys)
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
  · simpa [abstractNext, concreteResult, abstractResult] using hworkflowNext
  · trivial
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
        simpa [abstractNext, abstractResult, htransport.2] using hcovered
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
        exact ⟨by
          simpa [abstractNext, World.land, abstractResult] using
            hkeys activeFlight.key hknown,
          hcovered.land abstractResult,
          .inr trivial⟩
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
              simpa [abstractNext, abstractResult, htransport.2,
                houtputs] using hcovered
          · right
            trivial
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
  · exact related.cleanupCovered_transport
      (fun _ => by simp [World.land])
      (fun message hmessage => List.mem_append_left _ hmessage)

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
  · apply workflowAligned_store_commit hreachable related.workflow hphysical
      (physical.toAbstract.read key) concreteResult
      (by simp [concreteResult, Concrete.Store.fence])
    · rfl
    · intro activeAddress activeNode activeOp activeFlight hactiveAddress
        hactiveNode hactiveFlight hactivePhase hsend
      simp [concreteResult] at hsend
  · trivial
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
  · exact related.cleanupCovered_transport
      (fun _ => by simp [World.land])
      (fun message hmessage => hmessage)

theorem simulate_matching_put_store
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
      (hinstant : instant = semanticTime)
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
    cases hinstant
    let item : WorkItem := .occurrence request semanticTime
    have hitemKey : item.key = key := by
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have htx := hvalid.1
      rw [← hflightTransaction, htransaction] at htx
      simp only [Concrete.Transaction.key?, Option.some.injEq] at htx
      exact htx.trans hkey.symm
    let entry : WorkflowEntry := { request, instant := semanticTime }
    have hpendingTransaction :
        TransactionPending provenance.transaction =
          some (entry :: Concrete.pendingWorkflow rest) := by
      rw [htransaction]
      rfl
    have hpending :
        PendingEmbedded (entry :: Concrete.pendingWorkflow rest)
          (abstract.process .service).workflow.pending := by
      have hversion :
          flight.loaded.map (·.2) = physical.version flight.key := by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch
      exact (related.currentWorkflow physical address node op flight
        (entry :: Concrete.pendingWorkflow rest)
        haddress hphysical hnode hflight
        hphase hversion (by
          rw [← hflightTransaction]
          exact hpendingTransaction))
    have hentryMem :
        entry ∈ (abstract.process .service).workflow.pending :=
      hpending.subset (by simp)
    obtain ⟨abstractRest, hchoiceRaw, hpendingPerm⟩ :=
      pending_work_choice_of_mem
        { appConfig with unreliable := true }
        (abstract.process .service) now entry hentryMem
    let lifted :=
      Resonate.runWork { appConfig with unreliable := true }
        item semanticTime abstractRest (abstract.process .service)
    have hchoice :
        lifted ∈
          (Resonate.runTimeoutChoices
            { appConfig with unreliable := true } now
            (abstract.process .service)).val := by
      simpa [lifted, item, entry, WorkflowEntry.item] using hchoiceRaw
    have htransport :=
      work_cas_transport_rest hrep provenance htransaction hcurrent
        abstractRest
    have hconcreteTransport :=
      work_cas_transport hrep provenance htransaction hcurrent
    have hprovenanceContinuations :
        Concrete.pendingWorkflow provenance.continuations =
          Concrete.pendingWorkflow rest := by
      symm
      simpa [item, Resonate.runWork] using hconcreteTransport.2.2
    have hflightContinuations :
        Concrete.pendingWorkflow flight.continuations =
          Concrete.pendingWorkflow rest := by
      rw [← hcontinuations, hprovenanceContinuations]
    have hcontinuationsEmbedded :
        PendingEmbedded
          (Concrete.pendingWorkflow provenance.continuations)
          lifted.1.workflow.pending := by
      have hold := hpending.cancel_head hpendingPerm
      simpa [lifted, item, Resonate.runWork,
        hprovenanceContinuations] using hold
    have hworkflowNext :
        WorkflowAligned config
          (concrete.land .store now {
            state := .store (physical.commit key document)
            send := [(.node address,
              .storeReply { op, payload := reply })]
          })
          (abstract.land .service now {
            state := lifted.1
            send := Abstract.sends lifted.2
          }) := by
      apply workflowAligned_work_commit hreachable related.workflow hphysical
        haddress hnode hflight hphase
        (hflightTransaction.symm.trans htransaction) (by
          subst key
          simpa [hloaded] using provenance.expected_eq.trans hmatch)
        hflightContinuations document hkey
        {
          state := .store (physical.commit key document)
          send := [(.node address,
            .storeReply { op, payload := reply })]
        } rfl (hnoreply .written (.inl rfl)) (by
          intro replyAddress replyOp hsend
          simp at hsend
          exact ⟨hsend.1, hsend.2.1⟩) hpendingPerm
      simp [World.land, lifted, item, entry, Resonate.runWork]
    have hitemMem :=
      work_key_mem { appConfig with unreliable := true }
        item semanticTime abstractRest
          (abstract.process .service)
    rw [hitemKey] at hitemMem
    exact simulate_internal_committed_store hreachable related hphysical
      hrequest provenance hsnapshot hmatch
      (htransactionPending := hpendingTransaction)
      (hfailure := by simp [htransaction, Concrete.failureOutputs])
      haddress hnode hflight hphase hkey hloaded hflightTransaction
      houtputs hcontinuations lifted hchoice htransport
      hcontinuationsEmbedded hworkflowNext
      (work_keys_mono { appConfig with unreliable := true }
        item semanticTime abstractRest
          (abstract.process .service))
      (by simpa [lifted] using hitemMem)
      hreply htime hconcreteResult
  have hsweep
      {timer : Concrete.TimerKey} {instant : Time}
      {rest : List Concrete.PendingEntry}
      (htransaction :
        provenance.transaction = .sweep timer instant rest)
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
    have htarget : timer.target.key = key := by
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have htx := hvalid.1
      rw [← hflightTransaction, htransaction] at htx
      simp only [Concrete.Transaction.key?, Option.some.injEq] at htx
      exact htx.trans hkey.symm
    have hpendingTransaction :
        TransactionPending provenance.transaction =
          some (Concrete.pendingWorkflow rest) := by
      rw [htransaction]
      rfl
    have hpending :
        PendingEmbedded (Concrete.pendingWorkflow rest)
          (abstract.process .service).workflow.pending := by
      have hversion :
          flight.loaded.map (·.2) = physical.version flight.key := by
        subst key
        simpa [hloaded] using provenance.expected_eq.trans hmatch
      exact (related.currentWorkflow physical address node op flight
        (Concrete.pendingWorkflow rest)
        haddress hphysical hnode hflight
        hphase hversion (by
          rw [← hflightTransaction]
          exact hpendingTransaction))
    obtain ⟨sweepNode, hsweepNode, hsweeps⟩ :=
      reachable_nodes_sweeps_valid hreachable address haddress
    rw [hnode] at hsweepNode
    cases Concrete.Local.node.inj hsweepNode
    have hsweepValid :=
      hsweeps op flight hflight timer instant rest
        (hflightTransaction.symm.trans htransaction)
    have hkeyMem :
        key ∈ (abstract.process .service).store.keys := by
      apply hrep.relevantKeys
      rw [toAbstract_read_eq_loaded hcurrent]
      apply Selected.sweep_relevant
      simpa [htransaction] using provenance.selected
    have hinstant :
        instant ≤ now :=
      Nat.le_trans hsweepValid htime
    obtain ⟨lifted, added, hchoice, htransport, htransportOutputs,
        hprovenanceContinuations, habstractPending, hkeys, hliftedKey⟩ :=
      sweep_timeout_transport hrep provenance htransaction htarget hcurrent
        hinstant hkeyMem
    have hflightContinuations :
        Concrete.pendingWorkflow flight.continuations =
          Concrete.pendingWorkflow rest ++ added := by
      rw [← hcontinuations, hprovenanceContinuations]
    have hcontinuationsEmbedded :
        PendingEmbedded
          (Concrete.pendingWorkflow provenance.continuations)
          lifted.1.workflow.pending := by
      have hold := hpending.append_same added
      rw [hprovenanceContinuations]
      simpa [habstractPending] using hold
    have hworkflowNext :
        WorkflowAligned config
          (concrete.land .store now {
            state := .store (physical.commit key document)
            send := [(.node address,
              .storeReply { op, payload := reply })]
          })
          (abstract.land .service now {
            state := lifted.1
            send := Abstract.sends lifted.2
          }) := by
      apply workflowAligned_document_commit hreachable related.workflow
        hphysical haddress hnode hflight hphase
        (hflightTransaction.symm.trans htransaction) (by
          subst key
          simpa [hloaded] using provenance.expected_eq.trans hmatch)
        added hflightContinuations document hkey
        {
          state := .store (physical.commit key document)
          send := [(.node address,
            .storeReply { op, payload := reply })]
        } rfl (hnoreply .written (.inl rfl)) (by
          intro replyAddress replyOp hsend
          simp at hsend
          exact ⟨hsend.1, hsend.2.1⟩)
      simp [World.land, habstractPending]
    exact simulate_internal_committed_store hreachable related hphysical
      hrequest provenance hsnapshot hmatch
      (htransactionPending := hpendingTransaction)
      (hfailure := by simp [htransaction, Concrete.failureOutputs])
      haddress hnode hflight hphase hkey hloaded hflightTransaction
      houtputs hcontinuations lifted hchoice
      ⟨htransport, htransportOutputs⟩
      hcontinuationsEmbedded hworkflowNext
      hkeys hliftedKey
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
      · simp [Concrete.step, Concrete.storePut, hmatch,
          hflaky] at hresult
        rcases hresult with rfl | rfl | rfl
        · exact simulate_external_written_store hreachable related hphysical
            hrequest provenance hmatch htransaction hcurrent
            horigin haddress hnode hflight hphase hkey hflightTransaction
            houtputs htime
        · exact simulate_external_landed_failed_store hreachable related
            hphysical hflaky hrequest provenance hmatch
            htransaction hcurrent horigin haddress hnode hflight
            hflightTransaction htime
        · exact simulate_external_not_landed_failed_store hreachable related
            hphysical hflaky hrequest provenance hmatch
            htransaction horigin haddress hnode hflight hflightTransaction
            htime
      · have hflakyFalse : config.flaky = false := by
          cases ht : config.flaky <;> simp_all
        simp [Concrete.step, Concrete.storePut, hmatch,
          hflakyFalse, Outcomes.one] at hresult
        subst result
        exact simulate_external_written_store hreachable related hphysical
          hrequest provenance hmatch htransaction hcurrent
          horigin haddress hnode hflight hphase hkey hflightTransaction
          houtputs htime
  | work item instant rest =>
      have hvalid :=
        related.flights address node op flight haddress hnode hflight
      have hshape := hvalid.2.2
      rw [← hflightTransaction, htransaction, WorkShaped] at hshape
      obtain ⟨request, hitem⟩ := hshape
      subst item
      by_cases hflaky : config.flaky = true
      · simp [Concrete.step, Concrete.storePut, hmatch,
          hflaky] at hresult
        rcases hresult with rfl | rfl | rfl
        · exact hwork htransaction rfl (.inl rfl) (by
            simp [Concrete.step, Concrete.storePut, hmatch,
              hflaky])
        · exact hwork htransaction rfl (.inr rfl) (by
            simp [Concrete.step, Concrete.storePut, hmatch,
              hflaky])
        · exact hinternalFence
            (by simp [htransaction, Concrete.failureOutputs]) (by
              simp [Concrete.step, Concrete.storePut, hmatch,
                hflaky])
      · have hflakyFalse : config.flaky = false := by
          cases ht : config.flaky <;> simp_all
        simp [Concrete.step, Concrete.storePut, hmatch,
          hflakyFalse, Outcomes.one] at hresult
        subst result
        exact hwork htransaction rfl (.inl rfl) (by
          simp [Concrete.step, Concrete.storePut, hmatch,
            hflakyFalse, Outcomes.one])
  | sweep timer instant rest =>
      by_cases hflaky : config.flaky = true
      · simp [Concrete.step, Concrete.storePut, hmatch,
          hflaky] at hresult
        rcases hresult with rfl | rfl | rfl
        · exact hsweep htransaction (.inl rfl) (by
            simp [Concrete.step, Concrete.storePut, hmatch,
              hflaky])
        · exact hsweep htransaction (.inr rfl) (by
            simp [Concrete.step, Concrete.storePut, hmatch,
              hflaky])
        · exact hinternalFence
            (by simp [htransaction, Concrete.failureOutputs]) (by
              simp [Concrete.step, Concrete.storePut, hmatch,
                hflaky])
      · have hflakyFalse : config.flaky = false := by
          cases ht : config.flaky <;> simp_all
        simp [Concrete.step, Concrete.storePut, hmatch,
          hflakyFalse, Outcomes.one] at hresult
        subst result
        exact hsweep htransaction (.inl rfl) (by
          simp [Concrete.step, Concrete.storePut, hmatch,
            hflakyFalse, Outcomes.one])
theorem simulate_store_process
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
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
      {nextPhysical : Concrete.Store}
      (hmember :
        inert ∈
          (Concrete.step appConfig config .store (.store physical)
            now event).val)
      (hstate : inert.state = .store nextPhysical)
      (hvalues : nextPhysical.values = physical.values)
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
        hmember hstate hvalues hreplies hnoWritten hnoFailed,
      rfl⟩
  cases event with
  | timeout =>
      simp [Concrete.step, Outcomes.one] at hresult
      subst result
      exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
        (by simp) (by simp) (by simp)
  | receive sender message =>
      cases message with
      | request call =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
            (by simp) (by simp) (by simp)
      | output output =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
            (by simp) (by simp) (by simp)
      | storeReply reply =>
          simp [Concrete.step, Outcomes.one] at hresult
          subst result
          exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
            (by simp) (by simp) (by simp)
      | storeRequest rpc =>
          obtain ⟨op, payload⟩ := rpc
          cases payload with
          | get key =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | put key document expectedVersion =>
              obtain ⟨address, rfl⟩ :=
                reachable_store_request_sender hreachable hvalid
              by_cases hmatch :
                  expectedVersion = physical.version key
              · exact simulate_matching_put_store hreachable related
                  hphysical hvalid hmatch htime hresult
              · simp [Concrete.step, Concrete.storePut, hmatch,
                  Outcomes.one] at hresult
                subst result
                exact hinert (by
                  simp [Concrete.step, Concrete.storePut, hmatch,
                    Outcomes.one]) rfl rfl
                  (by simp) (by simp) (by simp)
          | armTimer timer =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | deleteTimer timer =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | deleteTimers timers =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | listTimers through =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | announce announcement =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | listAnnouncements =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | getMembership =>
              simp [Concrete.step, Outcomes.one] at hresult
              subst result
              exact hinert (by simp [Concrete.step, Outcomes.one]) rfl rfl
                (by simp) (by simp) (by simp)
          | putMembership expected next =>
              simp only [Concrete.step] at hresult
              split at hresult <;> simp [Outcomes.one] at hresult
              all_goals subst result
              all_goals
                exact hinert (by simp_all [Concrete.step, Outcomes.one])
                  rfl rfl (by simp) (by simp) (by simp)

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
    (hcurrent : True)
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
            (TransactionPending flight.transaction = none ∨ True)) ∧
        ((Concrete.Pid.store, .node currentAddress,
            .storeReply { op, payload := .failed }) ∈
              (concrete.land (.node address) now result).network →
          Covered abstractNext
            (Concrete.failureOutputs flight.transaction)))
    (hcleanup :
      ∀ currentAddress currentNode op outputs,
        currentAddress ∈ nodes →
        (concrete.land (.node address) now result).process
            (.node currentAddress) = .node currentNode →
        (op, Concrete.Control.cleanup outputs) ∈ currentNode.controls →
        Covered abstractNext outputs) :
    Related nodes appConfig config
      (concrete.land (.node address) now result) abstractNext := by
  have hstep :
      Step (CModel nodes appConfig) config concrete
        (.process (.node address) now event result.send)
        (concrete.land (.node address) now result) :=
    Step.process htime haddress hvalid (hnode ▸ hresult)
  apply related_after_land related hreachable haddress hstep
      habstractTime hnetwork hkeys hstore hworkflow hcurrent
      hnewRequest hnewOutput
  · intro target op hsend
    exact (node_step_no_store_reply hresult hsend).elim
  · intro target op hsend
    exact (node_step_no_store_reply hresult hsend).elim
  · exact hactive
  · exact hcleanup

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
  · apply workflowAligned_node_land (nextNode := node)
      related.workflow haddress hnode
      {
        state := .node node
        send := []
      } rfl
    · intro store part hpart
      exact hpart
    · intro parts hcommitted op flight hflight hphase hreply
      exact hcommitted address haddress node op flight hnode hflight hphase
        hreply
    · simp
  · trivial
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
  · intro currentAddress currentNode op outputs haddress hnodeNext hmem
    exact related.cleanupCovered currentAddress currentNode op outputs
      haddress (by simpa [hprocessEq] using hnodeNext) hmem

/-- Reachable flights are never in the deleting phase. The transition
system does not construct it; cleanup runs through `continueCleanup`. -/
def NodeNoDeleting (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights → flight.phase ≠ .deleting

def NodesNoDeleting
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧ NodeNoDeleting node

set_option maxHeartbeats 2000000 in
theorem node_step_no_deleting
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    (hphases : NodeNoDeleting node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    NodeNoDeleting next := by
  intro op flight hflight
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeNoDeleting, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishNode, Concrete.cleanupFlight, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals try decide
      all_goals try
        exact hphases op flight hflight
      all_goals try
        subst next
        simp only [finishNode_flights, noteArmed_flights] at hflight
        exact hphases _ _ (List.mem_filter.mp hflight).1
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [NodeNoDeleting, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup, Concrete.finishNode,
          Concrete.cleanupFlight, Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals try decide
      all_goals try
        exact hphases op flight hflight
      all_goals try
        subst next
        simp only [finishNode_flights, noteArmed_flights, cachePut_flights,
          cacheInvalidate_flights] at hflight
        first
        | exact hphases _ _ hflight
        | exact hphases _ _ (List.mem_filter.mp hflight).1
      all_goals first | contradiction | grind

theorem nodesNoDeleting_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesNoDeleting (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by simp [NodeNoDeleting]⟩

theorem nodesNoDeleting_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hvalid : NodesValid (nodes := nodes) (appConfig := appConfig) world)
    (hinvariant : NodesNoDeleting world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesNoDeleting next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalidEvent hresult =>
      intro address haddress
      obtain ⟨node, hnode, hphases⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨validNode, hvalidNode, hnodeValid⟩ :=
          hvalid address haddress
        rw [hnode] at hvalidNode
        cases Concrete.Local.node.inj hvalidNode
        obtain ⟨after, hstate, _⟩ :=
          node_step_valid hnodeValid (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate],
          node_step_no_deleting hphases (hnode ▸ hresult) hstate⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], hphases⟩

theorem reachable_nodes_no_deleting
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesNoDeleting world := by
  induction hreachable with
  | init hinit => exact nodesNoDeleting_initial hinit
  | step hreachable hstep ih =>
      exact nodesNoDeleting_step (reachable_nodes_valid hreachable) ih hstep

theorem reachable_node_no_deleting
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node) :
    NodeNoDeleting node := by
  obtain ⟨node', hnode', hphases⟩ :=
    reachable_nodes_no_deleting hreachable address haddress
  rw [hnode] at hnode'
  cases Concrete.Local.node.inj hnode'
  exact hphases


/-- A loading flight has not chosen outputs yet. `start` builds `selected`
empty, and only the arming or writing transition fills it. -/
def NodeLoadingQuiet (node : Concrete.Node) : Prop :=
  ∀ op flight, (op, flight) ∈ node.flights →
    flight.phase = .loading → flight.selected = []

def NodesLoadingQuiet
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧ NodeLoadingQuiet node

set_option maxHeartbeats 2000000 in
theorem node_step_loading_quiet
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    (hquiet : NodeLoadingQuiet node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    NodeLoadingQuiet next := by
  intro op flight hflight
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeLoadingQuiet, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishNode, Concrete.cleanupFlight, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals try decide
      all_goals try
        exact hquiet op flight hflight
      all_goals try
        subst next
        simp only [finishNode_flights, noteArmed_flights] at hflight
        exact hquiet _ _ (List.mem_filter.mp hflight).1
      all_goals try
        intro hphase
        first | rfl | cases hphase
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [NodeLoadingQuiet, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup, Concrete.finishNode,
          Concrete.cleanupFlight, Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals try decide
      all_goals try
        exact hquiet op flight hflight
      all_goals try
        subst next
        simp only [finishNode_flights, noteArmed_flights, cachePut_flights,
          cacheInvalidate_flights] at hflight
        first
        | exact hquiet _ _ hflight
        | exact hquiet _ _ (List.mem_filter.mp hflight).1
      all_goals try
        intro hphase
        first | rfl | cases hphase
      all_goals first | contradiction | grind



theorem nodesLoadingQuiet_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesLoadingQuiet (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by simp [NodeLoadingQuiet]⟩

theorem nodesLoadingQuiet_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hvalid : NodesValid (nodes := nodes) (appConfig := appConfig) world)
    (hinvariant : NodesLoadingQuiet world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesLoadingQuiet next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalidEvent hresult =>
      intro address haddress
      obtain ⟨node, hnode, hquiet⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨validNode, hvalidNode, hnodeValid⟩ :=
          hvalid address haddress
        rw [hnode] at hvalidNode
        cases Concrete.Local.node.inj hvalidNode
        obtain ⟨after, hstate, _⟩ :=
          node_step_valid hnodeValid (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate],
          node_step_loading_quiet hquiet (hnode ▸ hresult) hstate⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], hquiet⟩

theorem reachable_nodes_loading_quiet
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesLoadingQuiet world := by
  induction hreachable with
  | init hinit => exact nodesLoadingQuiet_initial hinit
  | step hreachable hstep ih =>
      exact nodesLoadingQuiet_step (reachable_nodes_valid hreachable) ih hstep

theorem reachable_node_loading_quiet
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node) :
    NodeLoadingQuiet node := by
  obtain ⟨node', hnode', hquiet⟩ :=
    reachable_nodes_loading_quiet hreachable address haddress
  rw [hnode] at hnode'
  cases Concrete.Local.node.inj hnode'
  exact hquiet


inductive CleanupSource
    (node : Concrete.Node) (event : Event Concrete.Pid Concrete.Msg)
    (op : Concrete.OpId) (outputs : List Output) : Prop
  | kept :
      (op, .cleanup outputs) ∈ node.controls →
      CleanupSource node event op outputs
  | vacant :
      outputs = [] →
      CleanupSource node event op outputs
  | parkedWriting (flightOp : Concrete.OpId) (flight : Concrete.Flight) :
      (flightOp, flight) ∈ node.flights →
      outputs = flight.selected →
      flight.phase = .writing →
      event = .receive .store
        (.storeReply { op := flightOp, payload := .written }) →
      CleanupSource node event op outputs
  | parkedLoading (flightOp : Concrete.OpId) (flight : Concrete.Flight) :
      (flightOp, flight) ∈ node.flights →
      outputs = flight.selected →
      flight.phase = .loading →
      CleanupSource node event op outputs
  | parkedDeleting (flightOp : Concrete.OpId) (flight : Concrete.Flight) :
      (flightOp, flight) ∈ node.flights →
      outputs = flight.selected →
      flight.phase = .deleting →
      CleanupSource node event op outputs

/-- `remaining` is the node `takeFlight` returns, so its controls are the
original node's controls. -/
theorem CleanupSource.kept_takeFlight
    {node : Concrete.Node} {event : Event Concrete.Pid Concrete.Msg}
    {cleanupOp flightOp : Concrete.OpId} {outputs : List Output}
    {taken : Option Concrete.Flight} {remaining stateNode : Concrete.Node}
    (ht : node.takeFlight flightOp = (taken, remaining))
    (hcontrols : stateNode.controls = remaining.controls)
    (hmem : (cleanupOp, .cleanup outputs) ∈ stateNode.controls) :
    CleanupSource node event cleanupOp outputs := by
  have hremaining : remaining = (node.takeFlight flightOp).2 :=
    (congrArg Prod.snd ht).symm
  exact .kept (by simpa [hcontrols, hremaining, takeFlight_controls] using hmem)

/-- A cleanup entry on the node returned by `takeControl` was already present. -/
theorem CleanupSource.kept_takeControl
    {node : Concrete.Node} {event : Event Concrete.Pid Concrete.Msg}
    {cleanupOp flightOp : Concrete.OpId} {outputs : List Output}
    {taken : Option Concrete.Control} {controlled stateNode : Concrete.Node}
    (hc : node.takeControl flightOp = (taken, controlled))
    (hcontrols : stateNode.controls = controlled.controls)
    (hmem : (cleanupOp, .cleanup outputs) ∈ stateNode.controls) :
    CleanupSource node event cleanupOp outputs := by
  have hcontrolled : controlled = (node.takeControl flightOp).2 :=
    (congrArg Prod.snd hc).symm
  exact .kept (takeControl_cleanup_kept (by
    simpa [hcontrols, hcontrolled] using hmem))

set_option maxHeartbeats 2000000 in
theorem step_cleanup_source
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    {op : Concrete.OpId} {outputs : List Output}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next)
    (hmem : (op, .cleanup outputs) ∈ next.controls) :
    CleanupSource node event op outputs := by
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      split at hresult
      · simp [Outcomes.one] at hresult
        subst result
        cases Concrete.Local.node.inj hstate
        exact .kept hmem
      · cases hp : node.pending with
        | cons entry rest =>
            simp only [hp, Outcomes.one, List.mem_singleton] at hresult
            subst result
            cases entry with
            | occurrence request instant =>
                rcases start_cleanup_mem (appConfig := appConfig)
                    (node := { node with pending := [] })
                    (transaction :=
                      .work (.occurrence request instant) instant rest)
                    (key := .origin request.id.origin)
                    (address := address) (fired := none) hstate hmem with
                  hkept | hempty
                · exact .kept hkept
                · exact .vacant hempty
        | nil =>
            simp only [hp] at hresult
            split at hresult
            · simp [Outcomes.one] at hresult
              subst result
              exact .kept (beginMembershipRefresh_cleanup_mem
                node address now hstate hmem)
            · let wheel := node.wheel.takeDue now config.fireConcurrency
              cases hb : wheel.beginOne with
              | some pair =>
                  obtain ⟨timer, nextWheel⟩ := pair
                  have hb' :
                      (node.wheel.takeDue now config.fireConcurrency).beginOne =
                        some (timer, nextWheel) := by
                    simpa [wheel] using hb
                  rw [hb'] at hresult
                  simp only [Option.some.injEq, Prod.mk.injEq] at hb' hresult
                  subst_vars
                  split at hresult
                  · simp [Outcomes.one, List.mem_singleton] at hresult
                    subst result
                    rcases start_cleanup_mem (appConfig := appConfig)
                        (fired := some timer) hstate hmem with
                      hkept | hempty
                    · exact .kept hkept
                    · exact .vacant hempty
                  · simp [Outcomes.one, List.mem_singleton] at hresult
                    subst result
                    cases Concrete.Local.node.inj hstate
                    exact .kept hmem
              | none =>
                  simp only [wheel, hb] at hresult
                  split at hresult
                  · simp [Outcomes.one, List.mem_singleton] at hresult
                    subst result
                    have hstate' :
                        (Concrete.beginTimerList { node with wheel } config now
                          (.relist node.wheel.closedThrough)).state =
                          Concrete.Local.node next := by
                      simpa [wheel, hp] using hstate
                    exact .kept (beginTimerList_cleanup_mem
                      (node := { node with wheel }) hstate' hmem)
                  · split at hresult
                    · simp [Outcomes.one, List.mem_singleton] at hresult
                      subst result
                      have hstate' :
                          (Concrete.beginTimerList { node with wheel } config now
                            .extend).state = Concrete.Local.node next := by
                        simpa [wheel, hp] using hstate
                      exact .kept (beginTimerList_cleanup_mem
                        (node := { node with wheel }) hstate' hmem)
                    · simp [Outcomes.one, List.mem_singleton] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept hmem
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals try
        simp [Outcomes.one] at hresult
        subst result
        cases Concrete.Local.node.inj hstate
        exact .kept hmem
      case outside.request call =>
        split at hresult
        · simp [Outcomes.one] at hresult
          subst result
          cases Concrete.Local.node.inj hstate
          exact .kept hmem
        · cases hk : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hk, Concrete.pureExternal, Outcomes.one] at hresult
              subst result
              cases Concrete.Local.node.inj hstate
              exact .kept hmem
          | some key =>
              simp only [hk] at hresult
              split at hresult
              · simp [hk, Outcomes.one] at hresult
                subst result
                rcases start_cleanup_mem (appConfig := appConfig)
                    (node := node) (transaction := .external call)
                    (key := key) (address := address) (fired := none)
                    hstate hmem with
                  hkept | hempty
                · exact .kept hkept
                · exact .vacant hempty
              · simp [hk, Outcomes.one] at hresult
                subst result
                cases Concrete.Local.node.inj hstate
                exact .kept hmem
      case store.storeReply rpc =>
        obtain ⟨flightOp, payload⟩ := rpc
        cases payload with
        | got key loaded =>
            cases ht : node.takeFlight flightOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact .kept hmem
              | some flight =>
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : flight.phase with
                    | loading =>
                        let loaded' := heq ▸ loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut flight.key
                                { document, version }
                          | none => remaining.cacheInvalidate flight.key
                        simp [ht, hp, loaded', cached, Outcomes.one] at hresult
                        subst result
                        rcases decide_cleanup_mem appConfig cached flight
                            loaded' hstate hmem with
                          hkept | hselected
                        · exact .kept_takeFlight ht (by
                            simp only [cached]
                            cases hloaded : loaded' <;>
                              simp [hloaded, cachePut_controls,
                                cacheInvalidate_controls]) hkept
                        · exact .parkedLoading flightOp flight
                            (takeFlight_some_mem ht) hselected hp
                    | arming | writing | deleting =>
                        simp [ht, hp, Outcomes.one] at hresult
                        subst result
                        cases Concrete.Local.node.inj hstate
                        exact .kept_takeFlight ht rfl hmem
                  next _ =>
                    simp [ht, Outcomes.one] at hresult
                    subst result
                    cases Concrete.Local.node.inj hstate
                    exact .kept_takeFlight ht rfl hmem
        | written =>
            cases ht : node.takeFlight flightOp with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact .kept hmem
              | some flight =>
                  cases hp : flight.phase with
                  | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      rcases committedFlight_cleanup_mem hstate hmem with
                        hkept | hselected
                      · exact .kept_takeFlight ht (by simp [noteArmed_controls])
                          hkept
                      · exact .parkedWriting flightOp flight
                          (takeFlight_some_mem ht) hselected hp rfl
                  | loading | arming | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeFlight ht rfl hmem
        | done =>
            cases ht : node.takeFlight flightOp with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  cases hp : flight.phase with
                  | arming =>
                      cases hd : flight.document with
                      | none =>
                          simp [ht, hp, hd, Outcomes.one] at hresult
                          subst result
                          cases Concrete.Local.node.inj hstate
                          exact .kept_takeFlight ht rfl hmem
                      | some document =>
                          simp [ht, hp, hd, Outcomes.one] at hresult
                          subst result
                          cases Concrete.Local.node.inj hstate
                          exact .kept_takeFlight ht (by simp [await_controls])
                            hmem
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      rcases continueCleanup_cleanup_mem hstate hmem with
                        hkept | hselected
                      · exact .kept_takeFlight ht rfl hkept
                      · exact .parkedDeleting flightOp flight
                          (takeFlight_some_mem ht) hselected hp
                  | loading | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeFlight ht rfl hmem
              | none =>
                  cases hc : node.takeControl flightOp with
                  | mk taken controlled =>
                    cases taken with
                    | none =>
                        simp [ht, hc, Outcomes.one] at hresult
                        subst result
                        cases Concrete.Local.node.inj hstate
                        exact .kept_takeControl hc rfl hmem
                    | some ctrl =>
                        cases ctrl with
                        | announced instant =>
                            simp [ht, hc, Outcomes.one] at hresult
                            subst result
                            cases Concrete.Local.node.inj hstate
                            rcases awaitControl_cleanup_mem hmem with
                              hkept | ⟨_, hbad⟩
                            · exact .kept_takeControl hc rfl hkept
                            · cases hbad
                        | membershipWrite instant =>
                            simp [ht, hc, Outcomes.one]
                              at hresult
                            subst result
                            exact .kept_takeControl hc rfl (refreshEnded_cleanup_mem hstate hmem)
                        | announcements _ | membership _ _
                        | timerList _ _ _ | cleanup _ =>
                            simp [ht, hc, Outcomes.one] at hresult
                            subst result
                            cases Concrete.Local.node.inj hstate
                            exact .kept_takeControl hc rfl hmem
        | announcements values =>
            cases hc : node.takeControl flightOp with
            | mk taken controlled =>
              cases taken with
              | none =>
                  simp [hc, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact .kept_takeControl hc rfl hmem
              | some ctrl =>
                  cases ctrl with
                  | announcements instant =>
                      simp [hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      rcases awaitControl_cleanup_mem hmem with
                        hkept | ⟨_, hbad⟩
                      · exact .kept_takeControl hc rfl hkept
                      · cases hbad
                  | announced _ | membership _ _ | membershipWrite _
                  | timerList _ _ _ | cleanup _ =>
                      simp [hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeControl hc rfl hmem
        | membership configuration version =>
            simp only [Concrete.step] at hresult
            cases hc : node.takeControl flightOp with
            | mk taken controlled =>
              cases taken with
              | none =>
                  simp [hc, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact .kept_takeControl hc rfl hmem
              | some ctrl =>
                  cases ctrl with
                  | membership instant live =>
                      simp only [hc] at hresult
                      split at hresult
                      · simp [hc, Outcomes.one]
                          at hresult
                        subst result
                        let view : Concrete.MembershipView := {
                          epoch := configuration.epoch
                          members := configuration.members
                          version
                          lastRead := instant
                          readAny := true
                        }
                        exact .kept_takeControl hc rfl
                          (refreshEnded_cleanup_mem
                            (node := { controlled with membership := view })
                            hstate hmem)
                      · simp [hc, Outcomes.one] at hresult
                        subst result
                        cases Concrete.Local.node.inj hstate
                        rcases awaitControl_cleanup_mem hmem with
                          hkept | ⟨_, hbad⟩
                        · exact .kept_takeControl hc rfl hkept
                        · cases hbad
                  | announced _ | announcements _ | membershipWrite _
                  | timerList _ _ _ | cleanup _ =>
                      simp [hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeControl hc rfl hmem
        | timers keys =>
            cases hc : node.takeControl flightOp with
            | mk taken controlled =>
              cases taken with
              | none =>
                  simp [hc, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact .kept_takeControl hc rfl hmem
              | some ctrl =>
                  cases ctrl with
                  | timerList _ _ _ =>
                      simp [hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeControl hc rfl hmem
                  | announced _ | announcements _ | membership _ _
                  | membershipWrite _ | cleanup _ =>
                      simp [hc, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeControl hc rfl hmem
        | conflict =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight flightOp with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  cases Concrete.Local.node.inj hstate
                  exact .kept_takeFlight ht rfl hmem
              | none =>
                  cases hc : node.takeControl flightOp with
                  | mk control controlled =>
                    cases control with
                    | none =>
                        simp [ht, hc, Outcomes.one] at hresult
                        subst result
                        cases Concrete.Local.node.inj hstate
                        exact .kept_takeControl hc rfl hmem
                    | some ctrl =>
                        cases ctrl with
                        | membershipWrite instant =>
                            simp [ht, hc, Outcomes.one]
                              at hresult
                            subst result
                            exact .kept_takeControl hc rfl (refreshEnded_cleanup_mem hstate hmem)
                        | announced _ | announcements _ | membership _ _
                        | timerList _ _ _ | cleanup _ =>
                            simp [ht, hc, Outcomes.one] at hresult
                            subst result
                            cases Concrete.Local.node.inj hstate
                            exact .kept_takeControl hc rfl hmem
        | failed =>
            simp only [Concrete.step] at hresult
            cases ht : node.takeFlight flightOp with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  cases hp : flight.phase with
                  | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      rcases continueCleanup_cleanup_mem hstate hmem with
                        hkept | hselected
                      · exact .kept_takeFlight ht rfl hkept
                      · exact .parkedDeleting flightOp flight
                          (takeFlight_some_mem ht) hselected hp
                  | loading | arming | writing =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      cases Concrete.Local.node.inj hstate
                      exact .kept_takeFlight ht rfl hmem
              | none =>
                  cases hc : node.takeControl flightOp with
                  | mk taken controlled =>
                    cases taken with
                    | none =>
                        simp [ht, hc, Outcomes.one] at hresult
                        subst result
                        cases Concrete.Local.node.inj hstate
                        exact .kept_takeControl hc rfl hmem
                    | some ctrl =>
                        cases ctrl with
                        | announced _ | announcements _ | membership _ _
                        | membershipWrite _ | timerList _ _ _ | cleanup _ =>
                            simp [ht, hc, Outcomes.one] at hresult
                            subst result
                            cases Concrete.Local.node.inj hstate
                            exact .kept_takeControl hc rfl hmem

theorem cleanup_mem_covered
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract abstractNext : World AModel}
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node next : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    (hnoDeleting : NodeNoDeleting node)
    (hquiet : NodeLoadingQuiet node)
    {op : Concrete.OpId} {outputs : List Output}
    (hmem : (op, .cleanup outputs) ∈ next.controls)
    (hcover : Covered abstract outputs → Covered abstractNext outputs)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    (hvalid : event.Valid concrete (.node address))
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    Covered abstractNext outputs := by
  cases step_cleanup_source hresult hstate hmem with
    | kept hkept =>
        exact hcover (related.cleanupCovered address node op outputs haddress
          hnode hkept)
    | vacant hempty =>
        intro output houtput
        cases hempty ▸ houtput
    | parkedWriting flightOp flight hflight houtputs _ hevent =>
        have hreply :
            (Concrete.Pid.store, .node address,
              .storeReply { op := flightOp, payload := .written }) ∈
              concrete.network := by
          cases hevent
          simpa [Event.Valid] using hvalid
        obtain ⟨hwritten, _⟩ :=
          related.activeReplies address node flightOp flight haddress hnode
            hflight
        obtain ⟨_, hcovered, _⟩ := hwritten hreply
        exact hcover (houtputs.symm ▸ hcovered)
    | parkedLoading flightOp flight hflight houtputs hphase =>
        intro output houtput
        cases hquiet flightOp flight hflight hphase ▸ houtputs.symm ▸ houtput
    | parkedDeleting flightOp flight hflight _ hphase =>
        exact absurd hphase (hnoDeleting flightOp flight hflight)

theorem related_after_metadata_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node nextNode : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node nextNode)
    (hflights : nextNode.flights = node.flights)
    (hpending : nextNode.pending = node.pending)
    (hnoRequest :
      ∀ target call, (target, Concrete.Msg.request call) ∉ result.send)
    (hnoOutput :
      ∀ output, (.outside, Concrete.Msg.output output) ∉ result.send) :
    Related nodes appConfig config
      (concrete.land (.node address) now result) abstract := by
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult (Nat.le_trans related.time htime)
      (fun _ h => h) (fun _ h => h)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical, hrep⟩
  · apply workflowAligned_node_land (nextNode := nextNode)
      related.workflow haddress hnode result hstate
    · intro store part hpart
      simpa [NodeWorkflowPart, hflights, hpending] using hpart
    · intro parts hcommitted op flight hflight hphase hreply
      apply hcommitted address haddress node op flight hnode
      · simpa [hflights] using hflight
      · exact hphase
      · exact hreply
    · intro target op hsend
      exact node_step_no_store_reply hresult hsend
  · trivial
  · intro target call hsend
    exact (hnoRequest (.node target) call hsend).elim
  · intro output hsend
    exact (hnoOutput output hsend).elim
  · intro currentAddress currentNode op flight hcurrentAddress hcurrentNode
      hflight
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [show
        (concrete.land (.node address) now result).process (.node address) =
          result.state by simp [World.land],
        hstate] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      obtain ⟨hwritten, hfailed⟩ :=
        related.activeReplies address node op flight haddress hnode
          (by simpa [hflights] using hflight)
      constructor
      · intro hreply
        exact hwritten (by
          simpa [World.land] using hreply)
      · intro hreply
        exact hfailed (by
          simpa [World.land] using hreply)
    · obtain ⟨hwritten, hfailed⟩ :=
        related.activeReplies currentAddress currentNode op flight
          hcurrentAddress (by simpa [World.land, heq] using hcurrentNode)
          hflight
      constructor
      · intro hreply
        exact hwritten (by simpa [World.land] using hreply)
      · intro hreply
        exact hfailed (by simpa [World.land] using hreply)
  · intro currentAddress currentNode op outputs haddress hnodeNext hmem
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [show
        (concrete.land (.node address) now result).process (.node address) =
          result.state by simp [World.land],
        hstate] at hnodeNext
      cases Concrete.Local.node.inj hnodeNext
      exact cleanup_mem_covered related haddress hnode
        (reachable_node_no_deleting hreachable haddress hnode)
        (reachable_node_loading_quiet hreachable haddress hnode)
        hmem (fun h => h) hvalid hresult hstate
    · exact related.cleanupCovered currentAddress currentNode op outputs
        haddress (by simpa [World.land, heq] using hnodeNext) hmem

set_option maxHeartbeats 2000000 in
theorem node_step_attempts
    {appConfig : Resonate.Config} {config : Concrete.Config}
    {address : Addr} {node next : Concrete.Node}
    (hattempts : NodeAttempts node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node next) :
    NodeAttempts next := by
  intro op flight hflight
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals
        simp_all [NodeAttempts, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.beginMembershipRefresh,
          Concrete.beginTimerList, Concrete.refreshEnded,
          Concrete.Node.await, Concrete.Node.awaitControl,
          Concrete.committedFlight, Concrete.continueCleanup,
          Concrete.finishNode, Concrete.cleanupFlight, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals try rfl
      all_goals try
        exact hattempts op flight hflight
      all_goals try
        subst next
        simp only [finishNode_flights, noteArmed_flights] at hflight
        exact hattempts _ _ (List.mem_filter.mp hflight).1
      all_goals first | contradiction | grind
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      all_goals repeat' first | split at hresult
      all_goals
        simp_all [NodeAttempts, Concrete.start, Concrete.decide,
          Concrete.writeCandidate, Concrete.retry, Concrete.pureExternal,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded, Concrete.Node.takeFlight,
          Concrete.Node.takeControl, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.committedFlight,
          Concrete.continueCleanup, Concrete.finishNode,
          Concrete.cleanupFlight, Concrete.Node.cachePut,
          Concrete.Node.cacheInvalidate, Concrete.sendOutputs, Outcomes.one]
      all_goals repeat' first | split at hresult
      all_goals try simp_all [Concrete.Node.await, Concrete.Node.awaitControl]
      all_goals try rfl
      all_goals try
        exact hattempts op flight hflight
      all_goals try
        subst next
        simp only [finishNode_flights, noteArmed_flights, cachePut_flights,
          cacheInvalidate_flights] at hflight
        first
        | exact hattempts _ _ hflight
        | exact hattempts _ _ (List.mem_filter.mp hflight).1
      all_goals first | contradiction | grind

def NodesAttempts
    {nodes : List Addr} {appConfig : Resonate.Config}
    (world : World (CModel nodes appConfig)) : Prop :=
  ∀ address, address ∈ nodes →
    ∃ node,
      world.process (.node address) = .node node ∧ NodeAttempts node

theorem nodesAttempts_initial
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {process : Concrete.Pid → Concrete.Local}
    (hinit : (CModel nodes appConfig).init config process) :
    NodesAttempts (nodes := nodes) (appConfig := appConfig)
      (World.initial process) := by
  intro address haddress
  exact ⟨{}, hinit.2.2 address haddress, by simp [NodeAttempts]⟩

theorem nodesAttempts_step
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world next : World (CModel nodes appConfig)}
    {label : Label (CModel nodes appConfig)}
    (hvalid : NodesValid (nodes := nodes) (appConfig := appConfig) world)
    (hinvariant : NodesAttempts world)
    (hstep : Step (CModel nodes appConfig) config world label next) :
    NodesAttempts next := by
  cases hstep with
  | inject => exact hinvariant
  | outside => exact hinvariant
  | @process pid now event result htime hprocess hvalidEvent hresult =>
      intro address haddress
      obtain ⟨node, hnode, hattempts⟩ := hinvariant address haddress
      by_cases hp : pid = .node address
      · subst pid
        obtain ⟨validNode, hvalidNode, hnodeValid⟩ :=
          hvalid address haddress
        rw [hnode] at hvalidNode
        cases Concrete.Local.node.inj hvalidNode
        obtain ⟨after, hstate, _⟩ :=
          node_step_valid hnodeValid (hnode ▸ hresult)
        exact ⟨after, by simp [World.land, hstate],
          node_step_attempts hattempts (hnode ▸ hresult) hstate⟩
      · exact ⟨node, by simp [World.land, Ne.symm hp, hnode], hattempts⟩

theorem reachable_nodes_attempts
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world) :
    NodesAttempts world := by
  induction hreachable with
  | init hinit => exact nodesAttempts_initial hinit
  | step hreachable hstep ih =>
      exact nodesAttempts_step (reachable_nodes_valid hreachable) ih hstep

theorem reachable_node_attempts
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {world : World (CModel nodes appConfig)}
    (hreachable : Reachable (CModel nodes appConfig) config world)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : world.process (.node address) = .node node) :
    NodeAttempts node := by
  obtain ⟨node', hnode', hattempts⟩ :=
    reachable_nodes_attempts hreachable address haddress
  rw [hnode] at hnode'
  cases Concrete.Local.node.inj hnode'
  exact hattempts

theorem perm_release_flatMap
    {nodes : List Addr} {parts : Addr → List WorkflowEntry}
    {address : Addr} {part' released slack : List WorkflowEntry}
    (hnodup : nodes.Nodup) (haddress : address ∈ nodes)
    (hparts : parts address = part' ++ released) :
    List.Perm (nodes.flatMap parts ++ slack)
      (nodes.flatMap (fun current =>
          if current = address then part' else parts current) ++
        (released ++ slack)) := by
  obtain ⟨before, after, rfl⟩ := List.append_of_mem haddress
  simp only [List.nodup_append, List.nodup_cons] at hnodup
  have hbefore : address ∉ before := by
    intro hmem
    exact hnodup.2.2 address hmem address (by simp) rfl
  have hafter : address ∉ after := hnodup.2.1.1
  let parts' : Addr → List WorkflowEntry := fun current =>
    if current = address then part' else parts current
  have hbeforeParts : before.flatMap parts' = before.flatMap parts := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro current hcurrent
    have hne : current ≠ address := fun heq => hbefore (heq ▸ hcurrent)
    simp [parts', hne]
  have hafterParts : after.flatMap parts' = after.flatMap parts := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro current hcurrent
    have hne : current ≠ address := fun heq => hafter (heq ▸ hcurrent)
    simp [parts', hne]
  have hmove :
      List.Perm (released ++ after.flatMap parts)
        (after.flatMap parts ++ released) :=
    List.perm_append_comm
  simpa [List.flatMap_append, parts', hbeforeParts, hafterParts, hparts,
    List.append_assoc] using
    ((hmove.append_right slack).append_left
      (before.flatMap parts ++ part'))

theorem related_after_stuttering_node_to
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract abstractNext : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node nextNode : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    (hnodeValid : NodeValid appConfig node)
    (hserial : NodeSerial node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node nextNode)
    (habstractTime : abstractNext.now ≤ now)
    (hservice :
      abstractNext.process .service = abstract.process .service)
    (hnetwork :
      ∀ message ∈ abstract.network, message ∈ abstractNext.network)
    (hcover :
      ∀ outputs, Covered abstract outputs → Covered abstractNext outputs)
    (houtputs :
      ∀ output,
        (.outside, Concrete.Msg.output output) ∈ result.send →
        (Abstract.Pid.service, .outside, Message.output output) ∈
          abstractNext.network) :
    Related nodes appConfig config
      (concrete.land (.node address) now result) abstractNext := by
  have replyOld
      {currentAddress : Addr} {op : Concrete.OpId}
      {payload : Concrete.StoreReply}
      (hreply :
        (Concrete.Pid.store, .node currentAddress,
          .storeReply { op, payload }) ∈
            (concrete.land (.node address) now result).network) :
      (Concrete.Pid.store, .node currentAddress,
        .storeReply { op, payload }) ∈ concrete.network := by
    simp only [World.land, List.mem_append] at hreply
    rcases hreply with hold | hnew
    · exact hold
    · obtain ⟨sent, hsent, heq⟩ := List.mem_map.mp hnew
      obtain ⟨target, message⟩ := sent
      simp only [Prod.mk.injEq] at heq
      obtain ⟨_, rfl, rfl⟩ := heq
      exact (node_step_no_store_reply hresult hsent).elim
  have noFreshWritten
      (hreply :
        (Concrete.Pid.store, .node address,
          .storeReply { op := node.nextOp, payload := .written }) ∈
            concrete.network) : False := by
    rcases reachable_put_replies_have_request hreachable (.inl rfl) hreply with
      ⟨key, document, expected, hput⟩ | ⟨hconflict, _⟩
    · exact (Nat.lt_irrefl node.nextOp
        ((reachable_rpc_ids hreachable).fresh haddress hnode hput)).elim
    · contradiction
  have noFreshFailed
      (hreply :
        (Concrete.Pid.store, .node address,
          .storeReply { op := node.nextOp, payload := .failed }) ∈
            concrete.network) : False := by
    rcases reachable_put_replies_have_request hreachable
      (.inr (.inr rfl)) hreply with
      ⟨key, document, expected, hput⟩ | ⟨hconflict, _⟩
    · exact (Nat.lt_irrefl node.nextOp
        ((reachable_rpc_ids hreachable).fresh haddress hnode hput)).elim
    · contradiction
  obtain ⟨workflowStore, parts, slack, hworkflowStore, hpending,
      hparts, hcommitted⟩ := related.workflow
  apply related_after_node_land hreachable related haddress hnode htime
      hvalid hresult habstractTime hnetwork
      (by
        intro key hkey
        simpa [hservice] using hkey)
  · obtain ⟨physical, hphysical, hrep⟩ := related.store
    exact ⟨physical, by simpa [World.land] using hphysical,
      by simpa [hservice] using hrep⟩
  · have hstepPart :=
      nodeWorkflowPart_step (event := event) hnodeValid hserial
        (hparts address haddress node hnode)
        (reachable_node_attempts hreachable haddress hnode)
        (fun op flight hflight hphase hevent => by
          have hvalid' := hvalid
          rw [hevent] at hvalid'
          exact hcommitted address haddress node op flight hnode hflight
            hphase hvalid')
        hresult hstate
    obtain ⟨part', released, hpart', hsplit, hstable⟩ := hstepPart
    let parts' : Addr → List WorkflowEntry := fun current =>
      if current = address then part' else parts current
    refine ⟨workflowStore, parts', released ++ slack,
        by simpa [World.land] using hworkflowStore, ?_, ?_, ?_⟩
    · simpa [hservice] using
        hpending.trans (perm_release_flatMap
          (reachable_nodes_nodup hreachable) haddress hsplit)
    · intro current hcurrent currentNode hcurrentNode
      by_cases heq : current = address
      · subst current
        rw [show
          (concrete.land (.node address) now result).process (.node address) =
            result.state by simp [World.land],
          hstate] at hcurrentNode
        cases Concrete.Local.node.inj hcurrentNode
        simpa [parts'] using hpart'
      · simpa [parts', heq] using
          hparts current hcurrent currentNode
            (by simpa [World.land, heq] using hcurrentNode)
    · intro current hcurrent currentNode op flight hcurrentNode hflight hphase
        hreply
      by_cases heq : current = address
      · subst current
        rw [show
          (concrete.land (.node address) now result).process (.node address) =
            result.state by simp [World.land],
          hstate] at hcurrentNode
        cases Concrete.Local.node.inj hcurrentNode
        rcases node_step_flight_origin hresult hstate hflight with
          holdFlight | hfresh
        · have hsame : part' = parts address :=
            hstable op flight hflight holdFlight
          simpa [parts', hsame] using
            hcommitted address haddress node op flight hnode holdFlight
              hphase (replyOld hreply)
        · subst op
          exact (noFreshWritten (replyOld hreply)).elim
      · simpa [parts', heq] using
          hcommitted current hcurrent currentNode op flight
            (by simpa [World.land, heq] using hcurrentNode) hflight hphase
            (replyOld hreply)
  · trivial
  · intro target call hsend
    exact (node_step_no_request hresult hsend).elim
  · intro output hsend
    exact houtputs output hsend
  · intro currentAddress currentNode op flight hcurrentAddress hcurrentNode
      hflight
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [show
        (concrete.land (.node address) now result).process (.node address) =
          result.state by simp [World.land],
        hstate] at hcurrentNode
      cases Concrete.Local.node.inj hcurrentNode
      rcases node_step_flight_origin hresult hstate hflight with
        holdFlight | hfresh
      · obtain ⟨hwritten, hfailed⟩ :=
          related.activeReplies address node op flight haddress hnode holdFlight
        constructor
        · intro hreply
          obtain ⟨hkey, hcovered, hpending⟩ :=
            hwritten (replyOld hreply)
          exact ⟨by simpa [hservice] using hkey,
            hcover _ hcovered, hpending⟩
        · intro hreply
          exact hcover _ (hfailed (replyOld hreply))
      · subst op
        constructor
        · intro hreply
          exact (noFreshWritten (replyOld hreply)).elim
        · intro hreply
          exact (noFreshFailed (replyOld hreply)).elim
    · have hcurrentNodeOld :
          concrete.process (.node currentAddress) = .node currentNode := by
        simpa [World.land, heq] using hcurrentNode
      obtain ⟨hwritten, hfailed⟩ :=
        related.activeReplies currentAddress currentNode op flight
          hcurrentAddress hcurrentNodeOld hflight
      constructor
      · intro hreply
        obtain ⟨hkey, hcovered, hpending⟩ := hwritten (replyOld hreply)
        exact ⟨by simpa [hservice] using hkey, hcover _ hcovered, hpending⟩
      · intro hreply
        exact hcover _ (hfailed (replyOld hreply))
  · intro currentAddress currentNode op outputs haddress' hnodeNext hmem
    by_cases heq : currentAddress = address
    · subst currentAddress
      rw [show
        (concrete.land (.node address) now result).process (.node address) =
          result.state by simp [World.land],
        hstate] at hnodeNext
      cases Concrete.Local.node.inj hnodeNext
      exact cleanup_mem_covered related haddress hnode
        (reachable_node_no_deleting hreachable haddress hnode)
        (reachable_node_loading_quiet hreachable haddress hnode)
        hmem (hcover outputs) hvalid hresult hstate
    · exact hcover _ (related.cleanupCovered currentAddress currentNode op
        outputs haddress' (by simpa [World.land, heq] using hnodeNext) hmem)

theorem related_after_stuttering_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node nextNode : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    (hnodeValid : NodeValid appConfig node)
    (hserial : NodeSerial node)
    {now : Time} {event : Event Concrete.Pid Concrete.Msg}
    {result : Result Concrete.Pid Concrete.Local Concrete.Msg}
    (htime : concrete.now ≤ now)
    (hvalid : event.Valid concrete (.node address))
    (hresult :
      result ∈
        (Concrete.step appConfig config (.node address) (.node node)
          now event).val)
    (hstate : result.state = .node nextNode)
    (houtputs :
      ∀ output,
        (.outside, Concrete.Msg.output output) ∈ result.send →
        (Abstract.Pid.service, .outside, Message.output output) ∈
          abstract.network) :
    Related nodes appConfig config
      (concrete.land (.node address) now result) abstract :=
  related_after_stuttering_node_to hreachable related haddress hnode
    hnodeValid hserial htime hvalid hresult hstate
    (Nat.le_trans related.time htime) rfl (fun _ h => h) (fun _ h => h)
    houtputs

theorem simulate_rejected_external_node
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    {concrete : World (CModel nodes appConfig)}
    {abstract : World AModel}
    (hreachable : Reachable (CModel nodes appConfig) config concrete)
    (related : Related nodes appConfig config concrete abstract)
    {address : Addr} (haddress : address ∈ nodes)
    {node : Concrete.Node}
    (hnode : concrete.process (.node address) = .node node)
    {call : Call} {now : Time}
    (htime : concrete.now ≤ now)
    (hrequest :
      (Concrete.Pid.outside, .node address, .request call) ∈
        concrete.network)
    (hvalidNode : NodeValid appConfig node)
    (hserial : NodeSerial node)
    (hresult :
      ({
        state := .node node
        send := Concrete.sendOutputs [Resonate.unavailable call]
      } : Result Concrete.Pid Concrete.Local Concrete.Msg) ∈
        (Concrete.step appConfig config (.node address) (.node node) now
          (.receive .outside (.request call))).val) :
    ∃ execution,
      Legal AModel { appConfig with unreliable := true }
        abstract execution ∧
      Related nodes appConfig config
        (concrete.land (.node address) now {
          state := .node node
          send := Concrete.sendOutputs [Resonate.unavailable call]
        })
        (endOf abstract execution) ∧
      Abstract.boundaryTrace execution = [] := by
  let shed := Resonate.runShed call (abstract.process .service)
  let abstractResult : Result Abstract.Pid State Message := {
    state := shed.1
    send := Abstract.sends shed.2
  }
  let abstractNext := abstract.land .service now abstractResult
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
      (related.requests address call hrequest) habstractResult
  have hstate :
      (abstractNext.process .service) = abstract.process .service := by
    simp [abstractNext, World.land, abstractResult, shed, Resonate.runShed]
  have hrelated :=
    related_after_stuttering_node_to
      (event := .receive .outside (.request call))
      hreachable related haddress hnode
      hvalidNode hserial htime hrequest hresult rfl
      (by simp [abstractNext, World.land]) hstate
      (fun _ hmem => List.mem_append_left _ hmem)
      (fun _ hcovered => hcovered.land abstractResult) (by
        intro output houtput
        have hcovered := covered_sent abstract now shed.1 shed.2
        apply hcovered output
        simpa [Concrete.sendOutputs, shed, Resonate.runShed] using houtput)
  exact ⟨[((.process .service now
      (.receive .outside (.request call)) abstractResult.send),
      abstractNext)], ⟨habstractStep, trivial⟩,
    by simpa [endOf] using hrelated, rfl⟩

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
    constructor
    · intro other
      rw [hrep other]
      simpa [abstractNext, World.land, abstractResult, served] using
        (hpure.1 other).symm
    · intro other hrelevant
      simpa [abstractNext, World.land, abstractResult, served] using
        external_keys_mono { appConfig with unreliable := true } call
          (abstract.process .service) other
          (hrep.relevantKeys other hrelevant)
  · have hold :
        WorkflowAligned config
          (concrete.land (.node address) now
            (Concrete.pureExternal appConfig node call)) abstract := by
      apply workflowAligned_node_land (nextNode := node)
        related.workflow haddress hnode
        (Concrete.pureExternal appConfig node call)
        (by simp [Concrete.pureExternal])
      · intro store part hpart
        exact hpart
      · intro parts hcommitted op flight hflight hphase hreply
        exact hcommitted address haddress node op flight hnode hflight hphase
          hreply
      · intro target op hsend
        simp [Concrete.pureExternal, Concrete.sendOutputs] at hsend
    rw [WorkflowAligned] at hold ⊢
    simpa only [hworkflowEq] using hold
  · trivial
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
  · intro currentAddress currentNode op outputs haddress' hnodeNext hmem
    exact (related.cleanupCovered currentAddress currentNode op outputs
      haddress' (by simpa [hprocessEq] using hnodeNext) hmem).land
      abstractResult

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
  obtain ⟨validNode, hvalidNodeState, hnodeValid⟩ :=
    reachable_nodes_valid hreachable address haddress
  rw [hnode] at hvalidNodeState
  cases Concrete.Local.node.inj hvalidNodeState
  obtain ⟨serialNode, hserialNode, hserial⟩ :=
    reachable_nodes_serial hreachable address haddress
  rw [hnode] at hserialNode
  cases Concrete.Local.node.inj hserialNode
  have stutter
      {nextNode : Concrete.Node}
      (hstate : result.state = .node nextNode)
      (houtputs :
        ∀ output,
          (.outside, Concrete.Msg.output output) ∈ result.send →
          (Abstract.Pid.service, .outside, Message.output output) ∈
            abstract.network) :
      ∃ execution,
        Legal AModel { appConfig with unreliable := true }
          abstract execution ∧
        Related nodes appConfig config
          (concrete.land (.node address) now result)
          (endOf abstract execution) ∧
        Abstract.boundaryTrace execution = [] :=
    ⟨[], trivial,
      related_after_stuttering_node hreachable related haddress hnode
        hnodeValid hserial htime hvalid hresult hstate houtputs,
      rfl⟩
  cases event with
  | timeout =>
      simp only [Concrete.step] at hresult
      repeat' first | split at hresult
      all_goals simp only [Outcomes.one, List.mem_singleton] at hresult
      all_goals subst result
      all_goals
        apply stutter (by
          first
          | rfl
          | exact (continueCleanup_state _ _).choose_spec.1
          | exact (start_state appConfig _ _ _ _ _).choose_spec
          | simp [Concrete.start, Concrete.decide,
              Concrete.writeCandidate, Concrete.beginMembershipRefresh,
              Concrete.beginTimerList, Concrete.refreshEnded,
              Concrete.Node.await, Concrete.Node.awaitControl,
              Concrete.continueCleanup, Concrete.cleanupFlight_cleanup,
              Concrete.finishNode, Concrete.Node.cachePut,
              Concrete.Node.cacheInvalidate])
        intro output houtput
        simp only [Concrete.sendOutputs, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.continueCleanup,
          Concrete.cleanupFlight_cleanup, Concrete.start,
          Concrete.decide, Concrete.writeCandidate,
          Concrete.beginMembershipRefresh, Concrete.beginTimerList,
          Concrete.refreshEnded] at houtput
        repeat' first | split at houtput
        all_goals simp [Concrete.sendOutputs, Concrete.Node.await,
          Concrete.Node.awaitControl, Concrete.continueCleanup,
          Concrete.cleanupFlight_cleanup] at houtput
  | receive sender message =>
      cases sender <;> cases message <;>
        simp only [Concrete.step] at hresult
      case outside.request call =>
        split at hresult
        next hbusy =>
          simp [hbusy, Outcomes.one] at hresult
          subst result
          apply stutter rfl
          intro output houtput
          simp at houtput
        next hready =>
          cases hkey : (Concrete.Transaction.external call).key? with
          | none =>
              simp [hready, hkey, Outcomes.one] at hresult
              subst result
              exact simulate_pure_external_node hreachable related haddress
                hnode hkey htime hvalid (by
                  simp [hready, hkey, Concrete.step, Outcomes.one])
          | some key =>
              simp only [hkey, hready] at hresult
              split at hresult
              next howns =>
                simp [howns, Outcomes.one] at hresult
                subst result
                apply stutter
                  (start_state appConfig node (.external call) key address).choose_spec
                intro output houtput
                simp only [Concrete.start, Concrete.decide,
                  Concrete.writeCandidate, Concrete.Node.await,
                  Concrete.continueCleanup, Concrete.cleanupFlight_cleanup,
                  Concrete.finishNode, Concrete.Node.awaitControl,
                  Concrete.sendOutputs] at houtput
                repeat' first | split at houtput
                all_goals simp_all [Concrete.Node.await, Concrete.sendOutputs,
                  Concrete.Node.awaitControl, Concrete.decide,
                  Concrete.writeCandidate, Concrete.continueCleanup,
                  Concrete.cleanupFlight_cleanup]
              next hnotOwns =>
                simp [Outcomes.one] at hresult
                subst result
                exact simulate_rejected_external_node hreachable related
                  haddress hnode htime hvalid hnodeValid hserial (by
                    simp [Concrete.step, hready, hkey, hnotOwns,
                      Outcomes.one])
      case store.storeReply rpc =>
        obtain ⟨op, payload⟩ := rpc
        cases payload with
        | written =>
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one] at hresult
                  subst result
                  apply stutter rfl
                  intro output houtput
                  simp at houtput
              | some flight =>
                  cases hp : flight.phase with
                  | writing =>
                      have hflight := takeFlight_some_mem ht
                      have hcovered :=
                        (related.activeReplies address node op flight haddress
                          hnode hflight).1 hvalid |>.2.1
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      apply stutter (committedFlight_state next flight).choose_spec
                      intro output houtput
                      exact hcovered output (committedFlight_outside_mem houtput)
                  | loading | arming | deleting =>
                      simp [ht, hp, Outcomes.one] at hresult
                      subst result
                      apply stutter rfl
                      intro output houtput
                      simp at houtput
        | failed =>
            cases ht : node.takeFlight op with
            | mk taken next =>
              cases taken with
              | none =>
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, Outcomes.one, List.mem_singleton] at hresult
                      subst result
                      apply stutter rfl
                      intro output houtput
                      simp at houtput
                  | some control =>
                      cases control with
                      | cleanup outputs =>
                          simp [ht, hc, Outcomes.one, List.mem_singleton] at hresult
                          subst result
                          apply stutter rfl
                          intro output houtput
                          simp [Concrete.sendOutputs] at houtput
                          exact related.cleanupCovered address node op outputs
                            haddress hnode (takeControl_cleanup_mem hc) output
                            houtput
                      | announced instant | announcements instant
                      | membershipWrite instant | membership instant live
                      | timerList instant through kind =>
                          simp [ht, hc, Outcomes.one, List.mem_singleton,
                            Concrete.refreshEnded, Concrete.beginTimerList,
                            Concrete.Node.awaitControl] at hresult
                          subst result
                          apply stutter rfl
                          intro output houtput
                          simp [Concrete.sendOutputs, Concrete.Node.awaitControl,
                            Concrete.refreshEnded, Concrete.beginTimerList] at houtput
              | some flight =>
                  have hflight := takeFlight_some_mem ht
                  have hcovered :=
                    (related.activeReplies address node op flight haddress
                      hnode hflight).2 hvalid
                  simp only [ht, Outcomes.one] at hresult
                  cases hp : flight.phase with
                  | deleting =>
                      exact absurd hp
                        (reachable_node_no_deleting hreachable haddress hnode
                          op flight hflight)
                  | loading | arming | writing =>
                      simp [hp, List.mem_singleton] at hresult
                      subst result
                      apply stutter rfl
                      intro output houtput
                      apply hcovered output
                      simpa [Concrete.sendOutputs] using houtput
        | done =>
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | some flight =>
                  cases hp : flight.phase with
                  | deleting =>
                      exact absurd hp
                        (reachable_node_no_deleting hreachable haddress hnode
                          op flight (takeFlight_some_mem ht))
                  | arming =>
                      cases hd : flight.document with
                      | none =>
                          simp [ht, hp, hd, Outcomes.one, List.mem_singleton]
                            at hresult
                          subst result
                          apply stutter rfl
                          intro output houtput
                          simp at houtput
                      | some document =>
                          simp [ht, hp, hd, Outcomes.one, List.mem_singleton]
                            at hresult
                          subst result
                          apply stutter rfl
                          intro output houtput
                          simp [Concrete.Node.await] at houtput
                  | loading | writing =>
                      simp [ht, hp, Outcomes.one, List.mem_singleton] at hresult
                      subst result
                      apply stutter rfl
                      intro output houtput
                      simp at houtput
              | none =>
                  cases hc : (node.takeControl op).1 with
                  | none =>
                      simp [ht, hc, Outcomes.one, List.mem_singleton] at hresult
                      subst result
                      apply stutter rfl
                      intro output houtput
                      simp at houtput
                  | some control =>
                      cases control with
                      | cleanup outputs =>
                          simp [ht, hc, Outcomes.one, List.mem_singleton]
                            at hresult
                          subst result
                          apply stutter rfl
                          intro output houtput
                          simp [Concrete.sendOutputs] at houtput
                          exact related.cleanupCovered address node op outputs
                            haddress hnode (takeControl_cleanup_mem hc) output
                            houtput
                      | announced instant | membershipWrite instant
                      | announcements instant | membership instant live
                      | timerList instant through kind =>
                          simp [ht, hc, Outcomes.one, List.mem_singleton,
                            Concrete.refreshEnded, Concrete.beginTimerList,
                            Concrete.Node.awaitControl] at hresult
                          subst result
                          apply stutter rfl
                          intro output houtput
                          simp [Concrete.sendOutputs, Concrete.Node.await,
                            Concrete.Node.awaitControl, Concrete.refreshEnded,
                            Concrete.beginTimerList] at houtput
        | got key loaded =>
            cases ht : node.takeFlight op with
            | mk taken remaining =>
              cases taken with
              | none =>
                  simp [ht, Outcomes.one, List.mem_singleton] at hresult
                  subst result
                  apply stutter rfl
                  intro output houtput
                  simp at houtput
              | some flight =>
                  simp only [ht] at hresult
                  split at hresult
                  next heq =>
                    cases hp : flight.phase with
                    | loading =>
                        have hflightMem := takeFlight_some_mem ht
                        have hflightValid :=
                          related.flights address node op flight haddress hnode
                            hflightMem
                        let loaded' := heq ▸ loaded
                        let cached :=
                          match loaded' with
                          | some (document, version) =>
                              remaining.cachePut flight.key
                                { document, version }
                          | none => remaining.cacheInvalidate flight.key
                        have hremaining :=
                          NodeValid.takeFlight hnodeValid op
                        rw [ht] at hremaining
                        have hcached : NodeValid appConfig cached := by
                          cases hloaded : loaded' with
                          | none =>
                              simpa [cached, hloaded] using
                                hremaining.cacheInvalidate flight.key
                          | some value =>
                              simpa [cached, hloaded] using
                                hremaining.cachePut flight.key {
                                  document := value.1
                                  version := value.2 }
                        simp [hp, loaded', cached, Outcomes.one,
                          List.mem_singleton] at hresult
                        subst result
                        apply stutter
                          (NodeValid.decide hcached hflightValid loaded').choose_spec.1
                        intro output houtput
                        simp only [Concrete.decide, Concrete.writeCandidate,
                          Concrete.continueCleanup, Concrete.cleanupFlight_cleanup,
                          Concrete.finishNode, Concrete.Node.await,
                          Concrete.Node.awaitControl, Concrete.sendOutputs]
                          at houtput
                        repeat' first | split at houtput
                        all_goals simp [Concrete.sendOutputs,
                          Concrete.Node.await, Concrete.Node.awaitControl] at houtput
                    | arming | writing | deleting =>
                        simp [hp, Outcomes.one, List.mem_singleton] at hresult
                        subst result
                        apply stutter rfl
                        intro output houtput
                        simp at houtput
                  next _ =>
                    simp [Outcomes.one, List.mem_singleton] at hresult
                    subst result
                    apply stutter rfl
                    intro output houtput
                    simp at houtput
        | conflict
        | timers keys
        | announcements values
        | membership configuration version =>
            simp only [Outcomes.one] at hresult
            repeat' first | split at hresult
            all_goals simp only [Outcomes.one, List.mem_singleton] at hresult
            all_goals subst result
            all_goals
              apply stutter (by
                first
                | rfl
                | exact (continueCleanup_state _ _).choose_spec.1
                | exact (start_state appConfig _ _ _ _ _).choose_spec
                | (repeat' split) <;> first
                    | rfl
                    | exact (continueCleanup_state _ _).choose_spec.1
                    | simp [Concrete.Node.await, Concrete.Node.awaitControl,
                        Concrete.refreshEnded, Concrete.beginTimerList,
                        Concrete.decide, Concrete.writeCandidate,
                        Concrete.retry, Concrete.Node.cachePut,
                        Concrete.Node.cacheInvalidate, Concrete.finishNode])
              intro output houtput
              simp only [Concrete.sendOutputs, Concrete.Node.await,
                Concrete.Node.awaitControl, Concrete.continueCleanup,
                Concrete.cleanupFlight_cleanup, Concrete.refreshEnded,
                Concrete.beginTimerList, Concrete.decide,
                Concrete.writeCandidate, Concrete.retry,
                Concrete.failureOutputs, Concrete.finishNode] at houtput
              repeat' first | split at houtput
              all_goals simp [Concrete.sendOutputs,
                Concrete.Node.awaitControl, Concrete.continueCleanup,
                Concrete.cleanupFlight_cleanup, Concrete.failureOutputs] at houtput
      all_goals
        try
          simp [Outcomes.one] at hresult
          subst result
          apply stutter rfl
          intro output houtput
          simp at houtput



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
    {config : Concrete.Config} :
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
      exact simulate_store_process hreachable related hphysical
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
    {config : Concrete.Config} :
    StepSimulation nodes appConfig config :=
  stepSimulation_of_processSimulation injectSimulation processSimulation

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
    store := ⟨{}, hinit.2.1, by
      constructor
      · intro key
        rfl
      · intro key hrelevant
        cases key <;> simp [RelevantDocument, Concrete.Store.toAbstract,
          Resonate.Store.read, emptyDocument] at hrelevant⟩
    requests := ?_
    outputs := ?_
    puts := ?_
    gotSnapshots := gotSnapshots_initial _
    ownedPutSnapshots := ownedPutSnapshots_initial _
    putReplyOrigins := putRepliesHaveRequest_initial _
    workflow := ?_
    currentWorkflow := ?_
    acknowledged := ?_
    failedCovered := ?_
    activeReplies := ?_
    flights := ?_
    gotReplies := ?_
    putReplies := ?_
    cleanupCovered := ?_
  }
  · intros
    contradiction
  · intros
    contradiction
  · intros
    contradiction
  · refine ⟨{}, fun _ => [], [], hinit.2.1, ?_, ?_, ?_⟩
    · change List.Perm [] _
      simp
    · intro address haddress node hnode
      have hnodeEmpty : Concrete.Local.node node = .node {} :=
        hnode.symm.trans (hinit.2.2 address haddress)
      cases hnodeEmpty
      constructor
      · intro _
        rfl
      · intro op flight hflight
        simp at hflight
    · intro address haddress node op flight hnode hflight
      have hnodeEmpty : Concrete.Local.node node = .node {} :=
        hnode.symm.trans (hinit.2.2 address haddress)
      cases hnodeEmpty
      simp at hflight
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
  · exact putRepliesHaveRequest_initial _
  · intro address node op outputs haddress hnode hmem
    have : Concrete.Local.node node = .node {} := hnode.symm.trans
      (hinit.2.2 address haddress)
    cases this
    simp at hmem

/-- Client-visible traces of a concrete fleet are client-visible traces of the
unreliable abstract service. -/
def Refines (nodes : List Addr) (appConfig : Resonate.Config)
    (config : Concrete.Config) : Prop :=
  ∀ events,
    Concrete.ValidBoundaryTrace nodes appConfig config events →
    Abstract.ValidBoundaryTrace
      { appConfig with unreliable := true } events

/-- End-to-end trace inclusion from a protocol-specific reachable one-step
simulation, including all execution and delayed-observation plumbing. -/
theorem boundary_refinement_of_stepSimulation
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config}
    (hsim : StepSimulation nodes appConfig config) :
    Refines nodes appConfig config := by
  unfold Refines
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
    {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Concrete.Config} :
    Refines nodes appConfig config :=
  boundary_refinement_of_stepSimulation stepSimulation

end Resonate.Refinement
