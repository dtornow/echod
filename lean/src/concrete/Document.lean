import Protocol

/-!
# Per-origin documents

The concrete store keeps each origin's objects as one document and each
schedule as its own document. `Store.read` and `Store.write` view the flat
abstract store through those documents.
-/

namespace Resonate

open ServerModel

/-- A document transaction key. -/
inductive DocumentKey where
  | origin (origin : String)
  | schedule (id : ServerModel.Ident)
  deriving Repr, DecidableEq

/-- A fused promise/task row.  The index prevents storing an id from another
origin in this document. -/
structure OriginObject (origin : String) where
  suffix : String
  promise : PromiseObject
  task : Option TaskObject := none
  deriving Repr

def OriginObject.id (object : OriginObject origin) : ServerModel.Ident :=
  { origin, suffix := object.suffix }

/-- Pure read projection at a logical time. -/
def OriginObject.project (object : OriginObject origin) (now : Nat) :
    OriginObject origin :=
  let promise := object.promise.project now
  { object with promise, task := object.task.map (·.view promise) }

abbrev OriginDocument (origin : String) := List (OriginObject origin)

/-- Schedule contents omit the id because it is fixed by the index. -/
structure ScheduleData (id : ServerModel.Ident) where
  cron : String
  promiseId : ServerModel.Ident
  promiseTimeout : Nat
  promiseParam : Value
  promiseTags : Tags
  nextRunAt : Nat
  lastRunAt : Option Nat := none
  createdAt : Nat
  deriving Repr

def ScheduleData.toSchedule {id : ServerModel.Ident}
    (data : ScheduleData id) : Schedule :=
  { id
    cron := data.cron
    promiseId := data.promiseId
    promiseTimeout := data.promiseTimeout
    promiseParam := data.promiseParam
    promiseTags := data.promiseTags
    nextRunAt := data.nextRunAt
    lastRunAt := data.lastRunAt
    createdAt := data.createdAt }

def ScheduleData.ofSchedule (schedule : Schedule) :
    ScheduleData schedule.id :=
  { cron := schedule.cron
    promiseId := schedule.promiseId
    promiseTimeout := schedule.promiseTimeout
    promiseParam := schedule.promiseParam
    promiseTags := schedule.promiseTags
    nextRunAt := schedule.nextRunAt
    lastRunAt := schedule.lastRunAt
    createdAt := schedule.createdAt }

abbrev ScheduleDocument (id : ServerModel.Ident) := Option (ScheduleData id)

/-- Public dependent document value family. -/
def Document : DocumentKey → Type
  | .origin origin => OriginDocument origin
  | .schedule id => ScheduleDocument id

def emptyDocument : (key : DocumentKey) → Document key
  | .origin _ => []
  | .schedule _ => none

/-- Generic pure Reader/State/Writer plumbing for one indexed document.
It contains no request or timeout transition logic. -/
def DocumentHandler (key : DocumentKey) (α : Type) : Type :=
  HandlerEnv → Document key → α × Document key × List OutboxEntry

instance (key : DocumentKey) : Monad (DocumentHandler key) where
  pure value := fun _ document => (value, document, [])
  bind action next := fun env document =>
    let (value, document', emitted₁) := action env document
    let (result, document'', emitted₂) := next value env document'
    (result, document'', emitted₁ ++ emitted₂)

def documentAsk {key : DocumentKey} : DocumentHandler key HandlerEnv :=
  fun env document => (env, document, [])

def documentGet {key : DocumentKey} : DocumentHandler key (Document key) :=
  fun _ document => (document, document, [])

def documentSet {key : DocumentKey} (document : Document key) :
    DocumentHandler key Unit :=
  fun _ _ => ((), document, [])

def documentModify {key : DocumentKey} (f : Document key → Document key) :
    DocumentHandler key Unit :=
  fun _ document => ((), f document, [])

def documentEmit {key : DocumentKey} (entry : OutboxEntry) :
    DocumentHandler key Unit :=
  fun _ document => ((), document, [entry])

def Object.ofOrigin {origin : String} (row : OriginObject origin) : Object where
  id := { origin, suffix := row.suffix }
  promise := row.promise
  task := row.task

def Object.toOriginRow? (origin : String) (object : Object) :
    Option (OriginObject origin) :=
  if object.id.origin == origin then
    some { suffix := object.id.suffix, promise := object.promise,
           task := object.task }
  else
    none

def Store.originRows (store : Store) (origin : String) : OriginDocument origin :=
  store.objects.filterMap (Object.toOriginRow? origin)

def Store.scheduleAt (store : Store) (id : Ident) : ScheduleDocument id :=
  go store.schedules
where
  go : List Schedule → ScheduleDocument id
  | [] => none
  | schedule :: rest =>
      if h : schedule.id = id then
        some (h ▸ ScheduleData.ofSchedule schedule)
      else
        go rest

def Store.read (store : Store) : (key : DocumentKey) → Document key
  | .origin origin => store.originRows origin
  | .schedule id => store.scheduleAt id

def Store.write (store : Store) (key : DocumentKey) (document : Document key) :
    Store :=
  { objects :=
      match key with
      | .origin origin =>
          store.objects.filter (·.id.origin != origin) ++
            document.map Object.ofOrigin
      | .schedule _ => store.objects
    schedules :=
      match key with
      | .origin _ => store.schedules
      | .schedule id =>
          store.schedules.filter (·.id != id) ++
            match document with
            | none => []
            | some data => [data.toSchedule] }

@[simp] theorem Object.toOriginRow?_ofOrigin {origin : String}
    (row : OriginObject origin) :
    Object.toOriginRow? origin (Object.ofOrigin row) = some row := by
  simp [Object.toOriginRow?, Object.ofOrigin]

theorem filterMap_ofOrigin {origin : String} (rows : List (OriginObject origin)) :
    rows.filterMap (Object.toOriginRow? origin ∘ Object.ofOrigin) = rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [ih, Object.toOriginRow?_ofOrigin]

theorem filterMap_origin_removed {origin : String} (objects : List Object) :
    (objects.filter (·.id.origin != origin)).filterMap
        (Object.toOriginRow? origin) = [] := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      simp only [List.filter_cons]
      by_cases horigin : object.id.origin = origin
      · simp [horigin, ih]
      · have hkeep : (object.id.origin != origin) = true := by
          simpa [bne_iff_ne] using horigin
        simp [hkeep, Object.toOriginRow?, horigin, ih]

theorem filterMap_origin_preserves_other {origin other : String}
    (h : other ≠ origin) (objects : List Object) :
    (objects.filter (·.id.origin != origin)).filterMap
        (Object.toOriginRow? other) =
      objects.filterMap (Object.toOriginRow? other) := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      simp only [List.filter_cons, List.filterMap_cons]
      by_cases horigin : object.id.origin = origin
      · simp [horigin, Object.toOriginRow?, h.symm, ih]
      · have hkeep : (object.id.origin != origin) = true := by
          simpa [bne_iff_ne] using horigin
        simp only [hkeep, ite_true, List.filterMap_cons, Object.toOriginRow?]
        by_cases hother : object.id.origin = other
        · simp [hother, ih]
        · simp [hother, ih]

theorem filterMap_append_same_origin {origin : String}
    (objects : List Object) (rows : List (OriginObject origin)) :
    (objects.filter (·.id.origin != origin) ++ rows.map Object.ofOrigin).filterMap
        (Object.toOriginRow? origin) = rows := by
  rw [List.filterMap_append, filterMap_origin_removed, List.nil_append,
    List.filterMap_map]
  exact filterMap_ofOrigin rows

theorem filterMap_mapped_other_origin {origin other : String}
    (h : other ≠ origin) (rows : List (OriginObject origin)) :
    (rows.map Object.ofOrigin).filterMap (Object.toOriginRow? other) = [] := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [Object.toOriginRow?, Object.ofOrigin, h.symm, ih]

theorem filterMap_append_other_origin {origin other : String}
    (h : other ≠ origin) (objects : List Object)
    (rows : List (OriginObject origin)) :
    (objects.filter (·.id.origin != origin) ++ rows.map Object.ofOrigin).filterMap
        (Object.toOriginRow? other) =
      objects.filterMap (Object.toOriginRow? other) := by
  rw [List.filterMap_append, filterMap_origin_preserves_other h,
    filterMap_mapped_other_origin h, List.append_nil]

theorem ScheduleData.ofSchedule_toSchedule {id : Ident}
    (data : ScheduleData id) :
    ScheduleData.ofSchedule data.toSchedule = data := by
  rfl

theorem scheduleAt_go_removed (id : Ident) (schedules : List Schedule) :
    Store.scheduleAt.go id (schedules.filter (·.id != id)) = none := by
  induction schedules with
  | nil => rfl
  | cons schedule rest ih =>
      simp only [List.filter_cons]
      by_cases hschedule : schedule.id = id
      · simp [hschedule, ih]
      · have hkeep : (schedule.id != id) = true := by
          simpa [bne_iff_ne] using hschedule
        simp [hkeep, Store.scheduleAt.go, hschedule, ih]

theorem scheduleAt_go_append_same (id : Ident) (schedules : List Schedule)
    (data : ScheduleData id) :
    Store.scheduleAt.go id
        (schedules.filter (·.id != id) ++ [data.toSchedule]) =
      some data := by
  induction schedules with
  | nil =>
      simp [Store.scheduleAt.go, ScheduleData.toSchedule, ScheduleData.ofSchedule]
  | cons schedule rest ih =>
      simp only [List.filter_cons]
      by_cases hschedule : schedule.id = id
      · simp [hschedule, ih]
      · have hkeep : (schedule.id != id) = true := by
          simpa [bne_iff_ne] using hschedule
        simp [hkeep, List.cons_append, Store.scheduleAt.go, hschedule, ih]

theorem scheduleAt_go_filter_other (id other : Ident) (h : other ≠ id)
    (schedules : List Schedule) :
    Store.scheduleAt.go other (schedules.filter (·.id != id)) =
      Store.scheduleAt.go other schedules := by
  induction schedules with
  | nil => rfl
  | cons schedule rest ih =>
      simp only [List.filter_cons]
      by_cases hschedule : schedule.id = id
      · simp [hschedule, Store.scheduleAt.go, h.symm, ih]
      · have hkeep : (schedule.id != id) = true := by
          simpa [bne_iff_ne] using hschedule
        simp only [hkeep, ite_true, Store.scheduleAt.go]
        by_cases hother : schedule.id = other
        · simp [hother]
        · simp [hother, ih]

theorem scheduleAt_go_append_other (id other : Ident) (h : other ≠ id)
    (schedules : List Schedule) (extra : List Schedule)
    (hextra : Store.scheduleAt.go other extra = none) :
    Store.scheduleAt.go other (schedules.filter (·.id != id) ++ extra) =
      Store.scheduleAt.go other schedules := by
  induction schedules with
  | nil =>
      simpa [Store.scheduleAt.go] using hextra
  | cons schedule rest ih =>
      simp only [List.filter_cons]
      by_cases hschedule : schedule.id = id
      · simp [hschedule, Store.scheduleAt.go, h.symm, ih]
      · have hkeep : (schedule.id != id) = true := by
          simpa [bne_iff_ne] using hschedule
        simp only [hkeep, ite_true, List.cons_append, Store.scheduleAt.go]
        by_cases hother : schedule.id = other
        · simp [hother]
        · simp [hother, ih]

@[simp] theorem Store.read_write_same (store : Store) (key : DocumentKey)
    (document : Document key) :
    (store.write key document).read key = document := by
  cases key with
  | origin origin =>
      simp only [Store.write, Store.read, Store.originRows]
      exact filterMap_append_same_origin store.objects document
  | schedule id =>
      cases document with
      | none =>
          simp [Store.write, Store.read, Store.scheduleAt, scheduleAt_go_removed]
      | some data =>
          simp [Store.write, Store.read, Store.scheduleAt, scheduleAt_go_append_same]

@[simp] theorem Store.read_write_other (store : Store) (key other : DocumentKey)
    (document : Document key) (h : other ≠ key) :
    (store.write key document).read other = store.read other := by
  cases key with
  | origin origin =>
      cases other with
      | origin otherOrigin =>
          have horigin : otherOrigin ≠ origin := by
            intro heq
            apply h
            simp [heq]
          simp [Store.write, Store.read, Store.originRows,
            filterMap_append_other_origin horigin]
      | schedule id =>
          rfl
  | schedule id =>
      cases other with
      | origin origin =>
          rfl
      | schedule otherId =>
          have hother : otherId ≠ id := by
            intro heq
            apply h
            simp [heq]
          cases document with
          | none =>
              simp only [Store.write, Store.read, Store.scheduleAt]
              exact scheduleAt_go_append_other id otherId hother
                store.schedules [] rfl
          | some data =>
              simp only [Store.write, Store.read, Store.scheduleAt]
              apply scheduleAt_go_append_other id otherId hother store.schedules
                [data.toSchedule]
              simp [Store.scheduleAt.go, ScheduleData.toSchedule, hother.symm]

theorem filter_ofOrigin {origin : String} (rows : List (OriginObject origin)) :
    (rows.map Object.ofOrigin).filter (·.id.origin != origin) = [] := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp [Object.ofOrigin, ih]

theorem Store.write_twice (key : DocumentKey) (before after : Document key) :
    ((({} : Store).write key before).write key after) =
      ({} : Store).write key after := by
  cases key with
  | origin origin =>
      simp [Store.write, filter_ofOrigin]
  | schedule id =>
      cases before <;> cases after <;>
        simp [Store.write, ScheduleData.toSchedule]

def WorkItem.key : WorkItem → DocumentKey
  | .promiseTimeout id => .origin id.origin
  | .callback req => .origin req.awaited.origin
  | .listener req => .origin req.awaited.origin
  | .taskLeaseTimeout id => .origin id.origin
  | .taskRetryTimeout id => .origin id.origin
  | .scheduleTimeout id => .schedule id
  | .occurrence req _ => .origin req.id.origin

def WorkflowEntry.key (entry : WorkflowEntry) : DocumentKey :=
  .origin entry.request.id.origin

def State.originDocument (state : State) (origin : String) :
    OriginDocument origin :=
  state.store.read (.origin origin)

def State.scheduleDocument (state : State) (id : ServerModel.Ident) :
    ScheduleDocument id :=
  state.store.read (.schedule id)

def State.withOrigin (state : State) (origin : String)
    (document : OriginDocument origin) : State :=
  { state with store := state.store.write (.origin origin) document }

def State.withSchedule (state : State) (schedule : Schedule) : State :=
  { state with
    store := state.store.write (.schedule schedule.id)
      (some (ScheduleData.ofSchedule schedule)) }

end Resonate
