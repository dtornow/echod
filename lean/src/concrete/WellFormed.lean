import «concrete».Model

/-!
# Well-formed documents

The catalogue a stored document satisfies: the promise rows, the task rows,
and the schedule rows. Every property is about one document and none reads a
clock. A decision runs at its transaction's logical time, which need not be
later than the stamps already in the document it loads, so properties such
as `createdAt ≤ settledAt` are not part of the catalogue. `nextCron` and
`occurrences` are opaque, so neither are the schedule's run times.
-/

namespace Resonate.Concrete

open ServerModel

/-- The promise rows of one promise with id `id`. -/
structure PromiseOk (id : Ident) (p : PromiseObject) : Prop where
  created_le_timeout : p.createdAt ≤ p.timeoutAt
  pending_before_timeout : p.state = .pending → p.createdAt < p.timeoutAt
  pending_iff_unsettled : p.state = .pending ↔ p.settledAt = none
  settled_le_timeout : ∀ time, p.settledAt = some time → time ≤ p.timeoutAt
  pending_no_value : p.state = .pending → p.value = {}
  deadline_no_value : p.settledAt = some p.timeoutAt → p.value = {}
  timedout_at_deadline : p.state = .rejectedTimedout → p.settledAt = some p.timeoutAt
  callbacks_nodup : p.callbacks.Nodup
  callbacks_not_self : id ∉ p.callbacks
  callbacks_same_origin : ∀ awaiter ∈ p.callbacks, awaiter.origin = id.origin
  listeners_nodup : p.listeners.Nodup

/-- The task rows of one task. -/
structure TaskOk (t : TaskObject) : Prop where
  acquired_iff_pid : t.state = .acquired ↔ t.pid.isSome
  acquired_iff_ttl : t.state = .acquired ↔ t.ttl.isSome
  acquired_iff_lease : t.state = .acquired ↔ t.leaseTimeoutAt.isSome
  pending_iff_retry : t.state = .pending ↔ t.retryTimeoutAt.isSome
  suspended_no_resumes : t.state = .suspended → t.resumes = []
  resumes_nodup : t.resumes.Nodup
  acquired_version : t.state = .acquired → 0 < t.version

/-- One fused row. A settled promise has finished its task. -/
structure ObjectOk {origin : String} (o : OriginObject origin) : Prop where
  promise : PromiseOk o.id o.promise
  task : ∀ t, o.task = some t → TaskOk t
  settled : ∀ t, o.task = some t → o.promise.state ≠ .pending → t.state = .fulfilled

/-- A schedule never creates a promise that is both a timer and targeted. -/
def ScheduleOk {id : Ident} (s : ScheduleData id) : Prop :=
  s.promiseTags.timerTargeted = false

/-- An origin document holds each suffix once, every row well-formed. A
schedule document holds a well-formed schedule, if any. -/
def DocumentOk : (key : DocumentKey) → Document key → Prop
  | .origin _, (document : OriginDocument _) =>
      (document.map (·.suffix)).Nodup ∧ ∀ o ∈ document, ObjectOk o
  | .schedule _, (document : ScheduleDocument _) =>
      ∀ s, document = some s → ScheduleOk s

/-- Every document the store holds is well-formed. -/
def Store.WellFormed (store : Store) : Prop :=
  ∀ key document version, store.read key = some (document, version) →
    DocumentOk key document

/-- A system is well-formed when its store is. -/
def Formed {nodes : List Addr} {appConfig : Resonate.Config}
    (system : Rover.System (model nodes appConfig)) : Prop :=
  ∀ store, system.process .store = .store store → store.WellFormed

end Resonate.Concrete
