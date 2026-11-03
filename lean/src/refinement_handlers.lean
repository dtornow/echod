import Lean
import «concrete».Model
import «abstract».Model

/-!
# Abstract handlers simulate the concrete document decisions

The abstract handlers run on the whole store and address objects by id. The
concrete decisions run on one document and address objects by suffix.
`Sim key R abstract concrete` says that running `abstract` on any store gives
what running `concrete` on that store's document `key` gives, with the result
document written back: the results are related by `R`, every document view of
the two stores agrees, and the emitted messages are equal.
-/

namespace Resonate.Refinement

open ServerModel

/-- Two stores whose document views all agree. -/
def Same (a b : Store) : Prop := ∀ key, a.read key = b.read key

theorem Same.refl (a : Store) : Same a a := fun _ => rfl

theorem Same.symm {a b : Store} (h : Same a b) : Same b a :=
  fun key => (h key).symm

theorem Same.trans {a b c : Store} (h₁ : Same a b) (h₂ : Same b c) :
    Same a c := fun key => (h₁ key).trans (h₂ key)

theorem Same.write {a b : Store} (h : Same a b) (key : DocumentKey)
    (document : Document key) : Same (a.write key document) (b.write key document) := by
  intro other
  by_cases hother : other = key
  · subst other
    simp
  · simp [Store.read_write_other _ _ _ _ hother, h other]

theorem Store.read_write_read (store : Store) (key : DocumentKey) :
    Same (store.write key (store.read key)) store := by
  intro other
  by_cases hother : other = key
  · subst other
    simp
  · simp [Store.read_write_other _ _ _ _ hother]

theorem Store.write_write_same (store : Store) (key : DocumentKey)
    (first second : Document key) :
    Same ((store.write key first).write key second) (store.write key second) := by
  intro other
  by_cases hother : other = key
  · subst other
    simp
  · simp [Store.read_write_other _ _ _ _ hother]

def Sim (key : DocumentKey) (R : α → β → Prop)
    (abstract : Abstract.Handler α) (concrete : DocumentHandler key β) : Prop :=
  ∀ env store,
    R (abstract env store).1 (concrete env (store.read key)).1 ∧
    Same (abstract env store).2.1
      (store.write key (concrete env (store.read key)).2.1) ∧
    (abstract env store).2.2 = (concrete env (store.read key)).2.2

theorem Sim.pure {key : DocumentKey} {R : α → β → Prop} {a : α} {b : β}
    (h : R a b) :
    Sim key R (Pure.pure a : Abstract.Handler α)
      (Pure.pure b : DocumentHandler key β) := by
  intro env store
  exact ⟨h, Same.symm (Store.read_write_read store key), rfl⟩

theorem Sim.bind {key : DocumentKey} {R : α → β → Prop} {S : γ → δ → Prop}
    {ma : Abstract.Handler α} {mc : DocumentHandler key β}
    {fa : α → Abstract.Handler γ} {fc : β → DocumentHandler key δ}
    (hm : Sim key R ma mc) (hf : ∀ a c, R a c → Sim key S (fa a) (fc c)) :
    Sim key S (ma >>= fa) (mc >>= fc) := by
  intro env store
  obtain ⟨hr, hsame, hemit⟩ := hm env store
  have hread : (ma env store).2.1.read key = (mc env (store.read key)).2.1 := by
    rw [hsame key]
    simp
  obtain ⟨hr', hsame', hemit'⟩ :=
    hf _ _ hr env (ma env store).2.1
  rw [hread] at hr' hsame' hemit'
  refine ⟨hr', ?_, ?_⟩
  · exact Same.trans hsame'
      ((Same.write hsame key _).trans (Store.write_write_same store key _ _))
  · show (ma env store).2.2 ++ (fa (ma env store).1 env (ma env store).2.1).2.2 =
      (mc env (store.read key)).2.2 ++
        (fc (mc env (store.read key)).1 env (mc env (store.read key)).2.1).2.2
    rw [hemit, hemit']

theorem Sim.map {key : DocumentKey} {R : α → β → Prop}
    {ma : Abstract.Handler α} {mc : DocumentHandler key β}
    {fa : α → γ} {fc : β → γ}
    (hm : Sim key R ma mc) (hf : ∀ a c, R a c → fa a = fc c) :
    Sim key Eq (fa <$> ma) (fc <$> mc) := by
  intro env store
  obtain ⟨hr, hsame, hemit⟩ := hm env store
  refine ⟨hf _ _ hr, ?_, ?_⟩
  · simpa [Functor.map] using hsame
  · simpa [Functor.map] using hemit


/-! ## Object lookups through an origin document -/

theorem Object.ofOrigin_toOriginRow {origin : String} {object : Object}
    {row : OriginObject origin} (h : Object.toOriginRow? origin object = some row) :
    Object.ofOrigin row = object := by
  unfold Object.toOriginRow? at h
  split at h
  · rename_i horigin
    cases h
    obtain ⟨⟨o, s⟩, p, t⟩ := object
    simp at horigin
    subst horigin
    rfl
  · contradiction

theorem toOriginRow?_eq_none {origin : String} {object : Object}
    (h : object.id.origin ≠ origin) : Object.toOriginRow? origin object = none := by
  simp [Object.toOriginRow?, h]

theorem toOriginRow?_eq_some {object : Object} :
    Object.toOriginRow? object.id.origin object =
      some { suffix := object.id.suffix, promise := object.promise, task := object.task } := by
  simp [Object.toOriginRow?]

theorem find?_originRows (objects : List Object) (id : Ident) :
    ((objects.filterMap (Object.toOriginRow? id.origin)).find?
        (·.suffix == id.suffix)).map Object.ofOrigin =
      objects.find? (·.id == id) := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      by_cases horigin : object.id.origin = id.origin
      · obtain ⟨row, hrow, hrowSuffix⟩ :
            ∃ row, Object.toOriginRow? id.origin object = some row ∧
              row.suffix = object.id.suffix :=
          ⟨{ suffix := object.id.suffix, promise := object.promise, task := object.task },
            by simp [Object.toOriginRow?, horigin], rfl⟩
        simp only [List.filterMap_cons, hrow]
        by_cases hsuffix : object.id.suffix = id.suffix
        · have hid : object.id = id := by
            cases hobj : object.id; cases id
            simp_all
          have hp : (row.suffix == id.suffix) = true := by simp [hrowSuffix, hsuffix]
          have hq : (object.id == id) = true := by simp [hid]
          simp only [List.find?_cons, hp, hq, Option.map_some]
          exact congrArg some (Object.ofOrigin_toOriginRow hrow)
        · have hid : ¬ object.id = id := fun h => hsuffix (by rw [h])
          have hp : (row.suffix == id.suffix) = false := by simp [hrowSuffix, hsuffix]
          have hq : (object.id == id) = false := by simp [hid]
          simp only [List.find?_cons, hp, hq]
          exact ih
      · have hid : ¬ object.id = id := fun h => horigin (by rw [h])
        have hq : (object.id == id) = false := by simp [hid]
        simp only [List.filterMap_cons, toOriginRow?_eq_none horigin, List.find?_cons, hq]
        exact ih

theorem getObject_eq_read (store : Store) (id : Ident) :
    store.getObject id =
      (((store.read (.origin id.origin)).find? (·.suffix == id.suffix)).map
        Object.ofOrigin) := by
  simp only [Store.getObject, Store.read, Store.originRows]
  exact (find?_originRows store.objects id).symm

/-- An abstract object read corresponds to the concrete row read, and the
row found has the requested suffix. -/
def ObjRel (origin suffix : String) (a : Option Object)
    (c : Option (OriginObject origin)) : Prop :=
  a = c.map Object.ofOrigin ∧ ∀ row, c = some row → row.suffix = suffix

theorem ObjRel.cases {origin suffix : String}
    {P : Option Object → Option (OriginObject origin) → Prop}
    (hnone : P none none)
    (hsome : ∀ promise task,
      P (some (Object.ofOrigin (⟨suffix, promise, task⟩ : OriginObject origin)))
        (some ⟨suffix, promise, task⟩)) :
    ∀ a c, ObjRel origin suffix a c → P a c := by
  rintro a (_ | ⟨rowSuffix, promise, task⟩) ⟨rfl, hsuffix⟩
  · exact hnone
  · have := hsuffix _ rfl
    simp only at this
    subst this
    exact hsome promise task

theorem find?_suffix {origin suffix : String} {document : OriginDocument origin}
    {row : OriginObject origin}
    (h : document.find? (·.suffix == suffix) = some row) : row.suffix = suffix := by
  simpa using List.find?_some h

theorem getObject_sim (id : Ident) :
    Sim (.origin id.origin) (ObjRel id.origin id.suffix) (Abstract.getObject id)
      (Concrete.Decision.getObject id.suffix) := by
  intro env store
  refine ⟨?_, Same.symm (Store.read_write_read store _), rfl⟩
  refine ⟨?_, fun row h => find?_suffix h⟩
  simp [Abstract.getObject, Concrete.Decision.getObject,
    getObject_eq_read, bind, Concrete.Decision.get, documentGet, pure]


theorem same_write_origin {a store : Store} {origin : String}
    {document : OriginDocument origin}
    (hschedules : a.schedules = store.schedules)
    (hsame : a.read (.origin origin) = document)
    (hother : ∀ other, other ≠ origin →
      a.read (.origin other) = store.read (.origin other)) :
    Same a (store.write (.origin origin) document) := by
  intro key
  cases key with
  | origin other =>
      by_cases h : other = origin
      · subst other
        rw [hsame]
        simp
      · rw [hother other h, Store.read_write_other]
        simpa using h
  | schedule id =>
      simp only [Store.read, Store.write, Store.scheduleAt, hschedules]

theorem filterMap_filter_id_same (objects : List Object) (id : Ident) :
    (objects.filter (·.id != id)).filterMap (Object.toOriginRow? id.origin) =
      (objects.filterMap (Object.toOriginRow? id.origin)).filter
        (·.suffix != id.suffix) := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      by_cases horigin : object.id.origin = id.origin
      · have hrow : Object.toOriginRow? id.origin object =
            some { suffix := object.id.suffix, promise := object.promise,
                   task := object.task } := by
          simp [Object.toOriginRow?, horigin]
        by_cases hsuffix : object.id.suffix = id.suffix
        · have hid : object.id = id := by
            cases hobj : object.id; cases id
            simp_all
          simp [List.filter_cons, hid, hrow, ih, hsuffix]
        · have hid : ¬ object.id = id := fun h => hsuffix (by rw [h])
          simp [List.filter_cons, hid, hrow, ih, hsuffix]
      · have hid : ¬ object.id = id := fun h => horigin (by rw [h])
        simp [List.filter_cons, hid, toOriginRow?_eq_none horigin, ih]

theorem filterMap_filter_id_other (objects : List Object) (id : Ident)
    {other : String} (h : other ≠ id.origin) :
    (objects.filter (·.id != id)).filterMap (Object.toOriginRow? other) =
      objects.filterMap (Object.toOriginRow? other) := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      by_cases hid : object.id = id
      · have horigin : object.id.origin ≠ other := by rw [hid]; exact Ne.symm h
        simp [List.filter_cons, hid, toOriginRow?_eq_none horigin, ih]
      · have hkeep : (object.id != id) = true := by simp [hid]
        rw [List.filter_cons, if_pos hkeep, List.filterMap_cons, List.filterMap_cons, ih]

theorem read_mk_origin (objects : List Object) (schedules : List Schedule)
    (origin : String) :
    Store.read { objects, schedules } (.origin origin) =
      objects.filterMap (Object.toOriginRow? origin) := rfl

theorem read_origin (store : Store) (origin : String) :
    store.read (.origin origin) =
      store.objects.filterMap (Object.toOriginRow? origin) := rfl

theorem toOriginRow?_mk (id : Ident) (promise : PromiseObject)
    (task : Option TaskObject) :
    Object.toOriginRow? id.origin { id, promise, task } =
      some { suffix := id.suffix, promise, task } := by
  simp [Object.toOriginRow?]

theorem toOriginRow?_mk_other (id : Ident) (promise : PromiseObject)
    (task : Option TaskObject) {other : String} (h : other ≠ id.origin) :
    Object.toOriginRow? other { id, promise, task } = none :=
  toOriginRow?_eq_none (Ne.symm h)

/-- What the abstract store does to an origin document when it upserts
`object` at its id. -/
theorem read_upsert_same (store : Store) (object : Object) (id : Ident)
    (hid : object.id = id) :
    Store.read { store with objects := object :: store.objects.filter (·.id != id) }
        (.origin id.origin) =
      (Object.toOriginRow? id.origin object).toList ++
        (store.read (.origin id.origin)).filter (·.suffix != id.suffix) := by
  rw [read_mk_origin, List.filterMap_cons, filterMap_filter_id_same, read_origin]
  cases Object.toOriginRow? id.origin object <;> rfl

theorem read_upsert_other (store : Store) (object : Object) (id : Ident)
    (hid : object.id = id) {other : String} (h : other ≠ id.origin) :
    Store.read { store with objects := object :: store.objects.filter (·.id != id) }
        (.origin other) = store.read (.origin other) := by
  subst hid
  rw [read_mk_origin, List.filterMap_cons, filterMap_filter_id_other _ _ h,
    toOriginRow?_eq_none (Ne.symm h), read_origin]

theorem setPromise_sim (id : Ident) (promise : PromiseObject) :
    Sim (.origin id.origin) Eq (Abstract.setPromise id promise)
      (Concrete.Decision.setPromise id.suffix promise) := by
  intro env store
  refine ⟨rfl, ?_, rfl⟩
  simp only [Abstract.setPromise, Concrete.Decision.setPromise,
    Concrete.Decision.modify, documentModify]
  have hget := getObject_eq_read store id
  cases hfind : (store.read (.origin id.origin)).find? (·.suffix == id.suffix) with
  | none =>
      rw [hfind] at hget
      simp only [Option.map_none] at hget
      simp only [Store.setPromise, hget]
      refine same_write_origin rfl ?_ ?_
      · rw [read_upsert_same _ _ _ rfl]
        simp [toOriginRow?_mk]
      · intro other hother
        exact read_upsert_other store _ _ rfl hother
  | some existing =>
      rw [hfind] at hget
      simp only [Option.map_some] at hget
      have hsuffix : existing.suffix = id.suffix := by
        simpa using List.find?_some hfind
      have hid : (Object.ofOrigin existing).id = id := by
        cases id
        simp [Object.ofOrigin, hsuffix]
      simp only [Store.setPromise, hget]
      refine same_write_origin rfl ?_ ?_
      · exact (read_upsert_same store
          { id := (Object.ofOrigin existing).id, promise := promise, task := existing.task }
          id hid).trans (by simp [Object.toOriginRow?, Object.ofOrigin, hsuffix])
      · intro other hother
        exact read_upsert_other store
          { id := (Object.ofOrigin existing).id, promise := promise, task := existing.task }
          id hid hother

theorem setObject_sim {origin : String} (row : OriginObject origin) :
    Sim (.origin origin) Eq (Abstract.setObject (Object.ofOrigin row))
      (Concrete.Decision.setObject row) := by
  intro env store
  refine ⟨rfl, ?_, rfl⟩
  simp only [Abstract.setObject, Concrete.Decision.setObject,
    Concrete.Decision.modify, documentModify, Store.setObject]
  have hid : (Object.ofOrigin row).id = { origin, suffix := row.suffix } := rfl
  refine same_write_origin (origin := origin) rfl ?_ ?_
  · exact (read_upsert_same store (Object.ofOrigin row) _ hid).trans
      (by rw [Object.toOriginRow?_ofOrigin]; rfl)
  · intro other hother
    exact read_upsert_other store (Object.ofOrigin row) _ hid hother

theorem filterMap_setTask_same (objects : List Object) (id : Ident)
    (task : TaskObject) :
    (objects.map fun object =>
        if object.id == id then { object with task := some task } else object).filterMap
        (Object.toOriginRow? id.origin) =
      (objects.filterMap (Object.toOriginRow? id.origin)).map fun object =>
        if object.suffix == id.suffix then { object with task := some task } else object := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      by_cases horigin : object.id.origin = id.origin
      · have hrow : Object.toOriginRow? id.origin object =
            some { suffix := object.id.suffix, promise := object.promise,
                   task := object.task } := by
          simp [Object.toOriginRow?, horigin]
        rw [hrow]
        by_cases hsuffix : object.id.suffix = id.suffix
        · have hid : object.id = id := by
            cases hobj : object.id; cases id
            simp_all
          have hq : (object.id == id) = true := by simp [hid]
          have hp : (object.id.suffix == id.suffix) = true := by simp [hsuffix]
          simp only [hq, hp, ite_true, List.map_cons]
          rw [ih]
          simp [Object.toOriginRow?, horigin]
        · have hid : ¬ object.id = id := fun h => hsuffix (by rw [h])
          have hq : (object.id == id) = false := by simp [hid]
          have hp : (object.id.suffix == id.suffix) = false := by simp [hsuffix]
          simp only [hq, hp, hrow, Bool.false_eq_true, ↓reduceIte, List.map_cons]
          rw [ih]
      · have hid : ¬ object.id = id := fun h => horigin (by rw [h])
        have hq : (object.id == id) = false := by simp [hid]
        simp only [hq, Bool.false_eq_true, ↓reduceIte, toOriginRow?_eq_none horigin]
        exact ih

theorem filterMap_setTask_other (objects : List Object) (id : Ident)
    (task : TaskObject) {other : String} (h : other ≠ id.origin) :
    (objects.map fun object =>
        if object.id == id then { object with task := some task } else object).filterMap
        (Object.toOriginRow? other) =
      objects.filterMap (Object.toOriginRow? other) := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      by_cases hid : object.id = id
      · have horigin : object.id.origin ≠ other := by rw [hid]; exact Ne.symm h
        have hq : (object.id == id) = true := by simp [hid]
        have hnone : Object.toOriginRow? other
            { object with task := some task } = none := toOriginRow?_eq_none horigin
        simp only [hq, ite_true, hnone, toOriginRow?_eq_none horigin]
        exact ih
      · have hq : (object.id == id) = false := by simp [hid]
        simp only [hq, Bool.false_eq_true, ↓reduceIte]
        rw [ih]

theorem setTask_sim (id : Ident) (task : TaskObject) :
    Sim (.origin id.origin) Eq (Abstract.setTask id task)
      (Concrete.Decision.setTask id.suffix task) := by
  intro env store
  refine ⟨rfl, ?_, rfl⟩
  simp only [Abstract.setTask, Concrete.Decision.setTask,
    Concrete.Decision.modify, documentModify, Store.setTask]
  refine same_write_origin rfl ?_ ?_
  · exact filterMap_setTask_same store.objects id task
  · intro other hother
    exact filterMap_setTask_other store.objects id task hother

theorem scheduleAt_go_find (id : Ident) (schedules : List Schedule) :
    (Store.scheduleAt.go id schedules).map ScheduleData.toSchedule =
      schedules.find? (·.id == id) := by
  induction schedules with
  | nil => rfl
  | cons schedule rest ih =>
      by_cases h : schedule.id = id
      · subst h
        simp [Store.scheduleAt.go, ScheduleData.toSchedule, ScheduleData.ofSchedule]
      · simp [Store.scheduleAt.go, h, ih]

theorem getSchedule_eq_read (store : Store) (id : Ident) :
    store.getSchedule id = (store.read (.schedule id)).map ScheduleData.toSchedule :=
  (scheduleAt_go_find id store.schedules).symm

theorem getSchedule_sim (id : Ident) :
    Sim (.schedule id) Eq (Abstract.getSchedule id)
      (Concrete.Decision.getSchedule (id := id)) := by
  intro env store
  refine ⟨?_, Same.symm (Store.read_write_read store _), rfl⟩
  simp [Abstract.getSchedule, Concrete.Decision.getSchedule, getSchedule_eq_read,
    bind, Concrete.Decision.get, documentGet, pure]

theorem setSchedule_sim (id : Ident) (schedule : Schedule) (h : schedule.id = id) :
    Sim (.schedule id) Eq (Abstract.setSchedule schedule)
      (Concrete.Decision.setScheduleValue (id := id) schedule) := by
  subst h
  intro env store
  refine ⟨rfl, ?_, rfl⟩
  have : store.setSchedule schedule =
      store.write (.schedule schedule.id)
        (some (ScheduleData.ofSchedule schedule)) := by
    simp [Store.setSchedule, Store.write, ScheduleData.toSchedule,
      ScheduleData.ofSchedule]
  simp only [Abstract.setSchedule, Concrete.Decision.setScheduleValue,
    Concrete.Decision.setSchedule, Concrete.Decision.set, documentSet, this]
  exact Same.refl _

theorem deleteSchedule_sim (id : Ident) :
    Sim (.schedule id) Eq (Abstract.deleteSchedule id)
      (Concrete.Decision.delSchedule (id := id)) := by
  intro env store
  refine ⟨rfl, ?_, rfl⟩
  have : store.deleteSchedule id = store.write (.schedule id) none := by
    simp [Store.deleteSchedule, Store.write]
  simp only [Abstract.deleteSchedule, Concrete.Decision.delSchedule,
    Concrete.Decision.set, documentSet, this]
  exact Same.refl _

theorem setMessage_sim {key : DocumentKey} (address : String)
    (message : ServerModel.Message) :
    Sim key Eq (Abstract.setMessage address message)
      (Concrete.Decision.setMessage (key := key) address message) := by
  intro env store
  exact ⟨rfl, Same.symm (Store.read_write_read store _), rfl⟩

theorem ask_sim {key : DocumentKey} :
    Sim key Eq Abstract.ask (Concrete.Decision.ask (key := key)) := by
  intro env store
  exact ⟨rfl, Same.symm (Store.read_write_read store _), rfl⟩

theorem ofOrigin_project {origin : String} (row : OriginObject origin) (now : Nat) :
    (Object.ofOrigin row).project now = Object.ofOrigin (row.project now) := rfl

theorem readObject_sim (id : Ident) (now : Nat) :
    Sim (.origin id.origin) (ObjRel id.origin id.suffix) (Abstract.readObject id now)
      (Concrete.Decision.readObject id.suffix now) := by
  unfold Abstract.readObject Concrete.Decision.readObject
  refine Sim.bind (getObject_sim id) ?_
  refine ObjRel.cases ?_ fun promise task => ?_
  · exact Sim.pure ⟨rfl, by simp⟩
  · exact Sim.pure ⟨rfl, by simp [OriginObject.project]⟩

/-- An abstract task read corresponds to the concrete read followed by a
match on the task. -/
def TaskRel (origin suffix : String) (a : Option (Object × TaskObject))
    (c : Option (OriginObject origin)) : Prop :=
  a = c.bind (fun row => row.task.map (Object.ofOrigin row, ·)) ∧
    ∀ row, c = some row → row.suffix = suffix

theorem readTask_sim (id : Ident) (now : Nat) :
    Sim (.origin id.origin) (TaskRel id.origin id.suffix) (Abstract.readTask id now)
      (Concrete.Decision.readTaskObject id.suffix now) := by
  intro env store
  have ha : Abstract.readTask id now env store =
      ((((store.getObject id).map (·.project now)).bind fun o => o.task.map (o, ·)),
        store, []) := by
    simp only [Abstract.readTask, Abstract.readObject, Abstract.getObject, bind, pure]
    cases store.getObject id <;> rfl
  have hc : Concrete.Decision.readTaskObject id.suffix now env
        (store.read (.origin id.origin)) =
      ((match (store.read (.origin id.origin)).find? (·.suffix == id.suffix) with
        | some row => if row.task.isSome then some (row.project now) else none
        | none => none),
        store.read (.origin id.origin), []) := by
    simp only [Concrete.Decision.readTaskObject, Concrete.Decision.readObject,
      Concrete.Decision.getObject, Concrete.Decision.get, documentGet, bind, pure]
    cases hfind : (store.read (.origin id.origin)).find? (·.suffix == id.suffix) with
    | none => rfl
    | some row => cases ht : row.task.isSome <;> simp [hfind, ht]
  rw [ha, hc, getObject_eq_read]
  refine ⟨?_, Same.symm (Store.read_write_read store _), rfl⟩
  cases hfind : (store.read (.origin id.origin)).find? (·.suffix == id.suffix) with
  | none => exact ⟨rfl, by simp⟩
  | some row =>
      have hsuffix := find?_suffix hfind
      cases htask : row.task with
      | none => exact ⟨by simp [htask, Object.project, Object.ofOrigin], by simp [htask]⟩
      | some task =>
          refine ⟨?_, ?_⟩
          · simp [htask, Object.project, Object.ofOrigin, OriginObject.project]
          · simpa [htask, OriginObject.project] using hsuffix

/-! ## Composing simulations -/

theorem Sim.ite {key : DocumentKey} {R : α → β → Prop} (p : Prop) [Decidable p]
    {a₁ a₂ : Abstract.Handler α} {c₁ c₂ : DocumentHandler key β}
    (h₁ : p → Sim key R a₁ c₁) (h₂ : ¬ p → Sim key R a₂ c₂) :
    Sim key R (if p then a₁ else a₂) (if p then c₁ else c₂) := by
  by_cases hp : p
  · simpa [hp] using h₁ hp
  · simpa [hp] using h₂ hp

theorem Sim.seq {key : DocumentKey} {S : γ → δ → Prop}
    {ma : Abstract.Handler Unit} {mc : DocumentHandler key Unit}
    {fa : Abstract.Handler γ} {fc : DocumentHandler key δ}
    (hm : Sim key Eq ma mc) (hf : Sim key S fa fc) :
    Sim key S (ma >>= fun _ => fa) (mc >>= fun _ => fc) :=
  Sim.bind hm fun _ _ _ => hf

theorem createPromiseAt_sim (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) :
    Sim (.origin id.origin) (fun a c => a = Object.ofOrigin c)
      (Abstract.createPromiseAt id timeoutAt now param tags)
      (Concrete.Decision.createPromiseAt id.suffix timeoutAt now param tags) := by
  unfold Abstract.createPromiseAt Concrete.Decision.createPromiseAt
  refine Sim.ite _ (fun _ => ?_) (fun _ => ?_)
  · refine Sim.bind (setPromise_sim _ _) fun _ _ _ => ?_
    refine Sim.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact Sim.bind (setTask_sim _ _) fun _ _ _ => Sim.pure rfl
    · exact Sim.pure rfl
  · refine Sim.bind (setPromise_sim _ _) fun _ _ _ => ?_
    refine Sim.ite _ (fun _ => ?_) (fun _ => ?_)
    · exact Sim.bind (setTask_sim _ _) fun _ _ _ => Sim.pure rfl
    · exact Sim.pure rfl

theorem createPromiseAt_sim' (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) {origin : String} (h : id.origin = origin) :
    Sim (.origin origin) (fun a c => a = Object.ofOrigin c)
      (Abstract.createPromiseAt id timeoutAt now param tags)
      (Concrete.Decision.createPromiseAt (origin := origin) id.suffix timeoutAt now
        param tags) := by
  subst h; exact createPromiseAt_sim id timeoutAt now param tags

theorem TaskRel.cases {origin suffix : String} {P : Option (Object × TaskObject) →
      Option (OriginObject origin) → Prop}
    (hnone : P none none)
    (hnotask : ∀ promise, P none (some ⟨suffix, promise, none⟩))
    (hsome : ∀ promise task,
      P (some (Object.ofOrigin (⟨suffix, promise, some task⟩ : OriginObject origin), task))
        (some ⟨suffix, promise, some task⟩)) :
    ∀ a c, TaskRel origin suffix a c → P a c := by
  rintro a (_ | ⟨rowSuffix, promise, _ | task⟩) ⟨rfl, hsuffix⟩
  · exact hnone
  · have := hsuffix _ rfl
    simp only at this
    subst this
    exact hnotask promise
  · have := hsuffix _ rfl
    simp only at this
    subst this
    exact hsome promise task

theorem getObject_sim' (id : Ident) {origin : String} (h : id.origin = origin) :
    Sim (.origin origin) (ObjRel origin id.suffix) (Abstract.getObject id)
      (Concrete.Decision.getObject (origin := origin) id.suffix) := by
  subst h; exact getObject_sim id

theorem readObject_sim' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) :
    Sim (.origin origin) (ObjRel origin id.suffix) (Abstract.readObject id now)
      (Concrete.Decision.readObject (origin := origin) id.suffix now) := by
  subst h; exact readObject_sim id now

theorem readTask_sim' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) :
    Sim (.origin origin) (TaskRel origin id.suffix) (Abstract.readTask id now)
      (Concrete.Decision.readTaskObject (origin := origin) id.suffix now) := by
  subst h; exact readTask_sim id now

theorem setPromise_sim' (id : Ident) (promise : PromiseObject) {origin : String}
    (h : id.origin = origin) :
    Sim (.origin origin) Eq (Abstract.setPromise id promise)
      (Concrete.Decision.setPromise (origin := origin) id.suffix promise) := by
  subst h; exact setPromise_sim id promise

theorem setTask_sim' (id : Ident) (task : TaskObject) {origin : String}
    (h : id.origin = origin) :
    Sim (.origin origin) Eq (Abstract.setTask id task)
      (Concrete.Decision.setTask (origin := origin) id.suffix task) := by
  subst h; exact setTask_sim id task

/-! ## Rewriting abstract handlers -/

theorem Abstract.bind_assoc (x : Abstract.Handler α) (f : α → Abstract.Handler β)
    (g : β → Abstract.Handler γ) : (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  funext env store
  simp only [bind, List.append_assoc]

theorem Abstract.pure_bind (a : α) (f : α → Abstract.Handler β) :
    (Pure.pure a : Abstract.Handler α) >>= f = f a := by
  funext env store
  simp only [bind, Pure.pure, List.nil_append]

instance : LawfulMonad Abstract.Handler := LawfulMonad.mk'
  (id_map := fun x => by
    funext env store
    show (let (v, s, e) := x env store; (v, s, e ++ [])) = x env store
    simp)
  (pure_bind := fun a f => Abstract.pure_bind a f)
  (bind_assoc := fun x f g => Abstract.bind_assoc x f g)

theorem Abstract.ite_bind (p : Prop) [Decidable p] (x y : Abstract.Handler α)
    (f : α → Abstract.Handler β) :
    (if p then x else y) >>= f = if p then x >>= f else y >>= f := by
  split <;> rfl

theorem Store.setTask_setTask (store : Store) (id : Ident) (first second : TaskObject) :
    (store.setTask id first).setTask id second = store.setTask id second := by
  simp only [Store.setTask, List.map_map, Store.mk.injEq, and_true]
  apply List.map_congr_left
  intro object _
  by_cases h : object.id = id <;> simp [h]

theorem Abstract.setTask_setTask (id : Ident) (first second : TaskObject)
    (f : Unit → Abstract.Handler α) :
    (Abstract.setTask id first >>= fun _ => Abstract.setTask id second >>= f) =
      Abstract.setTask id second >>= f := by
  funext env store
  simp only [bind, Abstract.setTask, Store.setTask_setTask, List.nil_append]

theorem Concrete.pure_bind {key : DocumentKey} (u : α) (f : α → DocumentHandler key β) :
    (Pure.pure u : DocumentHandler key α) >>= f = f u := by
  funext env document
  simp only [bind, Pure.pure, List.nil_append]

/-- Close the side condition that an id lies in the document's origin. -/
macro "sim_origin" : tactic => `(tactic| first
  | rfl
  | (simp_all [Ident.sameOrigin, TaskFenceAction.targetId]; done)
  | (simp_all [Ident.sameOrigin, TaskFenceAction.targetId, Ident.ext_iff]; done))

def lastString : Lean.Name → String
  | .str _ s => s
  | _ => ""

open Lean Meta Elab Tactic in
/-- One step of a handler simulation, chosen by the head of the abstract
handler. -/
elab "sim_dispatch" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Sim 6 do throwError "sim_step: not a Sim goal"
  let a := (← instantiateMVars target.getAppArgs[4]!).headBeta
  let run (stx : MetaM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)
  if a.isAppOf ``Pure.pure then
    run `(tactic| exact Sim.pure rfl)
  else if a.isAppOf ``ite then
    run `(tactic| refine Sim.ite _ (fun _ => ?_) (fun _ => ?_))
  else if a.isAppOf ``Bind.bind && a.getAppNumArgs == 6 then
    let ma := (← instantiateMVars a.getAppArgs[4]!).headBeta
    match ma.getAppFn.constName? with
    | some ``Pure.pure =>
        run `(tactic| refine Sim.bind (Sim.pure (R := Eq) rfl) fun _ _ _ => ?_)
    | some ``Resonate.Abstract.readObject =>
        run `(tactic| (refine Sim.bind (readObject_sim' _ _ (by sim_origin)) ?_
                       refine ObjRel.cases ?_ (fun _ _ => ?_)))
    | some ``Resonate.Abstract.getObject =>
        run `(tactic| (refine Sim.bind (getObject_sim' _ (by sim_origin)) ?_
                       refine ObjRel.cases ?_ (fun _ _ => ?_)))
    | some ``Resonate.Abstract.readTask =>
        run `(tactic| (refine Sim.bind (readTask_sim' _ _ (by sim_origin)) ?_
                       refine TaskRel.cases ?_ (fun _ => ?_) (fun _ _ => ?_)))
    | some ``Resonate.Abstract.getSchedule =>
        run `(tactic| (refine Sim.bind (getSchedule_sim _) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.createPromiseAt =>
        run `(tactic| (refine Sim.bind (createPromiseAt_sim' _ _ _ _ _ (by sim_origin)) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.setPromise =>
        run `(tactic| refine Sim.bind (setPromise_sim' _ _ (by sim_origin)) fun _ _ _ => ?_)
    | some ``Resonate.Abstract.setTask =>
        run `(tactic| refine Sim.bind (setTask_sim' _ _ (by sim_origin)) fun _ _ _ => ?_)
    | some ``Resonate.Abstract.ask =>
        run `(tactic| (refine Sim.bind ask_sim ?_; intro _ _ h; subst h))
    | some ``Bind.bind =>
        run `(tactic| refine Sim.bind (R := Eq) ?_ fun _ _ h => ?_)
    | some ``ite =>
        run `(tactic| refine Sim.bind (R := Eq) ?_ fun _ _ h => ?_)
    | some name =>
        let lemma := mkIdent (Name.mkSimple (lastString name ++ "_sim"))
        run `(tactic| (refine Sim.bind (R := Eq) ?_ ?_
                       · apply $lemma <;> sim_origin
                       intro _ _ h; subst h))
    | none =>
        run `(tactic| refine Sim.bind (R := Eq) ?_ fun _ _ h => ?_)
  else
    match a.getAppFn.constName? with
    | some ``Resonate.Abstract.setPromise =>
        run `(tactic| exact setPromise_sim' _ _ (by sim_origin))
    | some ``Resonate.Abstract.setTask =>
        run `(tactic| exact setTask_sim' _ _ (by sim_origin))
    | some ``Resonate.Abstract.setObject =>
        run `(tactic| exact setObject_sim _)
    | some ``Resonate.Abstract.setMessage =>
        run `(tactic| exact setMessage_sim _ _)
    | some ``Resonate.Abstract.deleteSchedule =>
        run `(tactic| exact deleteSchedule_sim _)
    | some ``Resonate.Abstract.setSchedule =>
        run `(tactic| exact setSchedule_sim _ _ rfl)
    | some name =>
        if (← Lean.Meta.isMatcher name) then
          run `(tactic| first
            | dsimp only [Object.ofOrigin]
            | (split <;> try (rename_i heq; simp only [heq])))
        else if name.getPrefix == `Resonate.Abstract then
          let lemma := mkIdent (Name.mkSimple (lastString name ++ "_sim"))
          run `(tactic| (apply $lemma <;> sim_origin))
        else
          run `(tactic| dsimp only [Object.ofOrigin])
    | none => run `(tactic| dsimp only [Object.ofOrigin])

macro "sim_step" : tactic => `(tactic| first
  | sim_dispatch
  | dsimp only [Object.ofOrigin]
  | simp only [Concrete.pure_bind, Abstract.pure_bind, Option.isNone_none,
      Option.isNone_some, Bool.false_eq_true, ↓reduceIte])

macro "sim" : tactic => `(tactic| repeat' sim_step)

theorem promiseGet_sim (req : PromiseGetReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.promiseGet req now)
      (Concrete.Decision.promiseGet req now) := by
  unfold Abstract.promiseGet Concrete.Decision.promiseGet
  sim

theorem promiseCreate_sim (req : PromiseCreateReq) (now : Nat) {origin : String}
    (h : req.id.origin = origin) :
    Sim (.origin origin) Eq (Abstract.promiseCreate req now)
      (Concrete.Decision.promiseCreateAt (origin := origin) req now) := by
  subst h
  unfold Abstract.promiseCreate Concrete.Decision.promiseCreateAt
  sim

theorem promiseSettle_sim (req : PromiseSettleReq) (now : Nat) {origin : String}
    (h : req.id.origin = origin) :
    Sim (.origin origin) Eq (Abstract.promiseSettle req now)
      (Concrete.Decision.promiseSettleAt (origin := origin) req now) := by
  subst h
  unfold Abstract.promiseSettle Concrete.Decision.promiseSettleAt
    Abstract.setSettled Concrete.Decision.setSettled
  sim

theorem promiseRegisterCallback_sim (req : PromiseRegisterCallbackReq) (now : Nat) :
    Sim (.origin req.awaited.origin) Eq (Abstract.promiseRegisterCallback req now)
      (Concrete.Decision.promiseRegisterCallback req now) := by
  unfold Abstract.promiseRegisterCallback Concrete.Decision.promiseRegisterCallback
  sim

theorem promiseRegisterListener_sim (req : PromiseRegisterListenerReq) (now : Nat) :
    Sim (.origin req.awaited.origin) Eq (Abstract.promiseRegisterListener req now)
      (Concrete.Decision.promiseRegisterListener req now) := by
  unfold Abstract.promiseRegisterListener Concrete.Decision.promiseRegisterListener
  sim

theorem scheduleGet_sim (req : ScheduleGetReq) (now : Nat) :
    Sim (.schedule req.id) Eq (Abstract.scheduleGet req now)
      (Concrete.Decision.scheduleGet req now) := by
  unfold Abstract.scheduleGet Concrete.Decision.scheduleGet
  sim

theorem scheduleCreate_sim (req : ScheduleCreateReq) (now : Nat) :
    Sim (.schedule req.id) Eq (Abstract.scheduleCreate req now)
      (Concrete.Decision.scheduleCreate req now) := by
  unfold Abstract.scheduleCreate Concrete.Decision.scheduleCreate
  sim

theorem scheduleDelete_sim (req : ScheduleDeleteReq) (now : Nat) :
    Sim (.schedule req.id) Eq (Abstract.scheduleDelete req now)
      (Concrete.Decision.scheduleDelete req now) := by
  unfold Abstract.scheduleDelete Concrete.Decision.scheduleDelete
  sim

theorem taskGet_sim (req : TaskGetReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskGet req now)
      (Concrete.Decision.taskGet req now) := by
  unfold Abstract.taskGet Concrete.Decision.taskGet
  sim

theorem taskAcquire_sim (req : TaskAcquireReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskAcquire req now)
      (Concrete.Decision.taskAcquire req now) := by
  unfold Abstract.taskAcquire Concrete.Decision.taskAcquire
  sim

theorem taskFence_sim (req : TaskFenceReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskFence req now)
      (Concrete.Decision.taskFence req now) := by
  obtain ⟨id, version, action⟩ := req
  unfold Abstract.taskFence Concrete.Decision.taskFence
  cases action <;> sim

theorem taskFulfill_sim (req : TaskFulfillReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskFulfill req now)
      (Concrete.Decision.taskFulfill req now) := by
  unfold Abstract.taskFulfill Concrete.Decision.taskFulfill
    Abstract.setSettled Concrete.Decision.setSettled
  sim

theorem taskRelease_sim (req : TaskReleaseReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskRelease req now)
      (Concrete.Decision.taskRelease req now) := by
  unfold Abstract.taskRelease Concrete.Decision.taskRelease
  sim

theorem taskHalt_sim (req : TaskHaltReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskHalt req now)
      (Concrete.Decision.taskHalt req now) := by
  unfold Abstract.taskHalt Concrete.Decision.taskHalt
  sim

theorem taskContinue_sim (req : TaskContinueReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskContinue req now)
      (Concrete.Decision.taskContinue req now) := by
  unfold Abstract.taskContinue Concrete.Decision.taskContinue
  sim

theorem Tags.not_timer_of_runnable {tags : Tags} (hrun : tags.otype = .runnable)
    (htimer : tags.timerTargeted = false) : tags.isTimer = false := by
  have htarget : tags.has "resonate:target" = true := by
    unfold Tags.otype at hrun
    split at hrun
    · assumption
    · split at hrun <;> cases hrun
  simpa [Tags.timerTargeted, htarget] using htimer

theorem taskCreate_sim (req : TaskCreateReq) (now : Nat) :
    Sim (.origin req.action.id.origin) Eq (Abstract.taskCreate req now)
      (Concrete.Decision.taskCreate req now) := by
  unfold Abstract.taskCreate Concrete.Decision.taskCreate
  sim
  rename_i hguard _ _ _
  simp only [not_or, bne_iff_ne, ne_eq, Decidable.not_not, Bool.not_eq_true] at hguard
  obtain ⟨hrun, htimer⟩ := hguard
  have hnotimer := Tags.not_timer_of_runnable hrun htimer
  unfold Abstract.createPromiseAt
  rw [Abstract.ite_bind]
  refine Sim.ite _ (fun _ => ?_) (fun _ => ?_)
  · simp only [Abstract.bind_assoc, Abstract.pure_bind, Abstract.ite_bind, AbstractModel.PromiseObject.otype, hrun,
      beq_self_eq_true, ↓reduceIte, Abstract.setTask_setTask]
    sim
  · simp only [Abstract.bind_assoc, Abstract.pure_bind, Abstract.ite_bind, AbstractModel.PromiseObject.otype, hrun,
      hnotimer, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte,
      show (PromiseState.rejectedTimedout == PromiseState.pending) = false from rfl]
    sim

theorem Sim.bind_left {key : DocumentKey} {R : α → β → Prop} {S : γ → δ → Prop}
    {ma : Abstract.Handler α} {u : β} {fa : α → Abstract.Handler γ}
    {mc : DocumentHandler key δ}
    (hm : Sim key R ma (Pure.pure u)) (hf : ∀ a, R a u → Sim key S (fa a) mc) :
    Sim key S (ma >>= fa) mc := by
  intro env store
  obtain ⟨hr, hsame, hemit⟩ := hm env store
  have hs : Same (ma env store).2.1 store :=
    hsame.trans (Store.read_write_read store key)
  have hread : (ma env store).2.1.read key = store.read key := hs key
  obtain ⟨hr', hsame', hemit'⟩ := hf _ hr env (ma env store).2.1
  rw [hread] at hr' hsame' hemit'
  refine ⟨hr', hsame'.trans (Same.write hs key _), ?_⟩
  show (ma env store).2.2 ++ (fa (ma env store).1 env (ma env store).2.1).2.2 = _
  rw [hemit', hemit]
  rfl

/-- A handler that only reads simulates doing nothing. -/
theorem Sim.readOnly {key : DocumentKey} {ma : Abstract.Handler α}
    (h : ∀ env store, (ma env store).2 = (store, [])) :
    Sim key (fun _ _ => True) ma (Pure.pure ()) := by
  intro env store
  refine ⟨trivial, ?_, ?_⟩
  · rw [h env store]
    exact Same.symm (Store.read_write_read store key)
  · rw [h env store]
    rfl

/-! ## Heartbeat -/

theorem heartbeatOne_sim (pid : String) (ref : TaskRef) (now : Nat) {origin : String}
    (h : ref.id.origin = origin) :
    Sim (.origin origin) Eq (Abstract.heartbeatOne pid ref now)
      (Concrete.Decision.heartbeatOne (origin := origin) pid ref now) := by
  subst h
  unfold Abstract.heartbeatOne Concrete.Decision.heartbeatOne
  sim

theorem heartbeatAll_sim (pid : String) (now : Nat) {origin : String} :
    ∀ refs : List TaskRef, (∀ ref ∈ refs, ref.id.origin = origin) →
      Sim (.origin origin) Eq (refs.forM (Abstract.heartbeatOne pid · now))
        (Concrete.Decision.heartbeatAll (origin := origin) pid now refs)
  | [], _ => by
      simp only [List.forM_nil, Concrete.Decision.heartbeatAll]
      exact Sim.pure rfl
  | ref :: rest, h => by
      simp only [List.forM_cons, Concrete.Decision.heartbeatAll]
      exact Sim.seq (heartbeatOne_sim pid ref now (h ref (by simp)))
        (heartbeatAll_sim pid now rest fun r hr => h r (by simp [hr]))

theorem taskHeartbeat_sim (req : TaskHeartbeatReq) (now : Nat) (first : TaskRef)
    (rest : List TaskRef) (htasks : req.tasks = first :: rest) :
    Sim (.origin first.id.origin) Eq (Abstract.taskHeartbeat req now)
      (Concrete.Decision.taskHeartbeat first.id.origin req now) := by
  unfold Abstract.taskHeartbeat Concrete.Decision.taskHeartbeat
  rw [htasks]
  have hcheck : (!sameOriginRefs first.id.origin (first :: rest)) =
      (first :: rest).any (fun ref => ref.id.origin != first.id.origin) := by
    simp only [sameOriginRefs, List.all_eq_not_any_not, Bool.not_not, bne]
  simp only [hcheck]
  refine Sim.ite _ (fun _ => Sim.pure rfl) (fun hall => ?_)
  refine Sim.seq (Sim.pure rfl) (Sim.seq (heartbeatAll_sim _ _ _ ?_) (Sim.pure rfl))
  simpa [bne_iff_ne] using hall

/-! ## Suspend -/

theorem mapM_readObject_state (now : Nat) :
    ∀ (actions : List PromiseRegisterCallbackReq) env store,
      (actions.mapM (Abstract.readObject ·.awaited now) env store).2 = (store, [])
  | [], _, _ => rfl
  | action :: rest, env, store => by
      rw [List.mapM_cons]
      have ih := mapM_readObject_state now rest
      generalize rest.mapM (Abstract.readObject ·.awaited now) = m at ih ⊢
      have hm := ih env store
      rcases h : m env store with ⟨v, s, e⟩
      rw [h] at hm
      cases hm
      simp [bind, Pure.pure, Abstract.readObject, Abstract.getObject, h]

/-- What the concrete `checkAwaited` says about the awaited objects. -/
def AwaitedRel (awaited : List (Option Object)) (check : Option Bool) : Prop :=
  check = if awaited.all (·.any (·.promise.otype.awaitable)) then
    some (awaited.any (·.any (·.promise.state != .pending))) else none

theorem checkAwaited_sim (now : Nat) {origin : String} :
    ∀ actions : List PromiseRegisterCallbackReq,
      (∀ action ∈ actions, action.awaited.origin = origin) →
      Sim (.origin origin) AwaitedRel (actions.mapM (Abstract.readObject ·.awaited now))
        (Concrete.Decision.checkAwaited (origin := origin) now actions)
  | [], _ => by
      simp only [List.mapM_nil, Concrete.Decision.checkAwaited]
      exact Sim.pure (by simp [AwaitedRel])
  | action :: rest, h => by
      rw [List.mapM_cons]
      simp only [Concrete.Decision.checkAwaited]
      refine Sim.bind (readObject_sim' _ _ (h action (by simp))) ?_
      refine ObjRel.cases ?_ (fun promise task => ?_)
      · exact Sim.bind_left (Sim.readOnly (mapM_readObject_state now rest))
          fun _ _ => Sim.pure (by simp [AwaitedRel])
      · dsimp only [Object.ofOrigin]
        by_cases hawait : promise.otype.awaitable
        · simp only [hawait, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Concrete.pure_bind]
          refine Sim.bind (checkAwaited_sim now rest fun a ha => h a (by simp [ha])) ?_
          intro awaited check hcheck
          rw [hcheck]
          by_cases hall : awaited.all (·.any (·.promise.otype.awaitable))
          · simp only [hall, ↓reduceIte]
            exact Sim.pure (by simp [AwaitedRel, hall, hawait, Bool.or_comm])
          · simp only [hall, Bool.false_eq_true, ↓reduceIte]
            exact Sim.pure (by simp [AwaitedRel, hall, hawait])
        · simp only [hawait, Bool.not_false, ↓reduceIte]
          exact Sim.bind_left (Sim.readOnly (mapM_readObject_state now rest))
            fun _ _ => Sim.pure (by simp [AwaitedRel, hawait])

theorem registerAwaited_sim (awaiter : Ident) (now : Nat) {origin : String} :
    ∀ actions : List PromiseRegisterCallbackReq,
      (∀ action ∈ actions, action.awaited.origin = origin) →
      Sim (.origin origin) Eq (actions.forM (Abstract.addCallback awaiter now))
        (Concrete.Decision.registerAwaited (origin := origin) awaiter now actions)
  | [], _ => by
      simp only [List.forM_nil, Concrete.Decision.registerAwaited]
      exact Sim.pure rfl
  | action :: rest, h => by
      have ih := registerAwaited_sim awaiter now rest fun a ha => h a (by simp [ha])
      simp only [List.forM, Concrete.Decision.registerAwaited, Abstract.addCallback,
        Abstract.bind_assoc]
      refine Sim.bind (readObject_sim' _ _ (h action (by simp))) ?_
      refine ObjRel.cases ?_ (fun _ _ => ?_)
      · exact Sim.seq (Sim.pure rfl) ih
      · exact Sim.seq (setPromise_sim' _ _ (h action (by simp))) ih

theorem taskSuspend_sim (req : TaskSuspendReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.taskSuspend req now)
      (Concrete.Decision.taskSuspend req now) := by
  unfold Abstract.taskSuspend Concrete.Decision.taskSuspend
  sim
  refine Sim.bind (checkAwaited_sim _ _ ?_) ?_
  · simp_all [Ident.sameOrigin]
  intro awaited check hcheck
  simp only [AwaitedRel] at hcheck
  subst hcheck
  by_cases hall : awaited.all (·.any (·.promise.otype.awaitable))
  · by_cases hany : awaited.any (·.any (·.promise.state != .pending))
    · simp only [hall, hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      sim
    · simp only [hall, hany, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      sim
      refine Sim.seq (registerAwaited_sim _ _ _ ?_) ?_
      · simp_all [Ident.sameOrigin]
      sim
  · simp only [hall, Bool.not_false, ↓reduceIte]
    sim

/-! ## Internal work -/

theorem processPromiseTimeout_sim (id : Ident) (now : Nat) :
    Sim (.origin id.origin) Eq (Abstract.processPromiseTimeout id now)
      (Concrete.Decision.processPromiseTimeout id now) := by
  unfold Abstract.processPromiseTimeout Concrete.Decision.processPromiseTimeout
  sim

theorem resumeOne_sim (awaited awaiter : Ident) (now : Nat) {origin : String}
    (h : awaiter.origin = origin) :
    Sim (.origin origin) Eq (Abstract.resumeOne awaited awaiter now)
      (Concrete.Decision.resumeOne (origin := origin) awaited awaiter now) := by
  subst h
  unfold Abstract.resumeOne Concrete.Decision.resumeOne
  sim

/-- The concrete callback step checks that the awaiter shares the awaited
origin; the abstract step relies on every registered callback doing so. -/
theorem processCallback_sim (req : PromiseRegisterCallbackReq) (now : Nat)
    (h : req.awaiter.origin = req.awaited.origin) :
    Sim (.origin req.awaited.origin) Eq (Abstract.processCallback req now)
      (Concrete.Decision.processCallback req now) := by
  unfold Abstract.processCallback Concrete.Decision.processCallback
  simp only [Ident.sameOrigin, h, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Concrete.pure_bind]
  sim

theorem processListener_sim (req : PromiseRegisterListenerReq) (now : Nat) :
    Sim (.origin req.awaited.origin) Eq (Abstract.processListener req now)
      (Concrete.Decision.processListener req now) := by
  unfold Abstract.processListener Concrete.Decision.processListener
  sim

theorem processLeaseTimeout_sim (id : Ident) (now : Nat) :
    Sim (.origin id.origin) Eq (Abstract.processLeaseTimeout id now)
      (Concrete.Decision.processLeaseTimeout id now) := by
  unfold Abstract.processLeaseTimeout Concrete.Decision.processLeaseTimeout
  sim

theorem processRetryTimeout_sim (id : Ident) (now : Nat) :
    Sim (.origin id.origin) Eq (Abstract.processRetryTimeout id now)
      (Concrete.Decision.processRetryTimeout id now) := by
  unfold Abstract.processRetryTimeout Concrete.Decision.processRetryTimeout
  sim

theorem createIfAbsent_sim (req : PromiseCreateReq) (now : Nat) :
    Sim (.origin req.id.origin) Eq (Abstract.createIfAbsent req now)
      (Concrete.Decision.processOccurrence req now) := by
  unfold Abstract.createIfAbsent Concrete.Decision.processOccurrence
    Concrete.Decision.createIfAbsent Concrete.Decision.createIfAbsentAt
  sim

theorem getSchedule_sim_id (id : Ident) :
    Sim (.schedule id) (fun a c => a = c ∧ ∀ schedule, c = some schedule → schedule.id = id)
      (Abstract.getSchedule id) (Concrete.Decision.getSchedule (id := id)) := by
  intro env store
  obtain ⟨h₁, h₂, h₃⟩ := getSchedule_sim id env store
  refine ⟨⟨h₁, ?_⟩, h₂, h₃⟩
  intro schedule hschedule
  simp only [Concrete.Decision.getSchedule, bind, documentGet, pure] at hschedule
  revert hschedule
  cases store.read (.schedule id) <;> simp
  rintro rfl
  rfl

/-- A concrete schedule step returns the occurrences as work items. -/
def OccurrenceRel (entries : List WorkflowEntry) (items : List WorkItem) : Prop :=
  items = entries.map fun entry => .occurrence entry.request entry.instant

theorem processSchedule_sim (id : Ident) (now : Nat) :
    Sim (.schedule id) OccurrenceRel (Abstract.processSchedule id now)
      (Concrete.Decision.processSchedule id now) := by
  unfold Abstract.processSchedule Concrete.Decision.processSchedule
  refine Sim.bind (getSchedule_sim_id id) ?_
  rintro a _ ⟨rfl, hid⟩
  cases a with
  | none => exact Sim.pure rfl
  | some schedule =>
    have hschedule : schedule.id = id := hid _ rfl
    dsimp only
    rcases (List.filter (fun x => decide (x ≤ now))
      (occurrences schedule.cron schedule.nextRunAt now)).getLast? with _ | last
    · exact Sim.seq (Sim.pure rfl) (Sim.pure (by simp [OccurrenceRel, hschedule]))
    · exact Sim.seq (setSchedule_sim _ _ hschedule)
        (Sim.pure (by simp [OccurrenceRel, hschedule]))

/-! ## Whole steps -/

theorem Abstract.map_apply (f : α → β) (m : Abstract.Handler α) (env : Abstract.Env)
    (store : Store) :
    (f <$> m) env store = (f (m env store).1, (m env store).2.1, (m env store).2.2) := by
  show (m >>= fun a => Pure.pure (f a)) env store = _
  simp only [bind, Pure.pure, List.append_nil]

/-- A request whose handler simulates a concrete decision runs as that
decision's candidate written back into the store. -/
theorem run_of_sim (appConfig : Resonate.Config) (call : Call) (state : State)
    {key : DocumentKey} {ma : Abstract.Handler β}
    {action : Concrete.Decision.Handler key β} {wrap : β → Response}
    (hhandler : Abstract.handler call.request call.requestedAt = wrap <$> ma)
    (hsim : Sim key Eq ma action) :
    let candidate :=
      Concrete.externalCandidate appConfig call (state.store.read key) action wrap
    let lifted := Abstract.run appConfig call state
    Same lifted.1.store (state.store.write key candidate.document) ∧
      lifted.1.workflow = state.workflow ∧
      lifted.2 = candidate.outputs ∧
      candidate.continuations = [] := by
  obtain ⟨hresult, hsame, hemit⟩ := hsim { config := appConfig.toServerConfig } state.store
  simp only [Abstract.run, Abstract.serve, hhandler, Abstract.map_apply,
    Concrete.externalCandidate, Concrete.Decision.run]
  exact ⟨hsame, trivial, by rw [hresult, hemit], trivial⟩

theorem external_sim_of (appConfig : Resonate.Config) (call : Call) (state : State)
    {key : DocumentKey} {ma : Abstract.Handler β}
    {action : Concrete.Decision.Handler key β} {wrap : β → Response}
    (hcandidate :
      Concrete.selectedExternalCandidate appConfig call key (state.store.read key) =
        some (Concrete.externalCandidate appConfig call (state.store.read key) action wrap))
    (hhandler : Abstract.handler call.request call.requestedAt = wrap <$> ma)
    (hsim : Sim key Eq ma action) :
    ∃ candidate,
      Concrete.selectedExternalCandidate appConfig call key (state.store.read key) =
        some candidate ∧
      let lifted := Abstract.run appConfig call state
      Same lifted.1.store (state.store.write key candidate.document) ∧
        lifted.1.workflow = state.workflow ∧
        lifted.2 = candidate.outputs ∧
        candidate.continuations = [] :=
  ⟨_, hcandidate, run_of_sim appConfig call state hhandler hsim⟩

/-- A request that names a document runs as the concrete candidate for that
document written back into the store. -/
theorem external_sim (appConfig : Resonate.Config) (call : Call) (key : DocumentKey)
    (hkey : (Concrete.Transaction.external call).key? = some key) (state : State) :
    ∃ candidate,
      Concrete.selectedExternalCandidate appConfig call key (state.store.read key) =
        some candidate ∧
      let lifted := Abstract.run appConfig call state
      Same lifted.1.store (state.store.write key candidate.document) ∧
        lifted.1.workflow = state.workflow ∧
        lifted.2 = candidate.outputs ∧
        candidate.continuations = [] := by
  cases hrequest : call.request <;>
    simp only [Concrete.Transaction.key?, hrequest] at hkey
  case promiseGet req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .promiseGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (promiseGet_sim req call.requestedAt)
  case promiseCreate req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .promiseCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast,
        Concrete.Decision.promiseCreate])
      (by rw [hrequest]; rfl) (promiseCreate_sim req call.requestedAt rfl)
  case promiseSettle req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .promiseSettle)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast,
        Concrete.Decision.promiseSettle])
      (by rw [hrequest]; rfl) (promiseSettle_sim req call.requestedAt rfl)
  case promiseRegisterCallback req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call state (wrap := .promiseRegisterCallback)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (promiseRegisterCallback_sim req call.requestedAt)
    · contradiction
  case promiseRegisterListener req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .promiseRegisterListener)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (promiseRegisterListener_sim req call.requestedAt)
  case scheduleGet req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .scheduleGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (scheduleGet_sim req call.requestedAt)
  case scheduleCreate req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .scheduleCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (scheduleCreate_sim req call.requestedAt)
  case scheduleDelete req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .scheduleDelete)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (scheduleDelete_sim req call.requestedAt)
  case taskGet req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .taskGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskGet_sim req call.requestedAt)
  case taskCreate req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .taskCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskCreate_sim req call.requestedAt)
  case taskAcquire req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .taskAcquire)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskAcquire_sim req call.requestedAt)
  case taskFence req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call state (wrap := .taskFence)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (taskFence_sim req call.requestedAt)
    · contradiction
  case taskHeartbeat req =>
    cases htasks : req.tasks with
    | nil => simp [htasks] at hkey
    | cons first rest =>
      simp only [htasks] at hkey
      split at hkey
      · cases hkey
        exact external_sim_of appConfig call state (wrap := .taskHeartbeat)
          (by simp [Concrete.selectedExternalCandidate, hrequest, htasks,
            Concrete.Candidate.cast])
          (by rw [hrequest]; rfl)
          (taskHeartbeat_sim req call.requestedAt first rest htasks)
      · contradiction
  case taskSuspend req =>
    split at hkey
    · contradiction
    · cases hkey
      exact external_sim_of appConfig call state (wrap := .taskSuspend)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (taskSuspend_sim req call.requestedAt)
  case taskFulfill req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call state (wrap := .taskFulfill)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (taskFulfill_sim req call.requestedAt)
    · contradiction
  case taskRelease req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .taskRelease)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskRelease_sim req call.requestedAt)
  case taskHalt req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .taskHalt)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskHalt_sim req call.requestedAt)
  case taskContinue req =>
    cases hkey
    exact external_sim_of appConfig call state (wrap := .taskContinue)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskContinue_sim req call.requestedAt)
  all_goals contradiction

/-- A request that names no document leaves the state alone and replies with
the concrete pure response. -/
theorem external_none (appConfig : Resonate.Config) (call : Call) (state : State)
    (hkey : (Concrete.Transaction.external call).key? = none) :
    Abstract.run appConfig call state =
      (state, [.response call.client call.id
        (Concrete.pureResponse call.requestedAt call.request)]) := by
  cases hrequest : call.request <;>
    simp only [Concrete.Transaction.key?, hrequest, reduceCtorEq] at hkey
  case promiseRegisterCallback req =>
    split at hkey
    · contradiction
    · rename_i horigin
      by_cases hsame : req.awaited == req.awaiter <;>
        simp_all [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
          Abstract.promiseRegisterCallback, Concrete.pureResponse, bind, Pure.pure]
  case taskFence req =>
    split at hkey
    · contradiction
    · rename_i hcondition
      by_cases hsame : req.action.targetId == req.id <;>
        simp_all [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
          Abstract.taskFence, Concrete.pureResponse, bind, Pure.pure]
  case taskHeartbeat req =>
    cases htasks : req.tasks with
    | nil =>
      simp [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
        Abstract.taskHeartbeat, Concrete.pureResponse, bind, Pure.pure, hrequest, htasks]
    | cons first rest =>
      simp only [htasks] at hkey
      split at hkey
      · contradiction
      · simp_all [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
          Abstract.taskHeartbeat, Concrete.pureResponse, bind, Pure.pure]
  case taskSuspend req =>
    split at hkey
    · rename_i hmismatch
      have hnonempty : req.actions.isEmpty = false := by
        cases hactions : req.actions <;> simp_all
      by_cases hself : req.actions.any (·.awaited == req.id) <;>
        simp_all [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
          Abstract.taskSuspend, Concrete.pureResponse, bind, Pure.pure]
    · contradiction
  case taskFulfill req =>
    split at hkey
    · contradiction
    · simp_all [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
        Abstract.taskFulfill, Concrete.pureResponse, bind, Pure.pure]
  all_goals
    simp [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
      Concrete.pureResponse, bind, Pure.pure, hrequest, Abstract.promiseSearch,
      Abstract.scheduleSearch, Abstract.taskSearch, Concrete.Decision.promiseSearch,
      Concrete.Decision.scheduleSearch, Concrete.Decision.taskSearch]

end Resonate.Refinement
