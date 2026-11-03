import Lean
import «concrete».Model
import «abstract».Model

/-!
# Abstract handlers simulate the concrete document decisions

The abstract handlers run on the whole store and address objects by id. The
concrete decisions run on one document and address objects by suffix.
`Sim key R abstract concrete` says that running `abstract` on a store with
unique ids gives what running `concrete` gives on any document with the same
entries as that store's document `key`, with the result document written back:
the results are related by `R`, every document view of the two stores has the
same entries, the emitted messages are equal, and ids stay unique.

Rows of an origin document are compared as a multiset: both sides look rows
up by suffix, so their order carries no meaning.
-/

namespace Resonate.Refinement

open ServerModel

/-- Two documents with the same entries. -/
def DocEquiv : (key : DocumentKey) → Document key → Document key → Prop
  | .origin _, a, b => List.Perm a b
  | .schedule _, a, b => a = b

theorem DocEquiv.refl : (key : DocumentKey) → (document : Document key) →
    DocEquiv key document document
  | .origin _, document => List.Perm.refl document
  | .schedule _, _ => rfl

theorem DocEquiv.of_eq {key : DocumentKey} {a b : Document key} (h : a = b) :
    DocEquiv key a b := h ▸ DocEquiv.refl key a

theorem DocEquiv.symm : {key : DocumentKey} → {a b : Document key} →
    DocEquiv key a b → DocEquiv key b a
  | .origin _, _, _, h => List.Perm.symm h
  | .schedule _, _, _, h => Eq.symm h

theorem DocEquiv.trans : {key : DocumentKey} → {a b c : Document key} →
    DocEquiv key a b → DocEquiv key b c → DocEquiv key a c
  | .origin _, _, _, _, h₁, h₂ => List.Perm.trans h₁ h₂
  | .schedule _, _, _, _, h₁, h₂ => Eq.trans h₁ h₂

/-- Two stores whose document views have the same entries. -/
def Same (a b : Store) : Prop := ∀ key, DocEquiv key (a.read key) (b.read key)

theorem Same.refl (a : Store) : Same a a := fun key => DocEquiv.refl key _

theorem Same.symm {a b : Store} (h : Same a b) : Same b a :=
  fun key => (h key).symm

theorem Same.trans {a b c : Store} (h₁ : Same a b) (h₂ : Same b c) :
    Same a c := fun key => (h₁ key).trans (h₂ key)

theorem Same.write {a b : Store} (h : Same a b) (key : DocumentKey)
    (document : Document key) : Same (a.write key document) (b.write key document) := by
  intro other
  by_cases hother : other = key
  · subst other
    simp only [Store.read_write_same]
    exact DocEquiv.refl _ _
  · simp only [Store.read_write_other _ _ _ _ hother]
    exact h other

theorem Same.write_equiv (store : Store) {key : DocumentKey} {a b : Document key}
    (h : DocEquiv key a b) : Same (store.write key a) (store.write key b) := by
  intro other
  by_cases hother : other = key
  · subst other
    simp only [Store.read_write_same]
    exact h
  · simp only [Store.read_write_other _ _ _ _ hother]
    exact DocEquiv.refl _ _

theorem Store.read_write_read (store : Store) (key : DocumentKey) :
    Same (store.write key (store.read key)) store := by
  intro other
  by_cases hother : other = key
  · subst other
    simp only [Store.read_write_same]
    exact DocEquiv.refl _ _
  · simp only [Store.read_write_other _ _ _ _ hother]
    exact DocEquiv.refl _ _

theorem Same.write_of {store : Store} {key : DocumentKey} {document : Document key}
    (h : DocEquiv key (store.read key) document) :
    Same store (store.write key document) :=
  (Store.read_write_read store key).symm.trans (Same.write_equiv store h)

theorem Store.write_write_same (store : Store) (key : DocumentKey)
    (first second : Document key) :
    Same ((store.write key first).write key second) (store.write key second) := by
  intro other
  by_cases hother : other = key
  · subst other
    simp only [Store.read_write_same]
    exact DocEquiv.refl _ _
  · simp only [Store.read_write_other _ _ _ _ hother]
    exact DocEquiv.refl _ _

theorem Same.read_of_write {a store : Store} {key : DocumentKey}
    {document : Document key} (h : Same a (store.write key document)) :
    DocEquiv key (a.read key) document := by
  have := h key
  simp only [Store.read_write_same] at this
  exact this

/-- Every object of the store has its own id. -/
def _root_.Resonate.Store.Unique (store : Store) : Prop := (store.objects.map (·.id)).Nodup

theorem _root_.Resonate.Store.Unique.setObject {store : Store} (h : store.Unique) (object : Object) :
    (store.setObject object).Unique := by
  simp only [Store.Unique, Store.setObject, List.map_cons, List.nodup_cons]
  refine ⟨?_, h.sublist (List.filter_sublist.map _)⟩
  simp only [List.mem_map, List.mem_filter, not_exists, not_and]
  intro other hmem hid
  simp [hid] at hmem

theorem _root_.Resonate.Store.Unique.schedules {a b : Store} (h : b.Unique)
    (hobjects : a.objects = b.objects) : a.Unique := by
  simp only [Store.Unique, hobjects]
  exact h

def Sim (key : DocumentKey) (R : α → β → Prop)
    (abstract : Abstract.Handler α) (concrete : DocumentHandler key β) : Prop :=
  ∀ env store document, store.Unique → DocEquiv key (store.read key) document →
    R (abstract env store).1 (concrete env document).1 ∧
    Same (abstract env store).2.1 (store.write key (concrete env document).2.1) ∧
    (abstract env store).2.2 = (concrete env document).2.2 ∧
    (abstract env store).2.1.Unique

theorem Sim.pure {key : DocumentKey} {R : α → β → Prop} {a : α} {b : β}
    (h : R a b) :
    Sim key R (Pure.pure a : Abstract.Handler α)
      (Pure.pure b : DocumentHandler key β) := by
  intro env store document hunique hdoc
  exact ⟨h, Same.write_of hdoc, rfl, hunique⟩

theorem Sim.bind {key : DocumentKey} {R : α → β → Prop} {S : γ → δ → Prop}
    {ma : Abstract.Handler α} {mc : DocumentHandler key β}
    {fa : α → Abstract.Handler γ} {fc : β → DocumentHandler key δ}
    (hm : Sim key R ma mc) (hf : ∀ a c, R a c → Sim key S (fa a) (fc c)) :
    Sim key S (ma >>= fa) (mc >>= fc) := by
  intro env store document hunique hdoc
  obtain ⟨hr, hsame, hemit, hunique'⟩ := hm env store document hunique hdoc
  obtain ⟨hr', hsame', hemit', hunique''⟩ :=
    hf _ _ hr env (ma env store).2.1 (mc env document).2.1 hunique'
      (Same.read_of_write hsame)
  refine ⟨hr', ?_, ?_, hunique''⟩
  · exact Same.trans hsame'
      ((Same.write hsame key _).trans (Store.write_write_same store key _ _))
  · show (ma env store).2.2 ++ (fa (ma env store).1 env (ma env store).2.1).2.2 =
      (mc env document).2.2 ++
        (fc (mc env document).1 env (mc env document).2.1).2.2
    rw [hemit, hemit']

theorem Sim.map {key : DocumentKey} {R : α → β → Prop}
    {ma : Abstract.Handler α} {mc : DocumentHandler key β}
    {fa : α → γ} {fc : β → γ}
    (hm : Sim key R ma mc) (hf : ∀ a c, R a c → fa a = fc c) :
    Sim key Eq (fa <$> ma) (fc <$> mc) := by
  intro env store document hunique hdoc
  obtain ⟨hr, hsame, hemit, hunique'⟩ := hm env store document hunique hdoc
  refine ⟨hf _ _ hr, ?_, ?_, ?_⟩
  · simpa [Functor.map] using hsame
  · simpa [Functor.map] using hemit
  · simpa [Functor.map] using hunique'


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

/-- The rows of an origin document have distinct suffixes. -/
abbrev RowsUnique {origin : String} (document : OriginDocument origin) : Prop :=
  (document.map (·.suffix)).Nodup

theorem rows_unique (origin : String) :
    ∀ objects : List Object, (objects.map (·.id)).Nodup →
      RowsUnique (objects.filterMap (Object.toOriginRow? origin))
  | [], _ => List.nodup_nil
  | object :: rest, h => by
      rw [List.map_cons, List.nodup_cons] at h
      obtain ⟨hnot, hrest⟩ := h
      have ih := rows_unique origin rest hrest
      by_cases horigin : object.id.origin = origin
      · have hrow : Object.toOriginRow? origin object =
            some { suffix := object.id.suffix, promise := object.promise,
                   task := object.task } := by
          simp [Object.toOriginRow?, horigin]
        simp only [List.filterMap_cons, hrow, RowsUnique, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih⟩
        intro hmem
        apply hnot
        simp only [List.mem_map, List.mem_filterMap] at hmem
        obtain ⟨row, ⟨other, hother, hotherRow⟩, hsuffix⟩ := hmem
        refine List.mem_map.mpr ⟨other, hother, ?_⟩
        unfold Object.toOriginRow? at hotherRow
        split at hotherRow
        · rename_i hotherOrigin
          cases hotherRow
          cases hid : object.id
          cases hotherId : other.id
          simp_all
        · contradiction
      · rw [List.filterMap_cons, toOriginRow?_eq_none horigin]
        exact ih

theorem _root_.Resonate.Store.Unique.rows {store : Store} (h : store.Unique) (origin : String) :
    RowsUnique (store.read (.origin origin)) :=
  rows_unique origin store.objects h

theorem find?_suffix_iff {origin : String} {document : OriginDocument origin}
    (hunique : RowsUnique document) {suffix : String} {row : OriginObject origin} :
    document.find? (·.suffix == suffix) = some row ↔
      row ∈ document ∧ row.suffix = suffix := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · rintro ⟨hmem, hsuffix⟩
    cases hfind : document.find? (·.suffix == suffix) with
    | none =>
        have := List.find?_eq_none.mp hfind row hmem
        simp [hsuffix] at this
    | some other =>
        have hother := List.mem_of_find?_eq_some hfind
        have hotherSuffix : other.suffix = suffix := by simpa using List.find?_some hfind
        exact congrArg some
          (inj_of_nodup_map hunique hother hmem (hotherSuffix.trans hsuffix.symm))
where
  inj_of_nodup_map {α β : Type} {f : α → β} :
      ∀ {l : List α}, (l.map f).Nodup → ∀ {x y : α}, x ∈ l → y ∈ l → f x = f y → x = y
    | [], _, _, _, hx, _, _ => by cases hx
    | z :: rest, h, x, y, hx, hy, hxy => by
        rw [List.map_cons, List.nodup_cons] at h
        obtain ⟨hz, hrest⟩ := h
        rcases List.mem_cons.mp hx with hxz | hx'
        · rcases List.mem_cons.mp hy with hyz | hy'
          · rw [hxz, hyz]
          · subst hxz
            exact (hz (by rw [hxy]; exact List.mem_map_of_mem hy')).elim
        · rcases List.mem_cons.mp hy with hyz | hy'
          · subst hyz
            exact (hz (by rw [← hxy]; exact List.mem_map_of_mem hx')).elim
          · exact inj_of_nodup_map hrest hx' hy' hxy

/-- Looking up a suffix gives the same row in documents with the same
entries. -/
theorem find?_perm {origin : String} {a b : OriginDocument origin}
    (hunique : RowsUnique a) (hperm : List.Perm a b) (suffix : String) :
    a.find? (·.suffix == suffix) = b.find? (·.suffix == suffix) := by
  have hunique' : RowsUnique b := ((hperm.map _).nodup_iff).mp hunique
  cases ha : a.find? (·.suffix == suffix) with
  | none =>
      symm
      rw [List.find?_eq_none] at ha ⊢
      exact fun x hx => ha x (hperm.mem_iff.mpr hx)
  | some row =>
      symm
      obtain ⟨hmem, hsuffix⟩ := (find?_suffix_iff hunique).mp ha
      exact (find?_suffix_iff hunique').mpr ⟨hperm.mem_iff.mp hmem, hsuffix⟩

/-- A document is its row with suffix `row.suffix` in front of the others. -/
theorem perm_cons_filter {origin : String} :
    ∀ {document : OriginDocument origin}, RowsUnique document →
      ∀ {row : OriginObject origin}, row ∈ document →
        List.Perm document (row :: document.filter (·.suffix != row.suffix))
  | [], _, _, hrow => by cases hrow
  | first :: rest, hunique, row, hrow => by
      have hunique' := hunique
      simp only [RowsUnique, List.map_cons, List.nodup_cons] at hunique'
      obtain ⟨hfirst, hrest⟩ := hunique'
      by_cases hsuffix : first.suffix = row.suffix
      · have hrowFirst : row = first := by
          rcases List.mem_cons.mp hrow with h | h
          · exact h
          · exact (hfirst (by rw [hsuffix]; exact List.mem_map_of_mem h)).elim
        subst hrowFirst
        have hkeep : rest.filter (·.suffix != row.suffix) = rest := by
          rw [List.filter_eq_self]
          intro other hother
          have : other.suffix ≠ row.suffix :=
            fun h => hfirst (by rw [← h]; exact List.mem_map_of_mem hother)
          simpa using this
        simp only [List.filter_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hkeep]
        exact List.Perm.refl _
      · have hrowRest : row ∈ rest := by
          rcases List.mem_cons.mp hrow with h | h
          · exact (hsuffix (by rw [h])).elim
          · exact h
        have hne : (first.suffix != row.suffix) = true := by simpa using hsuffix
        simp only [List.filter_cons, hne, ↓reduceIte]
        exact ((perm_cons_filter hrest hrowRest).cons first).trans (List.Perm.swap _ _ _)

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

/-- The abstract lookup of `id` is the concrete lookup of its suffix in any
document with the same entries. -/
theorem getObject_eq_document {store : Store} {id : Ident}
    {document : OriginDocument id.origin} (hunique : store.Unique)
    (hdoc : DocEquiv (.origin id.origin) (store.read (.origin id.origin)) document) :
    store.getObject id =
      (document.find? (·.suffix == id.suffix)).map Object.ofOrigin := by
  rw [getObject_eq_read, find?_perm (hunique.rows _) hdoc]

theorem getObject_sim (id : Ident) :
    Sim (.origin id.origin) (ObjRel id.origin id.suffix) (Abstract.getObject id)
      (Concrete.Decision.getObject id.suffix) := by
  intro env store document hunique hdoc
  refine ⟨?_, Same.write_of hdoc, rfl, hunique⟩
  refine ⟨?_, fun row h => find?_suffix h⟩
  simp only [Abstract.getObject, Concrete.Decision.getObject, bind, documentGet, pure]
  exact getObject_eq_document hunique hdoc

theorem same_write_origin {a store : Store} {origin : String}
    {document : OriginDocument origin}
    (hschedules : a.schedules = store.schedules)
    (hsame : List.Perm (a.read (.origin origin)) document)
    (hother : ∀ other, other ≠ origin →
      a.read (.origin other) = store.read (.origin other)) :
    Same a (store.write (.origin origin) document) := by
  intro key
  cases key with
  | origin other =>
      by_cases h : other = origin
      · subst other
        rw [Store.read_write_same]
        exact hsame
      · rw [hother other h, Store.read_write_other]
        · exact DocEquiv.refl _ _
        · simpa using h
  | schedule id =>
      apply DocEquiv.of_eq
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

/-- What the abstract store does to an origin document when it writes
`object` at its id. -/
theorem read_setObject_same (store : Store) (object : Object) :
    (store.setObject object).read (.origin object.id.origin) =
      { suffix := object.id.suffix, promise := object.promise, task := object.task } ::
        (store.read (.origin object.id.origin)).filter (·.suffix != object.id.suffix) := by
  rw [Store.setObject, read_mk_origin, List.filterMap_cons, filterMap_filter_id_same,
    read_origin, toOriginRow?_eq_some]

theorem read_setObject_other (store : Store) (object : Object) {other : String}
    (h : other ≠ object.id.origin) :
    (store.setObject object).read (.origin other) = store.read (.origin other) := by
  rw [Store.setObject, read_mk_origin, List.filterMap_cons, filterMap_filter_id_other _ _ h,
    toOriginRow?_eq_none (Ne.symm h), read_origin]

/-- Writing `object` matches putting its row in front of the document rows
with other suffixes. -/
theorem setObject_same {store : Store} (object : Object)
    {document : OriginDocument object.id.origin}
    (hdoc : DocEquiv (.origin object.id.origin)
      (store.read (.origin object.id.origin)) document) :
    Same (store.setObject object)
      (store.write (.origin object.id.origin)
        ({ suffix := object.id.suffix, promise := object.promise, task := object.task } ::
          document.filter (·.suffix != object.id.suffix))) := by
  refine same_write_origin rfl ?_ (fun other h => read_setObject_other store object h)
  rw [read_setObject_same]
  exact (List.Perm.filter _ hdoc).cons _

theorem setPromise_sim (id : Ident) (promise : PromiseObject) :
    Sim (.origin id.origin) Eq (Abstract.setPromise id promise)
      (Concrete.Decision.setPromise id.suffix promise) := by
  intro env store document hunique hdoc
  have hget := getObject_eq_document hunique hdoc
  refine ⟨rfl, ?_, rfl, hunique.setObject _⟩
  simp only [Abstract.setPromise, Concrete.Decision.setPromise,
    Concrete.Decision.modify, documentModify, Store.setPromise, hget]
  cases hfind : document.find? (·.suffix == id.suffix) with
  | none =>
      simp only [Option.map_none]
      exact setObject_same { id, promise } hdoc
  | some existing =>
      have hsuffix := find?_suffix hfind
      simp only [Option.map_some]
      rw [← hsuffix]
      exact setObject_same { Object.ofOrigin existing with promise } hdoc

theorem setObject_sim {origin : String} (row : OriginObject origin) :
    Sim (.origin origin) Eq (Abstract.setObject (Object.ofOrigin row))
      (Concrete.Decision.setObject row) := by
  intro env store document hunique hdoc
  refine ⟨rfl, ?_, rfl, hunique.setObject _⟩
  simp only [Abstract.setObject, Concrete.Decision.setObject,
    Concrete.Decision.modify, documentModify]
  exact setObject_same (Object.ofOrigin row) hdoc

theorem setTask_sim (id : Ident) (task : TaskObject) :
    Sim (.origin id.origin) Eq (Abstract.setTask id task)
      (Concrete.Decision.setTask id.suffix task) := by
  intro env store document hunique hdoc
  have hget := getObject_eq_document hunique hdoc
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp only [Abstract.setTask, Concrete.Decision.setTask,
      Concrete.Decision.modify, documentModify, Store.setTask, hget]
    cases hfind : document.find? (·.suffix == id.suffix) with
    | none =>
        have hkeep : (document.map fun object =>
            if object.suffix == id.suffix then { object with task := some task }
            else object) = document := by
          rw [List.map_congr_left (g := fun x => x), List.map_id']
          intro object hobject
          have := List.find?_eq_none.mp hfind object hobject
          simp only [Bool.not_eq_true] at this
          simp [this]
        simp only [Option.map_none]
        rw [hkeep]
        exact Same.write_of hdoc
    | some existing =>
        have hsuffix := find?_suffix hfind
        have hmem := List.mem_of_find?_eq_some hfind
        have hunique' : RowsUnique document :=
          ((List.Perm.map _ hdoc).nodup_iff).mp (hunique.rows _)
        simp only [Option.map_some]
        refine (Same.trans (setObject_same { Object.ofOrigin existing with task := some task }
          hdoc) ?_)
        apply Same.write_equiv
        show List.Perm _ _
        have hperm := (perm_cons_filter hunique' hmem).map (fun object =>
          if object.suffix == id.suffix then { object with task := some task } else object)
        rw [List.map_cons, hsuffix] at hperm
        simp only [beq_self_eq_true, ↓reduceIte] at hperm
        have hrest : ((document.filter (·.suffix != id.suffix)).map fun object =>
            if object.suffix == id.suffix then { object with task := some task }
            else object) = document.filter (·.suffix != id.suffix) := by
          rw [List.map_congr_left (g := fun x => x), List.map_id']
          intro object hobject
          have := (List.mem_filter.mp hobject).2
          simp only [bne_iff_ne, ne_eq] at this
          simp [this]
        rw [hrest] at hperm
        refine List.Perm.trans ?_ hperm.symm
        have e : (Object.ofOrigin existing).id.suffix = id.suffix := hsuffix
        rw [e]
        exact List.Perm.refl _
  · simp only [Abstract.setTask, Store.setTask, hget]
    cases document.find? (·.suffix == id.suffix) with
    | none => exact hunique
    | some _ => exact hunique.setObject _

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

theorem Store.setSchedule_same (store : Store) (schedule : Schedule) :
    Same (store.setSchedule schedule)
      (store.write (.schedule schedule.id) (some (ScheduleData.ofSchedule schedule))) := by
  intro key
  apply DocEquiv.of_eq
  by_cases hkey : key = .schedule schedule.id
  · subst hkey
    rw [Store.read_write_same]
    simp only [Store.setSchedule, Store.read, Store.scheduleAt]
    rw [Store.scheduleAt.go, dif_pos rfl]
  · rw [Store.read_write_other _ _ _ _ hkey]
    cases key with
    | origin origin => rfl
    | schedule other =>
        have hother : other ≠ schedule.id := fun h => hkey (by rw [h])
        have hne : ¬ schedule.id = other := fun h => hother h.symm
        simp only [Store.setSchedule, Store.read, Store.scheduleAt]
        rw [Store.scheduleAt.go, dif_neg hne,
          scheduleAt_go_filter_other _ _ hother]

theorem getSchedule_sim (id : Ident) :
    Sim (.schedule id) Eq (Abstract.getSchedule id)
      (Concrete.Decision.getSchedule (id := id)) := by
  intro env store document hunique hdoc
  obtain rfl : store.read (.schedule id) = document := hdoc
  refine ⟨?_, Same.symm (Store.read_write_read store _), rfl, hunique⟩
  simp [Abstract.getSchedule, Concrete.Decision.getSchedule, getSchedule_eq_read,
    bind, documentGet, pure]

theorem setSchedule_sim (id : Ident) (schedule : Schedule) (h : schedule.id = id) :
    Sim (.schedule id) Eq (Abstract.setSchedule schedule)
      (Concrete.Decision.setScheduleValue (id := id) schedule) := by
  subst h
  intro env store document hunique _
  refine ⟨rfl, ?_, rfl, hunique.schedules rfl⟩
  simp only [Abstract.setSchedule, Concrete.Decision.setScheduleValue,
    Concrete.Decision.setSchedule, Concrete.Decision.set, documentSet]
  exact Store.setSchedule_same store schedule

theorem deleteSchedule_sim (id : Ident) :
    Sim (.schedule id) Eq (Abstract.deleteSchedule id)
      (Concrete.Decision.delSchedule (id := id)) := by
  intro env store document hunique _
  refine ⟨rfl, ?_, rfl, hunique.schedules rfl⟩
  have : store.deleteSchedule id = store.write (.schedule id) none := by
    simp [Store.deleteSchedule, Store.write]
  simp only [Abstract.deleteSchedule, Concrete.Decision.delSchedule,
    Concrete.Decision.set, documentSet, this]
  exact Same.refl _

theorem setMessage_sim {key : DocumentKey} (address : String)
    (message : ServerModel.Message) :
    Sim key Eq (Abstract.setMessage address message)
      (Concrete.Decision.setMessage (key := key) address message) := by
  intro env store document hunique hdoc
  exact ⟨rfl, Same.write_of hdoc, rfl, hunique⟩

theorem ask_sim {key : DocumentKey} :
    Sim key Eq Abstract.ask (Concrete.Decision.ask (key := key)) := by
  intro env store document hunique hdoc
  exact ⟨rfl, Same.write_of hdoc, rfl, hunique⟩

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
  intro env store document hunique hdoc
  have ha : Abstract.readTask id now env store =
      ((((store.getObject id).map (·.project now)).bind fun o => o.task.map (o, ·)),
        store, []) := by
    simp only [Abstract.readTask, Abstract.readObject, Abstract.getObject, bind, pure]
    cases store.getObject id <;> rfl
  have hc : Concrete.Decision.readTaskObject id.suffix now env document =
      ((match document.find? (·.suffix == id.suffix) with
        | some row => if row.task.isSome then some (row.project now) else none
        | none => none),
        document, []) := by
    simp only [Concrete.Decision.readTaskObject, Concrete.Decision.readObject,
      Concrete.Decision.getObject, documentGet, bind, pure]
    cases hfind : document.find? (·.suffix == id.suffix) with
    | none => rfl
    | some row => cases ht : row.task.isSome <;> simp [hfind, ht]
  rw [ha, hc, getObject_eq_document hunique hdoc]
  refine ⟨?_, Same.write_of hdoc, rfl, hunique⟩
  cases hfind : document.find? (·.suffix == id.suffix) with
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

theorem taskCreate_sim (req : TaskCreateReq) (now : Nat) :
    Sim (.origin req.action.id.origin) Eq (Abstract.taskCreate req now)
      (Concrete.Decision.taskCreate req now) := by
  unfold Abstract.taskCreate Concrete.Decision.taskCreate
  sim

theorem Sim.bind_left {key : DocumentKey} {R : α → β → Prop} {S : γ → δ → Prop}
    {ma : Abstract.Handler α} {u : β} {fa : α → Abstract.Handler γ}
    {mc : DocumentHandler key δ}
    (hm : Sim key R ma (Pure.pure u)) (hf : ∀ a, R a u → Sim key S (fa a) mc) :
    Sim key S (ma >>= fa) mc := by
  intro env store document hunique hdoc
  obtain ⟨hr, hsame, hemit, hunique'⟩ := hm env store document hunique hdoc
  obtain ⟨hr', hsame', hemit', hunique''⟩ :=
    hf _ hr env (ma env store).2.1 document hunique' (Same.read_of_write hsame)
  refine ⟨hr', ?_, ?_, hunique''⟩
  · exact hsame'.trans
      ((Same.write hsame key _).trans (Store.write_write_same store key _ _))
  · show (ma env store).2.2 ++ (fa (ma env store).1 env (ma env store).2.1).2.2 = _
    rw [hemit', hemit]
    rfl

/-- A handler that only reads simulates doing nothing. -/
theorem Sim.readOnly {key : DocumentKey} {ma : Abstract.Handler α}
    (h : ∀ env store, (ma env store).2 = (store, [])) :
    Sim key (fun _ _ => True) ma (Pure.pure ()) := by
  intro env store document hunique hdoc
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [h env store]
    exact Same.write_of hdoc
  · rw [h env store]
    rfl
  · rw [h env store]
    exact hunique

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
  intro env store document hunique hdoc
  obtain rfl : store.read (.schedule id) = document := hdoc
  obtain ⟨h₁, h₂, h₃, h₄⟩ :=
    getSchedule_sim id env store _ hunique (DocEquiv.refl _ _)
  refine ⟨⟨h₁, ?_⟩, h₂, h₃, h₄⟩
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

/-- What a request does to every abstract state whose document `key` has the
entries of `before`: the concrete candidate written back. -/
def ExternalSim (appConfig : Resonate.Config) (call : Call) (key : DocumentKey)
    (before : Document key) : Prop :=
  ∃ candidate,
    Concrete.selectedExternalCandidate appConfig call key before = some candidate ∧
    candidate.continuations = [] ∧
    ∀ state : State, state.store.Unique → DocEquiv key (state.store.read key) before →
      let lifted := Abstract.run appConfig call state
      Same lifted.1.store (state.store.write key candidate.document) ∧
        lifted.1.store.Unique ∧
        lifted.1.workflow = state.workflow ∧
        lifted.2 = candidate.outputs

theorem externalCandidate_continuations {key : DocumentKey}
    (appConfig : Resonate.Config) (call : Call) (document : Document key)
    (action : Concrete.Decision.Handler key α) (wrap : α → Response) :
    (Concrete.externalCandidate appConfig call document action wrap).continuations = [] := by
  simp [Concrete.externalCandidate]

/-- A request whose handler simulates a concrete decision runs as that
decision's candidate written back into the store. -/
theorem run_of_sim (appConfig : Resonate.Config) (call : Call) (state : State)
    {key : DocumentKey} {before : Document key} {ma : Abstract.Handler β}
    {action : Concrete.Decision.Handler key β} {wrap : β → Response}
    (hhandler : Abstract.handler call.request call.requestedAt = wrap <$> ma)
    (hsim : Sim key Eq ma action) (hunique : state.store.Unique)
    (hdoc : DocEquiv key (state.store.read key) before) :
    let candidate := Concrete.externalCandidate appConfig call before action wrap
    let lifted := Abstract.run appConfig call state
    Same lifted.1.store (state.store.write key candidate.document) ∧
      lifted.1.store.Unique ∧
      lifted.1.workflow = state.workflow ∧
      lifted.2 = candidate.outputs := by
  obtain ⟨hresult, hsame, hemit, hunique'⟩ :=
    hsim { config := appConfig.toServerConfig } state.store before hunique hdoc
  simp only [Abstract.run, Abstract.serve, hhandler, Abstract.map_apply,
    Concrete.externalCandidate, Concrete.Decision.run]
  exact ⟨hsame, hunique', trivial, by rw [hresult, hemit]⟩

theorem external_sim_of (appConfig : Resonate.Config) (call : Call)
    {key : DocumentKey} (before : Document key) {ma : Abstract.Handler β}
    {action : Concrete.Decision.Handler key β} {wrap : β → Response}
    (hcandidate :
      Concrete.selectedExternalCandidate appConfig call key before =
        some (Concrete.externalCandidate appConfig call before action wrap))
    (hhandler : Abstract.handler call.request call.requestedAt = wrap <$> ma)
    (hsim : Sim key Eq ma action) :
    ExternalSim appConfig call key before :=
  ⟨_, hcandidate, externalCandidate_continuations _ _ _ _ _,
    fun state hunique hdoc => run_of_sim appConfig call state hhandler hsim hunique hdoc⟩

/-- A request that names a document runs as the concrete candidate for that
document written back into the store. -/
theorem external_sim (appConfig : Resonate.Config) (call : Call) (key : DocumentKey)
    (hkey : (Concrete.Transaction.external call).key? = some key)
    (before : Document key) : ExternalSim appConfig call key before := by
  cases hrequest : call.request <;>
    simp only [Concrete.Transaction.key?, hrequest] at hkey
  case promiseGet req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (promiseGet_sim req call.requestedAt)
  case promiseCreate req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast,
        Concrete.Decision.promiseCreate])
      (by rw [hrequest]; rfl) (promiseCreate_sim req call.requestedAt rfl)
  case promiseSettle req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseSettle)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast,
        Concrete.Decision.promiseSettle])
      (by rw [hrequest]; rfl) (promiseSettle_sim req call.requestedAt rfl)
  case promiseRegisterCallback req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .promiseRegisterCallback)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (promiseRegisterCallback_sim req call.requestedAt)
    · contradiction
  case promiseRegisterListener req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseRegisterListener)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (promiseRegisterListener_sim req call.requestedAt)
  case scheduleGet req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .scheduleGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (scheduleGet_sim req call.requestedAt)
  case scheduleCreate req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .scheduleCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (scheduleCreate_sim req call.requestedAt)
  case scheduleDelete req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .scheduleDelete)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (scheduleDelete_sim req call.requestedAt)
  case taskGet req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskGet_sim req call.requestedAt)
  case taskCreate req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskCreate_sim req call.requestedAt)
  case taskAcquire req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskAcquire)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskAcquire_sim req call.requestedAt)
  case taskFence req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .taskFence)
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
        exact external_sim_of appConfig call before (wrap := .taskHeartbeat)
          (by simp [Concrete.selectedExternalCandidate, hrequest, htasks,
            Concrete.Candidate.cast])
          (by rw [hrequest]; rfl)
          (taskHeartbeat_sim req call.requestedAt first rest htasks)
      · contradiction
  case taskSuspend req =>
    split at hkey
    · contradiction
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .taskSuspend)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (taskSuspend_sim req call.requestedAt)
  case taskFulfill req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .taskFulfill)
        (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
        (by rw [hrequest]; rfl) (taskFulfill_sim req call.requestedAt)
    · contradiction
  case taskRelease req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskRelease)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskRelease_sim req call.requestedAt)
  case taskHalt req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskHalt)
      (by simp [Concrete.selectedExternalCandidate, hrequest, Concrete.Candidate.cast])
      (by rw [hrequest]; rfl) (taskHalt_sim req call.requestedAt)
  case taskContinue req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskContinue)
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

/-- The abstract callback step assumes the awaiter shares the awaited origin. -/
def WorkLocal : WorkItem → Prop
  | .callback req => req.awaiter.origin = req.awaited.origin
  | _ => True

theorem work_sim_of (appConfig : Resonate.Config) (item : WorkItem) (now : Nat)
    (rest : List Concrete.PendingEntry) (abstractRest : List WorkflowEntry)
    (state : State) {key : DocumentKey} {before : Document key}
    {ma : Abstract.Handler Unit} {action : Concrete.Decision.Handler key Unit}
    (hcandidate :
      Concrete.selectedWorkCandidate appConfig item now rest key before =
        some (Concrete.workCandidate appConfig before action rest))
    (hwork : Abstract.processWork item now = (ma >>= fun _ => Pure.pure []))
    (hsim : Sim key Eq ma action) (hunique : state.store.Unique)
    (hdoc : DocEquiv key (state.store.read key) before) :
    ∃ candidate,
      Concrete.selectedWorkCandidate appConfig item now rest key before =
        some candidate ∧
      let lifted := Abstract.runWork appConfig item now abstractRest state
      Same lifted.1.store (state.store.write key candidate.document) ∧
        lifted.1.store.Unique ∧
        lifted.2 = candidate.outputs ∧
        ∃ added, lifted.1.workflow.pending = abstractRest ++ added ∧
          Concrete.pendingWorkflow candidate.continuations =
            Concrete.pendingWorkflow rest ++ added := by
  refine ⟨_, hcandidate, ?_⟩
  obtain ⟨_, hsame, hemit, hunique'⟩ :=
    hsim { config := appConfig.toServerConfig } state.store before hunique hdoc
  simp only [Abstract.runWork, hwork, Concrete.workCandidate, Concrete.Decision.run]
  refine ⟨hsame, ?_, ?_, [], rfl, by simp⟩
  · simpa [bind, Pure.pure] using hunique'
  · show List.map Output.message ((ma _ state.store).2.2 ++ []) = _
    rw [List.append_nil, hemit]

/-- One piece of due work runs as the concrete work candidate for its
document written back into the store. -/
theorem work_sim (appConfig : Resonate.Config) (item : WorkItem) (now : Nat)
    (rest : List Concrete.PendingEntry) (abstractRest : List WorkflowEntry)
    (state : State) (hlocal : WorkLocal item) (before : Document item.key)
    (hunique : state.store.Unique)
    (hdoc : DocEquiv item.key (state.store.read item.key) before) :
    ∃ candidate,
      Concrete.selectedWorkCandidate appConfig item now rest item.key before =
        some candidate ∧
      let lifted := Abstract.runWork appConfig item now abstractRest state
      Same lifted.1.store (state.store.write item.key candidate.document) ∧
        lifted.1.store.Unique ∧
        lifted.2 = candidate.outputs ∧
        ∃ added, lifted.1.workflow.pending = abstractRest ++ added ∧
          Concrete.pendingWorkflow candidate.continuations =
            Concrete.pendingWorkflow rest ++ added := by
  cases item with
  | promiseTimeout id =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.Candidate.cast]) rfl
      (processPromiseTimeout_sim id now) hunique hdoc
  | callback req =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.Candidate.cast]) rfl
      (processCallback_sim req now hlocal) hunique hdoc
  | listener req =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.Candidate.cast]) rfl
      (processListener_sim req now) hunique hdoc
  | taskLeaseTimeout id =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.Candidate.cast]) rfl
      (processLeaseTimeout_sim id now) hunique hdoc
  | taskRetryTimeout id =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.Candidate.cast]) rfl
      (processRetryTimeout_sim id now) hunique hdoc
  | occurrence req time =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.Candidate.cast]) rfl
      (createIfAbsent_sim req time) hunique hdoc
  | scheduleTimeout id =>
    obtain ⟨hresult, hsame, hemit, hunique'⟩ :=
      processSchedule_sim id now { config := appConfig.toServerConfig } state.store before
        hunique hdoc
    simp only [Concrete.selectedWorkCandidate, WorkItem.key, dite_true,
      Concrete.Candidate.cast, Abstract.runWork, Abstract.processWork,
      Concrete.Decision.run]
    refine ⟨_, rfl, hsame, hunique', by rw [hemit], _, rfl, ?_⟩
    rw [hresult]
    simp only [Concrete.pendingWorkflow, List.filterMap_append, List.filterMap_map]
    congr 1
    induction (Abstract.processSchedule id now { config := appConfig.toServerConfig }
      state.store).1 with
    | nil => rfl
    | cons entry entries ih =>
      simp [Concrete.PendingEntry.toWorkflow?, ih]

/-! ## Due work -/

theorem originObjectWork_eq {origin : String} (row : OriginObject origin) (now : Nat) :
    Concrete.Decision.originObjectWork row now = Abstract.objectWork (Object.ofOrigin row) now :=
  rfl

/-- Work the concrete sweep finds in an origin document is object work of the
abstract store. -/
theorem originWork_mem (store : Store) (origin : String) (now : Nat)
    {document : OriginDocument origin}
    (hdoc : DocEquiv (.origin origin) (store.read (.origin origin)) document)
    {item : WorkItem}
    (h : item ∈ Concrete.Decision.originWork origin document now) :
    item ∈ store.objects.flatMap (Abstract.objectWork · now) := by
  simp only [Concrete.Decision.originWork, List.mem_flatMap] at h
  obtain ⟨row, hrow, hitem⟩ := h
  have hrow : row ∈ store.objects.filterMap (Object.toOriginRow? origin) :=
    (List.Perm.mem_iff hdoc).mpr hrow
  simp only [Store.read, Store.originRows, List.mem_filterMap] at hrow
  obtain ⟨object, hobject, hrow⟩ := hrow
  rw [List.mem_flatMap]
  refine ⟨object, hobject, ?_⟩
  rw [← Object.ofOrigin_toOriginRow hrow, ← originObjectWork_eq]
  exact hitem

theorem scheduleAt_go_due (id : Ident) (now : Nat) :
    ∀ (schedules : List Schedule) (data : ScheduleData id),
      Store.scheduleAt.go id schedules = some data → data.nextRunAt ≤ now →
      WorkItem.scheduleTimeout id ∈ schedules.flatMap (Abstract.scheduleWork · now)
  | [], _, h, _ => by simp [Store.scheduleAt.go] at h
  | schedule :: rest, data, h, hdue => by
    simp only [Store.scheduleAt.go] at h
    split at h
    · rename_i hid
      subst hid
      cases h
      simp [Abstract.scheduleWork, ScheduleData.ofSchedule] at hdue ⊢
      simp [hdue]
    · simp only [List.flatMap_cons, List.mem_append]
      exact .inr (scheduleAt_go_due id now rest data h hdue)

/-- A due schedule document is schedule work of the abstract store. -/
theorem scheduleWork_mem (store : Store) (id : Ident) (now : Nat) {data : ScheduleData id}
    (h : store.read (.schedule id) = some data) (hdue : data.nextRunAt ≤ now) :
    WorkItem.scheduleTimeout id ∈ store.schedules.flatMap (Abstract.scheduleWork · now) :=
  scheduleAt_go_due id now store.schedules data h hdue

theorem runTimeout_mem_due (appConfig : Resonate.Config) (state : State) {now instant : Nat}
    {item : WorkItem} (hinstant : instant ≤ now)
    (h : item ∈ state.store.objects.flatMap (Abstract.objectWork · instant) ++
      state.store.schedules.flatMap (Abstract.scheduleWork · instant)) :
    Abstract.runWork appConfig item instant state.workflow.pending state ∈
      (Abstract.runTimeout appConfig now state).val := by
  simp only [Abstract.runTimeout, Abstract.dueWork, List.mem_cons, List.mem_map,
    List.mem_append]
  right
  refine ⟨(item, instant, state.workflow.pending), .inr ?_, rfl⟩
  exact List.mem_flatMap.mpr ⟨instant, List.mem_range.mpr (by omega),
    List.mem_map.mpr ⟨item, h, rfl⟩⟩

theorem runTimeout_mem_pending (appConfig : Resonate.Config) (state : State) (now : Nat)
    {entry : WorkflowEntry} (hmem : entry ∈ state.workflow.pending) :
    ∃ rest,
      Abstract.runWork appConfig entry.item entry.instant rest state ∈
        (Abstract.runTimeout appConfig now state).val ∧
      List.Perm state.workflow.pending (entry :: rest) := by
  obtain ⟨before, after, hpending⟩ := List.append_of_mem hmem
  refine ⟨before ++ after, ?_, ?_⟩
  · simp only [Abstract.runTimeout, Abstract.dueWork, List.mem_cons, List.mem_map,
      List.mem_append]
    right
    refine ⟨(entry.item, entry.instant, before ++ after), .inl ?_, rfl⟩
    rw [List.mem_mapIdx]
    refine ⟨before.length, by simp [hpending], ?_⟩
    simp [hpending, List.eraseIdx_append]
  · rw [hpending]
    simpa [List.append_assoc] using
      (List.perm_middle :
        List.Perm (before ++ entry :: after) (entry :: (before ++ after)))

end Resonate.Refinement
