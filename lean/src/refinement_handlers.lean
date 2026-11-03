import Lean
import «concrete».Model
import «abstract».Model

/-!
# Abstract handlers simulate the concrete document decisions

The abstract handlers run on the whole store and address objects by id. The
concrete decisions run on one document and address objects by suffix.

Documents are compared by what a read shows, not by what they store. A read
shows a task as its promise has it (`TaskObject.project`), so two rows with the
same normal form (`OriginObject.norm`) read alike at every instant. Rows are
compared as a multiset: both sides look rows up by suffix.

`Sim key P R Q abstract concrete` says that running `abstract` on a store
with unique ids gives what running `concrete` gives on any document with the
same normal forms as that store's document `key` and satisfying `P`, with
the result document written back: the results are related by `R`, the
concrete result satisfies `Q`, every document view of the two stores has the
same normal forms, the emitted messages are equal, and ids stay unique.

Abstract writes store whole objects as read; concrete writes update a field
of the stored row. A write is matched only knowing the row the handler read,
which `P` carries from the read to the write (`Fact`).
-/

namespace Resonate.Refinement

open ServerModel

/-- A row with its task as its promise shows it. -/
def _root_.Resonate.OriginObject.norm {origin : String} (row : OriginObject origin) :
    OriginObject origin :=
  { row with task := row.task.map (·.project row.promise) }

/-- Two documents that read alike. -/
def DocEquiv : (key : DocumentKey) → Document key → Document key → Prop
  | .origin _, a, b => List.Perm (a.map (·.norm)) (b.map (·.norm))
  | .schedule _, a, b => a = b

theorem DocEquiv.refl : (key : DocumentKey) → (document : Document key) →
    DocEquiv key document document
  | .origin _, document => List.Perm.refl _
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

theorem DocEquiv.of_perm {origin : String} {a b : OriginDocument origin}
    (h : List.Perm a b) : DocEquiv (.origin origin) a b := h.map _

/-- Two stores whose document views read alike. -/
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

theorem _root_.Resonate.Store.Unique.setObject {store : Store} (h : store.Unique)
    (object : Object) : (store.setObject object).Unique := by
  simp only [Store.Unique, Store.setObject, List.map_cons, List.nodup_cons]
  refine ⟨?_, h.sublist (List.filter_sublist.map _)⟩
  simp only [List.mem_map, List.mem_filter, not_exists, not_and]
  intro other hmem hid
  simp [hid] at hmem

theorem _root_.Resonate.Store.Unique.schedules {a b : Store} (h : b.Unique)
    (hobjects : a.objects = b.objects) : a.Unique := by
  simp only [Store.Unique, hobjects]
  exact h

def Sim (key : DocumentKey) (P : Document key → Prop) (R : α → β → Prop)
    (Q : β → Document key → Prop)
    (abstract : Abstract.Handler α) (concrete : DocumentHandler key β) : Prop :=
  ∀ env store document, store.Unique → DocEquiv key (store.read key) document →
    P document →
    R (abstract env store).1 (concrete env document).1 ∧
    Q (concrete env document).1 (concrete env document).2.1 ∧
    Same (abstract env store).2.1 (store.write key (concrete env document).2.1) ∧
    (abstract env store).2.2 = (concrete env document).2.2 ∧
    (abstract env store).2.1.Unique

theorem Sim.pure {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} {a : α} {b : β}
    (h : R a b) (hq : ∀ d, P d → Q b d) :
    Sim key P R Q (Pure.pure a : Abstract.Handler α)
      (Pure.pure b : DocumentHandler key β) := by
  intro env store document hunique hdoc hp
  exact ⟨h, hq _ hp, Same.write_of hdoc, rfl, hunique⟩

theorem Sim.bind {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} {S : γ → δ → Prop} {T : δ → Document key → Prop}
    {ma : Abstract.Handler α} {mc : DocumentHandler key β}
    {fa : α → Abstract.Handler γ} {fc : β → DocumentHandler key δ}
    (hm : Sim key P R Q ma mc) (hf : ∀ a c, R a c → Sim key (Q c) S T (fa a) (fc c)) :
    Sim key P S T (ma >>= fa) (mc >>= fc) := by
  intro env store document hunique hdoc hp
  obtain ⟨hr, hq, hsame, hemit, hunique'⟩ := hm env store document hunique hdoc hp
  obtain ⟨hr', hq', hsame', hemit', hunique''⟩ :=
    hf _ _ hr env (ma env store).2.1 (mc env document).2.1 hunique'
      (Same.read_of_write hsame) hq
  refine ⟨hr', hq', ?_, ?_, hunique''⟩
  · exact Same.trans hsame'
      ((Same.write hsame key _).trans (Store.write_write_same store key _ _))
  · show (ma env store).2.2 ++ (fa (ma env store).1 env (ma env store).2.1).2.2 =
      (mc env document).2.2 ++
        (fc (mc env document).1 env (mc env document).2.1).2.2
    rw [hemit, hemit']

theorem Sim.pre {key : DocumentKey} {P P' : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} {a : Abstract.Handler α} {c : DocumentHandler key β}
    (h : ∀ d, P d → P' d) (hs : Sim key P' R Q a c) : Sim key P R Q a c :=
  fun env store document hunique hdoc hp => hs env store document hunique hdoc (h _ hp)

theorem Sim.post {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q Q' : β → Document key → Prop} {a : Abstract.Handler α} {c : DocumentHandler key β}
    (h : ∀ b d, Q b d → Q' b d) (hs : Sim key P R Q a c) : Sim key P R Q' a c := by
  intro env store document hunique hdoc hp
  obtain ⟨hr, hq, hrest⟩ := hs env store document hunique hdoc hp
  exact ⟨hr, h _ _ hq, hrest⟩

/-- A step that needs nothing runs under any precondition. -/
theorem Sim.weaken {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} {a : Abstract.Handler α} {c : DocumentHandler key β}
    (hs : Sim key (fun _ => True) R Q a c) : Sim key P R Q a c :=
  Sim.pre (fun _ _ => trivial) hs

/-- A property the concrete step preserves holds after it. -/
theorem Sim.frame {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} {a : Abstract.Handler α} {c : DocumentHandler key β}
    (F : Document key → Prop) (hF : ∀ env d, F d → F (c env d).2.1)
    (hs : Sim key P R Q a c) :
    Sim key (fun d => P d ∧ F d) R (fun b d => Q b d ∧ F d) a c := by
  intro env store document hunique hdoc ⟨hp, hf⟩
  obtain ⟨hr, hq, hrest⟩ := hs env store document hunique hdoc hp
  exact ⟨hr, ⟨hq, hF env document hf⟩, hrest⟩

theorem Sim.ite {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} (p : Prop) [Decidable p]
    {a₁ a₂ : Abstract.Handler α} {c₁ c₂ : DocumentHandler key β}
    (h₁ : p → Sim key P R Q a₁ c₁) (h₂ : ¬ p → Sim key P R Q a₂ c₂) :
    Sim key P R Q (if p then a₁ else a₂) (if p then c₁ else c₂) := by
  by_cases hp : p
  · simpa [hp] using h₁ hp
  · simpa [hp] using h₂ hp

theorem Sim.seq {key : DocumentKey} {P : Document key → Prop}
    {Q : Unit → Document key → Prop} {S : γ → δ → Prop} {T : δ → Document key → Prop}
    {ma : Abstract.Handler Unit} {mc : DocumentHandler key Unit}
    {fa : Abstract.Handler γ} {fc : DocumentHandler key δ}
    (hm : Sim key P Eq Q ma mc) (hf : Sim key (Q ()) S T fa fc) :
    Sim key P S T (ma >>= fun _ => fa) (mc >>= fun _ => fc) :=
  Sim.bind hm fun _ _ _ => hf

theorem Sim.pure_bind {key : DocumentKey} {P : Document key → Prop} {S : γ → δ → Prop}
    {T : δ → Document key → Prop} {a : α}
    {fa : α → Abstract.Handler γ} {fc : α → DocumentHandler key δ}
    (h : Sim key P S T (fa a) (fc a)) :
    Sim key P S T ((Pure.pure a : Abstract.Handler α) >>= fa)
      ((Pure.pure a : DocumentHandler key α) >>= fc) :=
  Sim.bind (Sim.pure (R := fun x y => x = a ∧ y = a) (Q := fun _ d => P d) ⟨rfl, rfl⟩
    fun _ h => h) fun _ _ ⟨ha, hc⟩ => by subst ha; subst hc; exact h

theorem Sim.bind_left {key : DocumentKey} {P : Document key → Prop} {R : α → β → Prop}
    {Q : β → Document key → Prop} {S : γ → δ → Prop} {T : δ → Document key → Prop}
    {ma : Abstract.Handler α} {u : β} {fa : α → Abstract.Handler γ}
    {mc : DocumentHandler key δ}
    (hm : Sim key P R Q ma (Pure.pure u)) (hf : ∀ a, R a u → Sim key (Q u) S T (fa a) mc) :
    Sim key P S T (ma >>= fa) mc := by
  intro env store document hunique hdoc hp
  obtain ⟨hr, hq, hsame, hemit, hunique'⟩ := hm env store document hunique hdoc hp
  obtain ⟨hr', hq', hsame', hemit', hunique''⟩ :=
    hf _ hr env (ma env store).2.1 document hunique' (Same.read_of_write hsame) hq
  refine ⟨hr', hq', ?_, ?_, hunique''⟩
  · exact hsame'.trans
      ((Same.write hsame key _).trans (Store.write_write_same store key _ _))
  · show (ma env store).2.2 ++ (fa (ma env store).1 env (ma env store).2.1).2.2 = _
    rw [hemit', hemit]
    rfl

/-- A handler that only reads simulates doing nothing. -/
theorem Sim.readOnly {key : DocumentKey} {P : Document key → Prop}
    {ma : Abstract.Handler α}
    (h : ∀ env store, (ma env store).2 = (store, [])) :
    Sim key P (fun _ _ => True) (fun _ d => P d) ma (Pure.pure ()) := by
  intro env store document hunique hdoc hp
  refine ⟨trivial, hp, ?_, ?_, ?_⟩
  · rw [h env store]
    exact Same.write_of hdoc
  · rw [h env store]
    rfl
  · rw [h env store]
    exact hunique

/-! ## What a read shows -/

theorem task_project_of_pending {t : TaskObject} {p : PromiseObject} (h : p.state = .pending) :
    t.project p = t := by
  simp [AbstractModel.TaskObject.project, h]

theorem task_project_state_of_settled {t : TaskObject} {p : PromiseObject}
    (h : p.state ≠ .pending) : (t.project p).state = .fulfilled := by
  unfold AbstractModel.TaskObject.project
  by_cases ht : t.state = .fulfilled
  · simp [ht]
  · simp [h, ht, AbstractModel.TaskObject.fulfill]

theorem task_project_of_settled {t : TaskObject} {p : PromiseObject} (h : p.state ≠ .pending)
    (ht : t.state ≠ .fulfilled) : t.project p = t.fulfill := by
  simp [AbstractModel.TaskObject.project, h, ht]

/-- Viewing through `q` first changes nothing when `q` is settled whenever
`p` is. -/
theorem task_project_project {t : TaskObject} {p q : PromiseObject}
    (h : p.state = .pending → q.state = .pending) :
    (t.project q).project p = t.project p := by
  by_cases hq : q.state = .pending
  · rw [task_project_of_pending hq]
  · have hp : p.state ≠ .pending := fun hp => hq (h hp)
    by_cases ht : t.state = .fulfilled
    · simp [AbstractModel.TaskObject.project, ht]
    · rw [task_project_of_settled hq ht, task_project_of_settled hp ht]
      simp [AbstractModel.TaskObject.project, AbstractModel.TaskObject.fulfill]

theorem project_pending (p : PromiseObject) (now : Nat) :
    (p.project now).state = .pending → p.state = .pending := by
  unfold AbstractModel.PromiseObject.project
  split
  · split <;> simp
  · exact id

theorem project_cases (p : PromiseObject) (now : Nat) :
    p.project now = p ∨ (p.project now).state ≠ .pending := by
  unfold AbstractModel.PromiseObject.project
  split
  · right
    split <;> simp
  · left
    rfl

@[simp] theorem addCallback_state (p : PromiseObject) (awaiter : Ident) :
    (p.addCallback awaiter).state = p.state := by
  unfold AbstractModel.PromiseObject.addCallback
  split <;> rfl

@[simp] theorem addListener_state (p : PromiseObject) (address : String) :
    (p.addListener address).state = p.state := by
  unfold AbstractModel.PromiseObject.addListener
  split <;> rfl

theorem project_norm {origin : String} (row : OriginObject origin) (now : Nat) :
    row.norm.project now = row.project now := by
  obtain ⟨suffix, promise, _ | task⟩ := row
  · rfl
  · simp only [OriginObject.project, OriginObject.norm, Option.map_some,
      task_project_project (project_pending promise now)]

/-- Two rows with the same promise read alike when the stored task is projected
through a promise settled whenever this one is. -/
theorem norm_project {origin : String} (s : String) {p q : PromiseObject}
    (task : Option TaskObject) (h : p.state = .pending → q.state = .pending) :
    (⟨s, p, task.map (·.project q)⟩ : OriginObject origin).norm =
      (⟨s, p, task⟩ : OriginObject origin).norm := by
  cases task with
  | none => rfl
  | some t => simp only [OriginObject.norm, Option.map_some, task_project_project h]

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

theorem map_norm_suffix {origin : String} (document : OriginDocument origin) :
    (document.map (·.norm)).map (·.suffix) = document.map (·.suffix) := by
  rw [List.map_map]
  rfl

theorem RowsUnique.of_equiv {origin : String} {a b : OriginDocument origin}
    (ha : RowsUnique a) (h : DocEquiv (.origin origin) a b) : RowsUnique b := by
  have hb := ((List.Perm.map (·.suffix) h).nodup_iff).mp
    (by rw [map_norm_suffix]; exact ha)
  rwa [map_norm_suffix] at hb

theorem find?_map_norm {origin : String} (document : OriginDocument origin) (s : String) :
    (document.map (·.norm)).find? (·.suffix == s) =
      (document.find? (·.suffix == s)).map (·.norm) := by
  rw [List.find?_map]
  rfl

/-- Documents that read alike give rows that read alike for each suffix. -/
theorem find?_equiv {origin : String} {a b : OriginDocument origin}
    (ha : RowsUnique a) (h : DocEquiv (.origin origin) a b) (s : String) :
    (a.find? (·.suffix == s)).map (·.norm) = (b.find? (·.suffix == s)).map (·.norm) := by
  rw [← find?_map_norm, ← find?_map_norm]
  refine find?_perm ?_ h s
  show ((a.map _).map _).Nodup
  rw [map_norm_suffix]
  exact ha

theorem map_norm_filter {origin : String} (document : OriginDocument origin) (s : String) :
    (document.filter (·.suffix != s)).map (·.norm) =
      (document.map (·.norm)).filter (·.suffix != s) := by
  rw [List.filter_map]
  rfl

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

/-- What the abstract store shows at `id` is what the concrete document
shows at its suffix. -/
theorem readObject_eq_document {store : Store} {id : Ident}
    {document : OriginDocument id.origin} (hunique : store.Unique)
    (hdoc : DocEquiv (.origin id.origin) (store.read (.origin id.origin)) document)
    (now : Nat) :
    (store.getObject id).map (·.project now) =
      (document.find? (·.suffix == id.suffix)).map
        (fun row => Object.ofOrigin (row.project now)) := by
  have key : ∀ x : Option (OriginObject id.origin),
      x.map (fun row => Object.ofOrigin (row.project now)) =
        (x.map (·.norm)).map (fun row => Object.ofOrigin (row.project now)) := by
    intro x
    cases x <;> simp [project_norm]
  rw [getObject_eq_read, Option.map_map]
  show ((store.read (.origin id.origin)).find? (·.suffix == id.suffix)).map
    (fun row => Object.ofOrigin (row.project now)) = _
  rw [key, find?_equiv (hunique.rows _) hdoc, ← key]

/-- What a read of `suffix` at `now` showed. -/
def Fact {origin : String} (suffix : String) (now : Nat)
    (value : Option (OriginObject origin)) (document : OriginDocument origin) : Prop :=
  (document.find? (·.suffix == suffix)).map (·.project now) = value

/-- What a task read of `suffix` at `now` showed, when it found a task. -/
def TaskFact {origin : String} (suffix : String) (now : Nat)
    (value : Option (OriginObject origin)) (document : OriginDocument origin) : Prop :=
  ∀ row, value = some row → Fact suffix now (some row) document

theorem Fact.row {origin s : String} {now : Nat} {value : OriginObject origin}
    {document : OriginDocument origin} (h : Fact s now (some value) document) :
    ∃ row, document.find? (·.suffix == s) = some row ∧ row.project now = value := by
  unfold Fact at h
  cases hfind : document.find? (·.suffix == s) with
  | none => simp [hfind] at h
  | some row =>
      simp only [hfind, Option.map_some, Option.some.injEq] at h
      exact ⟨row, rfl, h⟩

theorem Fact.none {origin s : String} {now : Nat} {document : OriginDocument origin}
    (h : Fact s now none document) : document.find? (·.suffix == s) = none := by
  unfold Fact at h
  cases hfind : document.find? (·.suffix == s) with
  | none => rfl
  | some row => simp [hfind] at h

/-- The row a read found, with what it showed. -/
theorem Fact.cases {origin s : String} {now : Nat} {promise : PromiseObject}
    {task : Option TaskObject} {document : OriginDocument origin}
    (h : Fact s now (some ⟨s, promise, task⟩) document) :
    ∃ stored current, document.find? (·.suffix == s) = some ⟨s, stored, current⟩ ∧
      promise = stored.project now ∧ task = current.map (·.project (stored.project now)) := by
  obtain ⟨⟨rs, stored, current⟩, hfind, hrow⟩ := h.row
  simp only [OriginObject.project, OriginObject.mk.injEq] at hrow
  obtain ⟨rfl, rfl, rfl⟩ := hrow
  exact ⟨stored, current, hfind, rfl, rfl⟩

theorem readObject_sim (id : Ident) (now : Nat) {P : Document (.origin id.origin) → Prop} :
    Sim (.origin id.origin) P (ObjRel id.origin id.suffix)
      (fun found d => Fact id.suffix now found d ∧ P d)
      (Abstract.readObject id now) (Concrete.Decision.readObject id.suffix now) := by
  intro env store document hunique hdoc hp
  have ha : Abstract.readObject id now env store =
      ((store.getObject id).map (·.project now), store, []) := by
    simp only [Abstract.readObject, Abstract.getObject, bind, pure, List.append_nil]
  have hc : Concrete.Decision.readObject id.suffix now env document =
      ((document.find? (·.suffix == id.suffix)).map (·.project now), document, []) := by
    simp only [Concrete.Decision.readObject, Concrete.Decision.getObject, documentGet,
      bind, pure]
    cases document.find? (·.suffix == id.suffix) <;> rfl
  rw [ha, hc, readObject_eq_document hunique hdoc]
  refine ⟨⟨?_, ?_⟩, ⟨rfl, hp⟩, Same.write_of hdoc, rfl, hunique⟩
  · cases document.find? (·.suffix == id.suffix) <;> rfl
  · intro row h
    cases hfind : document.find? (·.suffix == id.suffix) with
    | none => simp [hfind] at h
    | some found =>
        simp only [hfind, Option.map_some, Option.some.injEq] at h
        subst h
        exact (find?_suffix hfind : found.suffix = id.suffix)

/-- An abstract task read corresponds to the concrete read followed by a
match on the task. -/
def TaskRel (origin suffix : String) (a : Option (Object × TaskObject))
    (c : Option (OriginObject origin)) : Prop :=
  a = c.bind (fun row => row.task.map (Object.ofOrigin row, ·)) ∧
    ∀ row, c = some row → row.suffix = suffix

theorem readTask_sim (id : Ident) (now : Nat) {P : Document (.origin id.origin) → Prop} :
    Sim (.origin id.origin) P (TaskRel id.origin id.suffix)
      (fun found d => TaskFact id.suffix now found d ∧ P d)
      (Abstract.readTask id now) (Concrete.Decision.readTaskObject id.suffix now) := by
  intro env store document hunique hdoc hp
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
  rw [ha, hc, readObject_eq_document hunique hdoc]
  refine ⟨?_, ⟨?_, hp⟩, Same.write_of hdoc, rfl, hunique⟩
  · cases hfind : document.find? (·.suffix == id.suffix) with
    | none => exact ⟨rfl, by simp⟩
    | some row =>
        have hsuffix := find?_suffix hfind
        cases htask : row.task with
        | none =>
            exact ⟨by simp [htask, Object.ofOrigin, OriginObject.project], by simp [htask]⟩
        | some task =>
            refine ⟨?_, ?_⟩
            · simp [htask, Object.project, Object.ofOrigin, OriginObject.project]
            · simpa [htask, OriginObject.project] using hsuffix
  · intro row h
    cases hfind : document.find? (·.suffix == id.suffix) with
    | none => simp [hfind] at h
    | some found =>
        cases htask : found.task with
        | none => simp [hfind, htask] at h
        | some task =>
            simp only [hfind, htask, Option.isSome_some, ↓reduceIte,
              Option.some.injEq] at h
            subst h
            simp [Fact, hfind]

/-- The timeout step reads the stored row and writes it back as read. -/
theorem readObject_getObject_sim (id : Ident) (now : Nat)
    {P : Document (.origin id.origin) → Prop} :
    Sim (.origin id.origin) P
      (fun a c => a = c.map (fun row => Object.ofOrigin (row.project now)))
      (fun _ d => P d)
      (Abstract.readObject id now) (Concrete.Decision.getObject id.suffix) := by
  intro env store document hunique hdoc hp
  refine ⟨?_, hp, Same.write_of hdoc, rfl, hunique⟩
  simp only [Abstract.readObject, Abstract.getObject, Concrete.Decision.getObject, bind,
    documentGet, pure]
  exact readObject_eq_document hunique hdoc now

/-! ## Writes -/

theorem same_write_origin {a store : Store} {origin : String}
    {document : OriginDocument origin}
    (hschedules : a.schedules = store.schedules)
    (hsame : DocEquiv (.origin origin) (a.read (.origin origin)) document)
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

/-- Writing `object` matches putting a row that reads alike in front of the
document rows with other suffixes. -/
theorem setObject_equiv {store : Store} (object : Object)
    {document : OriginDocument object.id.origin}
    (hdoc : DocEquiv (.origin object.id.origin)
      (store.read (.origin object.id.origin)) document)
    {row : OriginObject object.id.origin}
    (hrow : row.norm = (⟨object.id.suffix, object.promise, object.task⟩ :
      OriginObject object.id.origin).norm) :
    Same (store.setObject object)
      (store.write (.origin object.id.origin)
        (row :: document.filter (·.suffix != object.id.suffix))) := by
  refine same_write_origin rfl ?_ (fun other h => read_setObject_other store object h)
  rw [read_setObject_same]
  show List.Perm (List.map _ (_ :: _)) (List.map _ (_ :: _))
  simp only [List.map_cons]
  rw [hrow, map_norm_filter, map_norm_filter]
  exact (List.Perm.filter _ hdoc).cons _

theorem setPromise_apply {origin : String} (s : String) (p : PromiseObject) (env : HandlerEnv)
    (document : OriginDocument origin) :
    Concrete.Decision.setPromise s p env document =
      ((), (match document.find? (·.suffix == s) with
        | some existing => { existing with promise := p }
        | none => { suffix := s, promise := p }) :: document.filter (·.suffix != s), []) :=
  rfl

theorem setTask_apply {origin : String} (s : String) (t : TaskObject) (env : HandlerEnv)
    (document : OriginDocument origin) :
    Concrete.Decision.setTask s t env document =
      ((), document.map (fun object =>
        if object.suffix == s then { object with task := some t } else object), []) :=
  rfl

theorem map_setTask_filter {origin : String} (s : String) (t : TaskObject)
    (document : OriginDocument origin) :
    (document.filter (·.suffix != s)).map (fun object =>
        if object.suffix == s then { object with task := some t } else object) =
      document.filter (·.suffix != s) := by
  rw [List.map_congr_left (g := fun x => x), List.map_id']
  intro object hobject
  have := (List.mem_filter.mp hobject).2
  simp only [bne_iff_ne, ne_eq] at this
  simp [this]

@[simp] theorem map_setTask_filter' {origin : String} (s : String) (t : TaskObject)
    (document : OriginDocument origin) :
    (document.filter (·.suffix != s)).map (fun object =>
        if object.suffix = s then
          { suffix := object.suffix, promise := object.promise, task := some t }
        else object) =
      document.filter (·.suffix != s) := by
  rw [List.map_congr_left (g := fun x => x), List.map_id']
  intro object hobject
  have := (List.mem_filter.mp hobject).2
  simp only [bne_iff_ne, ne_eq] at this
  simp [this]

theorem setObject_sim {origin : String} (row : OriginObject origin)
    {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P Eq (fun _ _ => True) (Abstract.setObject (Object.ofOrigin row))
      (Concrete.Decision.setObject row) := by
  intro env store document hunique hdoc _
  refine ⟨rfl, trivial, ?_, rfl, hunique.setObject _⟩
  exact setObject_equiv (Object.ofOrigin row) hdoc (by rfl)

/-- Writing the read object with a new promise is setting the promise on the
stored row, as long as the new promise is settled when the read one was. -/
theorem setPromise_sim {origin : String} (s : String) {now : Nat}
    {promise p : PromiseObject} {task : Option TaskObject}
    {P : Document (.origin origin) → Prop}
    (hfact : ∀ d, P d → Fact s now (some ⟨s, promise, task⟩) d)
    (hstate : p.state = .pending → promise.state = .pending) :
    Sim (.origin origin) P Eq (fun _ _ => True)
      (Abstract.setObject { id := { origin, suffix := s }, promise := p, task })
      (Concrete.Decision.setPromise s p) := by
  intro env store document hunique hdoc hp
  obtain ⟨stored, current, hfind, rfl, rfl⟩ := (hfact document hp).cases
  refine ⟨rfl, trivial, ?_, rfl, hunique.setObject _⟩
  rw [setPromise_apply, hfind]
  exact setObject_equiv _ hdoc (by exact (norm_project s current hstate).symm)

/-- Writing the read object with a new task is setting the task on the
stored row, as long as the read promise is the stored one: it is pending,
or the read task is not finished. -/
theorem setTask_sim {origin : String} (s : String) {now : Nat}
    {promise : PromiseObject} {current : Option TaskObject} {task : TaskObject}
    {P : Document (.origin origin) → Prop}
    (hfact : ∀ d, P d → Fact s now (some ⟨s, promise, current⟩) d)
    (hpending : promise.state = .pending ∨ ∃ t, current = some t ∧ t.state ≠ .fulfilled) :
    Sim (.origin origin) P Eq (fun _ _ => True)
      (Abstract.setObject { id := { origin, suffix := s }, promise, task := some task })
      (Concrete.Decision.setTask s task) := by
  intro env store document hunique hdoc hp
  obtain ⟨stored, stask, hfind, rfl, rfl⟩ := (hfact document hp).cases
  have hstored : stored.project now = stored := by
    rcases project_cases stored now with h | h
    · exact h
    · rcases hpending with hp | ⟨t, ht, hfulfilled⟩
      · exact (h hp).elim
      · cases stask with
        | none => cases ht
        | some st =>
            simp only [Option.map_some, Option.some.injEq] at ht
            subst ht
            exact (hfulfilled (task_project_state_of_settled h)).elim
  have hunique' : RowsUnique document := (hunique.rows origin).of_equiv hdoc
  have hmem := List.mem_of_find?_eq_some hfind
  refine ⟨rfl, trivial, ?_, rfl, hunique.setObject _⟩
  rw [setTask_apply]
  refine (setObject_equiv _ hdoc (row := ⟨s, stored.project now, some task⟩)
    (by rfl)).trans
    (Same.write_equiv store (DocEquiv.of_perm ?_))
  have hperm := (perm_cons_filter hunique' hmem).map (fun object =>
    if object.suffix == s then { object with task := some task } else object)
  simp only [List.map_cons, beq_self_eq_true, ↓reduceIte] at hperm
  rw [map_setTask_filter] at hperm
  rw [hstored]
  exact hperm.symm

theorem settable_ne_pending {state : PromiseState} (h : state.settable = true) :
    state ≠ .pending := by
  rintro rfl
  simp [PromiseState.settable] at h

/-- A settled promise reads as it is, and its task as finished. -/
theorem Object.project_settled (o : Object) {p : PromiseObject} (now : Nat)
    (h : p.state ≠ .pending) :
    ({ o with promise := p }.project now) =
      { o with promise := p, task := o.task.map (·.project p) } := by
  simp [Object.project, h, AbstractModel.TaskObject.project]

/-- Settling the read object is setting the promise on the stored row and
finishing its task. -/
theorem setSettled_sim {origin : String} (s : String) {now : Nat}
    {promise p : PromiseObject} {task : Option TaskObject}
    {P : Document (.origin origin) → Prop}
    (hfact : ∀ d, P d → Fact s now (some ⟨s, promise, task⟩) d)
    (hstate : p.state = .pending → promise.state = .pending)
    (hsettled : p.state ≠ .pending) :
    Sim (.origin origin) P Eq (fun _ _ => True)
      (Abstract.setSettled { id := { origin, suffix := s }, promise, task } p now)
      (Concrete.Decision.setSettled ⟨s, promise, task⟩ p) := by
  unfold Abstract.setSettled
  rw [Object.project_settled _ _ hsettled]
  intro env store document hunique hdoc hp
  obtain ⟨stored, current, hfind, rfl, rfl⟩ := (hfact document hp).cases
  cases current with
  | none =>
      have hc : Concrete.Decision.setSettled ⟨s, stored.project now, none⟩ p env document =
          ((), ⟨s, p, none⟩ :: document.filter (·.suffix != s), []) := by
        by_cases hpending : p.state = .pending <;>
          simp [Concrete.Decision.setSettled, bind, pure, setPromise_apply, hfind, hpending] <;> rfl
      simp only [Option.map_none]
      rw [hc]
      exact ⟨by trivial, trivial, setObject_equiv _ hdoc (by rfl), by trivial, hunique.setObject _⟩
  | some t =>
      simp only [Option.map_some]
      by_cases hpending : p.state = .pending
      · have hc : Concrete.Decision.setSettled ⟨s, stored.project now,
            some (t.project (stored.project now))⟩ p env document =
            ((), ⟨s, p, some t⟩ :: document.filter (·.suffix != s), []) := by
          simp [Concrete.Decision.setSettled, bind, pure, setPromise_apply, hfind, hpending] <;> rfl
        rw [hc]
        refine ⟨by trivial, trivial, setObject_equiv _ hdoc ?_, by trivial, hunique.setObject _⟩
        simp [OriginObject.norm, task_project_of_pending hpending,
          task_project_of_pending (hstate hpending)]
      · by_cases ht : (t.project (stored.project now)).state = .fulfilled
        · have hc : Concrete.Decision.setSettled ⟨s, stored.project now,
              some (t.project (stored.project now))⟩ p env document =
              ((), ⟨s, p, some t⟩ :: document.filter (·.suffix != s), []) := by
            simp [Concrete.Decision.setSettled, bind, pure, setPromise_apply, hfind,
              hpending, ht] <;> rfl
          rw [hc]
          refine ⟨by trivial, trivial, setObject_equiv _ hdoc ?_, by trivial, hunique.setObject _⟩
          simp [OriginObject.norm, task_project_project hstate, task_project_project (t := t) (p := p) (q := p) id]
        · have hc : Concrete.Decision.setSettled ⟨s, stored.project now,
              some (t.project (stored.project now))⟩ p env document =
              ((), ⟨s, p, some (t.project (stored.project now)).fulfill⟩ ::
                document.filter (·.suffix != s), []) := by
            simp [Concrete.Decision.setSettled, bind, pure, setPromise_apply,
              setTask_apply, hfind, hpending, ht, map_setTask_filter] <;> rfl
          rw [hc]
          refine ⟨by trivial, trivial, setObject_equiv _ hdoc ?_, by trivial, hunique.setObject _⟩
          simp [task_project_of_settled hpending ht]

theorem setPromise_setTask_apply {origin : String} (s : String) (p : PromiseObject)
    (t : TaskObject) (env : HandlerEnv) (document : OriginDocument origin) :
    (Concrete.Decision.setPromise s p >>= fun _ => Concrete.Decision.setTask s t) env
        document =
      ((), ⟨s, p, some t⟩ :: document.filter (·.suffix != s), []) := by
  simp only [bind, setPromise_apply, setTask_apply, List.append_nil]
  cases hfind : document.find? (·.suffix == s) with
  | none => simp <;> rfl
  | some row =>
      have hsuffix := find?_suffix hfind
      obtain ⟨rs, rp, rt⟩ := row
      simp only at hsuffix
      subst hsuffix
      simp <;> rfl

theorem Concrete.bind_assoc {key : DocumentKey} (x : DocumentHandler key α)
    (f : α → DocumentHandler key β) (g : β → DocumentHandler key γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  funext env document
  simp only [bind, List.append_assoc]

theorem Concrete.pure_bind {key : DocumentKey} (u : α) (f : α → DocumentHandler key β) :
    (Pure.pure u : DocumentHandler key α) >>= f = f u := by
  funext env document
  simp only [bind, Pure.pure, List.nil_append]

/-- Creating an object with its task is setting the promise and then the
task, whatever the document held. -/
theorem setObject_create_sim {origin : String} (s : String) (p : PromiseObject)
    (t : TaskObject) {P : Document (.origin origin) → Prop} {S : γ → δ → Prop}
    {T : δ → Document (.origin origin) → Prop} {ka : Abstract.Handler γ}
    {kc : DocumentHandler (.origin origin) δ}
    (hk : Sim (.origin origin) (fun _ => True) S T ka kc) :
    Sim (.origin origin) P S T
      (Abstract.setObject { id := { origin, suffix := s }, promise := p, task := some t } >>=
        fun _ => ka)
      (Concrete.Decision.setPromise s p >>= fun _ => Concrete.Decision.setTask s t >>=
        fun _ => kc) := by
  rw [← Concrete.bind_assoc]
  refine Sim.seq (Q := fun _ _ => True) ?_ hk
  intro env store document hunique hdoc _
  rw [setPromise_setTask_apply]
  exact ⟨rfl, trivial, setObject_equiv _ hdoc (by rfl), rfl, hunique.setObject _⟩

theorem newObject_id (id : Ident) (timeoutAt now : Nat) (param : Value) (tags : Tags) :
    (Abstract.newObject id timeoutAt now param tags).id = id := by
  unfold Abstract.newObject
  dsimp only
  repeat' split
  all_goals rfl

theorem newObject_eq (id : Ident) (timeoutAt now : Nat) (param : Value) (tags : Tags) :
    ∃ promise task, Abstract.newObject id timeoutAt now param tags = { id, promise, task } := by
  have h := newObject_id id timeoutAt now param tags
  generalize Abstract.newObject id timeoutAt now param tags = object at h ⊢
  subst h
  exact ⟨_, _, rfl⟩

theorem createPromiseAt_apply (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) (env : HandlerEnv) {document : OriginDocument id.origin}
    (hnone : document.find? (·.suffix == id.suffix) = none) :
    Concrete.Decision.createPromiseAt id.suffix timeoutAt now param tags env document =
      (⟨id.suffix, (Abstract.newObject id timeoutAt now param tags).promise,
          (Abstract.newObject id timeoutAt now param tags).task⟩,
        ⟨id.suffix, (Abstract.newObject id timeoutAt now param tags).promise,
          (Abstract.newObject id timeoutAt now param tags).task⟩ ::
          document.filter (·.suffix != id.suffix), []) := by
  unfold Abstract.newObject Concrete.Decision.createPromiseAt
  by_cases htime : timeoutAt > now <;> by_cases hrun : tags.otype = .runnable <;>
    simp [htime, hrun, bind, pure, setPromise_apply, setTask_apply, map_setTask_filter,
      hnone, AbstractModel.PromiseObject.otype] <;> rfl

theorem createPromiseAt_sim (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) {n : Nat} {P : Document (.origin id.origin) → Prop}
    (hfact : ∀ d, P d → Fact id.suffix n none d) :
    Sim (.origin id.origin) P (fun a c => a = Object.ofOrigin c) (fun _ _ => True)
      (Abstract.createPromiseAt id timeoutAt now param tags)
      (Concrete.Decision.createPromiseAt id.suffix timeoutAt now param tags) := by
  intro env store document hunique hdoc hp
  have ha : Abstract.createPromiseAt id timeoutAt now param tags env store =
      (Abstract.newObject id timeoutAt now param tags,
        store.setObject (Abstract.newObject id timeoutAt now param tags), []) := rfl
  rw [ha, createPromiseAt_apply id timeoutAt now param tags env (hfact document hp).none]
  obtain ⟨promise, task, hobject⟩ := newObject_eq id timeoutAt now param tags
  rw [hobject]
  exact ⟨rfl, trivial, setObject_equiv { id, promise, task } hdoc (by rfl), rfl,
    hunique.setObject _⟩

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

theorem getSchedule_sim (id : Ident) {P : Document (.schedule id) → Prop} :
    Sim (.schedule id) P Eq (fun _ d => P d) (Abstract.getSchedule id)
      (Concrete.Decision.getSchedule (id := id)) := by
  intro env store document hunique hdoc hp
  obtain rfl : store.read (.schedule id) = document := hdoc
  refine ⟨?_, hp, Same.symm (Store.read_write_read store _), rfl, hunique⟩
  simp [Abstract.getSchedule, Concrete.Decision.getSchedule, getSchedule_eq_read,
    bind, documentGet, pure]

theorem setSchedule_sim (id : Ident) (schedule : Schedule) (h : schedule.id = id)
    {P : Document (.schedule id) → Prop} :
    Sim (.schedule id) P Eq (fun _ _ => True) (Abstract.setSchedule schedule)
      (Concrete.Decision.setScheduleValue (id := id) schedule) := by
  subst h
  intro env store document hunique _ _
  refine ⟨rfl, trivial, ?_, rfl, hunique.schedules rfl⟩
  simp only [Abstract.setSchedule, Concrete.Decision.setScheduleValue,
    Concrete.Decision.setSchedule, Concrete.Decision.set, documentSet]
  exact Store.setSchedule_same store schedule

theorem deleteSchedule_sim (id : Ident) {P : Document (.schedule id) → Prop} :
    Sim (.schedule id) P Eq (fun _ _ => True) (Abstract.deleteSchedule id)
      (Concrete.Decision.delSchedule (id := id)) := by
  intro env store document hunique _ _
  refine ⟨rfl, trivial, ?_, rfl, hunique.schedules rfl⟩
  have : store.deleteSchedule id = store.write (.schedule id) none := by
    simp [Store.deleteSchedule, Store.write]
  simp only [Abstract.deleteSchedule, Concrete.Decision.delSchedule,
    Concrete.Decision.set, documentSet, this]
  exact Same.refl _

theorem setMessage_sim {key : DocumentKey} (address : String)
    (message : ServerModel.Message) {P : Document key → Prop} :
    Sim key P Eq (fun _ d => P d) (Abstract.setMessage address message)
      (Concrete.Decision.setMessage (key := key) address message) := by
  intro env store document hunique hdoc hp
  exact ⟨rfl, hp, Same.write_of hdoc, rfl, hunique⟩

theorem ask_sim {key : DocumentKey} {P : Document key → Prop} :
    Sim key P Eq (fun _ d => P d) Abstract.ask (Concrete.Decision.ask (key := key)) := by
  intro env store document hunique hdoc hp
  exact ⟨rfl, hp, Same.write_of hdoc, rfl, hunique⟩

/-- Setting a promise leaves what reads of other suffixes show. -/
theorem find?_filter_ne {origin : String} {s s' : String} (h : s' ≠ s) :
    ∀ document : OriginDocument origin,
      (document.filter (·.suffix != s)).find? (·.suffix == s') =
        document.find? (·.suffix == s')
  | [] => rfl
  | row :: rest => by
      have ih := find?_filter_ne h rest
      by_cases hs : row.suffix = s
      · have hskip : (row.suffix == s') = false := by simp [hs, Ne.symm h]
        rw [List.filter_cons, if_neg (by simp [hs])]
        simp only [List.find?_cons, hskip]
        exact ih
      · have hkeep : (row.suffix != s) = true := by simpa using hs
        rw [List.filter_cons, if_pos hkeep]
        simp only [List.find?_cons]
        cases (row.suffix == s') with
        | true => rfl
        | false => exact ih

theorem setPromise_frame {origin : String} {s s' : String} (p : PromiseObject)
    (h : s' ≠ s) {now : Nat} {value : Option (OriginObject origin)} (env : HandlerEnv)
    (document : OriginDocument origin) (hfact : Fact s' now value document) :
    Fact s' now value (Concrete.Decision.setPromise s p env document).2.1 := by
  unfold Fact at hfact ⊢
  rw [setPromise_apply]
  have hhead : ∀ row : OriginObject origin, row.suffix = s →
      (row :: document.filter (·.suffix != s)).find? (·.suffix == s') =
        document.find? (·.suffix == s') := by
    intro row hrow
    have : (row.suffix == s') = false := by simp [hrow, Ne.symm h]
    rw [List.find?_cons, this, find?_filter_ne h]
  cases hfind : document.find? (·.suffix == s) with
  | none =>
      dsimp only
      rw [hhead _ rfl, hfact]
  | some row =>
      dsimp only
      rw [hhead { suffix := row.suffix, promise := p, task := row.task }
        (find?_suffix hfind : row.suffix = s), hfact]

theorem readObject_sim' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (ObjRel origin id.suffix)
      (fun found d => Fact id.suffix now found d ∧ P d) (Abstract.readObject id now)
      (Concrete.Decision.readObject (origin := origin) id.suffix now) := by
  subst h; exact readObject_sim id now

theorem readTask_sim' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (TaskRel origin id.suffix)
      (fun found d => TaskFact id.suffix now found d ∧ P d) (Abstract.readTask id now)
      (Concrete.Decision.readTaskObject (origin := origin) id.suffix now) := by
  subst h; exact readTask_sim id now

theorem createPromiseAt_sim' (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) {origin : String} (h : id.origin = origin) {n : Nat}
    {P : Document (.origin origin) → Prop}
    (hfact : ∀ d, P d → Fact id.suffix n none d) :
    Sim (.origin origin) P (fun a c => a = Object.ofOrigin c) (fun _ _ => True)
      (Abstract.createPromiseAt id timeoutAt now param tags)
      (Concrete.Decision.createPromiseAt (origin := origin) id.suffix timeoutAt now
        param tags) := by
  subst h; exact createPromiseAt_sim id timeoutAt now param tags hfact

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

/-- Close the side condition that an id lies in the document's origin. -/
macro "sim_origin" : tactic => `(tactic| first
  | rfl
  | (simp_all [Ident.sameOrigin, TaskFenceAction.targetId]; done))

/-- Find, among the facts the precondition carries, the read a write
needs. -/
macro "sim_fact" : tactic => `(tactic| first
  | exact fun _ h => h
  | exact fun _ h => h.1
  | exact fun _ h => h.1 _ rfl
  | exact fun _ h => h.2.1
  | exact fun _ h => h.2.1 _ rfl
  | exact fun _ h => h.2.2.1
  | exact fun _ h => h.2.2.1 _ rfl)

/-- The new promise is settled when the read one was. -/
macro "sim_state" : tactic => `(tactic| (intro; simp_all; done))

/-- The read promise is the stored one. -/
macro "sim_pending" : tactic => `(tactic| first
  | (apply Or.inl; simp_all; done)
  | (refine Or.inr ⟨_, rfl, ?_⟩; simp_all; done))

def lastString : Lean.Name → String
  | .str _ s => s
  | _ => ""

open Lean Meta Elab Tactic in
/-- One step of a handler simulation, chosen by the head of the abstract
handler. -/
elab "sim_dispatch" : tactic => withMainContext do
  let target ← whnfR (← instantiateMVars (← getMainTarget))
  unless target.isAppOfArity ``Sim 8 do throwError "sim_step: not a Sim goal"
  let a := (← instantiateMVars target.getAppArgs[6]!).headBeta
  let run (stx : MetaM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)
  if a.isAppOf ``Pure.pure then
    run `(tactic| exact Sim.pure rfl (fun _ _ => trivial))
  else if a.isAppOf ``ite then
    run `(tactic| refine Sim.ite _ (fun _ => ?_) (fun _ => ?_))
  else if a.isAppOf ``Bind.bind && a.getAppNumArgs == 6 then
    let ma := (← instantiateMVars a.getAppArgs[4]!).headBeta
    match ma.getAppFn.constName? with
    | some ``Pure.pure =>
        run `(tactic| refine Sim.pure_bind ?_)
    | some ``Resonate.Abstract.readObject =>
        run `(tactic| (refine Sim.bind (readObject_sim' _ _ (by sim_origin)) ?_
                       refine ObjRel.cases ?_ (fun _ _ => ?_)))
    | some ``Resonate.Abstract.readTask =>
        run `(tactic| (refine Sim.bind (readTask_sim' _ _ (by sim_origin)) ?_
                       refine TaskRel.cases ?_ (fun _ => ?_) (fun _ _ => ?_)))
    | some ``Resonate.Abstract.getSchedule =>
        run `(tactic| (refine Sim.bind (getSchedule_sim _) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.createPromiseAt =>
        run `(tactic| (refine Sim.bind
                         (createPromiseAt_sim' _ _ _ _ _ (by sim_origin) (by sim_fact)) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.setObject =>
        run `(tactic| first
          | (refine Sim.bind (setTask_sim _ (by sim_fact) ?_) fun _ _ _ => ?_
             next => sim_pending)
          | (refine Sim.bind (setPromise_sim _ (by sim_fact) ?_) fun _ _ _ => ?_
             next => sim_state)
          | refine setObject_create_sim _ _ _ ?_)
    | some ``Resonate.Abstract.setSettled =>
        run `(tactic|
          (refine Sim.bind (setSettled_sim _ (by sim_fact) ?_ ?_) fun _ _ _ => ?_
           next => sim_state
           next => (intro h; simp_all [PromiseState.settable]; done)))
    | some ``Resonate.Abstract.ask =>
        run `(tactic| (refine Sim.bind ask_sim ?_; intro _ _ h; subst h))
    | some ``Bind.bind =>
        run `(tactic| refine Sim.bind (R := Eq) (Q := fun _ _ => True) ?_ fun _ _ h => ?_)
    | some ``ite =>
        run `(tactic| refine Sim.bind (R := Eq) (Q := fun _ _ => True) ?_ fun _ _ h => ?_)
    | some name =>
        let lemma := mkIdent (Name.mkSimple (lastString name ++ "_sim"))
        run `(tactic| (refine Sim.bind (R := Eq) (Q := fun _ _ => True) (Sim.weaken ?_) ?_
                       · apply $lemma <;> sim_origin
                       intro _ _ h; subst h))
    | none =>
        run `(tactic| refine Sim.bind (R := Eq) (Q := fun _ _ => True) ?_ fun _ _ h => ?_)
  else
    match a.getAppFn.constName? with
    | some ``Resonate.Abstract.setObject =>
        run `(tactic| first
          | (refine setTask_sim _ (by sim_fact) ?_; sim_pending)
          | (refine setPromise_sim _ (by sim_fact) ?_; sim_state)
          | exact setObject_sim _)
    | some ``Resonate.Abstract.setMessage =>
        run `(tactic| exact Sim.post (fun _ _ _ => trivial) (setMessage_sim _ _))
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
          run `(tactic| (refine Sim.weaken ?_; apply $lemma <;> sim_origin))
        else
          run `(tactic| dsimp only [Object.ofOrigin])
    | none => run `(tactic| dsimp only [Object.ofOrigin])

macro "sim_step" : tactic => `(tactic| first
  | sim_dispatch
  | dsimp only [Object.ofOrigin]
  | simp only [Concrete.pure_bind, Abstract.pure_bind, Option.isNone_none,
      Option.isNone_some, Bool.false_eq_true, ↓reduceIte])

macro "sim" : tactic => `(tactic| repeat' sim_step)

/-- A handler simulation needs nothing of the document and promises nothing
of it. -/
abbrev HandlerSim (key : DocumentKey) (abstract : Abstract.Handler α)
    (concrete : DocumentHandler key α) : Prop :=
  Sim key (fun _ => True) Eq (fun _ _ => True) abstract concrete

theorem promiseGet_sim (req : PromiseGetReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.promiseGet req now)
      (Concrete.Decision.promiseGet req now) := by
  unfold Abstract.promiseGet Concrete.Decision.promiseGet
  sim

theorem promiseCreate_sim (req : PromiseCreateReq) (now : Nat) {origin : String}
    (h : req.id.origin = origin) :
    HandlerSim (.origin origin) (Abstract.promiseCreate req now)
      (Concrete.Decision.promiseCreateAt (origin := origin) req now) := by
  subst h
  unfold Abstract.promiseCreate Concrete.Decision.promiseCreateAt
  sim

theorem promiseSettle_sim (req : PromiseSettleReq) (now : Nat) {origin : String}
    (h : req.id.origin = origin) :
    HandlerSim (.origin origin) (Abstract.promiseSettle req now)
      (Concrete.Decision.promiseSettleAt (origin := origin) req now) := by
  subst h
  unfold Abstract.promiseSettle Concrete.Decision.promiseSettleAt
  sim

theorem promiseRegisterCallback_sim (req : PromiseRegisterCallbackReq) (now : Nat) :
    HandlerSim (.origin req.awaited.origin) (Abstract.promiseRegisterCallback req now)
      (Concrete.Decision.promiseRegisterCallback req now) := by
  unfold Abstract.promiseRegisterCallback Concrete.Decision.promiseRegisterCallback
  sim

theorem promiseRegisterListener_sim (req : PromiseRegisterListenerReq) (now : Nat) :
    HandlerSim (.origin req.awaited.origin) (Abstract.promiseRegisterListener req now)
      (Concrete.Decision.promiseRegisterListener req now) := by
  unfold Abstract.promiseRegisterListener Concrete.Decision.promiseRegisterListener
  sim

theorem scheduleGet_sim (req : ScheduleGetReq) (now : Nat) :
    HandlerSim (.schedule req.id) (Abstract.scheduleGet req now)
      (Concrete.Decision.scheduleGet req now) := by
  unfold Abstract.scheduleGet Concrete.Decision.scheduleGet
  sim

theorem scheduleCreate_sim (req : ScheduleCreateReq) (now : Nat) :
    HandlerSim (.schedule req.id) (Abstract.scheduleCreate req now)
      (Concrete.Decision.scheduleCreate req now) := by
  unfold Abstract.scheduleCreate Concrete.Decision.scheduleCreate
  sim

theorem scheduleDelete_sim (req : ScheduleDeleteReq) (now : Nat) :
    HandlerSim (.schedule req.id) (Abstract.scheduleDelete req now)
      (Concrete.Decision.scheduleDelete req now) := by
  unfold Abstract.scheduleDelete Concrete.Decision.scheduleDelete
  sim

theorem taskGet_sim (req : TaskGetReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskGet req now)
      (Concrete.Decision.taskGet req now) := by
  unfold Abstract.taskGet Concrete.Decision.taskGet
  sim

theorem taskAcquire_sim (req : TaskAcquireReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskAcquire req now)
      (Concrete.Decision.taskAcquire req now) := by
  unfold Abstract.taskAcquire Concrete.Decision.taskAcquire
  sim

theorem taskFence_sim (req : TaskFenceReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskFence req now)
      (Concrete.Decision.taskFence req now) := by
  obtain ⟨id, version, action⟩ := req
  unfold Abstract.taskFence Concrete.Decision.taskFence
  cases action <;> sim

theorem taskFulfill_sim (req : TaskFulfillReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskFulfill req now)
      (Concrete.Decision.taskFulfill req now) := by
  unfold Abstract.taskFulfill Concrete.Decision.taskFulfill
  sim

theorem taskRelease_sim (req : TaskReleaseReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskRelease req now)
      (Concrete.Decision.taskRelease req now) := by
  unfold Abstract.taskRelease Concrete.Decision.taskRelease
  sim

theorem taskHalt_sim (req : TaskHaltReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskHalt req now)
      (Concrete.Decision.taskHalt req now) := by
  unfold Abstract.taskHalt Concrete.Decision.taskHalt
  sim

theorem taskContinue_sim (req : TaskContinueReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskContinue req now)
      (Concrete.Decision.taskContinue req now) := by
  unfold Abstract.taskContinue Concrete.Decision.taskContinue
  sim

theorem taskCreate_sim (req : TaskCreateReq) (now : Nat) :
    HandlerSim (.origin req.action.id.origin) (Abstract.taskCreate req now)
      (Concrete.Decision.taskCreate req now) := by
  unfold Abstract.taskCreate Concrete.Decision.taskCreate
  sim

/-! ## Heartbeat -/

theorem heartbeatOne_sim (pid : String) (ref : TaskRef) (now : Nat) {origin : String}
    (h : ref.id.origin = origin) :
    HandlerSim (.origin origin) (Abstract.heartbeatOne pid ref now)
      (Concrete.Decision.heartbeatOne (origin := origin) pid ref now) := by
  subst h
  unfold Abstract.heartbeatOne Concrete.Decision.heartbeatOne
  sim

theorem heartbeatAll_sim (pid : String) (now : Nat) {origin : String} :
    ∀ refs : List TaskRef, (∀ ref ∈ refs, ref.id.origin = origin) →
      HandlerSim (.origin origin) (refs.forM (Abstract.heartbeatOne pid · now))
        (Concrete.Decision.heartbeatAll (origin := origin) pid now refs)
  | [], _ => by
      simp only [List.forM_nil, Concrete.Decision.heartbeatAll]
      exact Sim.pure rfl (fun _ _ => trivial)
  | ref :: rest, h => by
      simp only [List.forM_cons, Concrete.Decision.heartbeatAll]
      exact Sim.seq (heartbeatOne_sim pid ref now (h ref (by simp)))
        (heartbeatAll_sim pid now rest fun r hr => h r (by simp [hr]))

theorem taskHeartbeat_sim (req : TaskHeartbeatReq) (now : Nat) (first : TaskRef)
    (rest : List TaskRef) (htasks : req.tasks = first :: rest) :
    HandlerSim (.origin first.id.origin) (Abstract.taskHeartbeat req now)
      (Concrete.Decision.taskHeartbeat first.id.origin req now) := by
  unfold Abstract.taskHeartbeat Concrete.Decision.taskHeartbeat
  rw [htasks]
  have hcheck : (!sameOriginRefs first.id.origin (first :: rest)) =
      (first :: rest).any (fun ref => ref.id.origin != first.id.origin) := by
    simp only [sameOriginRefs, List.all_eq_not_any_not, Bool.not_not, bne]
  simp only [hcheck]
  refine Sim.ite _ (fun _ => Sim.pure rfl (fun _ _ => trivial)) (fun hall => ?_)
  refine Sim.seq (Q := fun _ _ => True) (Sim.pure rfl (fun _ _ => trivial))
    (Sim.seq (heartbeatAll_sim _ _ _ ?_) (Sim.pure rfl (fun _ _ => trivial)))
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

theorem checkAwaited_sim (now : Nat) {origin : String}
    {P : Document (.origin origin) → Prop} :
    ∀ actions : List PromiseRegisterCallbackReq,
      (∀ action ∈ actions, action.awaited.origin = origin) →
      Sim (.origin origin) P AwaitedRel (fun _ d => P d)
        (actions.mapM (Abstract.readObject ·.awaited now))
        (Concrete.Decision.checkAwaited (origin := origin) now actions)
  | [], _ => by
      simp only [List.mapM_nil, Concrete.Decision.checkAwaited]
      exact Sim.pure (by simp [AwaitedRel]) (fun _ h => h)
  | action :: rest, h => by
      rw [List.mapM_cons]
      simp only [Concrete.Decision.checkAwaited]
      refine Sim.bind (readObject_sim' _ _ (h action (by simp))) ?_
      refine ObjRel.cases ?_ (fun promise task => ?_)
      · exact Sim.bind_left (Sim.readOnly (mapM_readObject_state now rest))
          fun _ _ => Sim.pure (by simp [AwaitedRel]) (fun _ h => h.2)
      · dsimp only [Object.ofOrigin]
        by_cases hawait : promise.otype.awaitable
        · simp only [hawait, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Concrete.pure_bind]
          refine Sim.pre (fun _ h => h.2) ?_
          refine Sim.bind (checkAwaited_sim now rest fun a ha => h a (by simp [ha])) ?_
          intro awaited check hcheck
          rw [hcheck]
          by_cases hall : awaited.all (·.any (·.promise.otype.awaitable))
          · simp only [hall, ↓reduceIte]
            exact Sim.pure (by simp [AwaitedRel, hall, hawait, Bool.or_comm])
              (fun _ h => h)
          · simp only [hall, Bool.false_eq_true, ↓reduceIte]
            exact Sim.pure (by simp [AwaitedRel, hall, hawait]) (fun _ h => h)
        · simp only [hawait, Bool.not_false, ↓reduceIte]
          exact Sim.bind_left (Sim.readOnly (mapM_readObject_state now rest))
            fun _ _ => Sim.pure (by simp [AwaitedRel, hawait]) (fun _ h => h.2)

/-- Registering callbacks keeps every property that setting an awaited
promise keeps. -/
theorem registerAwaited_sim (awaiter : Ident) (now : Nat) {origin : String}
    (F : Document (.origin origin) → Prop) :
    ∀ actions : List PromiseRegisterCallbackReq,
      (∀ action ∈ actions, action.awaited.origin = origin) →
      (∀ action ∈ actions, ∀ env d p,
        F d → F (Concrete.Decision.setPromise action.awaited.suffix p env d).2.1) →
      Sim (.origin origin) F Eq (fun _ d => F d)
        (actions.forM (Abstract.addCallback awaiter now))
        (Concrete.Decision.registerAwaited (origin := origin) awaiter now actions)
  | [], _, _ => by
      simp only [List.forM_nil, Concrete.Decision.registerAwaited]
      exact Sim.pure rfl (fun _ h => h)
  | action :: rest, h, hF => by
      have ih := registerAwaited_sim awaiter now F rest (fun a ha => h a (by simp [ha]))
        (fun a ha => hF a (by simp [ha]))
      simp only [List.forM, Concrete.Decision.registerAwaited, Abstract.addCallback,
        Abstract.bind_assoc]
      refine Sim.bind (readObject_sim' _ _ (h action (by simp))) ?_
      refine ObjRel.cases ?_ (fun _ _ => ?_)
      · exact Sim.seq (Sim.pure (Q := fun _ d => F d) rfl (fun _ h => h.2)) ih
      · exact Sim.seq
          (Sim.frame F (fun env d hd => hF action (by simp) env d _ hd)
            (setPromise_sim _ (fun _ h => h) (by simp [Object.ofOrigin])))
          (Sim.pre (fun _ h => h.2) ih)

theorem taskSuspend_sim (req : TaskSuspendReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskSuspend req now)
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
      refine Sim.seq (registerAwaited_sim _ _ _ _ ?_ ?_) ?_
      · simp_all [Ident.sameOrigin]
      · intro action haction env d p hd
        have hne : req.id.suffix ≠ action.awaited.suffix := by
          intro hsuffix
          have horigin : action.awaited.origin = req.id.origin := by
            simp_all [Ident.sameOrigin]
          have hid : action.awaited ≠ req.id := by
            intro hid
            simp_all
          apply hid
          cases haw : action.awaited
          cases hreq : req.id
          simp_all
        exact ⟨fun row hrow => setPromise_frame p hne env d (hd.1 row hrow), hd.2⟩
      sim
  · simp only [hall, Bool.not_false, ↓reduceIte]
    sim

/-! ## Internal work -/

theorem processPromiseTimeout_sim (id : Ident) (now : Nat) :
    HandlerSim (.origin id.origin) (Abstract.processPromiseTimeout id now)
      (Concrete.Decision.processPromiseTimeout id now) := by
  unfold Abstract.processPromiseTimeout Concrete.Decision.processPromiseTimeout
  refine Sim.bind (readObject_getObject_sim id now) ?_
  rintro a (_ | row) rfl
  · exact Sim.pure rfl (fun _ _ => trivial)
  · exact setObject_sim (row.project now)

theorem resumeOne_sim (awaited awaiter : Ident) (now : Nat) {origin : String}
    (h : awaiter.origin = origin) :
    HandlerSim (.origin origin) (Abstract.resumeOne awaited awaiter now)
      (Concrete.Decision.resumeOne (origin := origin) awaited awaiter now) := by
  subst h
  unfold Abstract.resumeOne Concrete.Decision.resumeOne
  sim

/-- The concrete callback step checks that the awaiter shares the awaited
origin; the abstract step relies on every registered callback doing so. -/
theorem processCallback_sim (req : PromiseRegisterCallbackReq) (now : Nat)
    (h : req.awaiter.origin = req.awaited.origin) :
    HandlerSim (.origin req.awaited.origin) (Abstract.processCallback req now)
      (Concrete.Decision.processCallback req now) := by
  unfold Abstract.processCallback Concrete.Decision.processCallback
  simp only [Ident.sameOrigin, h, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, Concrete.pure_bind]
  sim

theorem processListener_sim (req : PromiseRegisterListenerReq) (now : Nat) :
    HandlerSim (.origin req.awaited.origin) (Abstract.processListener req now)
      (Concrete.Decision.processListener req now) := by
  unfold Abstract.processListener Concrete.Decision.processListener
  sim

theorem processLeaseTimeout_sim (id : Ident) (now : Nat) :
    HandlerSim (.origin id.origin) (Abstract.processLeaseTimeout id now)
      (Concrete.Decision.processLeaseTimeout id now) := by
  unfold Abstract.processLeaseTimeout Concrete.Decision.processLeaseTimeout
  sim

theorem processRetryTimeout_sim (id : Ident) (now : Nat) :
    HandlerSim (.origin id.origin) (Abstract.processRetryTimeout id now)
      (Concrete.Decision.processRetryTimeout id now) := by
  unfold Abstract.processRetryTimeout Concrete.Decision.processRetryTimeout
  sim

theorem createIfAbsent_sim (req : PromiseCreateReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.createIfAbsent req now)
      (Concrete.Decision.processOccurrence req now) := by
  unfold Abstract.createIfAbsent Concrete.Decision.processOccurrence
    Concrete.Decision.createIfAbsent Concrete.Decision.createIfAbsentAt
  sim

theorem getSchedule_sim_id (id : Ident) :
    Sim (.schedule id) (fun _ => True)
      (fun a c => a = c ∧ ∀ schedule, c = some schedule → schedule.id = id)
      (fun _ _ => True) (Abstract.getSchedule id) (Concrete.Decision.getSchedule (id := id)) := by
  intro env store document hunique hdoc _
  obtain rfl : store.read (.schedule id) = document := hdoc
  obtain ⟨h₁, _, h₂, h₃, h₄⟩ :=
    getSchedule_sim id (P := fun _ => True) env store _ hunique (DocEquiv.refl _ _) trivial
  refine ⟨⟨h₁, ?_⟩, trivial, h₂, h₃, h₄⟩
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
    Sim (.schedule id) (fun _ => True) OccurrenceRel (fun _ _ => True)
      (Abstract.processSchedule id now) (Concrete.Decision.processSchedule id now) := by
  unfold Abstract.processSchedule Concrete.Decision.processSchedule
  refine Sim.bind (getSchedule_sim_id id) ?_
  rintro a _ ⟨rfl, hid⟩
  cases a with
  | none => exact Sim.pure rfl (fun _ _ => trivial)
  | some schedule =>
    have hschedule : schedule.id = id := hid _ rfl
    dsimp only
    rcases (List.filter (fun x => decide (x ≤ now))
      (occurrences schedule.cron schedule.nextRunAt now)).getLast? with _ | last
    · exact Sim.seq (Q := fun _ _ => True) (Sim.pure rfl (fun _ _ => trivial))
        (Sim.pure (by simp [OccurrenceRel, hschedule]) (fun _ _ => trivial))
    · exact Sim.seq (setSchedule_sim _ _ (by exact hschedule))
        (Sim.pure (by simp [OccurrenceRel, hschedule]) (fun _ _ => trivial))

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
    (hsim : HandlerSim key ma action) (hunique : state.store.Unique)
    (hdoc : DocEquiv key (state.store.read key) before) :
    let candidate := Concrete.externalCandidate appConfig call before action wrap
    let lifted := Abstract.run appConfig call state
    Same lifted.1.store (state.store.write key candidate.document) ∧
      lifted.1.store.Unique ∧
      lifted.1.workflow = state.workflow ∧
      lifted.2 = candidate.outputs := by
  obtain ⟨hresult, -, hsame, hemit, hunique'⟩ :=
    hsim { config := appConfig.toServerConfig } state.store before hunique hdoc trivial
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
    (hsim : HandlerSim key ma action) :
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
    (hsim : HandlerSim key ma action) (hunique : state.store.Unique)
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
  obtain ⟨_, -, hsame, hemit, hunique'⟩ :=
    hsim { config := appConfig.toServerConfig } state.store before hunique hdoc trivial
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
    obtain ⟨hresult, -, hsame, hemit, hunique'⟩ :=
      processSchedule_sim id now { config := appConfig.toServerConfig } state.store before
        hunique hdoc trivial
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

/-- Work the concrete sweep finds in a row is a step of the abstract object. -/
theorem originObjectWork_mem {origin : String} (row : OriginObject origin) (now : Nat)
    {item : WorkItem} (h : item ∈ Concrete.Decision.originObjectWork row now) :
    item ∈ Abstract.objectWork (Object.ofOrigin row) := by
  simp only [Concrete.Decision.originObjectWork, Concrete.Decision.originSettledWork,
    Concrete.Decision.originTaskWork, List.mem_append] at h
  simp only [Abstract.objectWork, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false]
  rcases h with (h | h) | h
  · split at h
    · simp only [List.mem_singleton] at h
      exact .inl (.inl (.inl h))
    · cases h
  · split at h
    · cases h
    · simp only [List.mem_append, List.mem_map] at h
      rcases h with h | h
      · exact .inl (.inr h)
      · exact .inr h
  · split at h
    · cases h
    · simp only [List.mem_append] at h
      rcases h with h | h
      · split at h
        · split at h
          · simp only [List.mem_singleton] at h
            exact .inl (.inl (.inr (.inl h)))
          · cases h
        · cases h
      · split at h
        · split at h
          · simp only [List.mem_singleton] at h
            exact .inl (.inl (.inr (.inr h)))
          · cases h
        · cases h

theorem objectWork_ofOrigin {origin : String} {a b : OriginObject origin}
    (hsuffix : a.suffix = b.suffix) (hpromise : a.promise = b.promise) :
    Abstract.objectWork (Object.ofOrigin a) = Abstract.objectWork (Object.ofOrigin b) := by
  obtain ⟨_, _, _⟩ := a
  obtain ⟨_, _, _⟩ := b
  simp only at hsuffix hpromise
  subst hsuffix hpromise
  rfl

/-- Work the concrete sweep finds in an origin document is a step of an
object of the abstract store. -/
theorem originWork_mem (store : Store) (origin : String) (now : Nat)
    {document : OriginDocument origin}
    (hdoc : DocEquiv (.origin origin) (store.read (.origin origin)) document)
    {item : WorkItem}
    (h : item ∈ Concrete.Decision.originWork origin document now) :
    item ∈ store.objects.flatMap Abstract.objectWork := by
  simp only [Concrete.Decision.originWork, List.mem_flatMap] at h
  obtain ⟨row, hrow, hitem⟩ := h
  have hnorm : row.norm ∈ (store.read (.origin origin)).map (·.norm) :=
    (List.Perm.mem_iff hdoc).mpr (List.mem_map_of_mem hrow)
  obtain ⟨stored, hstored, hsame⟩ := List.mem_map.mp hnorm
  simp only [read_origin, List.mem_filterMap] at hstored
  obtain ⟨object, hobject, hstored⟩ := hstored
  rw [List.mem_flatMap]
  refine ⟨object, hobject, ?_⟩
  rw [← Object.ofOrigin_toOriginRow hstored,
    objectWork_ofOrigin (a := stored) (b := row)
      (congrArg OriginObject.suffix hsame :)
      (congrArg OriginObject.promise hsame :)]
  exact originObjectWork_mem row now hitem

theorem scheduleAt_go_mem (id : Ident) :
    ∀ (schedules : List Schedule) (data : ScheduleData id),
      Store.scheduleAt.go id schedules = some data →
      WorkItem.scheduleTimeout id ∈
        schedules.map (fun schedule => WorkItem.scheduleTimeout schedule.id)
  | [], _, h => by simp [Store.scheduleAt.go] at h
  | schedule :: rest, data, h => by
    simp only [Store.scheduleAt.go] at h
    split at h
    · rename_i hid
      simp [hid]
    · simp only [List.map_cons, List.mem_cons]
      exact .inr (scheduleAt_go_mem id rest data h)

/-- A stored schedule is a step of the abstract store. -/
theorem scheduleWork_mem (store : Store) (id : Ident) {data : ScheduleData id}
    (h : store.read (.schedule id) = some data) :
    WorkItem.scheduleTimeout id ∈
      store.schedules.map (fun schedule => WorkItem.scheduleTimeout schedule.id) :=
  scheduleAt_go_mem id store.schedules data h

theorem runTimeout_mem_due (appConfig : Resonate.Config) (state : State) {now instant : Nat}
    {item : WorkItem} (hinstant : instant ≤ now)
    (h : item ∈ state.store.objects.flatMap Abstract.objectWork ++
      state.store.schedules.map (fun schedule => WorkItem.scheduleTimeout schedule.id)) :
    Abstract.runWork appConfig item instant state.workflow.pending state ∈
      (Abstract.runTimeout appConfig now state).val := by
  simp only [Abstract.runTimeout, Abstract.timeoutWork, List.mem_cons, List.mem_map,
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
  · simp only [Abstract.runTimeout, Abstract.timeoutWork, List.mem_cons, List.mem_map,
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
