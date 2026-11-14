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

Both sides write whole objects as read, so a write needs nothing of the
document it replaces.
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
  | .origin _, _ => List.Perm.refl _
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

/-! ## What a read shows -/

theorem task_project_of_pending {t : TaskObject} {p : PromiseObject} (h : p.state = .pending) :
    t.project p = t := by
  simp [AbstractModel.TaskObject.project, h]

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
abbrev RowsUnique {origin : String} (document : WorkflowDocument origin) : Prop :=
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

theorem find?_suffix_iff {origin : String} {document : WorkflowDocument origin}
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
theorem find?_perm {origin : String} {a b : WorkflowDocument origin}
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
    ∀ {document : WorkflowDocument origin}, RowsUnique document →
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

theorem map_norm_suffix {origin : String} (document : WorkflowDocument origin) :
    (document.map (·.norm)).map (·.suffix) = document.map (·.suffix) := by
  rw [List.map_map]
  rfl

theorem origin_rows_suffixes (objects : List Object) (origin : String) :
    ((objects.filterMap (Object.toOriginRow? origin)).map OriginObject.suffix) =
      (objects.filter (·.id.origin == origin)).map (·.id.suffix) := by
  induction objects with
  | nil => rfl
  | cons object objects ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      by_cases h : object.id.origin = origin
      · simp [Object.toOriginRow?, h, ih]
      · simp [Object.toOriginRow?, h, ih]

theorem sortStrings_eq_of_perm {left right : List String}
    (h : left.Perm right) :
    sortStrings left = sortStrings right := by
  apply List.Perm.eq_of_pairwise (le := fun a b : String => a ≤ b)
  · intro a b _ _ hab hba
    exact String.le_antisymm hab hba
  · simpa only [sortStrings, decide_eq_true_eq] using
      (List.pairwise_mergeSort
        (le := fun a b : String => decide (a ≤ b))
        (fun _ _ _ hab hbc => by
          simp only [decide_eq_true_eq] at hab hbc ⊢
          exact String.le_trans hab hbc)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact String.le_total a b)
        left)
  · simpa only [sortStrings, decide_eq_true_eq] using
      (List.pairwise_mergeSort
        (le := fun a b : String => decide (a ≤ b))
        (fun _ _ _ hab hbc => by
          simp only [decide_eq_true_eq] at hab hbc ⊢
          exact String.le_trans hab hbc)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact String.le_total a b)
        right)
  · exact (List.mergeSort_perm _ _).trans
      (h.trans (List.mergeSort_perm _ _).symm)

theorem find?_map_norm {origin : String} (document : WorkflowDocument origin) (s : String) :
    (document.map (·.norm)).find? (·.suffix == s) =
      (document.find? (·.suffix == s)).map (·.norm) := by
  rw [List.find?_map]
  rfl

/-- Documents that read alike give rows that read alike for each suffix. -/
theorem find?_equiv {origin : String} {a b : WorkflowDocument origin}
    (ha : RowsUnique a) (h : DocEquiv (.origin origin) a b) (s : String) :
    (a.find? (·.suffix == s)).map (·.norm) = (b.find? (·.suffix == s)).map (·.norm) := by
  rw [← find?_map_norm, ← find?_map_norm]
  refine find?_perm ?_ h s
  show ((a.map _).map _).Nodup
  rw [map_norm_suffix]
  exact ha

theorem map_norm_filter {origin : String} (document : WorkflowDocument origin) (s : String) :
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

theorem find?_suffix {origin suffix : String} {document : WorkflowDocument origin}
    {row : OriginObject origin}
    (h : document.find? (·.suffix == suffix) = some row) : row.suffix = suffix := by
  simpa using List.find?_some h

/-- What the abstract store shows at `id` is what the concrete document
shows at its suffix. -/
theorem readObject_eq_document {store : Store} {id : Ident}
    {document : WorkflowDocument id.origin} (hunique : store.Unique)
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

theorem readObject_sim (id : Ident) (now : Nat) {P : Document (.origin id.origin) → Prop} :
    Sim (.origin id.origin) P (ObjRel id.origin id.suffix)
      (fun _ d => P d)
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
  refine ⟨⟨?_, ?_⟩, hp, Same.write_of hdoc, rfl, hunique⟩
  · cases document.find? (·.suffix == id.suffix) <;> rfl
  · intro row h
    cases hfind : document.find? (·.suffix == id.suffix) with
    | none => simp [hfind] at h
    | some found =>
        simp only [hfind, Option.map_some, Option.some.injEq] at h
        subst h
        exact (find?_suffix hfind : found.suffix = id.suffix)

/-- An abstract task read corresponds to the concrete one. -/
def TaskRel (origin suffix : String) (a : Option (Object × TaskObject))
    (c : Option (OriginObject origin × TaskObject)) : Prop :=
  a = c.map (fun found => (Object.ofOrigin found.1, found.2)) ∧
    ∀ row task, c = some (row, task) → row.suffix = suffix ∧ row.task = some task

theorem readTask_sim (id : Ident) (now : Nat) {P : Document (.origin id.origin) → Prop} :
    Sim (.origin id.origin) P (TaskRel id.origin id.suffix)
      (fun _ d => P d)
      (Abstract.readTask id now) (Concrete.Decision.readTask id.suffix now) := by
  intro env store document hunique hdoc hp
  have ha : Abstract.readTask id now env store =
      ((((store.getObject id).map (·.project now)).bind fun o => o.task.map (o, ·)),
        store, []) := by
    simp only [Abstract.readTask, Abstract.readObject, Abstract.getObject, bind, pure]
    cases store.getObject id <;> rfl
  have hc : Concrete.Decision.readTask id.suffix now env document =
      ((((document.find? (·.suffix == id.suffix)).map (·.project now)).bind
        fun o => o.task.map (o, ·)), document, []) := by
    simp only [Concrete.Decision.readTask, Concrete.Decision.readObject,
      Concrete.Decision.getObject, documentGet, bind, pure]
    cases document.find? (·.suffix == id.suffix) <;> rfl
  rw [ha, hc, readObject_eq_document hunique hdoc]
  refine ⟨⟨?_, ?_⟩, hp, Same.write_of hdoc, rfl, hunique⟩
  · cases document.find? (·.suffix == id.suffix) with
    | none => rfl
    | some row => cases h : (row.project now).task <;> simp [h, Object.ofOrigin]
  · intro row task h
    cases hfind : document.find? (·.suffix == id.suffix) with
    | none => simp [hfind] at h
    | some found =>
        cases ht : (found.project now).task with
        | none => simp [hfind, ht] at h
        | some t =>
            simp only [hfind, ht, Option.map_some, Option.bind_some, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨by simpa [OriginObject.project] using find?_suffix hfind, ht⟩

/-! ## Writes -/

theorem same_write_origin {a store : Store} {origin : String}
    {document : WorkflowDocument origin}
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
          simp [hid, hrow, ih]
        · have hid : ¬ object.id = id := fun h => hsuffix (by rw [h])
          simp [hid, hrow, ih, hsuffix]
      · have hid : ¬ object.id = id := fun h => horigin (by rw [h])
        simp [hid, toOriginRow?_eq_none horigin, ih]

theorem filterMap_filter_id_other (objects : List Object) (id : Ident)
    {other : String} (h : other ≠ id.origin) :
    (objects.filter (·.id != id)).filterMap (Object.toOriginRow? other) =
      objects.filterMap (Object.toOriginRow? other) := by
  induction objects with
  | nil => rfl
  | cons object rest ih =>
      by_cases hid : object.id = id
      · have horigin : object.id.origin ≠ other := by rw [hid]; exact Ne.symm h
        simp [hid, toOriginRow?_eq_none horigin, ih]
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
    {document : WorkflowDocument object.id.origin}
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

theorem setObject_sim {origin : String} (row : OriginObject origin) {object : Object}
    (h : Object.ofOrigin row = object) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P Eq (fun _ _ => True) (Abstract.setObject object)
      (Concrete.Decision.setObject row) := by
  subst h
  intro env store document hunique hdoc _
  refine ⟨rfl, trivial, ?_, rfl, hunique.setObject _⟩
  exact setObject_equiv (Object.ofOrigin row) hdoc (by rfl)

/-- A settled promise reads as it is, and its task as finished. -/
theorem Object.project_settled (o : Object) {p : PromiseObject} (now : Nat)
    (h : p.state ≠ .pending) :
    ({ o with promise := p }.project now) =
      { o with promise := p, task := o.task.map (·.project p) } := by
  simp [Object.project, h, AbstractModel.TaskObject.project]

theorem ask_sim_early {key : DocumentKey} {P : Document key → Prop} :
    Sim key P Eq (fun _ d => P d) Abstract.ask
      (Concrete.Decision.ask (key := key)) := by
  intro env store document hunique hdoc hp
  exact ⟨rfl, hp, Same.write_of hdoc, rfl, hunique⟩

theorem setMessage_sim_early {key : DocumentKey} (address : String)
    (message : ServerModel.Message) {P : Document key → Prop} :
    Sim key P Eq (fun _ d => P d) (Abstract.setMessage address message)
      (Concrete.Decision.setMessage (key := key) address message) := by
  intro env store document hunique hdoc hp
  exact ⟨rfl, hp, Same.write_of hdoc, rfl, hunique⟩

theorem dispatchTask_sim {origin : String} (row : OriginObject origin)
    (task : TaskObject) (now : Nat) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P Eq (fun _ _ => True)
      (Abstract.dispatchTask (Object.ofOrigin row) task now)
      (Concrete.Decision.dispatchTask row task now) := by
  unfold Abstract.dispatchTask Concrete.Decision.dispatchTask
  refine Sim.bind ask_sim_early ?_
  intro abstractEnv concreteEnv henv
  subst henv
  let next := { task with
    retryTimeoutAt := some (now + abstractEnv.config.retryTimeout) }
  refine Sim.seq (setObject_sim ({ row with task := some next }) rfl) ?_
  exact Sim.post (fun _ _ _ => trivial)
    (setMessage_sim_early
      ((row.promise.tags.get? "resonate:target").getD "")
      (.execute row.id task.version))

theorem dispatchIfDue_sim {origin : String} (row : OriginObject origin)
    (now : Nat) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P Eq (fun _ _ => True)
      (Abstract.dispatchIfDue (Object.ofOrigin row) now)
      (Concrete.Decision.dispatchIfDue row now) := by
  obtain ⟨suffix, promise, task?⟩ := row
  unfold Abstract.dispatchIfDue Concrete.Decision.dispatchIfDue
  cases task? with
  | none =>
      simp [Object.ofOrigin]
      exact Sim.pure (P := P) (R := Eq) (Q := fun _ _ => True)
        rfl (fun _ _ => trivial)
  | some task =>
      simp only [Object.ofOrigin]
      refine Sim.ite _
        (fun _ => dispatchTask_sim
          (⟨suffix, promise, some task⟩ : OriginObject origin) task now)
        (fun _ => Sim.pure (P := P) (R := Eq)
          (Q := fun _ _ => True) rfl (fun _ _ => trivial))

theorem readTask_sim_early' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (TaskRel origin id.suffix)
      (fun _ d => P d) (Abstract.readTask id now)
      (Concrete.Decision.readTask (origin := origin) id.suffix now) := by
  subst h
  exact readTask_sim id now

theorem TaskRel_cases_early {origin suffix : String}
    {P : Option (Object × TaskObject) →
      Option (OriginObject origin × TaskObject) → Prop}
    (hnone : P none none)
    (hsome : ∀ promise task,
      P (some (Object.ofOrigin
          (⟨suffix, promise, some task⟩ : OriginObject origin), task))
        (some (⟨suffix, promise, some task⟩, task))) :
    ∀ a c, TaskRel origin suffix a c → P a c := by
  rintro a (_ | ⟨⟨rowSuffix, promise, current⟩, task⟩) ⟨rfl, h⟩
  · exact hnone
  · obtain ⟨hs, ht⟩ := h _ _ rfl
    simp only at hs ht
    subst hs ht
    exact hsome promise task

theorem resumeOne_sim_early (awaited awaiter : Ident) (now : Nat)
    {origin : String} (h : awaited.origin = origin) :
    Sim (.origin origin) (fun _ => True) Eq (fun _ _ => True)
      (Abstract.resumeOne awaited awaiter now)
      (h ▸ Concrete.Decision.resumeOne awaited awaiter now) := by
  obtain ⟨awaitedOrigin, awaitedSuffix⟩ := awaited
  obtain ⟨awaiterOrigin, awaiterSuffix⟩ := awaiter
  simp only at h
  subst origin
  unfold Abstract.resumeOne Concrete.Decision.resumeOne
  by_cases hlocal : awaitedOrigin = awaiterOrigin
  · subst awaiterOrigin
    simp only [Ident.sameOrigin, beq_self_eq_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    refine Sim.bind
      (Sim.pure (P := fun _ => True) (R := Eq)
        (Q := fun _ _ => True) rfl (fun _ _ => trivial)) ?_
    intro _ _ hunit
    subst hunit
    let awaiter : Ident := { origin := awaitedOrigin, suffix := awaiterSuffix }
    refine Sim.bind
      (readTask_sim awaiter now (P := fun _ => True)) ?_
    refine TaskRel_cases_early (Sim.pure rfl (fun _ _ => trivial)) ?_
    intro promise task
    cases hstate : task.state with
    | suspended =>
        simpa [hstate, awaiter] using
          (dispatchTask_sim
            (⟨awaiterSuffix, promise, some task⟩ :
              OriginObject awaitedOrigin)
            { task with
              state := .pending
              pid := none
              ttl := none
              leaseTimeoutAt := none
              resumes := [{ origin := awaitedOrigin, suffix := awaitedSuffix }] }
            now)
    | fulfilled =>
        simp [hstate]
        exact Sim.pure rfl (fun _ _ => trivial)
    | pending | acquired | halted =>
        simp only [hstate]
        refine Sim.ite _
          (fun _ => by
            simpa [hstate, awaiter, Object.ofOrigin] using
              (setObject_sim
                ({ suffix := awaiterSuffix
                   promise
                   task := some { task with
                     resumes := task.resumes ++
                       [{ origin := awaitedOrigin, suffix := awaitedSuffix }] } } :
                  OriginObject awaitedOrigin)
                rfl))
          (fun _ => Sim.pure rfl (fun _ _ => trivial))
  · have hbeq : (awaitedOrigin == awaiterOrigin) = false := by
      simpa [beq_iff_eq] using hlocal
    simp [Ident.sameOrigin, hbeq]
    exact Sim.pure rfl (fun _ _ => trivial)

theorem resumeAll_sim {origin : String} (awaited : Ident) (now : Nat)
    (h : awaited.origin = origin) :
    ∀ callbacks : List Ident,
      Sim (.origin origin) (fun _ => True) Eq (fun _ _ => True)
        (Abstract.resumeAll awaited now callbacks)
        (h ▸ Concrete.Decision.resumeAll awaited now callbacks) := by
  subst h
  intro callbacks
  induction callbacks with
  | nil => exact Sim.pure rfl (fun _ _ => trivial)
  | cons awaiter rest ih =>
      exact Sim.seq
        (resumeOne_sim_early awaited awaiter now rfl) ih

theorem notifyAll_sim {origin : String} (promise : PromiseObject) (id : Ident) :
    ∀ listeners : List String,
      Sim (.origin origin) (fun _ => True) Eq (fun _ _ => True)
        (Abstract.notifyAll promise id listeners)
        (Concrete.Decision.notifyAll (origin := origin) promise id listeners)
  | [] => Sim.pure rfl (fun _ _ => trivial)
  | address :: rest =>
      Sim.seq
        (Sim.post (fun _ _ _ => trivial)
          (setMessage_sim_early address (.unblock (promise.toRecord id))))
        (notifyAll_sim promise id rest)

/-- Settling the read object writes it with the promise settled and its task
finished, drains its local callbacks, and emits every listener notification. -/
theorem setSettled_sim {origin : String} (row : OriginObject origin) {object : Object}
    (h : Object.ofOrigin row = object) {p : PromiseObject} {now : Nat}
    (hsettled : p.state ≠ .pending) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P Eq (fun _ _ => True) (Abstract.setSettled object p now)
      (Concrete.Decision.setSettled row p now) := by
  subst h
  let settled : PromiseObject := { p with callbacks := [], listeners := [] }
  unfold Abstract.setSettled Concrete.Decision.setSettled
  change Sim (.origin origin) P Eq (fun _ _ => True)
    (do
      Abstract.setObject ({ Object.ofOrigin row with promise := settled }.project now)
      Abstract.resumeAll row.id now p.callbacks
      Abstract.notifyAll settled row.id p.listeners)
    (do
      Concrete.Decision.setObject
        { row with
          promise := settled
          task := row.task.map (·.project settled) }
      Concrete.Decision.resumeAll row.id now p.callbacks
      Concrete.Decision.notifyAll settled row.id p.listeners)
  rw [Object.project_settled _ _ (by simpa [settled] using hsettled)]
  simp only [Object.ofOrigin]
  refine Sim.seq
    (setObject_sim
      ({ row with
        promise := settled
        task := row.task.map (·.project settled) })
      rfl) ?_
  refine Sim.seq (Sim.weaken (resumeAll_sim row.id now rfl p.callbacks)) ?_
  exact Sim.weaken (notifyAll_sim settled row.id p.listeners)

theorem Concrete.bind_assoc {key : DocumentKey} (x : DocumentHandler key α)
    (f : α → DocumentHandler key β) (g : β → DocumentHandler key γ) :
    (x >>= f) >>= g = x >>= fun a => f a >>= g := by
  funext env document
  simp only [bind, List.append_assoc]

theorem Concrete.pure_bind {key : DocumentKey} (u : α) (f : α → DocumentHandler key β) :
    (Pure.pure u : DocumentHandler key α) >>= f = f u := by
  funext env document
  simp only [bind, Pure.pure, List.nil_append]

theorem ofOrigin_newObject (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) :
    Object.ofOrigin (Concrete.Decision.newObject (origin := id.origin) id.suffix timeoutAt now
      param tags) = Abstract.newObject id timeoutAt now param tags := by
  unfold Abstract.newObject Concrete.Decision.newObject
  by_cases htime : timeoutAt > now <;> by_cases hrun : tags.otype = .runnable <;>
    simp [htime, hrun, Object.ofOrigin, AbstractModel.PromiseObject.otype] <;>
    cases tags.get? "resonate:delay" <;> rfl

theorem createPromiseAt_sim (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) {P : Document (.origin id.origin) → Prop} :
    Sim (.origin id.origin) P (fun a c => a = Object.ofOrigin c) (fun _ _ => True)
      (Abstract.createPromiseAt id timeoutAt now param tags)
      (Concrete.Decision.createPromiseAt id.suffix timeoutAt now param tags) := by
  have h := ofOrigin_newObject id timeoutAt now param tags
  unfold Abstract.createPromiseAt Concrete.Decision.createPromiseAt
  exact Sim.bind (setObject_sim _ h) fun _ _ _ => Sim.pure h.symm (fun _ _ => trivial)

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
      (Concrete.Decision.setSchedule (id := id) schedule) := by
  subst h
  intro env store document hunique _ _
  refine ⟨rfl, trivial, ?_, rfl, hunique.schedules rfl⟩
  simp only [Abstract.setSchedule, Concrete.Decision.setSchedule, Concrete.Decision.set,
    documentSet]
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

theorem readObject_sim' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (ObjRel origin id.suffix)
      (fun _ d => P d) (Abstract.readObject id now)
      (Concrete.Decision.readObject (origin := origin) id.suffix now) := by
  subst h; exact readObject_sim id now

theorem readTask_sim' (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (TaskRel origin id.suffix)
      (fun _ d => P d) (Abstract.readTask id now)
      (Concrete.Decision.readTask (origin := origin) id.suffix now) := by
  subst h; exact readTask_sim id now

theorem createPromiseAt_sim' (id : Ident) (timeoutAt now : Nat) (param : Value)
    (tags : Tags) {origin : String} (h : id.origin = origin)
    {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (fun a c => a = Object.ofOrigin c) (fun _ _ => True)
      (Abstract.createPromiseAt id timeoutAt now param tags)
      (Concrete.Decision.createPromiseAt (origin := origin) id.suffix timeoutAt now
        param tags) := by
  subst h; exact createPromiseAt_sim id timeoutAt now param tags

theorem readOrCreate_sim (req : PromiseCreateReq) (now : Nat) {origin : String}
    (h : req.id.origin = origin) {P : Document (.origin origin) → Prop} :
    Sim (.origin origin) P (fun a c => a = Object.ofOrigin c) (fun _ _ => True)
      (Abstract.readOrCreate req now)
      (Concrete.Decision.readOrCreate (origin := origin) req now) := by
  unfold Abstract.readOrCreate Concrete.Decision.readOrCreate
  refine Sim.bind (readObject_sim' _ _ h) ?_
  refine ObjRel.cases ?_ (fun _ _ => ?_)
  · exact createPromiseAt_sim' _ _ _ _ _ h
  · exact Sim.pure rfl (fun _ _ => trivial)

theorem TaskRel.cases {origin suffix : String} {P : Option (Object × TaskObject) →
      Option (OriginObject origin × TaskObject) → Prop}
    (hnone : P none none)
    (hsome : ∀ promise task,
      P (some (Object.ofOrigin (⟨suffix, promise, some task⟩ : OriginObject origin), task))
        (some (⟨suffix, promise, some task⟩, task))) :
    ∀ a c, TaskRel origin suffix a c → P a c := by
  rintro a (_ | ⟨⟨rowSuffix, promise, current⟩, task⟩) ⟨rfl, h⟩
  · exact hnone
  · obtain ⟨hs, ht⟩ := h _ _ rfl
    simp only at hs ht
    subst hs ht
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

instance {key : DocumentKey} : LawfulMonad (DocumentHandler key) := LawfulMonad.mk'
  (id_map := fun x => by
    funext env document
    show (let (v, s, e) := x env document; (v, s, e ++ [])) = x env document
    simp)
  (pure_bind := fun a f => Concrete.pure_bind a f)
  (bind_assoc := fun x f g => Concrete.bind_assoc x f g)

/-- Close the side condition that an id lies in the document's origin. -/
macro "sim_origin" : tactic => `(tactic| first
  | rfl
  | (simp_all [Ident.sameOrigin, TaskFenceAction.targetId]; done))

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
                       refine TaskRel.cases ?_ (fun _ _ => ?_)))
    | some ``Resonate.Abstract.getSchedule =>
        run `(tactic| (refine Sim.bind (getSchedule_sim _) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.createPromiseAt =>
        run `(tactic| (refine Sim.bind (createPromiseAt_sim' _ _ _ _ _ (by sim_origin)) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.readOrCreate =>
        run `(tactic| (refine Sim.bind (readOrCreate_sim _ _ (by sim_origin)) ?_
                       intro _ _ h; subst h))
    | some ``Resonate.Abstract.setObject =>
        run `(tactic| refine Sim.bind (setObject_sim _ (by rfl)) fun _ _ _ => ?_)
    | some ``Resonate.Abstract.setSettled =>
        run `(tactic|
          (refine Sim.bind (setSettled_sim _ (by rfl) ?_) fun _ _ _ => ?_
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
        run `(tactic| exact setObject_sim _ (by rfl))
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
      (Concrete.Decision.promiseCreate (origin := origin) req now) := by
  subst h
  unfold Abstract.promiseCreate Concrete.Decision.promiseCreate
  sim

theorem promiseSettle_sim (req : PromiseSettleReq) (now : Nat) {origin : String}
    (h : req.id.origin = origin) :
    HandlerSim (.origin origin) (Abstract.promiseSettle req now)
      (Concrete.Decision.promiseSettle (origin := origin) req now) := by
  subst h
  unfold Abstract.promiseSettle Concrete.Decision.promiseSettle
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

/-! ## Lists of steps -/

theorem forM_sim {key : DocumentKey} {fa : γ → Abstract.Handler Unit}
    {fc : γ → DocumentHandler key Unit} :
    ∀ l : List γ, (∀ x ∈ l, HandlerSim key (fa x) (fc x)) →
      HandlerSim key (l.forM fa) (l.forM fc)
  | [], _ => Sim.pure rfl (fun _ _ => trivial)
  | x :: rest, h =>
      Sim.seq (h x (by simp)) (forM_sim rest fun y hy => h y (by simp [hy]))

theorem mapM_sim {key : DocumentKey} {f : β → α} {fa : γ → Abstract.Handler α}
    {fc : γ → DocumentHandler key β} :
    ∀ l : List γ,
      (∀ x ∈ l, Sim key (fun _ => True) (fun a c => a = f c) (fun _ _ => True)
        (fa x) (fc x)) →
      Sim key (fun _ => True) (fun as cs => as = cs.map f) (fun _ _ => True)
        (l.mapM fa) (l.mapM fc)
  | [], _ => Sim.pure rfl (fun _ _ => trivial)
  | x :: rest, h => by
      simp only [List.mapM_cons]
      refine Sim.bind (h x (by simp)) fun a c hac => ?_
      refine Sim.bind (mapM_sim rest fun y hy => h y (by simp [hy])) fun as cs has => ?_
      exact Sim.pure (by simp [hac, has]) (fun _ _ => trivial)

theorem readObject_map_sim (id : Ident) (now : Nat) {origin : String}
    (h : id.origin = origin) :
    Sim (.origin origin) (fun _ => True) (fun a c => a = c.map Object.ofOrigin)
      (fun _ _ => True) (Abstract.readObject id now)
      (Concrete.Decision.readObject (origin := origin) id.suffix now) := by
  intro env store document hunique hdoc hp
  obtain ⟨⟨hr, _⟩, _, hrest⟩ := readObject_sim' id now h (P := fun _ => True) env store document hunique hdoc hp
  exact ⟨hr, trivial, hrest⟩

/-! ## Heartbeat -/

theorem heartbeatOne_sim (pid : String) (ref : TaskRef) (now : Nat) {origin : String}
    (h : ref.id.origin = origin) :
    HandlerSim (.origin origin) (Abstract.heartbeatOne pid ref now)
      (Concrete.Decision.heartbeatOne (origin := origin) pid ref now) := by
  subst h
  unfold Abstract.heartbeatOne Concrete.Decision.heartbeatOne
  sim

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
  have hall' : ∀ ref ∈ first :: rest, ref.id.origin = first.id.origin := by
    simpa [bne_iff_ne] using hall
  exact Sim.seq (Q := fun _ _ => True) (Sim.pure rfl (fun _ _ => trivial))
    (Sim.seq (forM_sim _ fun ref href => heartbeatOne_sim _ _ _ (hall' ref href))
      (Sim.pure rfl (fun _ _ => trivial)))

/-! ## Suspend -/

theorem addCallback_sim (awaiter : Ident) (now : Nat) (action : PromiseRegisterCallbackReq)
    {origin : String} (h : action.awaited.origin = origin) :
    HandlerSim (.origin origin) (Abstract.addCallback awaiter now action)
      (Concrete.Decision.addCallback (origin := origin) awaiter now action) := by
  subst h
  unfold Abstract.addCallback Concrete.Decision.addCallback
  sim

theorem taskSuspend_sim (req : TaskSuspendReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.taskSuspend req now)
      (Concrete.Decision.taskSuspend req now) := by
  unfold Abstract.taskSuspend Concrete.Decision.taskSuspend
  sim
  refine Sim.bind (Sim.weaken (mapM_sim (f := Option.map Object.ofOrigin) _
    fun action haction => readObject_map_sim _ _ ?_)) ?_
  · simp_all [Ident.sameOrigin]
  intro _ awaited h
  subst h
  simp only [List.all_map, List.any_map, Function.comp_def, Option.any_map]
  dsimp only [Object.ofOrigin]
  sim
  refine Sim.seq (Sim.weaken (forM_sim _ fun action haction => addCallback_sim _ _ _ ?_)) ?_
  · simp_all [Ident.sameOrigin]
  sim

/-! ## Internal work -/

theorem processPromiseTimeout_sim (id : Ident) (now : Nat) :
    HandlerSim (.origin id.origin) (Abstract.processPromiseTimeout id now)
      (Concrete.Decision.processPromiseTimeout id now) := by
  unfold Abstract.processPromiseTimeout Concrete.Decision.processPromiseTimeout
  sim

theorem resumeOne_sim (awaited awaiter : Ident) (now : Nat) :
    HandlerSim (.origin awaited.origin) (Abstract.resumeOne awaited awaiter now)
      (Concrete.Decision.resumeOne awaited awaiter now) := by
  apply resumeOne_sim_early awaited awaiter now rfl

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

theorem sweepObject_sim (id : Ident) (now : Nat) :
    HandlerSim (.origin id.origin) (Abstract.sweepObject id now)
      (Concrete.Decision.sweepObject id now) := by
  unfold Abstract.sweepObject Concrete.Decision.sweepObject
  exact Sim.seq (processPromiseTimeout_sim id now)
    (Sim.seq (processLeaseTimeout_sim id now) (processRetryTimeout_sim id now))

theorem getStore_suffixes_sim (origin : String) :
    Sim (.origin origin) (fun _ => True)
      (fun store document =>
        Abstract.originSuffixes store origin =
          sortStrings (document.map (·.suffix)))
      (fun _ _ => True) Abstract.getStore Concrete.Decision.get := by
  intro env store document hunique hdoc _
  have hp := hdoc.map (fun row => row.suffix)
  rw [map_norm_suffix, map_norm_suffix] at hp
  have hsuffixes :
      Abstract.originSuffixes store origin =
        sortStrings (document.map (·.suffix)) := by
    unfold Abstract.originSuffixes
    rw [← origin_rows_suffixes, ← read_origin]
    exact sortStrings_eq_of_perm hp
  exact ⟨hsuffixes, trivial, Same.write_of hdoc, rfl, hunique⟩

theorem sweepOrigin_sim (origin : String) (now : Nat) :
    HandlerSim (.origin origin) (Abstract.sweepOrigin origin now)
      (Concrete.Decision.sweepOrigin origin now) := by
  unfold Abstract.sweepOrigin Concrete.Decision.sweepOrigin
  refine Sim.bind (getStore_suffixes_sim origin) ?_
  intro store document hsuffixes
  rw [hsuffixes]
  exact forM_sim _ fun suffix _ =>
    sweepObject_sim { origin, suffix } now

theorem createIfAbsent_sim (req : PromiseCreateReq) (now : Nat) :
    HandlerSim (.origin req.id.origin) (Abstract.createIfAbsent req now)
      (Concrete.Decision.processOccurrence req now) := by
  unfold Abstract.createIfAbsent Concrete.Decision.processOccurrence
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

def Abstract.completeForKey (key : DocumentKey) (now : Nat)
    (action : Abstract.Handler α) : Abstract.Handler α :=
  match key with
  | .origin origin => Abstract.completeOrigin origin now action
  | .schedule _ => action

theorem completeDecision_sim (key : DocumentKey) (now : Nat)
    {ma : Abstract.Handler α} {action : Concrete.Decision.Handler key α}
    (hsim : HandlerSim key ma action) :
    HandlerSim key (Abstract.completeForKey key now ma)
      (Concrete.completeDecision key now action) := by
  cases key with
  | origin origin =>
      unfold Abstract.completeForKey Abstract.completeOrigin Concrete.completeDecision
      exact Sim.seq (sweepOrigin_sim origin now)
        (Sim.bind hsim fun a c h =>
          Sim.seq (sweepOrigin_sim origin now)
            (Sim.pure h (fun _ _ => trivial)))
  | schedule id =>
      simpa [Abstract.completeForKey, Concrete.completeDecision] using hsim

theorem Abstract.map_apply (f : α → β) (m : Abstract.Handler α) (env : Abstract.Env)
    (store : Store) :
    (f <$> m) env store = (f (m env store).1, (m env store).2.1, (m env store).2.2) := by
  show (m >>= fun a => Pure.pure (f a)) env store = _
  simp only [bind, Pure.pure, List.append_nil]

@[simp] theorem Concrete.candidateAt_same {key : DocumentKey} (document : Document key)
    (make : Document key → Concrete.Candidate key) :
    Concrete.candidateAt key document make = some (make document) := by
  simp [Concrete.candidateAt, Concrete.Candidate.cast]

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
    (hhandler : Abstract.handler call.request call.requestedAt =
      wrap <$> Abstract.completeForKey key call.requestedAt ma)
    (hsim : HandlerSim key ma action) (hunique : state.store.Unique)
    (hdoc : DocEquiv key (state.store.read key) before) :
    let candidate := Concrete.externalCandidate appConfig call before action wrap
    let lifted := Abstract.run appConfig call state
    Same lifted.1.store (state.store.write key candidate.document) ∧
      lifted.1.store.Unique ∧
      lifted.1.workflow = state.workflow ∧
      lifted.2 = candidate.outputs := by
  have hcomplete := completeDecision_sim key call.requestedAt hsim
  obtain ⟨hresult, -, hsame, hemit, hunique'⟩ :=
    hcomplete { config := appConfig.toServerConfig } state.store before hunique hdoc trivial
  simp only [Abstract.run, Abstract.serve, hhandler, Abstract.map_apply,
    Concrete.externalCandidate, Concrete.Decision.run]
  exact ⟨hsame, hunique', trivial, by rw [hresult, hemit]⟩

theorem external_sim_of (appConfig : Resonate.Config) (call : Call)
    {key : DocumentKey} (before : Document key) {ma : Abstract.Handler β}
    {action : Concrete.Decision.Handler key β} {wrap : β → Response}
    (hcandidate :
      Concrete.selectedExternalCandidate appConfig call key before =
        some (Concrete.externalCandidate appConfig call before action wrap))
    (hhandler : Abstract.handler call.request call.requestedAt =
      wrap <$> Abstract.completeForKey key call.requestedAt ma)
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
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (promiseGet_sim req call.requestedAt)
  case promiseCreate req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (promiseCreate_sim req call.requestedAt rfl)
  case promiseSettle req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseSettle)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (promiseSettle_sim req call.requestedAt rfl)
  case promiseRegisterCallback req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .promiseRegisterCallback)
        (by simp [Concrete.selectedExternalCandidate, hrequest])
        (by simp_all [Abstract.handler, Abstract.completeForKey])
        (promiseRegisterCallback_sim req call.requestedAt)
    · contradiction
  case promiseRegisterListener req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .promiseRegisterListener)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (promiseRegisterListener_sim req call.requestedAt)
  case scheduleGet req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .scheduleGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (scheduleGet_sim req call.requestedAt)
  case scheduleCreate req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .scheduleCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (scheduleCreate_sim req call.requestedAt)
  case scheduleDelete req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .scheduleDelete)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (scheduleDelete_sim req call.requestedAt)
  case taskGet req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskGet)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (taskGet_sim req call.requestedAt)
  case taskCreate req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskCreate)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (taskCreate_sim req call.requestedAt)
  case taskAcquire req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskAcquire)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (taskAcquire_sim req call.requestedAt)
  case taskFence req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .taskFence)
        (by simp [Concrete.selectedExternalCandidate, hrequest])
        (by simp_all [Abstract.handler, Abstract.completeForKey])
        (taskFence_sim req call.requestedAt)
    · contradiction
  case taskHeartbeat req =>
    cases htasks : req.tasks with
    | nil => simp [htasks] at hkey
    | cons first rest =>
      simp only [htasks] at hkey
      split at hkey
      · cases hkey
        exact external_sim_of appConfig call before (wrap := .taskHeartbeat)
          (by simp [Concrete.selectedExternalCandidate, hrequest, htasks])
          (by simp_all [Abstract.handler, Abstract.completeForKey])
          (taskHeartbeat_sim req call.requestedAt first rest htasks)
      · contradiction
  case taskSuspend req =>
    split at hkey
    · contradiction
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .taskSuspend)
        (by simp [Concrete.selectedExternalCandidate, hrequest])
        (by simp_all [Abstract.handler, Abstract.completeForKey])
        (taskSuspend_sim req call.requestedAt)
  case taskFulfill req =>
    split at hkey
    · cases hkey
      exact external_sim_of appConfig call before (wrap := .taskFulfill)
        (by simp [Concrete.selectedExternalCandidate, hrequest])
        (by simp_all [Abstract.handler, Abstract.completeForKey])
        (taskFulfill_sim req call.requestedAt)
    · contradiction
  case taskRelease req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskRelease)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (taskRelease_sim req call.requestedAt)
  case taskHalt req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskHalt)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
      (by rw [hrequest]; rfl) (taskHalt_sim req call.requestedAt)
  case taskContinue req =>
    cases hkey
    exact external_sim_of appConfig call before (wrap := .taskContinue)
      (by simp [Concrete.selectedExternalCandidate, hrequest])
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
        Abstract.taskHeartbeat, Concrete.pureResponse, Pure.pure, hrequest, htasks]
    | cons first rest =>
      simp only [htasks] at hkey
      split at hkey
      · contradiction
      · simp_all [Abstract.run, Abstract.serve, Abstract.handler, Abstract.map_apply,
          Abstract.taskHeartbeat, Concrete.pureResponse, Pure.pure]
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
        Abstract.taskFulfill, Concrete.pureResponse, Pure.pure]
  all_goals
    simp [Abstract.run, Abstract.serve, Abstract.handler,
      Concrete.pureResponse, Pure.pure, hrequest, Abstract.promiseSearch,
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
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key]) rfl
      (processPromiseTimeout_sim id now) hunique hdoc
  | callback req =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key]) rfl
      (processCallback_sim req now hlocal) hunique hdoc
  | listener req =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key]) rfl
      (processListener_sim req now) hunique hdoc
  | taskLeaseTimeout id =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key]) rfl
      (processLeaseTimeout_sim id now) hunique hdoc
  | taskRetryTimeout id =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key]) rfl
      (processRetryTimeout_sim id now) hunique hdoc
  | occurrence req time =>
    exact work_sim_of appConfig _ now rest abstractRest state
      (by simp [Concrete.selectedWorkCandidate, WorkItem.key]) rfl
      (createIfAbsent_sim req time) hunique hdoc
  | scheduleTimeout id =>
    obtain ⟨hresult, -, hsame, hemit, hunique'⟩ :=
      processSchedule_sim id now { config := appConfig.toServerConfig } state.store before
        hunique hdoc trivial
    simp only [Concrete.selectedWorkCandidate, WorkItem.key, Concrete.candidateAt_same,
      Abstract.runWork, Abstract.processWork,
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
  grind [Concrete.Decision.originObjectWork,
    Concrete.Decision.originTaskWork, Abstract.objectWork,
    Object.ofOrigin, OriginObject.id]

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
    {document : WorkflowDocument origin}
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
