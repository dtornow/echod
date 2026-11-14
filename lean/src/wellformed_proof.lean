import refinement_proof
import «concrete».WellFormed

/-!
# Concrete documents stay well-formed

Every concrete decision leaves a well-formed document well-formed
(`Keeps`). A PUT that lands was decided on exactly the document it
replaces, so the store holds only well-formed documents in every reachable
system.
-/

namespace Resonate.Concrete

open ServerModel
open Rover

/-! ## Rows -/

theorem TaskOk.fulfill (t : TaskObject) : TaskOk t.fulfill := by
  constructor <;> simp [AbstractModel.TaskObject.fulfill]

theorem TaskOk.project {t : TaskObject} (h : TaskOk t) (p : PromiseObject) :
    TaskOk (t.project p) := by
  unfold AbstractModel.TaskObject.project
  split
  · exact TaskOk.fulfill t
  · exact h

theorem project_fulfilled (t : TaskObject) {p : PromiseObject} (h : p.state ≠ .pending) :
    (t.project p).state = .fulfilled := by
  unfold AbstractModel.TaskObject.project
  by_cases ht : t.state = .fulfilled
  · simp [ht]
  · simp [h, ht, AbstractModel.TaskObject.fulfill]

theorem PromiseOk.project {id : Ident} {p : PromiseObject} (h : PromiseOk id p)
    (now : Nat) : PromiseOk id (p.project now) := by
  unfold AbstractModel.PromiseObject.project
  split
  · next hdue =>
    have hpending : p.state = .pending := by simpa using hdue.1
    have hvalue := h.pending_no_value hpending
    split <;> exact {
      created_le_timeout := h.created_le_timeout
      pending_before_timeout := by simp
      pending_iff_unsettled := by simp
      settled_le_timeout := by simp
      pending_no_value := by simp
      deadline_no_value := fun _ => hvalue
      timedout_at_deadline := by simp
      callbacks_nodup := h.callbacks_nodup
      callbacks_not_self := h.callbacks_not_self
      callbacks_same_origin := h.callbacks_same_origin
      listeners_nodup := h.listeners_nodup }
  · exact h

/-- A row read at `now`: a promise it still shows pending is not yet due. -/
def Fresh {origin : String} (now : Nat) (o : OriginObject origin) : Prop :=
  o.promise.state = .pending → now < o.promise.timeoutAt

theorem fresh_project {origin : String} (o : OriginObject origin) (now : Nat) :
    Fresh now (o.project now) := by
  intro hpending
  simp only [OriginObject.project] at hpending ⊢
  unfold AbstractModel.PromiseObject.project at hpending ⊢
  split at hpending
  · split at hpending <;> simp at hpending
  · next hdue =>
    rw [if_neg hdue]
    exact Nat.lt_of_not_le fun hle => hdue ⟨by simpa using hpending, hle⟩

theorem ObjectOk.project {origin : String} {o : OriginObject origin} (h : ObjectOk o)
    (now : Nat) : ObjectOk (o.project now) := by
  obtain ⟨suffix, promise, task⟩ := o
  refine ⟨h.promise.project now, ?_, ?_⟩
  · intro t ht
    cases task with
    | none => simp [OriginObject.project] at ht
    | some task =>
        simp only [OriginObject.project, Option.map_some, Option.some.injEq] at ht
        subst ht
        exact (h.task task rfl).project _
  · intro t ht hsettled
    cases task with
    | none => simp [OriginObject.project] at ht
    | some task =>
        simp only [OriginObject.project, Option.map_some, Option.some.injEq] at ht
        subst ht
        exact project_fulfilled task hsettled

theorem ObjectOk.withTask {origin : String} {o : OriginObject origin} (h : ObjectOk o)
    {t : TaskObject} (ht : TaskOk t)
    (hsettled : t.state ≠ .fulfilled → o.promise.state = .pending) :
    ObjectOk ({ o with task := some t } : OriginObject origin) := by
  refine ⟨h.promise, ?_, ?_⟩
  · rintro _ ⟨⟩; exact ht
  · rintro _ ⟨⟩ hp
    exact Classical.byContradiction fun hf => hp (hsettled hf)

theorem ObjectOk.replaceTask {origin : String} {o : OriginObject origin} (h : ObjectOk o)
    {t t' : TaskObject} (ht : o.task = some t) (hok : TaskOk t → TaskOk t')
    (hstate : t'.state ≠ .fulfilled → t.state ≠ .fulfilled) :
    ObjectOk ({ o with task := some t' } : OriginObject origin) :=
  h.withTask (hok (h.task t ht)) fun hf =>
    Classical.byContradiction fun hp => hstate hf (h.settled t ht hp)

theorem ObjectOk.withPromise {origin : String} {o : OriginObject origin} (h : ObjectOk o)
    {p : PromiseObject} (hp : PromiseOk o.id p) (hstate : p.state = o.promise.state) :
    ObjectOk ({ o with promise := p } : OriginObject origin) :=
  ⟨hp, h.task, fun t ht hs => h.settled t ht (hstate ▸ hs)⟩

theorem PromiseOk.addCallback {id : Ident} {p : PromiseObject} (h : PromiseOk id p)
    {awaiter : Ident} (hne : awaiter ≠ id) (horigin : awaiter.origin = id.origin) :
    PromiseOk id (p.addCallback awaiter) := by
  unfold AbstractModel.PromiseObject.addCallback
  split
  · exact h
  · next hnew =>
    exact { h with
      callbacks_nodup := List.nodup_append.mpr ⟨h.callbacks_nodup, by simp,
        by intro a ha b hb; simp at hb; subst hb; rintro rfl; simp_all⟩
      callbacks_not_self := by simp [h.callbacks_not_self, Ne.symm hne]
      callbacks_same_origin := by
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact h.callbacks_same_origin a ha
        · exact horigin }

theorem PromiseOk.addListener {id : Ident} {p : PromiseObject} (h : PromiseOk id p)
    (address : String) : PromiseOk id (p.addListener address) := by
  unfold AbstractModel.PromiseObject.addListener
  split
  · exact h
  · next hnew =>
    exact { h with
      listeners_nodup := List.nodup_append.mpr ⟨h.listeners_nodup, by simp,
        by intro a ha b hb; simp at hb; subst hb; rintro rfl; simp_all⟩ }

theorem PromiseOk.filterCallbacks {id : Ident} {p : PromiseObject} (h : PromiseOk id p)
    (f : Ident → Bool) : PromiseOk id { p with callbacks := p.callbacks.filter f } :=
  { h with
    callbacks_nodup := h.callbacks_nodup.filter f
    callbacks_not_self := fun hmem => h.callbacks_not_self (List.mem_filter.mp hmem).1
    callbacks_same_origin := fun a ha =>
      h.callbacks_same_origin a (List.mem_filter.mp ha).1 }

theorem PromiseOk.filterListeners {id : Ident} {p : PromiseObject} (h : PromiseOk id p)
    (f : String → Bool) : PromiseOk id { p with listeners := p.listeners.filter f } :=
  { h with listeners_nodup := h.listeners_nodup.filter f }

/-- A promise still pending at `now` settled at `now`, its task finished. -/
theorem ObjectOk.settle {origin : String} {o : OriginObject origin} (h : ObjectOk o)
    {now : Nat} (hfresh : Fresh now o) (hpending : o.promise.state = .pending)
    {state : PromiseState} (hsettable : state.settable = true) (value : Value) :
    let p := { o.promise with state, value, settledAt := some now }
    ObjectOk ({ o with promise := p, task := o.task.map (·.project p) } :
      OriginObject origin) := by
  intro p
  have hlt := hfresh hpending
  have hstate : state ≠ .pending := by rintro rfl; simp [PromiseState.settable] at hsettable
  have hpromise : PromiseOk o.id p := {
    created_le_timeout := h.promise.created_le_timeout
    pending_before_timeout := fun hp => absurd hp hstate
    pending_iff_unsettled := by simp [p, hstate]
    settled_le_timeout := by simp only [p, Option.some.injEq]; rintro _ rfl; omega
    pending_no_value := fun hp => absurd hp hstate
    deadline_no_value := by simp only [p, Option.some.injEq]; intro heq; omega
    timedout_at_deadline := by
      rintro rfl; simp [PromiseState.settable] at hsettable
    callbacks_nodup := h.promise.callbacks_nodup
    callbacks_not_self := h.promise.callbacks_not_self
    callbacks_same_origin := h.promise.callbacks_same_origin
    listeners_nodup := h.promise.listeners_nodup }
  refine ⟨hpromise, ?_, ?_⟩
  · intro t ht
    cases htask : o.task with
    | none => simp [htask] at ht
    | some task =>
        simp only [htask, Option.map_some, Option.some.injEq] at ht
        subst ht
        exact (h.task task htask).project p
  · intro t ht _
    cases htask : o.task with
    | none => simp [htask] at ht
    | some task =>
        simp only [htask, Option.map_some, Option.some.injEq] at ht
        subst ht
        exact project_fulfilled task hstate

theorem newObject_ok {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) :
    let o := Decision.newObject (origin := origin) suffix timeoutAt now param tags
    ObjectOk o ∧ o.suffix = suffix ∧ Fresh now o := by
  intro o
  have hfulfilled : TaskOk { state := .fulfilled, version := 0 } := by constructor <;> simp
  simp only [o, Decision.newObject]
  split
  · next hlive =>
    have hpromise : PromiseOk ⟨origin, suffix⟩
        { state := .pending, param, tags, timeoutAt, createdAt := now } := {
      created_le_timeout := Nat.le_of_lt hlive
      pending_before_timeout := fun _ => hlive
      pending_iff_unsettled := by simp
      settled_le_timeout := by simp
      pending_no_value := fun _ => rfl
      deadline_no_value := by simp
      timedout_at_deadline := by simp
      callbacks_nodup := List.nodup_nil
      callbacks_not_self := List.not_mem_nil
      callbacks_same_origin := by simp
      listeners_nodup := List.nodup_nil }
    split
    · refine ⟨⟨hpromise, ?_, by simp⟩, rfl, fun _ => hlive⟩
      rintro _ ⟨⟩
      constructor <;> simp
    · exact ⟨⟨hpromise, by simp, by simp⟩, rfl, fun _ => hlive⟩
  · next hdead =>
    have hpromise (state : PromiseState) (hstate : state ≠ .pending) :
        PromiseOk ⟨origin, suffix⟩
          { state, param, tags, timeoutAt, createdAt := timeoutAt,
            settledAt := some timeoutAt } := {
      created_le_timeout := Nat.le_refl _
      pending_before_timeout := fun h => absurd h hstate
      pending_iff_unsettled := by simp [hstate]
      settled_le_timeout := by simp
      pending_no_value := fun h => absurd h hstate
      deadline_no_value := fun _ => rfl
      timedout_at_deadline := fun _ => rfl
      callbacks_nodup := List.nodup_nil
      callbacks_not_self := List.not_mem_nil
      callbacks_same_origin := by simp
      listeners_nodup := List.nodup_nil }
    split <;> split <;>
      refine ⟨⟨hpromise _ (by simp), ?_, ?_⟩, rfl, fun h => absurd h (by simp)⟩ <;>
      first
        | (rintro _ ⟨⟩; exact hfulfilled)
        | (rintro _ ⟨⟩ _; rfl)
        | simp

/-! ## Handlers that keep documents well-formed -/

/-- From a well-formed document, `h` leaves a well-formed document and a
result satisfying `Q`. -/
def Keeps {key : DocumentKey} (h : DocumentHandler key α) (Q : α → Prop) : Prop :=
  ∀ env document, DocumentOk key document →
    DocumentOk key (h env document).2.1 ∧ Q (h env document).1

namespace Keeps

variable {key : DocumentKey}

theorem pure {a : α} {Q : α → Prop} (h : Q a) :
    Keeps (Pure.pure a : DocumentHandler key α) Q :=
  fun _ _ hd => ⟨hd, h⟩

theorem bind {m : DocumentHandler key α} {f : α → DocumentHandler key β}
    {R : α → Prop} {Q : β → Prop}
    (hm : Keeps m R) (hf : ∀ a, R a → Keeps (f a) Q) : Keeps (m >>= f) Q := by
  intro env document hd
  obtain ⟨hd', hr⟩ := hm env document hd
  exact hf _ hr env _ hd'

theorem post {m : DocumentHandler key α} {Q Q' : α → Prop}
    (hm : Keeps m Q) (h : ∀ a, Q a → Q' a) : Keeps m Q' := fun env document hd =>
  let ⟨hd', hq⟩ := hm env document hd
  ⟨hd', h _ hq⟩

theorem forM {f : γ → DocumentHandler key PUnit} :
    ∀ l : List γ, (∀ x ∈ l, Keeps (f x) (fun _ => True)) →
      Keeps (l.forM f) (fun _ => True)
  | [], _ => Keeps.pure trivial
  | x :: rest, h =>
      Keeps.bind (h x (by simp)) fun _ _ =>
        forM rest fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem mapM {f : γ → DocumentHandler key α} :
    ∀ l : List γ, (∀ x ∈ l, Keeps (f x) (fun _ => True)) →
      Keeps (l.mapM f) (fun _ => True)
  | [], _ => Keeps.pure trivial
  | x :: rest, h => by
      simp only [List.mapM_cons]
      exact Keeps.bind (h x (by simp)) fun _ _ =>
        Keeps.bind (mapM rest fun y hy => h y (by simp [hy])) fun _ _ => Keeps.pure trivial

end Keeps

/-- A row read at `now` for `suffix`. -/
def Read {origin : String} (suffix : String) (now : Nat) (o : OriginObject origin) : Prop :=
  ObjectOk o ∧ o.suffix = suffix ∧ Fresh now o

theorem get_keeps {key : DocumentKey} :
    Keeps (Decision.get (key := key)) (DocumentOk key) :=
  fun _ _ hd => ⟨hd, hd⟩

theorem getObject_keeps {origin : String} (suffix : String) :
    Keeps (Decision.getObject (origin := origin) suffix)
      (fun r => ∀ o, r = some o → ObjectOk o ∧ o.suffix = suffix) := by
  unfold Decision.getObject
  refine Keeps.bind get_keeps fun document hd => Keeps.pure ?_
  intro o ho
  refine ⟨hd.2 o (List.mem_of_find?_eq_some ho), ?_⟩
  simpa using List.find?_some ho

theorem readObject_keeps {origin : String} (suffix : String) (now : Nat) :
    Keeps (Decision.readObject (origin := origin) suffix now)
      (fun r => ∀ o, r = some o → Read suffix now o) := by
  unfold Decision.readObject
  refine Keeps.bind (getObject_keeps suffix) fun r hr => ?_
  cases r with
  | none => exact Keeps.pure (by simp)
  | some o =>
      obtain ⟨hok, hsuffix⟩ := hr o rfl
      exact Keeps.pure (by
        rintro _ ⟨⟩
        exact ⟨hok.project now, hsuffix, fresh_project o now⟩)

theorem readTask_keeps {origin : String} (suffix : String) (now : Nat) :
    Keeps (Decision.readTask (origin := origin) suffix now)
      (fun r => ∀ o t, r = some (o, t) → Read suffix now o ∧ o.task = some t) := by
  unfold Decision.readTask
  refine Keeps.bind (readObject_keeps suffix now) fun r hr => ?_
  cases r with
  | none => exact Keeps.pure (by simp)
  | some o =>
      refine Keeps.pure ?_
      intro o' t ht
      cases htask : o.task with
      | none => simp [htask] at ht
      | some task =>
          simp only [htask, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          exact ⟨hr _ rfl, htask⟩

theorem getSchedule_keeps {id : Ident} :
    Keeps (Decision.getSchedule (id := id))
      (fun r => ∀ s, r = some s → s.promiseTags.timerTargeted = false) := by
  unfold Decision.getSchedule
  refine Keeps.bind get_keeps fun document hd => Keeps.pure ?_
  intro s hs
  cases hdoc : (document : ScheduleDocument id) with
  | none => simp [hdoc] at hs
  | some data =>
      simp only [hdoc, Option.map_some, Option.some.injEq] at hs
      subst hs
      exact hd data hdoc

theorem setObject_keeps {origin : String} {o : OriginObject origin} (h : ObjectOk o) :
    Keeps (Decision.setObject o) (fun _ => True) := by
  intro env document hd
  refine ⟨?_, trivial⟩
  show DocumentOk (.origin origin) (o :: (document : OriginDocument origin).filter
    (·.suffix != o.suffix))
  obtain ⟨hnodup, hrows⟩ := hd
  refine ⟨?_, ?_⟩
  · simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, (hnodup.sublist (List.filter_sublist.map _))⟩
    simp
  · intro x hx
    simp only [List.mem_cons, List.mem_filter] at hx
    rcases hx with rfl | ⟨hx, _⟩
    · exact h
    · exact hrows x hx

theorem setSchedule_keeps {id : Ident} {schedule : Schedule}
    (h : schedule.promiseTags.timerTargeted = false) :
    Keeps (Decision.setSchedule (id := id) schedule) (fun _ => True) := by
  intro env document _
  refine ⟨?_, trivial⟩
  rintro _ ⟨⟩
  exact h

theorem delSchedule_keeps {id : Ident} :
    Keeps (Decision.delSchedule (id := id)) (fun _ => True) := by
  intro env document _
  exact ⟨by rintro _ ⟨⟩, trivial⟩

theorem setMessage_keeps {key : DocumentKey} (address : String) (message : ServerModel.Message) :
    Keeps (Decision.setMessage (key := key) address message) (fun _ => True) :=
  fun _ _ hd => ⟨hd, trivial⟩

theorem ask_keeps {key : DocumentKey} : Keeps (Decision.ask (key := key)) (fun _ => True) :=
  fun _ _ hd => ⟨hd, trivial⟩

theorem createPromiseAt_keeps {origin : String} (suffix : String) (timeoutAt now : Nat)
    (param : Value) (tags : Tags) :
    Keeps (Decision.createPromiseAt (origin := origin) suffix timeoutAt now param tags)
      (Read suffix now) := by
  unfold Decision.createPromiseAt
  obtain ⟨hok, hsuffix, hfresh⟩ := newObject_ok (origin := origin) suffix timeoutAt now param tags
  exact Keeps.bind (setObject_keeps hok) fun _ _ => Keeps.pure ⟨hok, hsuffix, hfresh⟩

theorem readOrCreate_keeps {origin : String} (req : PromiseCreateReq) (now : Nat) :
    Keeps (Decision.readOrCreate (origin := origin) req now) (Read req.id.suffix now) := by
  unfold Decision.readOrCreate
  refine Keeps.bind (readObject_keeps _ _) fun r hr => ?_
  cases r with
  | none => exact createPromiseAt_keeps _ _ _ _ _
  | some o => exact Keeps.pure (hr o rfl)

theorem setSettled_keeps {origin : String} {o : OriginObject origin} {now : Nat}
    (h : ObjectOk o) (hfresh : Fresh now o) (hpending : o.promise.state = .pending)
    {state : PromiseState} (hsettable : state.settable = true) (value : Value) :
    Keeps (Decision.setSettled o { o.promise with state, value, settledAt := some now })
      (fun _ => True) :=
  setObject_keeps (h.settle hfresh hpending hsettable value)

namespace Keeps

variable {origin : String} {Q : β → Prop}

theorem readObject {suffix : String} {now : Nat}
    {f : Option (OriginObject origin) → DocumentHandler (.origin origin) β}
    (hnone : Keeps (f none) Q)
    (hsome : ∀ o, ObjectOk o → o.suffix = suffix → Fresh now o → Keeps (f (some o)) Q) :
    Keeps (Decision.readObject suffix now >>= f) Q :=
  Keeps.bind (readObject_keeps suffix now) fun r hr => by
    cases r with
    | none => exact hnone
    | some o =>
        obtain ⟨hok, hsuffix, hfresh⟩ := hr o rfl
        exact hsome o hok hsuffix hfresh

theorem readTask {suffix : String} {now : Nat}
    {f : Option (OriginObject origin × TaskObject) → DocumentHandler (.origin origin) β}
    (hnone : Keeps (f none) Q)
    (hsome : ∀ o t, ObjectOk o → o.suffix = suffix → Fresh now o → o.task = some t →
      TaskOk t → (t.state ≠ .fulfilled → o.promise.state = .pending) →
      Keeps (f (some (o, t))) Q) :
    Keeps (Decision.readTask suffix now >>= f) Q :=
  Keeps.bind (readTask_keeps suffix now) fun r hr => by
    rcases r with _ | ⟨o, t⟩
    · exact hnone
    · obtain ⟨⟨hok, hsuffix, hfresh⟩, htask⟩ := hr o t rfl
      exact hsome o t hok hsuffix hfresh htask (hok.task t htask)
        fun hf => Classical.byContradiction fun hp => hf (hok.settled t htask hp)

theorem readOrCreate {req : PromiseCreateReq} {now : Nat}
    {f : OriginObject origin → DocumentHandler (.origin origin) β}
    (h : ∀ o, ObjectOk o → o.suffix = req.id.suffix → Fresh now o → Keeps (f o) Q) :
    Keeps (Decision.readOrCreate req now >>= f) Q :=
  Keeps.bind (readOrCreate_keeps req now) fun o ⟨hok, hsuffix, hfresh⟩ => h o hok hsuffix hfresh

theorem getSchedule {id : Ident} {f : Option Schedule → DocumentHandler (.schedule id) β}
    (hnone : Keeps (f none) Q)
    (hsome : ∀ s, s.promiseTags.timerTargeted = false → Keeps (f (some s)) Q) :
    Keeps (Decision.getSchedule >>= f) Q :=
  Keeps.bind getSchedule_keeps fun r hr => by
    cases r with
    | none => exact hnone
    | some s => exact hsome s (hr s rfl)

theorem seq {key : DocumentKey} {m : DocumentHandler key PUnit} {k : DocumentHandler key β}
    (hm : Keeps m (fun _ => True)) (hk : Keeps k Q) : Keeps (m >>= fun _ => k) Q :=
  Keeps.bind hm fun _ _ => hk

end Keeps

theorem OriginObject.id_eq {id : Ident} {o : OriginObject id.origin}
    (h : o.suffix = id.suffix) : o.id = id := by
  cases id; simp [OriginObject.id, h]

theorem ne_of_awaited {id awaited : Ident} (hne : awaited ≠ id)
    (horigin : awaited.origin = id.origin) :
    id ≠ { origin := id.origin, suffix := awaited.suffix } := by
  intro h
  apply hne
  cases awaited; cases id
  simp only [Ident.mk.injEq] at h horigin ⊢
  exact ⟨horigin, h.2.symm⟩

/-- The read facts about a row's task. -/
theorem Read.task {origin suffix : String} {now : Nat} {o : OriginObject origin}
    {t : TaskObject} (h : Read suffix now o) (ht : o.task = some t) :
    TaskOk t ∧ (t.state ≠ .fulfilled → o.promise.state = .pending) :=
  ⟨h.1.task t ht, fun hf => Classical.byContradiction fun hp => hf (h.1.settled t ht hp)⟩

open Lean Meta Elab Tactic in
/-- One step through a handler, chosen by the head of the handler. -/
elab "keeps_step" : tactic => withMainContext do
  let target ← whnfR (← instantiateMVars (← getMainTarget))
  unless target.isAppOfArity ``Keeps 4 do throwError "keeps_step: not a Keeps goal"
  let h ← instantiateMVars target.getAppArgs[2]!
  let run (stx : MetaM (TSyntax `tactic)) : TacticM Unit := do evalTactic (← stx)
  if h.isHeadBetaTarget || h.isLet || h.isAppOf ``letFun then
    run `(tactic| dsimp only)
    return
  let lemmaOf (name : Name) : Lean.Ident :=
    mkIdent (Name.mkSimple (Resonate.Refinement.lastString name ++ "_keeps"))
  if h.isAppOf ``Pure.pure then
    run `(tactic| exact Keeps.pure trivial)
  else if h.isAppOf ``ite || h.isAppOf ``dite then
    run `(tactic| split)
  else if h.isAppOf ``Bind.bind && h.getAppNumArgs == 6 then
    let m := (← instantiateMVars h.getAppArgs[4]!).headBeta
    match m.getAppFn.constName? with
    | some ``Pure.pure => run `(tactic| rw [pure_bind])
    | some ``Resonate.Concrete.Decision.readObject =>
        run `(tactic| refine Keeps.readObject ?_ (fun _ _ _ _ => ?_))
    | some ``Resonate.Concrete.Decision.readTask =>
        run `(tactic| refine Keeps.readTask ?_ (fun _ _ _ _ _ _ _ _ => ?_))
    | some ``Resonate.Concrete.Decision.readOrCreate =>
        run `(tactic| refine Keeps.readOrCreate (fun _ _ _ _ => ?_))
    | some ``Resonate.Concrete.Decision.getSchedule =>
        run `(tactic| refine Keeps.getSchedule ?_ (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.createPromiseAt =>
        run `(tactic| refine Keeps.bind (createPromiseAt_keeps _ _ _ _ _) (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.setObject =>
        run `(tactic| refine Keeps.bind (setObject_keeps ?_) (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.setSettled =>
        run `(tactic| refine Keeps.bind (setSettled_keeps ?_ ?_ ?_ ?_ _) (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.setSchedule =>
        run `(tactic| refine Keeps.bind (setSchedule_keeps ?_) (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.delSchedule =>
        run `(tactic| refine Keeps.bind delSchedule_keeps (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.setMessage =>
        run `(tactic| refine Keeps.bind (setMessage_keeps _ _) (fun _ _ => ?_))
    | some ``Resonate.Concrete.Decision.ask =>
        run `(tactic| refine Keeps.bind ask_keeps (fun _ _ => ?_))
    | _ =>
        run `(tactic| refine Keeps.bind (R := fun _ => True) ?_ (fun _ _ => ?_))
  else
    match h.getAppFn.constName? with
    | some ``Resonate.Concrete.Decision.setObject => run `(tactic| refine setObject_keeps ?_)
    | some ``Resonate.Concrete.Decision.readObject =>
        run `(tactic| exact Keeps.post (readObject_keeps _ _) (fun _ _ => trivial))
    | some ``Resonate.Concrete.Decision.setSchedule => run `(tactic| refine setSchedule_keeps ?_)
    | some ``Resonate.Concrete.Decision.delSchedule => run `(tactic| exact delSchedule_keeps)
    | some ``Resonate.Concrete.Decision.setMessage => run `(tactic| exact setMessage_keeps _ _)
    | some ``List.forM => run `(tactic| refine Keeps.forM _ (fun _ _ => ?_))
    | some ``List.mapM => run `(tactic| refine Keeps.mapM _ (fun _ _ => ?_))
    | some name =>
        if ← isMatcher name then run `(tactic| first | dsimp only | split)
        else
          let lemma := lemmaOf name
          run `(tactic| apply $lemma)
    | none => throwError "keeps_step: no handler head"

macro "task_ok" : tactic => `(tactic|
  (intro hold
   obtain ⟨_, _, _, _, _, _, _⟩ := hold
   constructor <;> simp_all [List.nodup_append] <;> (intro _ _ heq; subst heq; simp_all)))

macro "keeps" : tactic =>
  `(tactic| repeat' (first
    | keeps_step
    | assumption
    | (simp_all; done)
    | (refine ObjectOk.replaceTask (by assumption) (by assumption) ?_ ?_)
    | (refine ObjectOk.withPromise (by assumption) ?_ (by simp))
    | (refine PromiseOk.addCallback (ObjectOk.promise (by assumption)) ?_ ?_)
    | (rw [OriginObject.id_eq (by assumption)]; intro heq; simp_all [Ident.sameOrigin]; done)
    | (simp_all [OriginObject.id, Ident.sameOrigin]; done)
    | (apply ne_of_awaited <;> simp_all [Ident.sameOrigin]; done)
    | (refine PromiseOk.addListener (ObjectOk.promise (by assumption)) _)
    | (refine PromiseOk.filterCallbacks (ObjectOk.promise (by assumption)) _)
    | (refine PromiseOk.filterListeners (ObjectOk.promise (by assumption)) _)
    | task_ok))

theorem promiseGet_keeps (req : PromiseGetReq) (now : Nat) :
    Keeps (Decision.promiseGet req now) (fun _ => True) := by
  unfold Decision.promiseGet
  keeps

theorem promiseCreate_keeps {origin : String} (req : PromiseCreateReq) (now : Nat) :
    Keeps (Decision.promiseCreate (origin := origin) req now) (fun _ => True) := by
  unfold Decision.promiseCreate
  keeps

theorem promiseSettle_keeps {origin : String} (req : PromiseSettleReq) (now : Nat) :
    Keeps (Decision.promiseSettle (origin := origin) req now) (fun _ => True) := by
  unfold Decision.promiseSettle
  keeps

theorem promiseRegisterCallback_keeps (req : PromiseRegisterCallbackReq) (now : Nat) :
    Keeps (Decision.promiseRegisterCallback req now) (fun _ => True) := by
  unfold Decision.promiseRegisterCallback
  keeps

theorem promiseRegisterListener_keeps (req : PromiseRegisterListenerReq) (now : Nat) :
    Keeps (Decision.promiseRegisterListener req now) (fun _ => True) := by
  unfold Decision.promiseRegisterListener
  keeps

theorem taskGet_keeps (req : TaskGetReq) (now : Nat) :
    Keeps (Decision.taskGet req now) (fun _ => True) := by
  unfold Decision.taskGet
  keeps

theorem taskCreate_keeps (req : TaskCreateReq) (now : Nat) :
    Keeps (Decision.taskCreate req now) (fun _ => True) := by
  unfold Decision.taskCreate
  keeps

theorem taskAcquire_keeps (req : TaskAcquireReq) (now : Nat) :
    Keeps (Decision.taskAcquire req now) (fun _ => True) := by
  unfold Decision.taskAcquire
  keeps

theorem taskFence_keeps (req : TaskFenceReq) (now : Nat) :
    Keeps (Decision.taskFence req now) (fun _ => True) := by
  unfold Decision.taskFence
  keeps

theorem heartbeatOne_keeps {origin : String} (pid : String) (ref : TaskRef) (now : Nat) :
    Keeps (Decision.heartbeatOne (origin := origin) pid ref now) (fun _ => True) := by
  unfold Decision.heartbeatOne
  keeps

theorem taskHeartbeat_keeps (origin : String) (req : TaskHeartbeatReq) (now : Nat) :
    Keeps (Decision.taskHeartbeat origin req now) (fun _ => True) := by
  unfold Decision.taskHeartbeat
  keeps

theorem addCallback_keeps {origin : String} (awaiter : Ident) (now : Nat)
    (action : PromiseRegisterCallbackReq)
    (hne : awaiter ≠ { origin, suffix := action.awaited.suffix })
    (horigin : awaiter.origin = origin) :
    Keeps (Decision.addCallback (origin := origin) awaiter now action) (fun _ => True) := by
  unfold Decision.addCallback
  keeps

theorem taskSuspend_keeps (req : TaskSuspendReq) (now : Nat) :
    Keeps (Decision.taskSuspend req now) (fun _ => True) := by
  unfold Decision.taskSuspend
  keeps

theorem taskFulfill_keeps (req : TaskFulfillReq) (now : Nat) :
    Keeps (Decision.taskFulfill req now) (fun _ => True) := by
  unfold Decision.taskFulfill
  keeps

theorem taskRelease_keeps (req : TaskReleaseReq) (now : Nat) :
    Keeps (Decision.taskRelease req now) (fun _ => True) := by
  unfold Decision.taskRelease
  keeps

theorem taskHalt_keeps (req : TaskHaltReq) (now : Nat) :
    Keeps (Decision.taskHalt req now) (fun _ => True) := by
  unfold Decision.taskHalt
  keeps

theorem taskContinue_keeps (req : TaskContinueReq) (now : Nat) :
    Keeps (Decision.taskContinue req now) (fun _ => True) := by
  unfold Decision.taskContinue
  keeps

theorem scheduleGet_keeps (req : ScheduleGetReq) (now : Nat) :
    Keeps (Decision.scheduleGet req now) (fun _ => True) := by
  unfold Decision.scheduleGet
  keeps

theorem scheduleCreate_keeps (req : ScheduleCreateReq) (now : Nat) :
    Keeps (Decision.scheduleCreate req now) (fun _ => True) := by
  unfold Decision.scheduleCreate
  keeps

theorem scheduleDelete_keeps (req : ScheduleDeleteReq) (now : Nat) :
    Keeps (Decision.scheduleDelete req now) (fun _ => True) := by
  unfold Decision.scheduleDelete
  keeps

theorem processPromiseTimeout_keeps (id : Ident) (now : Nat) :
    Keeps (Decision.processPromiseTimeout id now) (fun _ => True) := by
  unfold Decision.processPromiseTimeout
  keeps

theorem resumeOne_keeps {origin : String} (awaited awaiter : Ident) (now : Nat) :
    Keeps (Decision.resumeOne (origin := origin) awaited awaiter now) (fun _ => True) := by
  unfold Decision.resumeOne
  keeps

theorem processCallback_keeps (req : PromiseRegisterCallbackReq) (now : Nat) :
    Keeps (Decision.processCallback req now) (fun _ => True) := by
  unfold Decision.processCallback
  keeps

theorem processListener_keeps (req : PromiseRegisterListenerReq) (now : Nat) :
    Keeps (Decision.processListener req now) (fun _ => True) := by
  unfold Decision.processListener
  keeps

theorem processLeaseTimeout_keeps (id : Ident) (now : Nat) :
    Keeps (Decision.processLeaseTimeout id now) (fun _ => True) := by
  unfold Decision.processLeaseTimeout
  keeps

theorem processRetryTimeout_keeps (id : Ident) (now : Nat) :
    Keeps (Decision.processRetryTimeout id now) (fun _ => True) := by
  unfold Decision.processRetryTimeout
  keeps

theorem processSchedule_keeps (id : Ident) (now : Nat) :
    Keeps (Decision.processSchedule id now) (fun _ => True) := by
  unfold Decision.processSchedule
  keeps

theorem processOccurrence_keeps (req : PromiseCreateReq) (time : Nat) :
    Keeps (Decision.processOccurrence req time) (fun _ => True) := by
  unfold Decision.processOccurrence
  keeps

/-! ## Candidates -/

theorem Keeps.run {key : DocumentKey} {h : DocumentHandler key α} {Q : α → Prop}
    (hk : Keeps h Q) (config : ServerConfig) {document : Document key}
    (hd : DocumentOk key document) :
    DocumentOk key (Decision.run config h document).2.1 :=
  (hk _ _ hd).1

theorem candidateAt_ok {decided key : DocumentKey} {document : Document key}
    {make : Document decided → Candidate decided} {candidate : Candidate key}
    (h : candidateAt key document make = some candidate)
    (hmake : ∀ d, DocumentOk decided d → DocumentOk decided (make d).document)
    (hd : DocumentOk key document) : DocumentOk key candidate.document := by
  unfold candidateAt at h
  split at h
  · next heq =>
    subst heq
    simp only [Option.some.injEq] at h
    subst h
    exact hmake _ hd
  · contradiction

@[simp] theorem externalCandidate_document {key : DocumentKey}
    (appConfig : Resonate.Config) (call : Call) (document : Document key)
    (action : Decision.Handler key α) (wrap : α → Response) :
    (externalCandidate appConfig call document action wrap).document =
      (Decision.run appConfig.toServerConfig action document).2.1 := rfl

@[simp] theorem workCandidate_document {key : DocumentKey}
    (appConfig : Resonate.Config) (document : Document key)
    (action : Decision.Handler key α) (continuations : List PendingEntry) :
    (workCandidate appConfig document action continuations).document =
      (Decision.run appConfig.toServerConfig action document).2.1 := rfl

macro "candidate_ok" : tactic => `(tactic|
  (refine candidateAt_ok ‹_› (fun _ hd => ?_) ‹_›
   simp only [externalCandidate_document, workCandidate_document]
   refine Keeps.run (Q := fun _ => True) ?_ _ hd
   keeps))

theorem external_ok (appConfig : Resonate.Config) (call : Call) {key : DocumentKey}
    {before : Document key} {candidate : Candidate key}
    (h : selectedExternalCandidate appConfig call key before = some candidate)
    (hd : DocumentOk key before) : DocumentOk key candidate.document := by
  unfold selectedExternalCandidate at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       · contradiction
       · candidate_ok)
    | candidate_ok

theorem work_ok (appConfig : Resonate.Config) (item : WorkItem) (now : Time)
    (rest : List PendingEntry) {key : DocumentKey} {before : Document key}
    {candidate : Candidate key}
    (h : selectedWorkCandidate appConfig item now rest key before = some candidate)
    (hd : DocumentOk key before) : DocumentOk key candidate.document := by
  unfold selectedWorkCandidate at h
  split at h
  all_goals first
    | exact candidateAt_ok h (fun _ hd => Keeps.run (processSchedule_keeps _ _) _ hd) hd
    | candidate_ok

theorem scan_ok (appConfig : Resonate.Config) (key : DocumentKey) (now : Time)
    (rest : List PendingEntry) {before : Document key} {candidate : Candidate key}
    (h : selectScan appConfig key now rest before = some candidate)
    (hd : DocumentOk key before) : DocumentOk key candidate.document := by
  unfold selectScan at h
  split at h
  · next hwork =>
    simp only [Option.some.injEq] at h
    subst h
    unfold selectScanWork at hwork
    split at hwork
    · split at hwork
      · contradiction
      · exact work_ok _ _ _ _ hwork hd
    · split at hwork
      · split at hwork
        · exact work_ok _ _ _ _ hwork hd
        · contradiction
      · contradiction
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact hd
    · contradiction

/-- A selected transaction leaves a well-formed document well-formed. -/
theorem selected_ok {appConfig : Resonate.Config} {key : DocumentKey}
    {transaction : Transaction} {before document : Document key}
    {outputs : List Output} {continuations : List PendingEntry}
    (h : Refinement.Selected appConfig key transaction before document outputs continuations)
    (hd : DocumentOk key before) : DocumentOk key document := by
  cases h with
  | external _ hcandidate => exact external_ok _ _ hcandidate hd
  | work hcandidate => exact work_ok _ _ _ _ hcandidate hd
  | sweep _ hkey hcandidate =>
      subst hkey
      exact scan_ok _ _ _ _ hcandidate hd

/-! ## The store -/

theorem emptyDocument_ok : (key : DocumentKey) → DocumentOk key (emptyDocument key)
  | .origin _ => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | .schedule _ => fun _ h => nomatch h

theorem Store.WellFormed.empty : ({} : Store).WellFormed := by
  intro key document version h
  simp [Store.read] at h

theorem Store.WellFormed.commit {store : Store} (h : store.WellFormed) {key : DocumentKey}
    {document : Document key} (hd : DocumentOk key document) :
    (store.commit key document).WellFormed := by
  intro other d v hread
  by_cases hother : other = key
  · subst hother
    simp only [Store.read_commit_same, Option.some.injEq, Prod.mk.injEq] at hread
    obtain ⟨rfl, -⟩ := hread
    exact hd
  · rw [Store.read_commit_other _ _ _ _ hother] at hread
    exact h _ _ _ hread

theorem Store.WellFormed.documentAt {store : Store} (h : store.WellFormed)
    (key : DocumentKey) : DocumentOk key (store.documentAt key) := by
  unfold Store.documentAt
  split
  · next value hvalue => exact h key _ value.version (by simp [Store.read, hvalue])
  · exact emptyDocument_ok key

theorem Store.WellFormed.of_values {store next : Store} (h : store.WellFormed)
    (hvalues : next.values = store.values) : next.WellFormed := by
  intro key document version hread
  exact h key document version (by simpa [Store.read, hvalues] using hread)

/-- A store step keeps the store well-formed when every PUT it can commit
carries a well-formed document. -/
theorem store_step_ok {config : Config} {store : Store} {event : Event Pid Msg}
    {result : Result Pid Local Msg} (hwf : store.WellFormed)
    (hput : ∀ sender op key document expected,
      event = .receive sender (.storeRequest { op, payload := .put key document expected }) →
      expected = store.version key → DocumentOk key document)
    (hresult : result ∈ (storeStep Local.store config store event).val) :
    ∃ next, result.state = .store next ∧ next.WellFormed := by
  cases event with
  | timeout =>
      simp [storeStep, Outcomes.one] at hresult
      subst result
      exact ⟨store, rfl, hwf⟩
  | receive sender message =>
      cases message with
      | request _ | output _ | storeReply _ =>
          simp [storeStep, Outcomes.one] at hresult
          subst result
          exact ⟨store, rfl, hwf⟩
      | storeRequest rpc =>
          obtain ⟨op, payload⟩ := rpc
          cases payload with
          | put key document expected =>
              have hok := hput sender op key document expected rfl
              simp only [storeStep, storePut] at hresult
              split at hresult
              · simp [Outcomes.one] at hresult
                subst result
                exact ⟨store, rfl, hwf⟩
              · next hversion =>
                have hd := hok (by simpa using hversion)
                split at hresult
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hresult
                  rcases hresult with rfl | rfl | rfl
                  · exact ⟨_, rfl, hwf.commit hd⟩
                  · exact ⟨_, rfl, hwf.commit hd⟩
                  · exact ⟨_, rfl, hwf.commit (hwf.documentAt key)⟩
                · simp [Outcomes.one] at hresult
                  subst result
                  exact ⟨_, rfl, hwf.commit hd⟩
          | _ =>
              simp only [storeStep] at hresult
              try split at hresult
              all_goals
                simp [Outcomes.one] at hresult
                subst result
                exact ⟨_, rfl, hwf.of_values rfl⟩



/-- Every document the store holds is well-formed, in every reachable system. -/
theorem reachable_store_well_formed {nodes : List Addr} {appConfig : Resonate.Config}
    {config : Config} {system : System (model nodes appConfig)}
    (hreachable : Reachable (model nodes appConfig) config system) :
    ∀ {store}, system.process .store = .store store → store.WellFormed := by
  induction hreachable with
  | init hinit =>
      intro store hstore
      have h : Local.store store = Local.store {} := hstore.symm.trans hinit.2.1
      cases h
      exact Store.WellFormed.empty
  | @step previous label next hprevious hstep ih =>
      intro nextStore hnext
      obtain ⟨store, hstore⟩ := Refinement.reachable_store_exists hprevious
      have hwf := ih hstore
      cases hstep with
      | inject => exact ih (by simpa [System.inject] using hnext)
      | outside => exact ih (by simpa [System.observeOutside] using hnext)
      | @process pid now event result htime hprocess hvalid hresult =>
          by_cases hp : pid = .store
          · subst hp
            have hresult' := hresult
            rw [hstore] at hresult'
            have hput : ∀ sender op key document expected,
                event = .receive sender
                  (.storeRequest { op, payload := .put key document expected }) →
                expected = store.version key → DocumentOk key document := by
              intro sender op key document expected hevent hexpected
              subst hevent
              have hmem := hvalid
              obtain ⟨address, rfl⟩ := Refinement.reachable_store_request_sender hprevious hmem
              obtain ⟨provenance, hsnapshot⟩ :=
                Refinement.reachable_owned_put_snapshots hprevious hstore hmem
              have hread := Refinement.Snapshot.eq_of_version hsnapshot
                (provenance.expected_eq.trans hexpected)
              refine selected_ok provenance.selected ?_
              cases hloaded : provenance.loaded with
              | none => exact emptyDocument_ok key
              | some value =>
                  rw [hloaded] at hread
                  exact hwf key value.1 value.2 hread
            obtain ⟨store', hstate, hwf'⟩ := store_step_ok hwf hput hresult'
            have heq : Local.store nextStore = Local.store store' := by
              rw [← hnext, ← hstate]
              simp [System.land]
            cases heq
            exact hwf'
          · exact ih (by simpa [System.land, Ne.symm hp] using hnext)

end Resonate.Concrete
