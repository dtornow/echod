import Experiment.Promise
import Experiment.Concurrent

/-!
# Framing promise handlers by key

Storage keeps one document per promise while the abstract service keeps all
promises in one state.  The bridge is that a request for `key` neither reads
nor changes promises with another id.  This file proves that frame property
directly for the handler code.
-/

namespace Experiment

def State.withFrame (s : State) (frame : List Promise) : State :=
  { promises := s.promises ++ frame }

def AwayFrom (key : Ident) (frame : List Promise) : Prop :=
  ∀ p ∈ frame, p.id ≠ key

def promiseAt (s : State) (key : Ident) : Option Promise :=
  s.promises.find? (·.id == key)

/-- States are equal as key-value stores; list order is irrelevant. -/
def SameState (a b : State) : Prop :=
  ∀ key, promiseAt a key = promiseAt b key

def SameOutcome (x y : α × State × List (Out Msg)) : Prop :=
  x.1 = y.1 ∧ SameState x.2.1 y.2.1 ∧ x.2.2 = y.2.2

/-- A handler is insensitive to the representation order of promises. -/
def RespectsState (h : Handler α) : Prop :=
  ∀ cfg a b, SameState a b → ∀ x ∈ (h cfg a).val,
    ∃ y ∈ (h cfg b).val, SameOutcome x y

theorem SameState.refl (s : State) : SameState s s := fun _ => rfl

theorem SameState.symm {a b : State} (h : SameState a b) : SameState b a :=
  fun key => (h key).symm

theorem RespectsState.pure (a : α) : RespectsState (Pure.pure a : Handler α) := by
  intro cfg s t hst x hx
  change x ∈ [(a, s, [])] at hx
  simp only [List.mem_singleton] at hx
  subst x
  refine ⟨(a, t, []), ?_, rfl, hst, rfl⟩
  change (a, t, []) ∈ [(a, t, [])]
  simp

theorem RespectsState.bind {x : Handler α} {f : α → Handler β}
    (hx : RespectsState x) (hf : ∀ a, RespectsState (f a)) :
    RespectsState (x >>= f) := by
  intro cfg s t hst out hout
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap, List.mem_map] at hout
  obtain ⟨⟨a, s₁, w₁⟩, h₁, ⟨b, s₂, w₂⟩, h₂, rfl⟩ := hout
  obtain ⟨⟨a', t₁, v₁⟩, h₁', ha, hs₁, hw₁⟩ := hx cfg s t hst _ h₁
  change a = a' at ha
  subst a'
  obtain ⟨⟨b', t₂, v₂⟩, h₂', hb, hs₂, hw₂⟩ := hf a cfg s₁ t₁ hs₁ _ h₂
  change b = b' at hb
  subst b'
  refine ⟨(b, t₂, v₁ ++ v₂), ?_, rfl, hs₂, ?_⟩
  · simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap, List.mem_map]
    exact ⟨(a, t₁, v₁), h₁', (b, t₂, v₂), h₂', rfl⟩
  · change w₁ = v₁ at hw₁
    change w₂ = v₂ at hw₂
    simp [hw₁, hw₂]

theorem RespectsState.read : RespectsState (read : Handler Config) := by
  intro cfg s t hst x hx
  change x ∈ [(cfg, s, [])] at hx
  simp only [List.mem_singleton] at hx
  subst x
  refine ⟨(cfg, t, []), ?_, rfl, hst, rfl⟩
  change (cfg, t, []) ∈ [(cfg, t, [])]
  simp

theorem RespectsState.readDefaultTimeout :
    RespectsState Experiment.readDefaultTimeout := by
  intro cfg s t hst x hx
  change x ∈ [(cfg.defaultTimeout, s, [])] at hx
  simp only [List.mem_singleton] at hx
  subst x
  refine ⟨(cfg.defaultTimeout, t, []), ?_, rfl, hst, rfl⟩
  change (cfg.defaultTimeout, t, []) ∈ [(cfg.defaultTimeout, t, [])]
  simp

theorem RespectsState.emit (o : Out Msg) : RespectsState (emit o : Handler Unit) := by
  intro cfg s t hst x hx
  change x ∈ [((), s, [o])] at hx
  simp only [List.mem_singleton] at hx
  subst x
  refine ⟨((), t, [o]), ?_, rfl, hst, rfl⟩
  change ((), t, [o]) ∈ [((), t, [o])]
  simp

theorem RespectsState.choose (xs : Some α) : RespectsState (choose xs : Handler α) := by
  intro cfg s t hst x hx
  change x ∈ xs.val.map (fun a => (a, s, [])) at hx
  simp only [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨(a, t, []), ?_, rfl, hst, rfl⟩
  change (a, t, []) ∈ xs.val.map (fun a => (a, t, []))
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

theorem find?_filter_other (xs : List Promise) {keep drop : Ident} (h : keep ≠ drop) :
    (xs.filter (·.id != drop)).find? (·.id == keep) = xs.find? (·.id == keep) := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    simp only [List.filter_cons, List.find?_cons]
    by_cases hd : p.id = drop
    · have hk : p.id ≠ keep := by
        intro he
        exact h (he.symm.trans hd)
      rw [show (p.id != drop) = false from bne_eq_false_iff_eq.mpr hd]
      rw [show (p.id == keep) = false from beq_eq_false_iff_ne.mpr hk]
      simp only [Bool.false_eq_true, if_false]
      exact ih
    · rw [show (p.id != drop) = true from bne_iff_ne.mpr hd]
      change (p :: rest.filter (·.id != drop)).find? (·.id == keep) =
        (p :: rest).find? (·.id == keep)
      by_cases hk : p.id = keep
      · rw [List.find?_cons, List.find?_cons,
          show (p.id == keep) = true from beq_iff_eq.mpr hk]
      · rw [List.find?_cons, List.find?_cons,
          show (p.id == keep) = false from beq_eq_false_iff_ne.mpr hk]
        exact ih

theorem promiseAt_saved (p : Promise) (s : State) (key : Ident) :
    promiseAt { promises := p :: s.promises.filter (·.id != p.id) } key =
      if key = p.id then some p else promiseAt s key := by
  by_cases h : key = p.id
  · subst key
    simp [promiseAt]
  · simp only [promiseAt, List.find?_cons]
    rw [show (p.id == key) = false from beq_eq_false_iff_ne.mpr (Ne.symm h)]
    rw [if_neg h]
    simp only
    exact find?_filter_other _ h

theorem SameState.saved (p : Promise) {a b : State} (h : SameState a b) :
    SameState ({ promises := p :: a.promises.filter (·.id != p.id) } : State)
      ({ promises := p :: b.promises.filter (·.id != p.id) } : State) := by
  intro key
  rw [promiseAt_saved, promiseAt_saved]
  split
  · rfl
  · exact h key

theorem RespectsState.save (p : Promise) : RespectsState (Experiment.save p) := by
  intro cfg s t hst x hx
  change x ∈ [((), ({ promises := p :: s.promises.filter (·.id != p.id) } : State), [])] at hx
  simp only [List.mem_singleton] at hx
  subst x
  refine ⟨((), ({ promises := p :: t.promises.filter (·.id != p.id) } : State), []),
    ?_, rfl, ?_, rfl⟩
  · change ((), ({ promises := p :: t.promises.filter (·.id != p.id) } : State), []) ∈
      [((), ({ promises := p :: t.promises.filter (·.id != p.id) } : State), [])]
    simp
  · exact hst.saved p

theorem RespectsState.lookup (key : Ident) : RespectsState (Experiment.lookup key) := by
  intro cfg s t hst x hx
  change x ∈ [(promiseAt s key, s, [])] at hx
  simp only [List.mem_singleton] at hx
  subst x
  refine ⟨(promiseAt t key, t, []), ?_, hst key, hst, rfl⟩
  change (promiseAt t key, t, []) ∈ [(promiseAt t key, t, [])]
  simp

theorem RespectsState.send (to : Addr) (m : Msg) :
    RespectsState (Experiment.send to m) :=
  RespectsState.emit _

theorem RespectsState.always (name : String) (ok : Bool) :
    RespectsState (Experiment.always name ok) :=
  RespectsState.emit _

def frameResult (frame : List Promise) (r : α × State × List (Out Msg)) :
    α × State × List (Out Msg) :=
  (r.1, r.2.1.withFrame frame, r.2.2)

/-- A handler has the same ordered outcomes with `frame` adjoined to every
resulting state. -/
def Frames (frame : List Promise) (h : Handler α) : Prop :=
  ∀ cfg s, (h cfg (s.withFrame frame)).val = (h cfg s).val.map (frameResult frame)

/-- Every return value of a handler has `P`. -/
def Returns (h : Handler α) (P : α → Prop) : Prop :=
  ∀ cfg s r, r ∈ (h cfg s).val → P r.1

theorem Returns.pure (a : α) (P : α → Prop) (h : P a) :
    Returns (Pure.pure a : Handler α) P := by
  intro cfg s r hr
  change r ∈ [(a, s, [])] at hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h

theorem Returns.bind_on {x : Handler α} {f : α → Handler β}
    {P : α → Prop} {Q : β → Prop}
    (hx : Returns x P) (hf : ∀ a, P a → Returns (f a) Q) :
    Returns (x >>= f) Q := by
  intro cfg s r hr
  simp only [Bind.bind, Some.bind, Some.map, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨⟨a, s₁, w₁⟩, h₁, ⟨b, s₂, w₂⟩, h₂, heq⟩ := hr
  have hb := hf a (hx cfg s _ h₁) cfg s₁ (b, s₂, w₂) h₂
  subst r
  exact hb

theorem Returns.bind {x : Handler α} {f : α → Handler β} {Q : β → Prop}
    (hf : ∀ a, Returns (f a) Q) : Returns (x >>= f) Q := by
  have hx : Returns x (fun _ => True) := by
    intro cfg s r hr
    trivial
  exact Returns.bind_on hx (fun a _ => hf a)

theorem Frames.pure (frame : List Promise) (a : α) :
    Frames frame (pure a : Handler α) := by
  intro cfg s
  rfl

theorem Frames.bind {frame : List Promise} {x : Handler α} {f : α → Handler β}
    (hx : Frames frame x) (hf : ∀ a, Frames frame (f a)) :
    Frames frame (x >>= f) := by
  intro cfg s
  simp only [Bind.bind, Some.bind, Some.map]
  rw [hx cfg s]
  simp only [List.flatMap_map]
  generalize (x cfg s).val = xs
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.flatMap_cons, List.map_append]
    rw [ih]
    obtain ⟨a, s', w⟩ := r
    simp only [frameResult]
    rw [hf a cfg s']
    simp [frameResult, Function.comp_def]

theorem Frames.bind_of {frame : List Promise} {x : Handler α} {f : α → Handler β}
    (hx : Frames frame x) (P : α → Prop)
    (hP : ∀ cfg s r, r ∈ (x cfg s).val → P r.1)
    (hf : ∀ a, P a → Frames frame (f a)) :
    Frames frame (x >>= f) := by
  intro cfg s
  simp only [Bind.bind, Some.bind, Some.map]
  rw [hx cfg s]
  simp only [List.flatMap_map]
  generalize hxs : (x cfg s).val = xs
  have hall : ∀ r ∈ xs, P r.1 := by
    intro r hr
    exact hP cfg s r (hxs ▸ hr)
  clear hxs
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    simp only [List.flatMap_cons, List.map_append]
    rw [ih (fun q hq => hall q (List.mem_cons_of_mem r hq))]
    obtain ⟨a, s', w⟩ := r
    simp only [frameResult]
    rw [hf a (hall (a, s', w) (List.mem_cons_self)) cfg s']
    simp [frameResult, Function.comp_def]

theorem Frames.read (frame : List Promise) : Frames frame (read : Handler Config) := by
  intro cfg s
  rfl

theorem Frames.readDefaultTimeout (frame : List Promise) :
    Frames frame Experiment.readDefaultTimeout := by
  intro cfg s
  rfl

theorem Frames.emit (frame : List Promise) (o : Out Msg) : Frames frame (emit o : Handler Unit) := by
  intro cfg s
  rfl

theorem Frames.send (frame : List Promise) (to : Addr) (m : Msg) :
    Frames frame (send to m) :=
  Frames.emit frame _

theorem Frames.always (frame : List Promise) (name : String) (ok : Bool) :
    Frames frame (always name ok) :=
  Frames.emit frame _

theorem Frames.choose (frame : List Promise) (xs : Some α) :
    Frames frame (choose xs : Handler α) := by
  intro cfg s
  change xs.val.map (fun a => (a, s.withFrame frame, [])) =
    (xs.val.map fun a => (a, s, [])).map (frameResult frame)
  simp [frameResult]

theorem find?_away {key : Ident} {frame : List Promise} (h : AwayFrom key frame) :
    frame.find? (·.id == key) = none := by
  rw [List.find?_eq_none]
  intro p hp heq
  exact h p hp (beq_iff_eq.mp heq)

theorem filter_away {key : Ident} {frame : List Promise} (h : AwayFrom key frame) :
    frame.filter (·.id != key) = frame := by
  apply List.filter_eq_self.mpr
  intro p hp
  exact bne_iff_ne.mpr (h p hp)

theorem save_frame (p : Promise) {frame : List Promise} (hf : AwayFrom p.id frame)
    (cfg : Config) (s : State) :
    (save p cfg (s.withFrame frame)).val =
      (save p cfg s).val.map fun (r, s', outs) => (r, s'.withFrame frame, outs) := by
  change [((), ({ promises := p :: (s.promises ++ frame).filter (·.id != p.id) } : State), [])] =
    [((), ({ promises := (p :: s.promises.filter (·.id != p.id)) ++ frame } : State), [])]
  rw [List.filter_append, filter_away hf]
  rfl

theorem Frames.save (p : Promise) {frame : List Promise} (hf : AwayFrom p.id frame) :
    Frames frame (save p) := by
  intro cfg s
  exact save_frame p hf cfg s

theorem Frames.lookup {key : Ident} {frame : List Promise} (hf : AwayFrom key frame) :
    Frames frame (lookup key) := by
  intro cfg s
  change [(List.find? (fun x => x.id == key) (s.promises ++ frame),
    s.withFrame frame, [])] =
    [(List.find? (fun x => x.id == key) s.promises, s.withFrame frame, [])]
  rw [List.find?_append, find?_away hf]
  simp

def AtKey (key : Ident) : Option Promise → Prop
  | none => True
  | some p => p.id = key

theorem lookup_atKey (key : Ident) (cfg : Config) (s : State) (r : Option Promise × State × List (Out Msg))
    (h : r ∈ (lookup key cfg s).val) : AtKey key r.1 := by
  change r ∈ [(s.promises.find? (·.id == key), s, [])] at h
  simp only [List.mem_singleton] at h
  subst r
  cases hf : s.promises.find? (·.id == key) with
  | none => trivial
  | some p =>
    have hp := List.find?_some hf
    exact beq_iff_eq.mp hp

theorem lookup_returns (key : Ident) : Returns (lookup key) (AtKey key) :=
  lookup_atKey key

theorem Frames.notifyAll (frame : List Promise) (p : Record) :
    ∀ addresses, Frames frame (notifyAll p addresses) := by
  intro addresses
  induction addresses with
  | nil => exact Frames.pure _ _
  | cons a rest ih =>
    exact Frames.bind (Frames.send frame _ _) fun _ => ih

theorem Frames.settle (p : Promise) (state : PromiseState) (value : String)
    {frame : List Promise} (hf : AwayFrom p.id frame) :
    Frames frame (Experiment.settle p state value) := by
  unfold Experiment.settle
  refine Frames.bind (Frames.always frame _ _) fun _ => ?_
  refine Frames.bind (Frames.always frame _ _) fun _ => ?_
  refine Frames.bind (Frames.save { p with state, value, listeners := [] } hf) fun _ => ?_
  refine Frames.bind (Frames.notifyAll frame _ _) fun _ => ?_
  exact Frames.pure _ _

theorem settle_returns (p : Promise) (state : PromiseState) (value : String) :
    Returns (Experiment.settle p state value) (fun q => q.id = p.id) := by
  unfold Experiment.settle
  apply Returns.bind
  intro _
  apply Returns.bind
  intro _
  apply Returns.bind
  intro _
  apply Returns.bind
  intro _
  exact Returns.pure _ _ rfl

theorem Frames.load {key : Ident} {frame : List Promise} (hf : AwayFrom key frame)
    (now : Time) : Frames frame (Experiment.load key now) := by
  unfold Experiment.load
  refine Frames.bind_of (Frames.lookup hf) (AtKey key) (lookup_atKey key) ?_
  intro doc hdoc
  cases doc with
  | none =>
    change Frames frame (Pure.pure none : Handler (Option Promise))
    exact Frames.pure _ _
  | some p =>
    have hp : p.id = key := hdoc
    change Frames frame
      (if p.state == .pending && decide (p.timeoutAt ≤ now) then
        do let p' ← Experiment.settle p .rejectedTimedout ""; return some p'
       else (Pure.pure (some p) : Handler (Option Promise)))
    split
    · refine Frames.bind (Frames.settle p .rejectedTimedout "" ?_) fun _ => Frames.pure _ _
      simpa [hp] using hf
    · exact Frames.pure _ _

theorem load_returns (key : Ident) (now : Time) :
    Returns (Experiment.load key now) (AtKey key) := by
  unfold Experiment.load
  refine Returns.bind_on (lookup_returns key) ?_
  intro doc hdoc
  cases doc with
  | none =>
    change Returns (Pure.pure none : Handler (Option Promise)) (AtKey key)
    exact Returns.pure _ _ trivial
  | some p =>
    change Returns
      (if p.state == .pending && decide (p.timeoutAt ≤ now) then
        do let p' ← Experiment.settle p .rejectedTimedout ""; return some p'
       else (Pure.pure (some p) : Handler (Option Promise)))
      (AtKey key)
    split
    · refine Returns.bind_on (settle_returns p .rejectedTimedout "") ?_
      intro p' hp'
      change p.id = key at hdoc
      exact Returns.pure _ _ (hp'.trans hdoc)
    · exact Returns.pure _ _ hdoc

theorem Frames.promiseGet {key : Ident} {frame : List Promise} (hf : AwayFrom key frame)
    (now : Time) : Frames frame (Experiment.promiseGet key now) := by
  unfold Experiment.promiseGet
  refine Frames.bind (Frames.load hf now) ?_
  intro doc
  cases doc <;> exact Frames.pure _ _

theorem Frames.promiseCreate {key : Ident} {frame : List Promise} (hf : AwayFrom key frame)
    (timeoutAt : Option Time) (now : Time) :
    Frames frame (Experiment.promiseCreate key timeoutAt now) := by
  unfold Experiment.promiseCreate
  refine Frames.bind_of (Frames.load hf now) (AtKey key) (load_returns key now) ?_
  intro doc hdoc
  cases doc with
  | some p =>
    refine Frames.bind (Frames.emit frame _) fun _ => Frames.pure _ _
  | none =>
    refine Frames.bind (Frames.readDefaultTimeout frame) fun defaultTimeout => ?_
    let deadline := timeoutAt.getD (now + defaultTimeout)
    let p : Promise :=
      { id := key, timeoutAt := deadline,
        state := if deadline ≤ now then .rejectedTimedout else .pending }
    refine Frames.bind (Frames.save p ?_) fun _ => Frames.pure _ _
    exact hf

theorem Frames.promiseSettle {key : Ident} {frame : List Promise} (hf : AwayFrom key frame)
    (state : PromiseState) (value : String) (now : Time) :
    Frames frame (Experiment.promiseSettle key state value now) := by
  unfold Experiment.promiseSettle
  split
  · exact Frames.pure _ _
  · refine Frames.bind (Frames.pure frame ()) fun _ => ?_
    refine Frames.bind_of (Frames.load hf now) (AtKey key) (load_returns key now) ?_
    intro doc hdoc
    cases doc with
    | none =>
      change Frames frame (Pure.pure { status := 404 } : Handler Response)
      exact Frames.pure _ _
    | some p =>
      change p.id = key at hdoc
      change Frames frame
        (if p.state == .pending then
          do let p' ← Experiment.settle p state value; return ok p'
         else do
          sometimes "settle arrives after the timeout" (p.state == .rejectedTimedout)
          return ok p)
      split
      · refine Frames.bind (Frames.settle p state value ?_) fun _ => Frames.pure _ _
        simpa [hdoc] using hf
      · refine Frames.bind (Frames.emit frame _) fun _ => Frames.pure _ _

theorem Frames.promiseListen {key : Ident} {frame : List Promise} (hf : AwayFrom key frame)
    (address : Addr) (now : Time) :
    Frames frame (Experiment.promiseListen key address now) := by
  unfold Experiment.promiseListen
  refine Frames.bind_of (Frames.load hf now) (AtKey key) (load_returns key now) ?_
  intro doc hdoc
  cases doc with
  | none =>
    change Frames frame (Pure.pure { status := 404 } : Handler Response)
    exact Frames.pure _ _
  | some p =>
    change p.id = key at hdoc
    change Frames frame
      (if p.state == .pending && !p.listeners.contains address then
        let p' := { p with listeners := p.listeners ++ [address] }
        do Experiment.save p'; return ok p'
       else Pure.pure (ok p))
    split
    · refine Frames.bind (Frames.save { p with listeners := p.listeners ++ [address] } ?_) fun _ =>
        Frames.pure _ _
      simpa [hdoc] using hf
    · exact Frames.pure _ _

theorem Frames.dispatch (r : Request) {frame : List Promise} (hf : AwayFrom r.key frame)
    (now : Time) : Frames frame (Experiment.dispatch r now) := by
  cases r with
  | get key => exact Frames.promiseGet hf now
  | create key timeoutAt => exact Frames.promiseCreate hf timeoutAt now
  | settle key state value => exact Frames.promiseSettle hf state value now
  | listen key address => exact Frames.promiseListen hf address now

theorem Frames.request (r : Request) {frame : List Promise} (hf : AwayFrom r.key frame)
    (now : Time) : Frames frame (Experiment.request r now) := by
  unfold Experiment.request
  refine Frames.bind (Frames.read frame) fun cfg => ?_
  split
  · refine Frames.bind (Frames.choose frame ⟨[Fate.serve, .shed, .lose], by simp⟩) ?_
    intro fate
    cases fate with
    | serve => exact Frames.dispatch r hf now
    | shed => exact Frames.pure _ _
    | lose =>
      refine Frames.bind (Frames.dispatch r hf now) fun _ => Frames.pure _ _
  · exact Frames.dispatch r hf now

/-- The membership form used by the storage refinement: a local handler
outcome is the same global outcome with untouched promises framed back in. -/
theorem request_frame_mem (r : Request) {frame : List Promise} (hf : AwayFrom r.key frame)
    (now : Time) (cfg : Config) (before after : State) (res : Response) (outs : List (Out Msg))
    (h : (res, after, outs) ∈ (Experiment.request r now cfg before).val) :
    (res, after.withFrame frame, outs) ∈
      (Experiment.request r now cfg (before.withFrame frame)).val := by
  have heq := Frames.request r hf now cfg before
  rw [heq]
  exact List.mem_map.mpr ⟨(res, after, outs), h, rfl⟩

theorem RespectsState.notifyAll (p : Record) :
    ∀ addresses, RespectsState (Experiment.notifyAll p addresses) := by
  intro addresses
  induction addresses with
  | nil => exact RespectsState.pure _
  | cons a rest ih =>
    exact RespectsState.bind (RespectsState.send _ _) fun _ => ih

theorem RespectsState.settle (p : Promise) (state : PromiseState) (value : String) :
    RespectsState (Experiment.settle p state value) := by
  unfold Experiment.settle
  refine RespectsState.bind (RespectsState.always _ _) fun _ => ?_
  refine RespectsState.bind (RespectsState.always _ _) fun _ => ?_
  refine RespectsState.bind (RespectsState.save { p with state, value, listeners := [] }) fun _ => ?_
  refine RespectsState.bind (RespectsState.notifyAll _ _) fun _ => ?_
  exact RespectsState.pure _

theorem RespectsState.load (key : Ident) (now : Time) :
    RespectsState (Experiment.load key now) := by
  unfold Experiment.load
  refine RespectsState.bind (RespectsState.lookup key) ?_
  intro doc
  cases doc with
  | none =>
    change RespectsState (Pure.pure none : Handler (Option Promise))
    exact RespectsState.pure _
  | some p =>
    change RespectsState
      (if p.state == .pending && decide (p.timeoutAt ≤ now) then
        do let p' ← Experiment.settle p .rejectedTimedout ""; return some p'
       else (Pure.pure (some p) : Handler (Option Promise)))
    split
    · refine RespectsState.bind (RespectsState.settle p .rejectedTimedout "") fun _ =>
        RespectsState.pure _
    · exact RespectsState.pure _

theorem RespectsState.promiseGet (key : Ident) (now : Time) :
    RespectsState (Experiment.promiseGet key now) := by
  unfold Experiment.promiseGet
  refine RespectsState.bind (RespectsState.load key now) ?_
  intro doc
  cases doc <;> exact RespectsState.pure _

theorem RespectsState.promiseCreate (key : Ident) (timeoutAt : Option Time) (now : Time) :
    RespectsState (Experiment.promiseCreate key timeoutAt now) := by
  unfold Experiment.promiseCreate
  refine RespectsState.bind (RespectsState.load key now) ?_
  intro doc
  cases doc with
  | some p =>
    refine RespectsState.bind (RespectsState.emit _) fun _ => RespectsState.pure _
  | none =>
    refine RespectsState.bind RespectsState.readDefaultTimeout fun defaultTimeout => ?_
    let deadline := timeoutAt.getD (now + defaultTimeout)
    let p : Promise :=
      { id := key, timeoutAt := deadline,
        state := if deadline ≤ now then .rejectedTimedout else .pending }
    refine RespectsState.bind (RespectsState.save p) fun _ => RespectsState.pure _

theorem RespectsState.promiseSettle (key : Ident) (state : PromiseState)
    (value : String) (now : Time) :
    RespectsState (Experiment.promiseSettle key state value now) := by
  unfold Experiment.promiseSettle
  split
  · exact RespectsState.pure _
  · refine RespectsState.bind (RespectsState.pure ()) fun _ => ?_
    refine RespectsState.bind (RespectsState.load key now) ?_
    intro doc
    cases doc with
    | none =>
      change RespectsState (Pure.pure { status := 404 } : Handler Response)
      exact RespectsState.pure _
    | some p =>
      change RespectsState
        (if p.state == .pending then
          do let p' ← Experiment.settle p state value; return ok p'
         else do
          sometimes "settle arrives after the timeout" (p.state == .rejectedTimedout)
          return ok p)
      split
      · refine RespectsState.bind (RespectsState.settle p state value) fun _ =>
          RespectsState.pure _
      · refine RespectsState.bind (RespectsState.emit _) fun _ => RespectsState.pure _

theorem RespectsState.promiseListen (key : Ident) (address : Addr) (now : Time) :
    RespectsState (Experiment.promiseListen key address now) := by
  unfold Experiment.promiseListen
  refine RespectsState.bind (RespectsState.load key now) ?_
  intro doc
  cases doc with
  | none =>
    change RespectsState (Pure.pure { status := 404 } : Handler Response)
    exact RespectsState.pure _
  | some p =>
    change RespectsState
      (if p.state == .pending && !p.listeners.contains address then
        let p' := { p with listeners := p.listeners ++ [address] }
        do Experiment.save p'; return ok p'
       else Pure.pure (ok p))
    split
    · refine RespectsState.bind
        (RespectsState.save { p with listeners := p.listeners ++ [address] }) fun _ =>
          RespectsState.pure _
    · exact RespectsState.pure _

theorem RespectsState.dispatch (r : Request) (now : Time) :
    RespectsState (Experiment.dispatch r now) := by
  cases r with
  | get key => exact RespectsState.promiseGet key now
  | create key timeoutAt => exact RespectsState.promiseCreate key timeoutAt now
  | settle key state value => exact RespectsState.promiseSettle key state value now
  | listen key address => exact RespectsState.promiseListen key address now

theorem RespectsState.request (r : Request) (now : Time) :
    RespectsState (Experiment.request r now) := by
  unfold Experiment.request
  refine RespectsState.bind RespectsState.read fun cfg => ?_
  split
  · refine RespectsState.bind
      (RespectsState.choose ⟨[Fate.serve, .shed, .lose], by simp⟩) ?_
    intro fate
    cases fate with
    | serve => exact RespectsState.dispatch r now
    | shed => exact RespectsState.pure _
    | lose =>
      refine RespectsState.bind (RespectsState.dispatch r now) fun _ => RespectsState.pure _
  · exact RespectsState.dispatch r now

/-- A single-key footprint, framed with all other promises, represents the
same key-value state as the original global state. -/
theorem footprint_frame_same (global : State) (key : Ident) (doc : Option Promise)
    (hdoc : promiseAt global key = doc) :
    SameState
      (({ promises := doc.toList } : State).withFrame
        (global.promises.filter (·.id != key)))
      global := by
  intro other
  have haway : AwayFrom key (global.promises.filter (·.id != key)) := by
    intro p hp
    exact bne_iff_ne.mp (List.mem_filter.mp hp).2
  by_cases h : other = key
  · subst other
    cases doc with
    | none =>
      change (global.promises.filter (·.id != key)).find? (·.id == key) =
        global.promises.find? (·.id == key)
      rw [find?_away haway]
      exact hdoc.symm
    | some p =>
      have hp : p.id = key := by
        have hf := List.find?_some hdoc
        exact beq_iff_eq.mp hf
      change (p :: global.promises.filter (·.id != key)).find? (·.id == key) =
        global.promises.find? (·.id == key)
      rw [List.find?_cons, show (p.id == key) = true from beq_iff_eq.mpr hp]
      exact hdoc.symm
  · cases doc with
    | none =>
      change (global.promises.filter (·.id != key)).find? (·.id == other) =
        global.promises.find? (·.id == other)
      exact find?_filter_other _ h
    | some p =>
      have hp : p.id = key := by
        have hf := List.find?_some hdoc
        exact beq_iff_eq.mp hf
      have hpo : p.id ≠ other := by
        intro he
        exact h (he.symm.trans hp)
      change (p :: global.promises.filter (·.id != key)).find? (·.id == other) =
        global.promises.find? (·.id == other)
      rw [List.find?_cons, show (p.id == other) = false from beq_eq_false_iff_ne.mpr hpo]
      exact find?_filter_other _ h

/-- Lift a handler outcome computed on one loaded document to any global
state that represents the same document at the request's key. -/
theorem request_transport (r : Request) (now : Time) (cfg : Config)
    (global localAfter : State) (doc : Option Promise)
    (res : Response) (outs : List (Out Msg))
    (hdoc : promiseAt global r.key = doc)
    (hout : (res, localAfter, outs) ∈
      (Experiment.request r now cfg { promises := doc.toList }).val) :
    ∃ globalAfter,
      (res, globalAfter, outs) ∈ (Experiment.request r now cfg global).val ∧
      SameState
        (localAfter.withFrame (global.promises.filter (·.id != r.key)))
        globalAfter := by
  let frame := global.promises.filter (·.id != r.key)
  have haway : AwayFrom r.key frame := by
    intro p hp
    exact bne_iff_ne.mp (List.mem_filter.mp hp).2
  have hframed := request_frame_mem r haway now cfg { promises := doc.toList }
    localAfter res outs hout
  have hsame := footprint_frame_same global r.key doc hdoc
  obtain ⟨⟨res', globalAfter, outs'⟩, hglobal, hres, hstate, houts⟩ :=
    RespectsState.request r now cfg _ _ hsame _ hframed
  change res = res' at hres
  change outs = outs' at houts
  subst res'
  subst outs'
  exact ⟨globalAfter, hglobal, hstate⟩

end Experiment
