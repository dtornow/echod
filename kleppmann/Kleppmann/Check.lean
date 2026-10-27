import Kleppmann.World

/-!
# Checking a trace

Everything is in the trace but one kind of step: the server receiving a
request. A **certificate** puts those back: before each observed event,
which requests the server took (the `i`-th message on the network, with its
`j`-th outcome), and, for the event itself, which of its outcomes it had
(only a server's tick can have more than one). A hidden step happens at the
instant of the step before it: between observed events, time stands still.
That is an assumption of the checker, not of the model; `Valid` allows any
instant in between.

`certify` replays trace and certificate; `accepted_valid` proves that what
it accepts is valid. `search` finds a certificate, trying every order in
which the server could have taken the requests outstanding at each point,
up to `k` before each event; what it finds is checked the same way
(`search_sound`).

Where the window for a request comes from: its answer can only be received
after it was sent, which was when the server took the request, which was
after the client sent it. Message causality; no rule says so.
-/

namespace Kleppmann.World

variable {m : Model}

/-- A hidden step: the server receives the `i`-th message on the network,
    with its `j`-th outcome. -/
structure Silent where
  i : Nat
  j : Nat
  deriving Repr

/-- For each event of the trace: the hidden steps just before it, and which
    of its outcomes it had. -/
abbrev Certificate := List (List Silent × Nat)

/-- One step of a replay. -/
inductive Move (m : Model) where
  | obs (p : Proc) (t : Time) (ev : Event m) (j : Nat)
  | silent (s : Silent)

/-- The first element satisfying `p`, with what is before and after it. -/
def splitAt? {α : Type} (p : α → Bool) : List α → Option (List α × α × List α)
  | [] => none
  | x :: xs => if p x then some ([], x, xs) else (splitAt? p xs).map fun (pre, y, post) => (x :: pre, y, post)

theorem splitAt?_spec {α : Type} {p : α → Bool} {l pre post : List α} {x : α}
    (h : splitAt? p l = some (pre, x, post)) : l = pre ++ x :: post ∧ p x = true := by
  induction l generalizing pre with
  | nil => simp [splitAt?] at h
  | cons y ys ih =>
    simp only [splitAt?] at h
    split at h
    · rename_i hy
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hy⟩
    · obtain ⟨⟨pre', z, post'⟩, hz, he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨h1, h2⟩ := ih hz
      exact ⟨by simp [h1], h2⟩

theorem split_at {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l = l.take i ++ a :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

/-- The same message from the server to a client: a response or a dispatch. -/
def sameOut : Msg m → Msg m → Bool
  | .res i r, .res i' r' => i == i' && @decide (r = r') (m.decRes r r')
  | .out d, .out d' => @decide (d = d') (m.decDis d d')
  | _, _ => false

theorem sameOut_eq {a b : Msg m} (h : sameOut a b = true) : a = b := by
  cases a <;> cases b <;> simp [sameOut] at h ⊢ <;> simp_all

/-- Where a step leads, given the network after it took its message. -/
def land (p : Proc) (t : Time) (net' : Net m) (r : Result m) : Conf m :=
  ⟨net' ++ r.sent.map (fun (to, msg) => (p, to, msg)), r.next, t⟩

/-- One move from `c`: the step it makes and where it leads, if it can happen. -/
def Conf.move (c : Conf m) : Move m → Option ((Proc × Time × Event m) × Conf m)
  | .obs (.client a) t (.request id r) _ =>
      if c.now ≤ t then
        some ((.client a, t, .request id r), land (.client a) t c.net ⟨c.state, [(.server, .req id r)]⟩)
      else none
  | .obs (.client a) t (.receive .server msg) _ =>
      if c.now ≤ t then
        match splitAt? (fun e => e.1 == Proc.server && e.2.1 == Proc.client a && sameOut e.2.2 msg) c.net with
        | some (pre, _, post) =>
            some ((.client a, t, .receive .server msg), land (.client a) t (pre ++ post) ⟨c.state, []⟩)
        | none => none
      else none
  | .obs .server t .timeout j =>
      if c.now ≤ t then
        match (m.tick c.state t).val[j]? with
        | some o => some ((.server, t, .timeout), land .server t c.net ⟨o.next, outs o.send⟩)
        | none => none
      else none
  | .obs _ _ _ _ => none
  | .silent ⟨i, j⟩ =>
      match c.net[i]? with
      | some (Proc.client a, Proc.server, Msg.req id r) =>
          match (m.external r c.state c.now).val[j]? with
          | some o =>
              some ((.server, c.now, .receive (.client a) (.req id r)),
                land .server c.now (c.net.take i ++ c.net.drop (i + 1))
                  ⟨o.next, (.client a, .res id o.resp) :: outs o.send⟩)
          | none => none
      | _ => none

/-- Every move `move` makes is a step of the rule. -/
theorem move_step {c c' : Conf m} {mv : Move m} {e : Proc × Time × Event m}
    (h : c.move mv = some (e, c')) : Step m c e c' := by
  cases mv with
  | obs p t ev j =>
    cases p <;> cases ev <;> simp only [Conf.move, reduceCtorEq] at h
    · -- server timeout
      split at h <;> try simp at h
      rename_i ht
      split at h <;> try simp at h
      rename_i o hj
      obtain ⟨rfl, rfl⟩ := h
      refine .step ht .timeout ?_
      simp only [stepOf, List.mem_map]
      exact ⟨o, List.mem_of_getElem? hj, rfl⟩
    · -- client receive
      rename_i a sender msg
      cases sender <;> simp only [reduceCtorEq] at h
      split at h <;> try simp at h
      rename_i ht
      split at h <;> try simp at h
      rename_i pre x post hsp
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := splitAt?_spec hsp
      obtain ⟨xs, xc, xm⟩ := x
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨rfl, rfl⟩, h3⟩ := h2
      have := sameOut_eq h3
      subst this
      have hT : Takes (.client a) (.receive .server xm) (pre ++ (Proc.server, Proc.client a, xm) :: post)
          (pre ++ post) := .receive
      rw [← h1] at hT
      exact .step ht hT (by simp [stepOf])
    · -- client request
      split at h <;> try simp at h
      rename_i ht
      obtain ⟨rfl, rfl⟩ := h
      exact .step ht .request (by simp [stepOf])
  | silent s =>
    obtain ⟨i, j⟩ := s
    simp only [Conf.move] at h
    split at h <;> try simp at h
    rename_i a id r hi
    split at h <;> try simp at h
    rename_i o hj
    obtain ⟨rfl, rfl⟩ := h
    have hT : Takes .server (.receive (.client a) (.req id r))
        (c.net.take i ++ (Proc.client a, Proc.server, Msg.req id r) :: c.net.drop (i + 1))
        (c.net.take i ++ c.net.drop (i + 1)) := .receive
    rw [← split_at hi] at hT
    refine .step (Nat.le_refl _) hT ?_
    simp only [stepOf, List.mem_map]
    exact ⟨o, List.mem_of_getElem? hj, rfl⟩

/-- What a move shows: an observed move its event; a hidden one nothing. -/
def Move.shows : Move m → List (Proc × Time × Event m)
  | .obs p t ev _ => [(p, t, ev)]
  | .silent _ => []

theorem move_shows {c c' : Conf m} {mv : Move m} {e : Proc × Time × Event m}
    (h : c.move mv = some (e, c')) : (if Event.seenAt e.1 e.2.2 then [e] else []) = mv.shows := by
  cases mv with
  | obs p t ev j =>
    cases p <;> cases ev <;> simp only [Conf.move, reduceCtorEq] at h <;>
      (try (rename_i _ sender _; cases sender <;> simp only [reduceCtorEq] at h)) <;>
      (repeat' split at h) <;> (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) <;>
      (try obtain ⟨rfl, -⟩ := h) <;> simp_all [Move.shows, Event.seenAt]
  | silent s =>
    obtain ⟨i, j⟩ := s
    simp only [Conf.move] at h
    (repeat' split at h) <;> (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) <;>
      (try obtain ⟨rfl, -⟩ := h) <;> simp_all [Move.shows, Event.seenAt]

/-! ## Replay and certificates -/

def replay (c : Conf m) : List (Move m) → Option (Execution m)
  | [] => some []
  | mv :: rest =>
      match c.move mv with
      | none => none
      | some (e, c') => (replay c' rest).map ((e, c') :: ·)

/-- The trace and a certificate as one list of moves. -/
def moves : List (Proc × Time × Event m) → Certificate → List (Move m)
  | (p, t, ev) :: es, (ss, j) :: rest => ss.map .silent ++ .obs p t ev j :: moves es rest
  | _, _ => []

def certify (m : Model) (init : m.State) (trace : List (Proc × Time × Event m)) (cert : Certificate) :
    Option (List (Proc × Time × Event m)) :=
  (replay (initial init) (moves trace cert)).map observe

def Accepted (m : Model) (init : m.State) (trace : List (Proc × Time × Event m)) : Prop :=
  ∃ cert, certify m init trace cert = some trace

theorem replay_legal {c : Conf m} {mvs : List (Move m)} {x : Execution m}
    (h : replay c mvs = some x) : Legal m c x := by
  induction mvs generalizing c x with
  | nil => simp [replay] at h; subst h; trivial
  | cons mv rest ih =>
    simp only [replay] at h
    split at h
    · simp at h
    · rename_i e c' hmv
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      exact ⟨move_step hmv, ih hy⟩

/-- Checking a certificate is enough: what it accepts is valid. -/
theorem accepted_valid {init : m.State} {trace : List (Proc × Time × Event m)}
    (h : Accepted m init trace) : Valid m init trace := by
  obtain ⟨cert, hc⟩ := h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact ⟨x, replay_legal hx, rfl⟩

/-! ## The search -/

/-- Every request on the network the server could take now, with every outcome. -/
def silents (c : Conf m) : List Silent :=
  (List.range c.net.length).flatMap fun i =>
    match c.net[i]? with
    | some (_, Proc.server, Msg.req _ r) =>
        (List.range (m.external r c.state c.now).val.length).map (Silent.mk i)
    | _ => []

/-- The outcomes an observed event may have: a server tick, any of its
    outcomes; anything else, its one. -/
def choices (c : Conf m) (p : Proc) (t : Time) (ev : Event m) : List Nat :=
  match p, ev with
  | .server, .timeout => List.range (m.tick c.state t).val.length
  | _, _ => [0]

/-- A configuration and the moves that reached it, latest first. -/
abbrev Frontier (m : Model) := List (Conf m × List (Move m))

def next (fr : Frontier m) : Frontier m :=
  fr.flatMap fun dp =>
    (silents dp.1).filterMap fun s =>
      (dp.1.move (.silent s)).map fun ec => (ec.2, .silent s :: dp.2)

def explore : Nat → Frontier m → Frontier m
  | 0, fr => fr
  | k + 1, fr => fr ++ explore k (next fr)

def advance (p : Proc) (t : Time) (ev : Event m) (fr : Frontier m) : Frontier m :=
  fr.flatMap fun dp =>
    (choices dp.1 p t ev).filterMap fun j =>
      (dp.1.move (.obs p t ev j)).map fun ec => (ec.2, .obs p t ev j :: dp.2)

def run (k : Nat) : List (Proc × Time × Event m) → Frontier m → Frontier m
  | [], fr => fr
  | (p, t, ev) :: es, fr => run k es (advance p t ev (explore k fr))

/-- Moves explaining the trace, with at most `k` hidden steps before each
    event, if the search finds them. -/
def search (m : Model) (init : m.State) (k : Nat) (trace : List (Proc × Time × Event m)) :
    Option (List (Move m)) :=
  (run k trace [(initial init, [])]).head?.map fun dp => dp.2.reverse

/-! ### Soundness: what the search finds replays to the trace -/

def endOf (c : Conf m) : Execution m → Conf m
  | [] => c
  | (_, c') :: rest => endOf c' rest

theorem endOf_snoc (c : Conf m) (ex : Execution m) (ec : (Proc × Time × Event m) × Conf m) :
    endOf c (ex ++ [ec]) = ec.2 := by
  induction ex generalizing c with
  | nil => rfl
  | cons x rest ih => exact ih x.2

theorem observe_append (x y : Execution m) : observe (x ++ y) = observe x ++ observe y := by
  induction x with
  | nil => rfl
  | cons ec rest ih =>
    obtain ⟨⟨p, t, ev⟩, c⟩ := ec
    simp only [List.cons_append, observe]
    split <;> simp [ih]

theorem replay_snoc {c₀ : Conf m} {mvs : List (Move m)} {ex : Execution m} {mv : Move m}
    {e : Proc × Time × Event m} {c' : Conf m}
    (h : replay c₀ mvs = some ex) (hm : (endOf c₀ ex).move mv = some (e, c')) :
    replay c₀ (mvs ++ [mv]) = some (ex ++ [(e, c')]) := by
  induction mvs generalizing c₀ ex with
  | nil =>
    simp only [replay, Option.some.injEq] at h
    subst h
    simp [replay, endOf] at hm ⊢
    simp [hm]
  | cons mv₁ rest ih =>
    simp only [replay] at h
    split at h
    · simp at h
    · rename_i e₁ c₁ hmv₁
      obtain ⟨ex', hex', rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [List.cons_append, replay, hmv₁]
      rw [ih hex' hm]
      rfl

/-- Every entry replays to the trace so far and ends where it says. -/
def Good (init : m.State) (pre : List (Proc × Time × Event m)) (fr : Frontier m) : Prop :=
  ∀ dp ∈ fr, ∃ ex, replay (initial init) dp.2.reverse = some ex ∧
    observe ex = pre ∧ endOf (initial init) ex = dp.1

theorem good_step {init : m.State} {pre : List (Proc × Time × Event m)} {dp : Conf m × List (Move m)}
    {mv : Move m} {e : Proc × Time × Event m} {c' : Conf m}
    (hgood : ∃ ex, replay (initial init) dp.2.reverse = some ex ∧ observe ex = pre ∧
      endOf (initial init) ex = dp.1)
    (hmv : dp.1.move mv = some (e, c')) :
    ∃ ex, replay (initial init) (mv :: dp.2).reverse = some ex ∧
      observe ex = pre ++ mv.shows ∧ endOf (initial init) ex = c' := by
  obtain ⟨ex, hre, hob, hend⟩ := hgood
  refine ⟨ex ++ [(e, c')], ?_, ?_, endOf_snoc _ _ _⟩
  · rw [List.reverse_cons]; exact replay_snoc hre (hend ▸ hmv)
  · rw [observe_append, hob, ← move_shows hmv]
    obtain ⟨p, t, ev⟩ := e
    by_cases hs : Event.seenAt p ev <;> simp [observe, hs]

theorem next_good {init : m.State} {pre : List (Proc × Time × Event m)} {fr : Frontier m}
    (h : Good init pre fr) : Good init pre (next fr) := by
  intro cp hcp
  simp only [next, List.mem_flatMap, List.mem_filterMap] at hcp
  obtain ⟨dp, hdp, s, _, hcp⟩ := hcp
  obtain ⟨⟨e, c'⟩, hmv, rfl⟩ := Option.map_eq_some_iff.mp hcp
  simpa [Move.shows] using good_step (h dp hdp) hmv

theorem explore_good {init : m.State} {pre : List (Proc × Time × Event m)} {k : Nat} {fr : Frontier m}
    (h : Good init pre fr) : Good init pre (explore k fr) := by
  induction k generalizing fr with
  | zero => exact h
  | succ k ih =>
    intro dp hdp
    simp only [explore, List.mem_append] at hdp
    rcases hdp with hdp | hdp
    · exact h dp hdp
    · exact ih (next_good h) dp hdp

theorem advance_good {init : m.State} {pre : List (Proc × Time × Event m)} {p : Proc} {t : Time}
    {ev : Event m} {fr : Frontier m} (h : Good init pre fr) :
    Good init (pre ++ [(p, t, ev)]) (advance p t ev fr) := by
  intro cp hcp
  simp only [advance, List.mem_flatMap, List.mem_filterMap] at hcp
  obtain ⟨dp, hdp, j, _, hcp⟩ := hcp
  obtain ⟨⟨e, c'⟩, hmv, rfl⟩ := Option.map_eq_some_iff.mp hcp
  simpa [Move.shows] using good_step (h dp hdp) hmv

theorem run_good {init : m.State} {pre : List (Proc × Time × Event m)} {k : Nat}
    {es : List (Proc × Time × Event m)} {fr : Frontier m} (h : Good init pre fr) :
    Good init (pre ++ es) (run k es fr) := by
  induction es generalizing pre fr with
  | nil => simpa [run] using h
  | cons e es ih =>
    obtain ⟨p, t, ev⟩ := e
    simp only [run]
    simpa using ih (advance_good (p := p) (t := t) (ev := ev) (explore_good (k := k) h))

/-- Soundness: whatever the search finds is valid. -/
theorem search_sound {init : m.State} {k : Nat} {trace : List (Proc × Time × Event m)}
    {mvs : List (Move m)} (h : search m init k trace = some mvs) : Valid m init trace := by
  simp only [search] at h
  obtain ⟨dp, hhead, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem : dp ∈ run k trace [(initial init, [])] :=
    List.mem_of_mem_head? (Option.mem_def.mpr hhead)
  have hgood : Good init [] [(initial init, [])] := by
    intro dp hdp
    simp only [List.mem_singleton] at hdp
    subst hdp
    exact ⟨[], rfl, rfl, rfl⟩
  obtain ⟨ex, hre, hob, _⟩ := run_good (k := k) (es := trace) hgood dp hmem
  exact ⟨ex, replay_legal hre, by simpa using hob⟩

/-- The verdict, computed. -/
def check (m : Model) (init : m.State) (k : Nat) (trace : List (Proc × Time × Event m)) : Bool :=
  (search m init k trace).isSome

/-- Where the server took each request, as the search found it: for each
    hidden step, the client and the request id. -/
def explain (m : Model) (init : m.State) (k : Nat) (trace : List (Proc × Time × Event m)) :
    Option (List String) :=
  (search m init k trace).map fun mvs =>
    let rec go (c : Conf m) : List (Move m) → List String
      | [] => []
      | mv :: rest =>
        match c.move mv with
        | none => []
        | some ((p, t, ev), c') =>
          let line := match p, ev with
            | .server, .receive (.client a) (.req id _) => s!"  at {t}: server takes {a}'s request {id}"
            | .server, .timeout => s!"t={t}: server tick"
            | .client a, .request id _ => s!"t={t}: {a} sends request {id}"
            | .client a, .receive _ (.res id _) => s!"t={t}: {a} receives the answer to {id}"
            | .client a, .receive _ (.out _) => s!"t={t}: {a} receives a dispatch"
            | _, _ => s!"t={t}: ?"
          line :: go c' rest
    go (initial init) mvs

/-! ## A small model: a counter with a timer

`incr` adds one and answers the count; `arm` answers the count and arms a
timer five units out. A tick at or after that time resets the count. -/

/-- The count, and when the armed timer fires. -/
abbrev Counter := Nat × Option Time

abbrev timed : Model where
  State    := Counter
  Request  := Bool                -- true: increment; false: arm
  Response := Nat
  Dispatch := Empty
  external := fun req (n, at_) now =>
    if req then .one ⟨(n + 1, at_), n + 1, []⟩ else .one ⟨(n, some (now + 5)), n, []⟩
  tick := fun (n, at_) now =>
    match at_ with
    | some t => if t ≤ now then .one ⟨(0, none), []⟩ else .one ⟨(n, at_), []⟩
    | none => .one ⟨(n, none), []⟩

open Proc in
def call (a : Client) (t : Time) (id : CallId) (req : Bool) (res : Nat) : List (Proc × Time × Event timed) :=
  [(client a, t, .request id req), (client a, t, .receive server (.res id res))]

def tick (t : Time) : List (Proc × Time × Event timed) := [(.server, t, .timeout)]

-- Arm at 0, increment, a tick at 9, increment: the tick reset the count.
#guard check timed (0, none) 2 (call "c" 0 1 false 0 ++ call "c" 0 2 true 1 ++ tick 9 ++ call "c" 9 3 true 1)
#guard !check timed (0, none) 2 (call "c" 0 1 false 0 ++ call "c" 0 2 true 1 ++ tick 9 ++ call "c" 9 3 true 2)
-- A tick at 4 is too early to reset.
#guard check timed (0, none) 2 (call "c" 0 1 false 0 ++ call "c" 0 2 true 1 ++ tick 4 ++ call "c" 4 3 true 2)
-- No tick, no reset, however late: the server only acts when ticked.
#guard check timed (0, none) 2 (call "c" 0 1 false 0 ++ call "c" 0 2 true 1 ++ call "c" 9 3 true 2)
-- Two clients, overlapping: either increment may take effect first, but not both.
#guard check timed (0, none) 3
  [(.client "a", 0, .request 1 true), (.client "b", 0, .request 2 true),
   (.client "b", 0, .receive .server (.res 2 1)), (.client "a", 0, .receive .server (.res 1 2))]
#guard !check timed (0, none) 3
  [(.client "a", 0, .request 1 true), (.client "b", 0, .request 2 true),
   (.client "b", 0, .receive .server (.res 2 1)), (.client "a", 0, .receive .server (.res 1 1))]
-- A response nobody asked for.
#guard !check timed (0, none) 3 [(.client "a", 0, .receive .server (.res 1 1))]
-- Time does not go back.
#guard !check timed (0, none) 1 (tick 9 ++ tick 4)

end Kleppmann.World
