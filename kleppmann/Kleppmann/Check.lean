import Kleppmann.World

/-!
# Checking a trace

The trace has every step but the system's. A **certificate** puts those
back: before each observed event, which requests the system received (the
`i`-th message on the network, with its `j`-th outcome) and which ticks it
took (the `j`-th tick outcome). `certify` replays trace and certificate
together and fails on the first step that cannot happen; `accepted_valid`
proves that what it accepts is valid.

`search` finds a certificate: before each observed event, up to `k` system
steps, every one tried. What it finds is checked the same way, so it is
sound by construction (`search_sound`).

The shape does the pruning a checker needs:

* a response a client receives must have been sent, so the system received
  that request somewhere between the client's sending it and receiving the
  answer: the linearization window is message causality, not a rule;
* each request is received once, so it is placed once;
* only outcomes whose response is the one observed survive the receive;
* ticks are tried where something is due, or where an observation needs them.
-/

namespace Kleppmann.World

variable {m : Model}

/-- A system step, as a certificate names it. -/
inductive Silent where
  /-- The system receives the `i`-th message on the network, with its `j`-th outcome. -/
  | recv (i j : Nat)
  /-- The system ticks, with its `j`-th tick outcome. -/
  | tick (j : Nat)
  deriving Repr

/-- For each event of the trace, the system's steps just before it. -/
abbrev Certificate := List (List Silent)

/-- One step of a replay: an event of the trace, or a system step. -/
inductive Move (m : Model) where
  | obs (p : Proc) (ev : Event m)
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

/-- `Owed`, computed. -/
def Conf.isOwed (c : Conf m) : Bool :=
  match m.due c.state with
  | some d => decide (d ≤ c.now) && !(m.tick c.state c.now).isEmpty
  | none => false

theorem not_owed {c : Conf m} (h : c.isOwed = false) : ¬ c.Owed := by
  rintro ⟨d, hd, hle, hne⟩
  simp only [Conf.isOwed, hd, decide_eq_true hle, Bool.true_and, Bool.not_eq_false',
    List.isEmpty_iff] at h
  exact hne h

/-- The same message from the system to a client: a response or a dispatch. -/
def sameOut : Msg m → Msg m → Bool
  | .res i r, .res i' r' => i == i' && @decide (r = r') (m.decRes r r')
  | .out d, .out d' => @decide (d = d') (m.decDis d d')
  | _, _ => false

theorem sameOut_eq {a b : Msg m} (h : sameOut a b = true) : a = b := by
  cases a <;> cases b <;> simp [sameOut] at h ⊢ <;> simp_all

/-- Where a step leads, given the network after it took its message. -/
def Conf.apply (c : Conf m) (p : Proc) (net' : Net m) (r : Result m) : Conf m :=
  ⟨net' ++ r.sent.map (fun (to, msg) => (p, to, msg)), r.next, r.now⟩

/-- One move from `c`: the step it makes and where it leads, if it can happen. -/
def Conf.move (c : Conf m) : Move m → Option ((Proc × Event m) × Conf m)
  | .obs (.client a) (.request id r) =>
      if c.isOwed then none
      else some ((.client a, .request id r), c.apply (.client a) c.net ⟨c.state, [(.sys, .req id r)], c.now⟩)
  | .obs (.client a) (.receive .sys msg) =>
      if c.isOwed then none else
      match splitAt? (fun e => e.1 == Proc.sys && e.2.1 == Proc.client a && sameOut e.2.2 msg) c.net with
      | some (pre, _, post) =>
          some ((.client a, .receive .sys msg), c.apply (.client a) (pre ++ post) ⟨c.state, [], c.now⟩)
      | none => none
  | .obs .clock (.time t) =>
      if decide (c.now ≤ t) && !c.isOwed then
        some ((.clock, .time t), c.apply .clock c.net ⟨c.state, [], t⟩)
      else none
  | .obs _ _ => none
  | .silent (.recv i j) =>
      if c.isOwed then none else
      match c.net[i]? with
      | some (.client a, .sys, .req id r) =>
          match (m.external r c.state c.now).val[j]? with
          | some o =>
              some ((.sys, .receive (.client a) (.req id r)),
                c.apply .sys (c.net.take i ++ c.net.drop (i + 1))
                  ⟨o.next, (.client a, .res id o.resp) :: outs o.send, c.now⟩)
          | none => none
      | _ => none
  | .silent (.tick j) =>
      match (m.tick c.state c.now)[j]? with
      | some o => some ((.sys, .timeout), c.apply .sys c.net ⟨o.next, outs o.send, c.now⟩)
      | none => none

/-- Every move `move` makes is a step of the rule. -/
theorem move_step {c c' : Conf m} {mv : Move m} {e : Proc × Event m}
    (h : c.move mv = some (e, c')) : Step m c e c' := by
  cases mv with
  | obs p ev =>
    cases p <;> cases ev <;> simp only [Conf.move, reduceCtorEq] at h
    · -- client receive
      rename_i a sender msg
      cases sender <;> simp only [Conf.move, reduceCtorEq] at h
      split at h <;> try simp at h
      split at h <;> try simp at h
      rename_i ho _ pre x post hsp
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := splitAt?_spec hsp
      obtain ⟨xs, xc, xm⟩ := x
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨rfl, rfl⟩, h3⟩ := h2
      have := sameOut_eq h3
      subst this
      have ho : c.isOwed = false := by simpa using ho
      have hT : Takes (.client a) (.receive .sys xm) (pre ++ (Proc.sys, Proc.client a, xm) :: post)
          (pre ++ post) := .receive
      rw [← h1] at hT
      exact .step hT (fun h => absurd h (not_owed ho)) (by simp [stepOf])
    · -- client request
      split at h <;> try simp at h
      rename_i ho
      obtain ⟨rfl, rfl⟩ := h
      have ho : c.isOwed = false := by simpa using ho
      exact .step .request (fun h => absurd h (not_owed ho)) (by simp [stepOf])
    · -- clock
      split at h <;> try simp at h
      rename_i hc
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
      exact .step .time (fun h => absurd h (not_owed hc.2)) (by simp [stepOf, hc.1])
  | silent s =>
    cases s with
    | recv i j =>
      simp only [Conf.move] at h
      split at h <;> try simp at h
      rename_i ho
      split at h <;> try simp at h
      rename_i a id r hi
      split at h <;> try simp at h
      rename_i o hj
      obtain ⟨rfl, rfl⟩ := h
      have ho : c.isOwed = false := by simpa using ho
      have hT : Takes .sys (.receive (.client a) (.req id r))
          (c.net.take i ++ (Proc.client a, Proc.sys, Msg.req id r) :: c.net.drop (i + 1))
          (c.net.take i ++ c.net.drop (i + 1)) := .receive
      rw [← split_at hi] at hT
      refine .step hT (fun h => absurd h (not_owed ho)) ?_
      simp only [stepOf, List.mem_map]
      exact ⟨o, List.mem_of_getElem? hj, rfl⟩
    | tick j =>
      simp only [Conf.move] at h
      split at h <;> try simp at h
      rename_i o hj
      obtain ⟨rfl, rfl⟩ := h
      refine .step .timeout (fun _ => ⟨rfl, rfl⟩) ?_
      simp only [stepOf, List.mem_map]
      exact ⟨o, List.mem_of_getElem? hj, rfl⟩

/-- What a move shows: an observed move shows its own event, at a process
    other than the system; a system step shows nothing. -/
def Move.shows : Move m → List (Proc × Event m)
  | .obs p ev => [(p, ev)]
  | .silent _ => []

theorem move_shows {c c' : Conf m} {mv : Move m} {e : Proc × Event m}
    (h : c.move mv = some (e, c')) : (if e.1 = .sys then [] else [e]) = mv.shows := by
  cases mv with
  | obs p ev =>
    cases p <;> cases ev <;> simp only [Conf.move, reduceCtorEq] at h <;>
      (try (rename_i _ sender _; cases sender <;> simp only [reduceCtorEq] at h)) <;>
      (repeat' split at h) <;> (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) <;>
      (try obtain ⟨rfl, -⟩ := h) <;> simp_all [Move.shows]
  | silent s =>
    cases s <;> simp only [Conf.move] at h <;> (repeat' split at h) <;>
      (try simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h) <;>
      (try obtain ⟨rfl, -⟩ := h) <;> simp_all [Move.shows]

/-! ## Replay and certificates -/

def replay (c : Conf m) : List (Move m) → Option (Execution m)
  | [] => some []
  | mv :: rest =>
      match c.move mv with
      | none => none
      | some (e, c') => (replay c' rest).map ((e, c') :: ·)

/-- The trace and a certificate as one list of moves. -/
def moves : List (Proc × Event m) → Certificate → List (Move m)
  | (p, ev) :: es, ss :: rest => ss.map .silent ++ .obs p ev :: moves es rest
  | _, _ => []

def certify (m : Model) (init : m.State) (trace : List (Proc × Event m)) (cert : Certificate) :
    Option (List (Proc × Event m)) :=
  (replay (initial init) (moves trace cert)).map observe

def Accepted (m : Model) (init : m.State) (trace : List (Proc × Event m)) : Prop :=
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
theorem accepted_valid {init : m.State} {trace : List (Proc × Event m)}
    (h : Accepted m init trace) : Valid m init trace := by
  obtain ⟨cert, hc⟩ := h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hc
  exact ⟨x, replay_legal hx, rfl⟩

/-! ## The search -/

/-- Every system step a configuration offers: receiving any request on the
    network, with any outcome; ticking, with any tick outcome. -/
def silents (c : Conf m) : List Silent :=
  ((List.range c.net.length).flatMap fun i =>
    match c.net[i]? with
    | some (_, Proc.sys, Msg.req _ r) => (List.range (m.external r c.state c.now).val.length).map (Silent.recv i)
    | _ => []) ++
  (List.range (m.tick c.state c.now).length).map Silent.tick

/-- A configuration and the moves that reached it, latest first. -/
abbrev Frontier (m : Model) := List (Conf m × List (Move m))

def next (fr : Frontier m) : Frontier m :=
  fr.flatMap fun dp =>
    (silents dp.1).filterMap fun s =>
      (dp.1.move (.silent s)).map fun ec => (ec.2, .silent s :: dp.2)

def explore : Nat → Frontier m → Frontier m
  | 0, fr => fr
  | k + 1, fr => fr ++ explore k (next fr)

def advance (p : Proc) (ev : Event m) (fr : Frontier m) : Frontier m :=
  fr.filterMap fun dp => (dp.1.move (.obs p ev)).map fun ec => (ec.2, .obs p ev :: dp.2)

def run (k : Nat) : List (Proc × Event m) → Frontier m → Frontier m
  | [], fr => fr
  | (p, ev) :: es, fr => run k es (advance p ev (explore k fr))

/-- Moves explaining the trace, with at most `k` system steps before each
    event, if the search finds them. -/
def search (m : Model) (init : m.State) (k : Nat) (trace : List (Proc × Event m)) :
    Option (List (Move m)) :=
  (run k trace [(initial init, [])]).head?.map fun dp => dp.2.reverse

/-! ### Soundness: what the search finds replays to the trace -/

def endOf (c : Conf m) : Execution m → Conf m
  | [] => c
  | (_, c') :: rest => endOf c' rest

theorem endOf_snoc (c : Conf m) (ex : Execution m) (ec : (Proc × Event m) × Conf m) :
    endOf c (ex ++ [ec]) = ec.2 := by
  induction ex generalizing c with
  | nil => rfl
  | cons x rest ih => exact ih x.2

theorem observe_append (x y : Execution m) : observe (x ++ y) = observe x ++ observe y := by
  induction x with
  | nil => rfl
  | cons ec rest ih =>
    obtain ⟨⟨p, ev⟩, c⟩ := ec
    simp only [List.cons_append, observe]
    split <;> simp [ih]

theorem replay_snoc {c₀ : Conf m} {mvs : List (Move m)} {ex : Execution m} {mv : Move m}
    {e : Proc × Event m} {c' : Conf m}
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
def Good (init : m.State) (pre : List (Proc × Event m)) (fr : Frontier m) : Prop :=
  ∀ dp ∈ fr, ∃ ex, replay (initial init) dp.2.reverse = some ex ∧
    observe ex = pre ∧ endOf (initial init) ex = dp.1

theorem good_step {init : m.State} {pre : List (Proc × Event m)} {dp : Conf m × List (Move m)}
    {mv : Move m} {e : Proc × Event m} {c' : Conf m}
    (hgood : ∃ ex, replay (initial init) dp.2.reverse = some ex ∧ observe ex = pre ∧
      endOf (initial init) ex = dp.1)
    (hmv : dp.1.move mv = some (e, c')) :
    ∃ ex, replay (initial init) (mv :: dp.2).reverse = some ex ∧
      observe ex = pre ++ mv.shows ∧ endOf (initial init) ex = c' := by
  obtain ⟨ex, hre, hob, hend⟩ := hgood
  refine ⟨ex ++ [(e, c')], ?_, ?_, endOf_snoc _ _ _⟩
  · rw [List.reverse_cons]; exact replay_snoc hre (hend ▸ hmv)
  · rw [observe_append, hob, ← move_shows hmv]
    obtain ⟨p, ev⟩ := e
    by_cases hp : p = .sys <;> simp [observe, hp]

theorem next_good {init : m.State} {pre : List (Proc × Event m)} {fr : Frontier m}
    (h : Good init pre fr) : Good init pre (next fr) := by
  intro cp hcp
  simp only [next, List.mem_flatMap, List.mem_filterMap] at hcp
  obtain ⟨dp, hdp, s, _, hcp⟩ := hcp
  obtain ⟨⟨e, c'⟩, hmv, rfl⟩ := Option.map_eq_some_iff.mp hcp
  simpa [Move.shows] using good_step (h dp hdp) hmv

theorem explore_good {init : m.State} {pre : List (Proc × Event m)} {k : Nat} {fr : Frontier m}
    (h : Good init pre fr) : Good init pre (explore k fr) := by
  induction k generalizing fr with
  | zero => exact h
  | succ k ih =>
    intro dp hdp
    simp only [explore, List.mem_append] at hdp
    rcases hdp with hdp | hdp
    · exact h dp hdp
    · exact ih (next_good h) dp hdp

theorem advance_good {init : m.State} {pre : List (Proc × Event m)} {p : Proc} {ev : Event m}
    {fr : Frontier m} (h : Good init pre fr) : Good init (pre ++ [(p, ev)]) (advance p ev fr) := by
  intro cp hcp
  simp only [advance, List.mem_filterMap] at hcp
  obtain ⟨dp, hdp, hcp⟩ := hcp
  obtain ⟨⟨e, c'⟩, hmv, rfl⟩ := Option.map_eq_some_iff.mp hcp
  simpa [Move.shows] using good_step (h dp hdp) hmv

theorem run_good {init : m.State} {pre : List (Proc × Event m)} {k : Nat}
    {es : List (Proc × Event m)} {fr : Frontier m} (h : Good init pre fr) :
    Good init (pre ++ es) (run k es fr) := by
  induction es generalizing pre fr with
  | nil => simpa [run] using h
  | cons e es ih =>
    obtain ⟨p, ev⟩ := e
    simp only [run]
    simpa using ih (advance_good (p := p) (ev := ev) (explore_good (k := k) h))

/-- Soundness: whatever the search finds is valid. -/
theorem search_sound {init : m.State} {k : Nat} {trace : List (Proc × Event m)}
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
def check (m : Model) (init : m.State) (k : Nat) (trace : List (Proc × Event m)) : Bool :=
  (search m init k trace).isSome

/-! ## A small model: a counter with a timer

`incr` adds one and answers the count; `arm` answers the count and arms a
timer five units out, which resets the count. The timer is state, and the
model says when it is due. -/

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
    | some t => if t ≤ now then [⟨(0, none), []⟩] else []
    | none => []
  due := fun (_, at_) => at_

open Proc in
def call (a : Client) (id : CallId) (req : Bool) (res : Nat) : List (Proc × Event timed) :=
  [(client a, .request id req), (client a, .receive sys (.res id res))]

-- Arm at 0, increment, the clock passes 5, increment: the timer reset the count.
#guard check timed (0, none) 2 (call "c" 1 false 0 ++ call "c" 2 true 1 ++ [(.clock, .time 9)] ++ call "c" 3 true 1)
-- Without the reset it would be 2: refuted, because the tick was due before the request.
#guard !check timed (0, none) 2 (call "c" 1 false 0 ++ call "c" 2 true 1 ++ [(.clock, .time 9)] ++ call "c" 3 true 2)
-- Not yet due at 4: the count is 2.
#guard check timed (0, none) 2 (call "c" 1 false 0 ++ call "c" 2 true 1 ++ [(.clock, .time 4)] ++ call "c" 3 true 2)
#guard !check timed (0, none) 2 (call "c" 1 false 0 ++ call "c" 2 true 1 ++ [(.clock, .time 4)] ++ call "c" 3 true 1)
-- Two clients, overlapping: either increment may take effect first.
#guard check timed (0, none) 3
  [(.client "a", .request 1 true), (.client "b", .request 2 true),
   (.client "b", .receive .sys (.res 2 1)), (.client "a", .receive .sys (.res 1 2))]
-- But not both first.
#guard !check timed (0, none) 3
  [(.client "a", .request 1 true), (.client "b", .request 2 true),
   (.client "b", .receive .sys (.res 2 1)), (.client "a", .receive .sys (.res 1 1))]
-- A response nobody asked for.
#guard !check timed (0, none) 3 [(.client "a", .receive .sys (.res 1 1))]
-- The clock does not go back.
#guard !check timed (0, none) 1 [(.clock, .time 9), (.clock, .time 4)]

end Kleppmann.World
