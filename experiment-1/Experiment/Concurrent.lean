import Experiment.Sequential

/-!
# Shell 2: concurrent

The service as one process among many, in Kleppmann's world: a server
running the service's handlers, clients at addresses, and a network of
messages sent and not yet received. The environment decides who steps
next; every step happens at an instant no earlier than the last. A client
sends what is typed in and keeps what it receives; a message is received at
most once.

A step is labelled with what happened and what the server emitted, so the
assertions a handler makes are there to collect in this shell too.

**The theorems.** Whatever happens in this world, the server's steps, in
the order it took them, are a run of the sequential shell sending exactly
what it sent here (`server_seq`), and causality holds: the server only
takes a request its client sent before (`request_before`), and a client
only receives what the server sent before (`answer_before`). That is the
sequential shell explaining the concurrent one, proved once for every
service.
-/

namespace Experiment

inductive Proc where
  | server
  | client (a : Addr)
  deriving DecidableEq, Repr

/-- Kleppmann's events. -/
inductive Event (M : Type) where
  | receive (sender : Proc) (m : M)
  | request (m : M)
  | timeout
  deriving DecidableEq, Repr

/-- Messages sent and not yet received: (sender, recipient, message). -/
abbrev Net (M : Type) := List (Proc × Proc × M)

/-- Which process, when, what. -/
abbrev Label (M : Type) := Proc × Time × Event M

variable {svc : Service} {cfg : svc.Config}

structure Conf (svc : Service) where
  net   : Net svc.Msg
  state : svc.State
  /-- The instant of the last step. -/
  now   : Time

/-- What a step puts on the network: a client's request goes to the server;
    what the server sends goes to the clients it names. -/
def emits {M : Type} : Proc → Event M → List (Out M) → Net M
  | .client a, .request m, _ => [(.client a, .server, m)]
  | .server, _, outs => (sends outs).map fun (to, m) => (.server, .client to, m)
  | _, _, _ => []

/-- **The rule**: one step, and what it emitted. -/
inductive Step (svc : Service) (cfg : svc.Config) :
    Conf svc → Label svc.Msg → List (Out svc.Msg) → Conf svc → Prop where
  /-- A client sends a request. -/
  | request {c a t m} : c.now ≤ t →
      Step svc cfg c (.client a, t, .request m) [] ⟨c.net ++ [(.client a, .server, m)], c.state, t⟩
  /-- A client receives what the server sent it. -/
  | deliver {c a t m pre post} : c.now ≤ t → c.net = pre ++ (.server, .client a, m) :: post →
      Step svc cfg c (.client a, t, .receive .server m) [] ⟨pre ++ post, c.state, t⟩
  /-- The server receives a client's message: the service's `receive`. -/
  | receive {c a t m pre post r} : c.now ≤ t → c.net = pre ++ (.client a, .server, m) :: post →
      r ∈ (svc.step cfg c.state t (.msg a m)).val →
      Step svc cfg c (.server, t, .receive (.client a) m) r.2
        ⟨pre ++ post ++ emits .server (.receive (.client a) m) r.2, r.1, t⟩
  /-- The server is ticked: the service's `tick`. -/
  | tick {c t r} : c.now ≤ t → r ∈ (svc.step cfg c.state t .tick).val →
      Step svc cfg c (.server, t, .timeout) r.2 ⟨c.net ++ emits .server .timeout r.2, r.1, t⟩

abbrev Execution (svc : Service) := List (Label svc.Msg × List (Out svc.Msg) × Conf svc)

def Legal (svc : Service) (cfg : svc.Config) : Conf svc → Execution svc → Prop
  | _, [] => True
  | c, (l, o, c') :: rest => Step svc cfg c l o c' ∧ Legal svc cfg c' rest

def endOf : Conf svc → Execution svc → Conf svc
  | c, [] => c
  | _, (_, _, c') :: rest => endOf c' rest

def initial (s : svc.State) : Conf svc := ⟨[], s, 0⟩

/-! ## What the server did -/

/-- The server's inputs, in the order it took them. -/
def serverInputs : Execution svc → List (Time × Input svc.Msg)
  | [] => []
  | ((.server, t, .receive (.client a) m), _, _) :: rest => (t, .msg a m) :: serverInputs rest
  | ((.server, t, .timeout), _, _) :: rest => (t, .tick) :: serverInputs rest
  | _ :: rest => serverInputs rest

/-- Everything sent, in order. Only the server's steps send through `Out`. -/
def serverSends : Execution svc → List (Addr × svc.Msg)
  | [] => []
  | (_, o, _) :: rest => sends o ++ serverSends rest

/-- **The sequential shell explains the server.** -/
theorem server_seq {c : Conf svc} {x : Execution svc} {lo : Time}
    (h : Legal svc cfg c x) (hlo : lo ≤ c.now) :
    SeqRun svc cfg lo c.state (serverInputs x) (serverSends x) := by
  induction x generalizing c lo with
  | nil => exact .nil
  | cons e rest ih =>
    obtain ⟨l, o, c'⟩ := e
    obtain ⟨hs, hr⟩ := h
    cases hs with
    | request ht =>
      simpa [serverInputs, serverSends, sends] using ih hr (Nat.le_trans hlo ht)
    | deliver ht _ =>
      simpa [serverInputs, serverSends, sends] using ih hr (Nat.le_trans hlo ht)
    | receive ht _ hr' =>
      simp only [serverInputs, serverSends]
      exact .cons (Nat.le_trans hlo ht) hr' (ih hr (Nat.le_refl _))
    | tick ht hr' =>
      simp only [serverInputs, serverSends]
      exact .cons (Nat.le_trans hlo ht) hr' (ih hr (Nat.le_refl _))

/-! ## Causality -/

/-- Everything put on the network, in order. -/
def emitted : Execution svc → Net svc.Msg
  | [] => []
  | ((p, _, ev), o, _) :: rest => emits p ev o ++ emitted rest

theorem legal_append {c : Conf svc} {x y : Execution svc} (h : Legal svc cfg c (x ++ y)) :
    Legal svc cfg c x ∧ Legal svc cfg (endOf c x) y := by
  induction x generalizing c with
  | nil => exact ⟨trivial, h⟩
  | cons e rest ih =>
    obtain ⟨l, o, c'⟩ := e
    obtain ⟨hs, hr⟩ := h
    exact ⟨⟨hs, (ih hr).1⟩, (ih hr).2⟩

/-- What is on the network was there to begin with, or was sent. -/
theorem net_sent {c : Conf svc} {x : Execution svc} (h : Legal svc cfg c x) :
    ∀ e ∈ (endOf c x).net, e ∈ c.net ∨ e ∈ emitted x := by
  induction x generalizing c with
  | nil => intro e he; exact .inl he
  | cons st rest ih =>
    obtain ⟨l, o, c'⟩ := st
    obtain ⟨hs, hr⟩ := h
    intro e he
    simp only [endOf] at he
    rcases ih hr e he with h1 | h1
    · cases hs with
      | request _ =>
        simp only [List.mem_append, List.mem_singleton] at h1
        rcases h1 with h1 | h1
        · exact .inl h1
        · subst h1; exact .inr (by simp [emitted, emits])
      | deliver _ hn =>
        left; rw [hn]; simp only [List.mem_append, List.mem_cons] at h1 ⊢; rcases h1 with h1 | h1 <;> simp [h1]
      | receive _ hn _ =>
        simp only [List.mem_append] at h1
        rcases h1 with (h1 | h1) | h1
        · left; rw [hn]; simp [h1]
        · left; rw [hn]; simp [h1]
        · exact .inr (by simp only [emitted, List.mem_append]; exact .inl h1)
      | tick _ _ =>
        simp only [List.mem_append] at h1
        rcases h1 with h1 | h1
        · exact .inl h1
        · exact .inr (by simp only [emitted, List.mem_append]; exact .inl h1)
    · exact .inr (by simp only [emitted, List.mem_append]; exact .inr h1)

/-- A message to the server on the network was a client's request. -/
theorem emitted_to_server {x : Execution svc} {a : Addr} {m : svc.Msg}
    (h : (Proc.client a, Proc.server, m) ∈ emitted x) :
    ∃ t o c, ((Proc.client a, t, Event.request m), o, c) ∈ x := by
  induction x with
  | nil => simp [emitted] at h
  | cons st rest ih =>
    obtain ⟨⟨p, t, ev⟩, o, c⟩ := st
    simp only [emitted, List.mem_append] at h
    rcases h with h | h
    · cases p <;> cases ev <;> simp [emits] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t, o, c, by simp⟩
    · obtain ⟨t', o', c', hm⟩ := ih h
      exact ⟨t', o', c', List.mem_cons_of_mem _ hm⟩

/-- A message to a client on the network was sent by the server. -/
theorem emitted_to_client {x : Execution svc} {a : Addr} {m : svc.Msg}
    (h : (Proc.server, Proc.client a, m) ∈ emitted x) :
    ∃ t ev o c, ((Proc.server, t, ev), o, c) ∈ x ∧ (a, m) ∈ sends o := by
  induction x with
  | nil => simp [emitted] at h
  | cons st rest ih =>
    obtain ⟨⟨p, t, ev⟩, o, c⟩ := st
    simp only [emitted, List.mem_append] at h
    rcases h with h | h
    · cases p with
      | server =>
        simp only [emits, List.mem_map] at h
        obtain ⟨⟨a', m'⟩, hs, he⟩ := h
        simp only [Prod.mk.injEq, Proc.client.injEq, true_and] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨t, ev, o, c, List.mem_cons_self .., hs⟩
      | client b => cases ev <;> simp [emits] at h
    · obtain ⟨t', ev', o', c', hm, hs⟩ := ih h
      exact ⟨t', ev', o', c', List.mem_cons_of_mem _ hm, hs⟩

/-- **The server only takes a request its client sent before.** -/
theorem request_before {s : svc.State} {x₁ x₂ : Execution svc} {t : Time} {a : Addr}
    {m : svc.Msg} {o : List (Out svc.Msg)} {c' : Conf svc}
    (h : Legal svc cfg (initial s) (x₁ ++ ((.server, t, .receive (.client a) m), o, c') :: x₂)) :
    ∃ t' o' c'', ((Proc.client a, t', Event.request m), o', c'') ∈ x₁ := by
  obtain ⟨h₁, h₂, -⟩ := legal_append h
  have hin : ∀ c₀, Step svc cfg c₀ (.server, t, .receive (.client a) m) o c' →
      (Proc.client a, Proc.server, m) ∈ c₀.net := by
    intro c₀ hs
    cases hs with
    | receive _ hn _ => rw [hn]; simp
  rcases net_sent h₁ _ (hin _ h₂) with h | h
  · simp [initial] at h
  · exact emitted_to_server h

/-- **A client only receives what the server sent it before.** -/
theorem answer_before {s : svc.State} {x₁ x₂ : Execution svc} {t : Time} {a : Addr}
    {m : svc.Msg} {o : List (Out svc.Msg)} {c' : Conf svc}
    (h : Legal svc cfg (initial s) (x₁ ++ ((.client a, t, .receive .server m), o, c') :: x₂)) :
    ∃ t' ev o' c'', ((Proc.server, t', ev), o', c'') ∈ x₁ ∧ (a, m) ∈ sends o' := by
  obtain ⟨h₁, h₂, -⟩ := legal_append h
  have hin : ∀ c₀, Step svc cfg c₀ (.client a, t, .receive .server m) o c' →
      (Proc.server, Proc.client a, m) ∈ c₀.net := by
    intro c₀ hs
    cases hs with
    | deliver _ hn => rw [hn]; simp
  rcases net_sent h₁ _ (hin _ h₂) with h | h
  · simp [initial] at h
  · exact emitted_to_client h

/-! ## What is observed -/

/-- Every step but the server receiving: when it took a request is hidden. -/
def seen : Label svc.Msg → Bool
  | (.server, _, .receive _ _) => false
  | _ => true

def observe : Execution svc → List (Label svc.Msg)
  | [] => []
  | (l, _, _) :: rest => if seen l then l :: observe rest else observe rest

def Valid (svc : Service) (cfg : svc.Config) (s : svc.State) (trace : List (Label svc.Msg)) : Prop :=
  ∃ x, Legal svc cfg (initial s) x ∧ observe x = trace

/-! ## Running it: a schedule -/

/-- One choice of the environment. `j` picks among the server's outcomes,
    modulo how many there are: any `j` is a choice. -/
inductive Act (M : Type) where
  | request (a : Addr) (m : M)
  /-- Deliver the `i`-th message on the network. -/
  | deliver (i : Nat) (j : Nat := 0)
  | tick (j : Nat := 0)

def pick {α : Type} (xs : Some α) (j : Nat) : α :=
  xs.val[j % xs.val.length]'(Nat.mod_lt _ (List.length_pos_iff.mpr xs.property))

theorem pick_mem {α : Type} (xs : Some α) (j : Nat) : pick xs j ∈ xs.val :=
  List.getElem_mem ..

/-- One step at `t`, if the environment can make it. -/
def Conf.take (c : Conf svc) (cfg : svc.Config) (t : Time) :
    Act svc.Msg → Option (Label svc.Msg × List (Out svc.Msg) × Conf svc)
  | .request a m =>
      if c.now ≤ t then some ((.client a, t, .request m), [], ⟨c.net ++ [(.client a, .server, m)], c.state, t⟩)
      else none
  | .deliver i j =>
      if c.now ≤ t then
        match c.net[i]? with
        | some (.server, .client a, m) =>
            some ((.client a, t, .receive .server m), [], ⟨c.net.eraseIdx i, c.state, t⟩)
        | some (.client a, .server, m) =>
            let r := pick (svc.step cfg c.state t (.msg a m)) j
            some ((.server, t, .receive (.client a) m), r.2,
              ⟨c.net.eraseIdx i ++ emits .server (.receive (.client a) m) r.2, r.1, t⟩)
        | _ => none
      else none
  | .tick j =>
      if c.now ≤ t then
        let r := pick (svc.step cfg c.state t .tick) j
        some ((.server, t, .timeout), r.2, ⟨c.net ++ emits .server .timeout r.2, r.1, t⟩)
      else none

theorem split_at {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l = l.take i ++ a :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

/-- The executable scheduler takes only steps admitted by the rule. -/
theorem take_step {c c' : Conf svc} {cfg : svc.Config} {t : Time}
    {act : Act svc.Msg} {l : Label svc.Msg} {outs : List (Out svc.Msg)}
    (h : c.take cfg t act = some (l, outs, c')) :
    Step svc cfg c l outs c' := by
  cases act with
  | request a m =>
    simp only [Conf.take] at h
    split at h <;> try simp at h
    rename_i ht
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .request ht
  | deliver i j =>
    simp only [Conf.take] at h
    split at h <;> try simp at h
    rename_i ht
    split at h <;> try simp at h
    · rename_i a m hi
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.eraseIdx_eq_take_drop_succ]
      exact .deliver ht (split_at hi)
    · rename_i a m hi
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [List.eraseIdx_eq_take_drop_succ]
      exact .receive ht (split_at hi) (pick_mem _ _)
  | tick j =>
    simp only [Conf.take] at h
    split at h <;> try simp at h
    rename_i ht
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact .tick ht (pick_mem _ _)

def runSchedule (cfg : svc.Config) (c : Conf svc) :
    List (Time × Act svc.Msg) → Option (Execution svc)
  | [] => some []
  | (t, a) :: rest => do
      let (l, o, c') ← c.take cfg t a
      let x ← runSchedule cfg c' rest
      return (l, o, c') :: x

theorem runSchedule_legal {c : Conf svc} {cfg : svc.Config}
    {acts : List (Time × Act svc.Msg)} {x : Execution svc}
    (h : runSchedule cfg c acts = some x) : Legal svc cfg c x := by
  induction acts generalizing c x with
  | nil =>
    simp [runSchedule] at h
    subst h
    trivial
  | cons ta rest ih =>
    obtain ⟨t, act⟩ := ta
    simp only [runSchedule] at h
    obtain ⟨⟨l, outs, c'⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    change some ((l, outs, c') :: xs) = some x at h
    simp only [Option.some.injEq] at h
    subst x
    exact ⟨take_step ht, ih hxs⟩

/-- Run a schedule from the start; `none` if a step cannot be made. -/
def schedule (svc : Service) (cfg : svc.Config) (s : svc.State) (acts : List (Time × Act svc.Msg)) :
    Option (Execution svc) :=
  runSchedule cfg (initial s) acts

theorem schedule_legal {cfg : svc.Config} {s : svc.State}
    {acts : List (Time × Act svc.Msg)} {x : Execution svc}
    (h : schedule svc cfg s acts = some x) : Legal svc cfg (initial s) x :=
  runSchedule_legal h

theorem valid_of_schedule {cfg : svc.Config} {s : svc.State}
    {acts : List (Time × Act svc.Msg)} {x : Execution svc} {trace : List (Label svc.Msg)}
    (hs : schedule svc cfg s acts = some x) (ho : observe x = trace) :
    Valid svc cfg s trace :=
  ⟨x, schedule_legal hs, ho⟩

end Experiment
