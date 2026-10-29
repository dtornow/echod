import Experiment.Fuzz

/-!
# Shell 4: many processes

Kleppmann's world with several processes, each at an address, each with
its own state, all running one service: his step function, the same for
every process, the state telling them apart. Clients as before: they send
what is typed in, to a process they name, and keep what they receive.

What a process sends goes to a process if one is at that address, and to a
client otherwise.

Executable only, for now: a schedule, and a fuzzer.
-/

namespace Experiment.Network

open Experiment (Service Input Out sends Time Addr Some pick lcg)

/-- Who steps. -/
inductive Who where
  | proc (a : Addr)
  | client (a : Addr)
  deriving DecidableEq, Repr

def Who.addr : Who → Addr
  | .proc a | .client a => a

inductive Event (M : Type) where
  | receive (sender : Who) (m : M)
  /-- A client sends `m` to the process at `to`. -/
  | request (to : Addr) (m : M)
  | timeout
  deriving DecidableEq, Repr

abbrev Label (M : Type) := Who × Time × Event M

variable {svc : Service}

structure Conf (svc : Service) where
  net    : List (Who × Who × svc.Msg)
  states : List (Addr × svc.State)
  now    : Time

def Conf.state? (c : Conf svc) (a : Addr) : Option svc.State :=
  (c.states.find? (·.1 == a)).map (·.2)

def Conf.isProc (c : Conf svc) (a : Addr) : Bool := c.states.any (·.1 == a)

def Conf.route (c : Conf svc) (a : Addr) : Who := if c.isProc a then .proc a else .client a

abbrev Execution (svc : Service) := List (Label svc.Msg × List (Out svc.Msg) × Conf svc)

inductive Act (M : Type) where
  | request (a : Addr) (to : Addr) (m : M)
  /-- Deliver the `i`-th message on the network; `j` picks the outcome. -/
  | deliver (i : Nat) (j : Nat := 0)
  | tick (a : Addr) (j : Nat := 0)

/-- Process `p` runs input `i` at `t` with outcome `j`. -/
def Conf.run (c : Conf svc) (cfg : svc.Config) (p : Addr) (t : Time) (i : Input svc.Msg) (j : Nat)
    (net : List (Who × Who × svc.Msg)) : Option (List (Out svc.Msg) × Conf svc) :=
  (c.state? p).map fun s =>
    let (s', outs) := pick (svc.step cfg s t i) j
    (outs, ⟨net ++ (sends outs).map (fun (to, m) => (.proc p, c.route to, m)),
            c.states.map (fun (a, x) => if a == p then (a, s') else (a, x)), t⟩)

def Conf.take (c : Conf svc) (cfg : svc.Config) (t : Time) :
    Act svc.Msg → Option (Label svc.Msg × List (Out svc.Msg) × Conf svc)
  | .request a to m =>
      if c.now ≤ t && c.isProc to then
        some ((.client a, t, .request to m), [], ⟨c.net ++ [(.client a, .proc to, m)], c.states, t⟩)
      else none
  | .deliver i j =>
      if c.now ≤ t then
        match c.net[i]? with
        | some (from_, .client a, m) =>
            some ((.client a, t, .receive from_ m), [], ⟨c.net.eraseIdx i, c.states, t⟩)
        | some (from_, .proc p, m) =>
            (c.run cfg p t (.msg from_.addr m) j (c.net.eraseIdx i)).map fun (o, c') =>
              ((.proc p, t, .receive from_ m), o, c')
        | none => none
      else none
  | .tick p j =>
      if c.now ≤ t then
        (c.run cfg p t .tick j c.net).map fun (o, c') => ((.proc p, t, .timeout), o, c')
      else none

/-- One executable network step.  `take` is the rule for this shell; retaining
    it as a proposition lets later proofs quantify over executions produced by
    any driver, rather than over one particular schedule. -/
def Step (svc : Service) (cfg : svc.Config) (c : Conf svc)
    (l : Label svc.Msg) (outs : List (Out svc.Msg)) (c' : Conf svc) : Prop :=
  ∃ t act, c.take cfg t act = some (l, outs, c')

/-- Every entry is a step from the configuration before it. -/
def Legal (svc : Service) (cfg : svc.Config) : Conf svc → Execution svc → Prop
  | _, [] => True
  | c, (l, outs, c') :: rest => Step svc cfg c l outs c' ∧ Legal svc cfg c' rest

def initial (states : List (Addr × svc.State)) : Conf svc := ⟨[], states, 0⟩

def run (cfg : svc.Config) (c : Conf svc) :
    List (Time × Act svc.Msg) → Option (Execution svc)
  | [] => some []
  | (t, a) :: rest => do
      let (l, o, c') ← c.take cfg t a
      let x ← run cfg c' rest
      return (l, o, c') :: x

def schedule (svc : Service) (cfg : svc.Config) (states : List (Addr × svc.State))
    (acts : List (Time × Act svc.Msg)) : Option (Execution svc) :=
  run cfg (initial states) acts

theorem run_legal {c : Conf svc} {acts : List (Time × Act svc.Msg)} {x : Execution svc}
    (h : run cfg c acts = some x) : Legal svc cfg c x := by
  induction acts generalizing c x with
  | nil =>
    simp [run] at h
    subst h
    trivial
  | cons ta rest ih =>
    obtain ⟨t, act⟩ := ta
    simp only [run] at h
    obtain ⟨⟨l, outs, c'⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨xs, hxs, h⟩ := Option.bind_eq_some_iff.mp h
    change some ((l, outs, c') :: xs) = some x at h
    simp only [Option.some.injEq] at h
    subst x
    exact ⟨⟨t, act, ht⟩, ih hxs⟩

/-- Every execution returned by `schedule` is legal. -/
theorem schedule_legal {states : List (Addr × svc.State)}
    {acts : List (Time × Act svc.Msg)} {x : Execution svc}
    (h : schedule svc cfg states acts = some x) :
    Legal svc cfg (initial states) x :=
  run_legal h

/-- A random execution: at each step a client sends one of `inputs` to a
    random one of `to`, or a message on the network is delivered; time
    moves on a little. -/
def fuzz (svc : Service) (cfg : svc.Config) (states : List (Addr × svc.State))
    (inputs : List (Addr × svc.Msg)) (to : List Addr) (seed n : Nat) : Execution svc :=
  go (initial states) seed n
where
  go (c : Conf svc) (r : Nat) : Nat → Execution svc
    | 0 => []
    | k + 1 =>
      let r₁ := lcg r
      let r₂ := lcg r₁
      let r₃ := lcg r₂
      let t := c.now + r₁ % 3
      let act : Option (Act svc.Msg) :=
        if r₁ / 3 % 3 == 0 then
          (inputs[r₂ % inputs.length]?).bind fun (a, m) =>
            (to[r₃ % to.length]?).map fun n => .request a n m
        else some (.deliver (r₂ % max 1 c.net.length) r₃)
      match act.bind (c.take cfg t) with
      | some (l, o, c') => (l, o, c') :: go c' r₃ k
      | none => go c r₃ k

def outs (x : Execution svc) : List (Out svc.Msg) := x.flatMap (·.2.1)

end Experiment.Network
