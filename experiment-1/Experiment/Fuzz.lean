import Experiment.Concurrent

/-!
# Shell 3: fuzzing

The concurrent world again, driven by a seed instead of a schedule: at
each step a client sends one of the given messages, a message on the
network is delivered, or the server is ticked, and time moves on a
little. Where a handler chooses, the seed chooses. The run is an
execution of the concurrent shell, so everything proved there holds of
it; what this shell adds is the assertions the handlers emitted.
-/

namespace Experiment

variable {svc : Service}

def lcg (x : Nat) : Nat := (x * 1103515245 + 12345) % 2147483648

/-- A random execution of up to `n` steps. -/
def fuzz (svc : Service) (cfg : svc.Config) (s : svc.State)
    (inputs : List (Addr × svc.Msg)) (seed n : Nat) : Execution svc :=
  go (initial s) seed n
where
  go (c : Conf svc) (r : Nat) : Nat → Execution svc
    | 0 => []
    | k + 1 =>
      let r₁ := lcg r
      let r₂ := lcg r₁
      let r₃ := lcg r₂
      let t := c.now + r₁ % 5
      let act : Option (Act svc.Msg) :=
        match r₁ / 5 % 4 with
        | 0 | 1 => (inputs[r₂ % inputs.length]?).map fun (a, m) => .request a m
        | 2 => some (.deliver (r₂ % max 1 c.net.length) r₃)
        | _ => some (.tick r₃)
      match act.bind (c.take cfg t) with
      | some (l, o, c') => (l, o, c') :: go c' r₃ k
      | none => go c r₃ k

/-- Everything emitted along an execution. -/
def outs (x : Execution svc) : List (Out svc.Msg) := x.flatMap (·.2.1)

end Experiment
