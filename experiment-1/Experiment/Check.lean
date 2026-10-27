import Experiment.Concurrent

/-!
# Checking a trace against a service

Could this trace of the concurrent shell have happened? The trace is
every step but the server receiving a request; the search puts those back.
Before each observed event it tries every set of requests the server could
have taken, in every order, with every outcome, keeping the
configurations it reaches: each once, the earliest of those that differ only
in time, and forgetting answers no later step receives. A hidden step happens at the
instant of the step before it or at the instant of the event after it:
which instant in between makes no difference a handler could see, as
long as a handler reads time only by comparing it with instants it holds
(a deadline is either passed at both ends of an interval it is not in, or
not passed at either).

Hidden steps are tried only while something is still to be received:
after the last receive nothing can tell whether, or how, a request took
effect.

Executable; the steps it takes are `Conf.take`'s, not proved against `Step`.
-/

namespace Experiment

variable {svc : Service} [DecidableEq svc.Msg] [DecidableEq svc.State]

/-- Of two configurations with the same network and state, the earlier
    can do everything the later can: keep it. -/
def dedup (cs : List (Conf svc)) : List (Conf svc) :=
  cs.foldl (init := []) fun acc c =>
    match acc.findIdx? fun d => d.net == c.net && d.state == c.state with
    | some i => if c.now < (acc[i]?.map (·.now)).getD 0 then acc.set i c else acc
    | none => acc ++ [c]

/-- Forget what the server sent that no later step receives: it cannot be
    seen, and configurations that differ only there are the same. -/
def prune (later : List (Label svc.Msg)) (c : Conf svc) : Conf svc :=
  { c with net := c.net.filter fun
      | (.server, .client a, m) => later.any fun
          | (.client b, _, .receive .server m') => a == b && m == m'
          | _ => false
      | _ => true }

/-- One hidden step from `c`: the server takes any request on the network,
    with any outcome, now or at `t`. -/
def hidden (cfg : svc.Config) (later : List (Label svc.Msg)) (t : Time) (c : Conf svc) :
    List (Conf svc) :=
  (List.range c.net.length).flatMap fun i =>
    match c.net[i]? with
    | some (Proc.client a, Proc.server, m) =>
      [c.now, t].eraseDups.flatMap fun t' =>
        (List.range (svc.step cfg c.state t' (.msg a m)).val.length).filterMap fun j =>
          (c.take cfg t' (.deliver i j)).map fun s => prune later s.2.2
    | _ => []

/-- Every configuration reachable by hidden steps (up to `fuel` of them). -/
def closure (cfg : svc.Config) (later : List (Label svc.Msg)) (t : Time) :
    Nat → List (Conf svc) → List (Conf svc)
  | 0, cs => cs
  | fuel + 1, cs =>
    let more := dedup (cs ++ cs.flatMap (hidden cfg later t))
    if more.length == cs.length && more.all (fun c => cs.any fun d => d.net == c.net && d.state == c.state && d.now == c.now)
    then cs else closure cfg later t fuel more

/-- An observed event, from `c`: every way it can happen. -/
def observed (cfg : svc.Config) (c : Conf svc) : Label svc.Msg → List (Conf svc)
  | (.client a, t, .request m) => ((c.take cfg t (.request a m)).map (·.2.2)).toList
  | (.client a, t, .receive .server m) =>
    match c.net.findIdx? (· == (.server, .client a, m)) with
    | some i => ((c.take cfg t (.deliver i)).map (·.2.2)).toList
    | none => []
  | (.server, t, .timeout) =>
    (List.range (svc.step cfg c.state t .tick).val.length).filterMap fun j =>
      (c.take cfg t (.tick j)).map (·.2.2)
  | _ => []

/-- Whether a step is something received: what constrains hidden steps. -/
def receives : Label svc.Msg → Bool
  | (_, _, .receive _ _) => true
  | _ => false

/-- Whether some execution of the concurrent shell shows exactly `trace`
    (as far as the search sees: at most `fuel` hidden steps between events).
    Once nothing more is received, hidden steps cannot be seen, and none
    are tried. -/
def check (svc : Service) [DecidableEq svc.Msg] [DecidableEq svc.State] (cfg : svc.Config)
    (s : svc.State) (trace : List (Label svc.Msg)) (fuel : Nat := 16) : Bool :=
  let rec go (cs : List (Conf svc)) : List (Label svc.Msg) → Bool
    | [] => !cs.isEmpty
    | e :: rest =>
      let before := if (e :: rest).any receives then closure cfg (e :: rest) e.2.1 fuel cs else cs
      let next := dedup (before.flatMap fun c => (observed cfg c e).map (prune rest))
      !next.isEmpty && go next rest
  go [initial s] trace

end Experiment
