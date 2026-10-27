import Experiment.Handler

/-!
# The contract between handlers and shells

A service is what a developer writes: its configuration, its state, its
messages, and two handlers, Kleppmann's step function split by event: a
message arrives from a sender, or a tick. A **shell** runs a service: it
decides where inputs come from, where sent messages go, when time moves,
and what is observed. The handlers never know which shell they are in.

Every shell runs a handler call as one atomic step: it can order calls,
not look inside one.
-/

namespace Experiment

structure Service where
  Config  : Type
  State   : Type
  Msg     : Type
  receive : Addr → Msg → Time → H Config State (Out Msg) Unit
  tick    : Time → H Config State (Out Msg) Unit

/-- What a shell hands a service: a message from a sender, or a tick. -/
inductive Input (M : Type) where
  | msg (sender : Addr) (m : M)
  | tick
  deriving DecidableEq, Repr

/-- Every outcome of one input at `t`: the next state, and what was emitted. -/
def Service.step (svc : Service) (cfg : svc.Config) (s : svc.State) (t : Time) :
    Input svc.Msg → Some (svc.State × List (Out svc.Msg))
  | .msg a m => ((svc.receive a m t).run cfg s).map fun (_, s', outs) => (s', outs)
  | .tick    => ((svc.tick t).run cfg s).map fun (_, s', outs) => (s', outs)

end Experiment
