import Experiment.Service

/-!
# Shell 1: sequential

The service alone in the world. Inputs arrive one at a time, in order, at
instants that never go back; whatever it sends is simply what comes out.
No network, no other processes, no concurrency. This is the shell to
think in, and the specification the concurrent shell is held to.
-/

namespace Experiment

variable {svc : Service}

/-- From state `s`, no earlier than `lo`, these inputs can make the service
    send exactly these messages, in this order. -/
inductive SeqRun (svc : Service) (cfg : svc.Config) :
    Time → svc.State → List (Time × Input svc.Msg) → List (Addr × svc.Msg) → Prop where
  | nil {lo s} : SeqRun svc cfg lo s [] []
  | cons {lo s t i r rest out} :
      lo ≤ t → r ∈ (svc.step cfg s t i).val → SeqRun svc cfg t r.1 rest out →
      SeqRun svc cfg lo s ((t, i) :: rest) (sends r.2 ++ out)

/-- Every run, computed: each final state with everything emitted. -/
def runs (svc : Service) (cfg : svc.Config) (s : svc.State) :
    List (Time × Input svc.Msg) → List (svc.State × List (Out svc.Msg))
  | [] => [(s, [])]
  | (t, i) :: rest =>
      (svc.step cfg s t i).val.flatMap fun (s', outs) =>
        (runs svc cfg s' rest).map fun (s'', outs') => (s'', outs ++ outs')

end Experiment
