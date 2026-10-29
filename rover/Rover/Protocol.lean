import Rover.World
import Experiment.Promise

/-!
# Rover's shared promise protocol

The abstract service and the concrete server/store deployment use the same
client calls and boundary messages.  The promise data and handlers are reused
from experiment 1 (through experiment 2's path dependency); Rover supplies the
append-only transport and a boundary type that does not expose internal
process identifiers.
-/

namespace Rover.Protocol

abbrev Addr := Experiment.Addr
abbrev CallId := Experiment.CallId
abbrev Request := Experiment.Request
abbrev Response := Experiment.Response
abbrev Notification := Experiment.Record
abbrev PromiseState := Experiment.PromiseState
abbrev Promise := Experiment.Promise
abbrev State := Experiment.State
abbrev Config := Experiment.Config

/-- A complete client call. `requestedAt` is protocol data and remains stable
when a delayed or retried operation is eventually applied. -/
structure Call where
  client : Addr
  id : CallId
  requestedAt : Time
  request : Request
  deriving DecidableEq, Repr

/-- Messages emitted by the service. Requests are deliberately absent, which
prevents an internal result from manufacturing a new injectable call. -/
inductive Output where
  | response (client : Addr) (id : CallId) (response : Response)
  | notification (client : Addr) (record : Notification)
  deriving DecidableEq, Repr

/-- Messages crossing the system boundary. -/
inductive Message where
  | request (call : Call)
  | output (output : Output)
  deriving DecidableEq, Repr

/-- Process-independent observations used by both Rover models. -/
inductive BoundaryEvent where
  | request (time : Time) (call : Call)
  | response (time : Time) (client : Addr) (id : CallId) (response : Response)
  | notification (time : Time) (client : Addr) (record : Notification)
  deriving DecidableEq, Repr

def Message.observeInput (time : Time) : Message → Option BoundaryEvent
  | .request call => some (.request time call)
  | _ => none

def Message.observeOutput (time : Time) : Message → Option BoundaryEvent
  | .output (.response client id response) =>
      some (.response time client id response)
  | .output (.notification client record) =>
      some (.notification time client record)
  | .request _ => none

/-- Translate the promise handler's sends to clean Rover boundary messages.
Assertions remain internal proof/checking instrumentation. -/
def outputs (outs : List (Experiment.Out Experiment.Msg)) : List Output :=
  outs.filterMap fun
    | .send client (.res id response) => some (.response client id response)
    | .send client (.notify record) => some (.notification client record)
    | _ => none

/-- Every abstract result of applying one request to the global promise state.
This is the common linearization operation used by both models. -/
def run (config : Config) (call : Call) (state : State) :
    Outcomes (State × List Output) :=
  let results :=
    (Experiment.promises.step config state call.requestedAt
      (.msg call.client (.req call.id call.requestedAt call.request))).val
  ⟨results.map fun (next, outs) => (next, outputs outs), by
    simpa using
      (Experiment.promises.step config state call.requestedAt
        (.msg call.client (.req call.id call.requestedAt call.request))).property⟩

end Rover.Protocol
