import Resonate.Refinement

/-!
# Executable Rover examples

These checks exercise the shared transition and the concrete conditional-write
boundary. They are intentionally data-oriented: a later trace checker can
decode boundary events and replay the same `Resonate.run` transitions.  The
raw PUT example also illustrates that semantic provenance is a ghost invariant,
not protocol data.
-/

namespace Resonate.Examples

open Rover

def createCall : Call := {
  client := "client-a"
  id := 7
  requestedAt := 0
  request := .create "promise-a" (some 10)
}

def createOutcome : State × List Output :=
  (Resonate.dispatch {} createCall {}).val.headD ({}, [])

theorem createOutcome_valid :
    createOutcome ∈ (Resonate.dispatch {} createCall {}).val := by
  native_decide

#guard createOutcome.1.promises.length == 1
#guard createOutcome.1.promises.head?.map (·.id) == some "promise-a"
#guard createOutcome.2.length == 1
#guard createOutcome.2 == [
  .response "client-a" 7 {
    status := 200
    promise := some {
      id := "promise-a"
      state := .pending
      value := ""
      timeoutAt := 10
    }
  }]

def createdDocument : Promise :=
  createOutcome.1.promises.headD {
    id := "missing"
    timeoutAt := 0
  }

/-- The store sees only protocol data. No call, response, notification, prior
state, operation id, or proof witness is present in this raw PUT payload. -/
def rawPut : Concrete.StoreRequest :=
  .put "promise-a" createdDocument none

/-- Correlation belongs to the RPC envelope around the raw payload. -/
def rawPutCall : Concrete.Msg ({} : Resonate.Config) :=
  .call 0 rawPut

def commitResult : Result Concrete.Pid Concrete.Local
    (Concrete.Msg ({} : Resonate.Config)) :=
  (Concrete.step {} {} .store (.store {}) 0
    (.receive (.server "node-a") rawPutCall)).val.headD {
      state := .outside
      send := []
    }

#guard match commitResult.state with
  | .store store =>
      store.docs == [("promise-a", createdDocument, 1)]
  | _ => false

#guard commitResult.send == [(.server "node-a", .reply 0 .written)]

/-- Receiving the same append-only raw PUT again cannot publish twice: its
stale `none` expected version conflicts with the document's current version. -/
def duplicateResult : Result Concrete.Pid Concrete.Local
    (Concrete.Msg ({} : Resonate.Config)) :=
  (Concrete.step {} {} .store
    (.store { docs := [("promise-a", createdDocument, 1)] }) 1
    (.receive (.server "node-a") rawPutCall)).val.headD {
      state := .outside
      send := []
    }

#guard match duplicateResult.send with
  | [(.server "node-a", .reply 0 .conflict)] => true
  | _ => false

/-- A flaky matching PUT has all three faithful outcomes: acknowledged land,
failed-after-land, and failed-without-landing. -/
def flakyPutResults : List (Result Concrete.Pid Concrete.Local
    (Concrete.Msg ({} : Resonate.Config))) :=
  (Concrete.storePutResults { flaky := true } "node-a" {}
    0 "promise-a" createdDocument none).val

#guard flakyPutResults.length == 3
#guard match flakyPutResults[1]? with
  | some result => match result.state with
    | .store store => store.docs == [("promise-a", createdDocument, 1)]
    | _ => false
  | _ => false
#guard match flakyPutResults[1]? with
  | some result => match result.send with
    | [(.server "node-a", .reply 0 .failed)] => true
    | _ => false
  | _ => false
#guard match flakyPutResults[2]? with
  | some result => match result.state with
    | .store store => store.docs.isEmpty
    | _ => false
  | _ => false

end Resonate.Examples
