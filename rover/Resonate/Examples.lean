import Resonate.Refinement

/-!
# Executable Rover examples

These checks exercise the shared transition and the concrete conditional-write
boundary. They are intentionally data-oriented: a later trace checker can
decode boundary events, replay the same `Resonate.run` transitions, and use
`Refinement.boundary_refinement` as its semantic justification.
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
  (Resonate.run {} createCall {}).val.headD ({}, [])

theorem createOutcome_valid :
    createOutcome ∈ (Resonate.run {} createCall {}).val := by
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

def candidate : Concrete.Candidate ({} : Resonate.Config) := {
  call := createCall
  before := {}
  version := 0
  after := createOutcome.1
  outputs := createOutcome.2
  valid := createOutcome_valid
}

def commitResult : Result Concrete.Pid Concrete.Local
    (Concrete.Msg ({} : Resonate.Config)) :=
  (Concrete.step {} {} .store (.store {} 0) 0
    (.receive (.server "node-a") (.cas candidate))).val.headD {
      state := .outside
      send := []
    }

#guard match commitResult.state with
  | .store state version =>
      version == 1 && state.promises.length == 1
  | _ => false

#guard commitResult.send.length == 1

/-- Receiving the same append-only CAS message again cannot publish twice:
its old version conflicts and the store requests a fresh snapshot. -/
def duplicateResult : Result Concrete.Pid Concrete.Local
    (Concrete.Msg ({} : Resonate.Config)) :=
  (Concrete.step {} {} .store (.store createOutcome.1 1) 1
    (.receive (.server "node-a") (.cas candidate))).val.headD {
      state := .outside
      send := []
    }

#guard match duplicateResult.send with
  | [(.server "node-a", .retry call)] => call == createCall
  | _ => false

/-- The theorem is available for deployments of any finite size. -/
example : ∀ events,
    Concrete.ValidBoundaryTrace ["node-a", "node-b", "node-c"] {} {} events →
    Abstract.ValidBoundaryTrace {} events :=
  Refinement.boundary_refinement
    ["node-a", "node-b", "node-c"] {} {} rfl

end Resonate.Examples
