import Resonate.TraceChecker
import Resonate.Concrete

/-! Focused executable checks for every state family and timeout delivery. -/

namespace Resonate.Examples

open ServerModel

def ident (suffix : String) : Ident := { origin := "example", suffix }

def createCall : Call := {
  client := "client"
  id := 1
  requestedAt := 0
  request := .promiseCreate {
    id := ident "promise"
    timeoutAt := 10
    param := {}
    tags := []
  }
}

def createResult : State × List Output := Resonate.run {} createCall {}

#guard (createResult.1.originDocument "example").length == 1
#guard (createResult.1.originDocument "example").head?.map (·.id) ==
  some (ident "promise")
#guard createResult.2.length == 1
#guard match createResult.2 with
  | [.response "client" 1 (.promiseCreate response)] =>
      response.status == 200
  | _ => false

/-- `taskCreate` writes the promise and then immediately observes that row
when `setTask` maps it. This specifically exercises read-your-own-writes. -/
def taskCreateCall : Call := {
  client := "worker"
  id := 2
  requestedAt := 1
  request := .taskCreate {
    pid := "worker-1"
    ttl := 20
    action := {
      id := ident "task"
      timeoutAt := 100
      param := {}
      tags := [("resonate:target", "queue")]
    }
  }
}

def taskCreateResult : State × List Output :=
  Resonate.run {} taskCreateCall {}

#guard (taskCreateResult.1.originDocument "example").length == 1
#guard match (taskCreateResult.1.originDocument "example").head? with
  | some object =>
      object.promise.state == .pending &&
      object.task.map (·.state) == some .acquired
  | none => false

def exampleSchedule : Schedule := {
  id := ident "schedule"
  cron := "* * * * *"
  promiseId := ident "scheduled-promise"
  promiseTimeout := 100
  promiseParam := {}
  promiseTags := []
  nextRunAt := 10
  createdAt := 0
}

def deleteScheduleCall : Call := {
  client := "scheduler"
  id := 3
  requestedAt := 2
  request := .scheduleDelete { id := ident "schedule" }
}

def scheduleResult : State × List Output :=
  Resonate.run {} deleteScheduleCall (State.init.withSchedule exampleSchedule)

#guard (scheduleResult.1.scheduleDocument (ident "schedule")).isNone
#guard match scheduleResult.2 with
  | [.response "scheduler" 3 (.scheduleDelete response)] =>
      response.status == 200
  | _ => false

/-- A schedule timeout is confined to its schedule document. (`occurrences`
is intentionally opaque in the pinned public specification, so the executable
occurrence continuation below is supplied explicitly.) -/
def scheduleFireFirst : State × List Output :=
  Resonate.runInternal {}
    (.scheduleTimeout { schedule := ident "schedule" }) 10
    (State.init.withSchedule exampleSchedule)

#guard (scheduleFireFirst.1.originDocument "example").isEmpty

def occurrenceContinuation : WorkItem :=
  .occurrence {
    id := ident "scheduled-promise"
    timeoutAt := 110
    param := {}
    tags := []
  } 10

def occurrenceState : State :=
  { scheduleFireFirst.1 with
    workflow := {
      pending := [.work occurrenceContinuation 10] } }

def scheduleFireSecond : State × List Output :=
  Resonate.runTimeout {} 10 occurrenceState

#guard scheduleFireSecond.1.workflow.pending.isEmpty
#guard (scheduleFireSecond.1.originDocument "example").length == 1
#guard (scheduleFireSecond.1.originDocument "example").head?.map (·.id) ==
  some (ident "scheduled-promise")

def listenerState : State :=
  State.init.withOrigin "example" [{
    suffix := "settled"
    promise := {
      state := .resolved
      param := {}
      value := { data := some "done" }
      tags := []
      timeoutAt := 10
      createdAt := 0
      settledAt := some 1
      listeners := ["listener"]
    }
  }]

def listenerResult : State × List Output :=
  Resonate.runInternal {}
    (.listener { awaited := ident "settled", address := "listener" })
    2 listenerState

#guard (listenerResult.1.originDocument "example").head?.map
  (·.promise.listeners) == some []
#guard match listenerResult.2 with
  | [.message { address := "listener", message := .unblock promise }] =>
      promise.id == ident "settled"
  | _ => false

/-- The service discovers and executes the listener work from its state when
Rover delivers a timeout; the event carries no internal request. -/
def listenerRoverResult :
    Rover.Result Abstract.Pid State Message :=
  let discovered := (Resonate.runTimeout {} 2 listenerState).1
  (Abstract.step {} .service discovered 3
    .timeout)
    |>.val.headD { state := {}, send := [] }

#guard (listenerRoverResult.state.originDocument "example").head?.map
  (·.promise.listeners) == some []
#guard match listenerRoverResult.send with
  | [(.outside, .output (.message
      { address := "listener", message := .unblock promise }))] =>
      promise.id == ident "settled"
  | _ => false

/-- Equal-key messages are transient emissions: both survive, in order, while
the abstract state remains unchanged. -/
def duplicateEmissionResult : Unit × Store × List OutboxEntry :=
  Direct.run (.origin "example") (do
    Direct.setMessage "queue" (.execute (ident "duplicate") 1)
    Direct.setMessage "queue" (.execute (ident "duplicate") 2)) {}

#guard match duplicateEmissionResult with
  | (_, store, [
      { address := "queue", message := .execute first 1 },
      { address := "queue", message := .execute second 2 }]) =>
      (store.read (.origin "example")).isEmpty &&
        (store.read (.schedule (ident "schedule"))).isNone &&
        first == ident "duplicate" && second == ident "duplicate"
  | _ => false

def timeoutState : State :=
  State.init.withOrigin "example" [{
    suffix := "timeout"
    promise := {
      state := .pending
      param := {}
      tags := []
      timeoutAt := 5
      createdAt := 0
    }
  }]

def timeoutResult : State × List Output :=
  Resonate.runTimeout {} 6 (Resonate.runTimeout {} 5 timeoutState).1

#guard (timeoutResult.1.originDocument "example").head?.map (·.promise.state) ==
  some .rejectedTimedout

/-- Work enabled by an internal handler is absent from that timeout's snapshot
and runs on the next timeout. -/
def deferredRetryState : State :=
  State.init.withOrigin "example" [
    {
      suffix := "awaited"
      promise := {
        state := .resolved
        param := {}
        tags := []
        timeoutAt := 10
        createdAt := 0
        settledAt := some 1
        callbacks := [ident "awaiter"]
      }
    },
    {
      suffix := "awaiter"
      promise := {
        state := .pending
        param := {}
        tags := [("resonate:target", "queue")]
        timeoutAt := 100
        createdAt := 0
      }
      task := some {
        state := .suspended
        version := 0
      }
    }
  ]

def deferredRetryFirst : State × List Output :=
  Resonate.runTimeout {} 3
    (Resonate.runTimeout {} 2 deferredRetryState).1

#guard deferredRetryFirst.2.isEmpty
#guard ((((deferredRetryFirst.1.originDocument "example").find?
  (·.suffix == "awaiter")).bind (·.task)).map (·.state)) == some .pending

def deferredRetrySecond : State × List Output :=
  let discovered := (Resonate.runTimeout {} 4 deferredRetryFirst.1).1
  Resonate.runTimeout {} 5 discovered

#guard match deferredRetrySecond.2 with
  | [.message { address := "queue", message := .execute taskId 0 }] =>
      taskId == ident "awaiter"
  | _ => false

def absentScheduleStep : State × List Output :=
  Resonate.runInternal {}
    (.scheduleTimeout { schedule := ident "absent-schedule" }) 5 {}

#guard (absentScheduleStep.1.originDocument "example").isEmpty
#guard (absentScheduleStep.1.scheduleDocument
  (ident "absent-schedule")).isNone
#guard absentScheduleStep.2.isEmpty

def retryState : State :=
  State.init.withOrigin "example" [{
    suffix := "retry"
    promise := {
      state := .pending
      param := {}
      tags := [("resonate:target", "queue")]
      timeoutAt := 100
      createdAt := 0
    }
    task := some {
      state := .pending
      version := 4
      retryTimeoutAt := some 3
    }
  }]

def retryResult : State × List Output :=
  Resonate.runTimeout { retryTimeout := 7 } 4
    (Resonate.runTimeout { retryTimeout := 7 } 3 retryState).1

#guard match retryResult.2 with
  | [.message { address := "queue", message := .execute taskId 4 }] =>
      taskId == ident "retry"
  | _ => false

def createResponse : Response :=
  .promiseCreate {
    status := 200
    promise := some {
      id := ident "promise"
      state := .pending
      param := {}
      tags := []
      timeoutAt := 10
      createdAt := 0
    }
  }

def createTrace : List BoundaryEvent := [
  .request 0 createCall,
  .response 1 "client" 1 createResponse
]

#guard (TraceChecker.check {} createTrace).isValid

def nonmonotoneTrace : List BoundaryEvent := [
  .request 2 createCall,
  .response 1 "client" 1 createResponse
]

#guard (TraceChecker.check {} nonmonotoneTrace).isInvalid

-- A zero resource bound cannot inspect a valid nonempty trace.
#guard (TraceChecker.checkWithBound 0 {} createTrace).isUnknown

def unsupportedTrace : List BoundaryEvent := [
  .response 0 "client" 1 createResponse
]

-- Exhausting an ordered but unsupported trace is not a refutation.
#guard (TraceChecker.check {} unsupportedTrace).isUnknown

def unavailableCreateTrace : List BoundaryEvent := [
  .request 0 createCall,
  .response 1 "client" 1 (unavailableResponse createCall.request)
]

-- The full checker explores serve, landed-but-lost, and shed branches.
#guard (TraceChecker.check { unreliable := true }
  unavailableCreateTrace).isValid

/-- Store application payloads contain only the dependent key, document, and
expected version. Correlation is supplied separately by `RpcRequest`. -/
def rawOriginPut : Concrete.RpcRequest := {
  op := 7
  payload := .put (.origin "example") [] none
}

#guard match rawOriginPut with
  | { op := 7, payload := .put (.origin "example") [] none } => true
  | _ => false

-- Flaky conditional PUT exposes written, landed-failed, and not-landed-failed.
#guard (Concrete.storePut { flaky := true } (.node "n") {} 9
  (.origin "example") [] none).val.length == 3

end Resonate.Examples
