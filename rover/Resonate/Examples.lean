import Resonate.TraceChecker

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

#guard createResult.1.objects.length == 1
#guard createResult.1.objects.head?.map (·.id) == some (ident "promise")
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

#guard taskCreateResult.1.objects.length == 1
#guard match taskCreateResult.1.objects.head? with
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
  Resonate.run {} deleteScheduleCall { schedules := [exampleSchedule] }

#guard scheduleResult.1.schedules.isEmpty
#guard match scheduleResult.2 with
  | [.response "scheduler" 3 (.scheduleDelete response)] =>
      response.status == 200
  | _ => false

def listenerState : State := {
  objects := [{
    id := ident "settled"
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
}

def listenerResult : State × List Output :=
  Resonate.runInternal {}
    (.listener { awaited := ident "settled", address := "listener" })
    2 listenerState

#guard listenerResult.1.objects.head?.map (·.promise.listeners) == some []
#guard match listenerResult.2 with
  | [.message { address := "listener", message := .unblock promise }] =>
      promise.id == ident "settled"
  | _ => false

/-- The service discovers and executes the listener work from its state when
Rover delivers a timeout; the event carries no internal request. -/
def listenerRoverResult :
    Rover.Result Abstract.Pid State Message :=
  (Abstract.step {} .service listenerState 2
    .timeout)
    |>.val.headD { state := {}, send := [] }

#guard listenerRoverResult.state.objects.head?.map (·.promise.listeners) ==
  some []
#guard match listenerRoverResult.send with
  | [(.outside, .output (.message
      { address := "listener", message := .unblock promise }))] =>
      promise.id == ident "settled"
  | _ => false

/-- Equal-key messages are transient emissions: both survive, in order, while
the abstract state remains unchanged. -/
def duplicateEmissionResult : Unit × State × List OutboxEntry :=
  Direct.run (do
    Direct.setMessage "queue" (.execute (ident "duplicate") 1)
    Direct.setMessage "queue" (.execute (ident "duplicate") 2)) {}

#guard match duplicateEmissionResult with
  | (_, state, [
      { address := "queue", message := .execute first 1 },
      { address := "queue", message := .execute second 2 }]) =>
      state.objects.isEmpty && state.schedules.isEmpty &&
        first == ident "duplicate" && second == ident "duplicate"
  | _ => false

def timeoutState : State := {
  objects := [{
    id := ident "timeout"
    promise := {
      state := .pending
      param := {}
      tags := []
      timeoutAt := 5
      createdAt := 0
    }
  }]
}

def timeoutResult : State × List Output :=
  Resonate.runTimeout {} 5 timeoutState

#guard timeoutResult.1.objects.head?.map (·.promise.state) ==
  some .rejectedTimedout

/-- Work enabled by an internal handler is absent from that timeout's snapshot
and runs on the next timeout. -/
def deferredRetryState : State := {
  objects := [
    {
      id := ident "awaited"
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
      id := ident "awaiter"
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
}

def deferredRetryFirst : State × List Output :=
  Resonate.runTimeout {} 2 deferredRetryState

#guard deferredRetryFirst.2.isEmpty
#guard (((deferredRetryFirst.1.objects.find?
  (·.id == ident "awaiter")).bind (·.task)).map (·.state)) == some .pending

def deferredRetrySecond : State × List Output :=
  Resonate.runTimeout {} 2 deferredRetryFirst.1

#guard match deferredRetrySecond.2 with
  | [.message { address := "queue", message := .execute taskId 0 }] =>
      taskId == ident "awaiter"
  | _ => false

def absentScheduleStep : State × List Output :=
  Resonate.runInternal {}
    (.scheduleTimeout { schedule := ident "absent-schedule" }) 5 {}

#guard absentScheduleStep.1.objects.isEmpty
#guard absentScheduleStep.1.schedules.isEmpty
#guard absentScheduleStep.2.isEmpty

def retryState : State := {
  objects := [{
    id := ident "retry"
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
}

def retryResult : State × List Output :=
  Resonate.runTimeout { retryTimeout := 7 } 3 retryState

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

end Resonate.Examples
