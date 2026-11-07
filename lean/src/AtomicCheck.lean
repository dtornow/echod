import «concrete».ProcessNode

/-! Executable checks for complete, CAS-gated workflow request effects. -/

namespace Resonate.AtomicCheck

open ServerModel
open Concrete

def config : ServerConfig := { retryTimeout := 100 }
def appConfig : Resonate.Config := { retryTimeout := 100 }

def ident (suffix : String) : Ident := { origin := "wf", suffix }

def runnableTags : Tags := [("resonate:target", "worker")]

def pendingPromise (tags : Tags := []) : PromiseObject :=
  { state := .pending
    param := {}
    tags
    timeoutAt := 10000
    createdAt := 1000 }

def createReq : PromiseCreateReq :=
  { id := ident "task"
    timeoutAt := 10000
    param := {}
    tags := runnableTags }

def created :=
  Concrete.Decision.run config
    (Concrete.Decision.promiseCreate createReq 1000)
    ([] : WorkflowDocument "wf")

example :
    created.2.2 =
      [{ address := "worker", message := .execute (ident "task") 0 }] := by
  native_decide

example :
    ((created.2.1.find? (·.suffix == "task")).bind (·.task)).bind
        (·.retryTimeoutAt) =
      some 1100 := by
  native_decide

def acquiredTask : OriginObject "wf" :=
  { suffix := "task"
    promise := pendingPromise runnableTags
    task := some {
      state := .acquired
      version := 1
      pid := some "worker"
      ttl := some 500
      leaseTimeoutAt := some 1800 } }

def released :=
  Concrete.Decision.run config
    (Concrete.Decision.taskRelease
      { id := ident "task", version := 1 } 1400)
    [acquiredTask]

example :
    released.2.2 =
      [{ address := "worker", message := .execute (ident "task") 1 }] := by
  native_decide

example :
    ((released.2.1.find? (·.suffix == "task")).bind (·.task)).bind
        (·.retryTimeoutAt) =
      some 1500 := by
  native_decide

def haltedTask : OriginObject "wf" :=
  { acquiredTask with
    task := acquiredTask.task.map fun task =>
      { task with
        state := .halted
        pid := none
        ttl := none
        leaseTimeoutAt := none } }

def continued :=
  Concrete.Decision.run config
    (Concrete.Decision.taskContinue { id := ident "task" } 1600)
    [haltedTask]

example :
    continued.2.2 =
      [{ address := "worker", message := .execute (ident "task") 1 }] := by
  native_decide

example :
    ((continued.2.1.find? (·.suffix == "task")).bind (·.task)).bind
        (·.retryTimeoutAt) =
      some 1700 := by
  native_decide

def outOfRangeCreate : PromiseCreateReq :=
  { createReq with timeoutAt := MAX_TIME + 1 }

def rejectedCreate :=
  Concrete.Decision.run config
    (Concrete.Decision.promiseCreate outOfRangeCreate 1000)
    ([] : WorkflowDocument "wf")

example : rejectedCreate.1.status = 400 := by native_decide
example : rejectedCreate.2.1.isEmpty = true := by native_decide

def boundedPendingTask : OriginObject "wf" :=
  { suffix := "task"
    promise := pendingPromise runnableTags
    task := some {
      state := .pending
      version := 0
      retryTimeoutAt := some 5000 } }

def rejectedZeroTtl :=
  Concrete.Decision.run config
    (Concrete.Decision.taskAcquire
      { id := ident "task", version := 0, pid := "worker", ttl := 0 }
      1000)
    [boundedPendingTask]

example : rejectedZeroTtl.1.status = 400 := by native_decide

def exhaustedTask : OriginObject "wf" :=
  { boundedPendingTask with
    task := boundedPendingTask.task.map fun task =>
      { task with version := MAX_VERSION } }

def rejectedExhaustedVersion :=
  Concrete.Decision.run config
    (Concrete.Decision.taskAcquire
      { id := ident "task"
        version := MAX_VERSION
        pid := "worker"
        ttl := 1 }
      1000)
    [exhaustedTask]

example : rejectedExhaustedVersion.1.status = 409 := by native_decide

def awaitedWithListener : OriginObject "wf" :=
  { suffix := "awaited"
    promise :=
      { pendingPromise with
        callbacks := [ident "awaiter"]
        listeners := ["listener"] } }

def suspendedAwaiter : OriginObject "wf" :=
  { suffix := "awaiter"
    promise := pendingPromise runnableTags
    task := some { state := .suspended, version := 1 } }

def settlementDocument : WorkflowDocument "wf" :=
  [awaitedWithListener, suspendedAwaiter]

def settleReq : PromiseSettleReq :=
  { id := ident "awaited", state := .resolved, value := {} }

def settled :=
  Concrete.Decision.run config
    (Concrete.Decision.promiseSettle settleReq 1200)
    settlementDocument

example : settled.2.2.length = 2 := by native_decide

def resumedExecute : OutboxEntry :=
  { address := "worker"
    message := .execute (ident "awaiter") 1 }

example :
    settled.2.2.head? = some resumedExecute := by
  native_decide

example : (settled.2.2[1]?).map (·.address) = some "listener" := by
  native_decide

example :
    ((settled.2.1.find? (·.suffix == "awaiter")).bind (·.task)).map
        (fun task => (task.state, task.retryTimeoutAt, task.resumes)) =
      some (.pending, some 1300, [ident "awaited"]) := by
  native_decide

example :
    (settled.2.1.find? (·.suffix == "awaited")).map
        (fun object =>
          (object.promise.callbacks, object.promise.listeners)) =
      some ([], []) := by
  native_decide

def awaitedWithoutListener : OriginObject "wf" :=
  { suffix := "awaited"
    promise := { pendingPromise with callbacks := [ident "awaiter"] } }

def pendingAwaiter : OriginObject "wf" :=
  { suffix := "awaiter"
    promise := pendingPromise runnableTags
    task := some {
      state := .pending
      version := 3
      retryTimeoutAt := some 5000 } }

def pendingAwaiterDocument : WorkflowDocument "wf" :=
  [awaitedWithoutListener, pendingAwaiter]

def settledPending :=
  Concrete.Decision.run config
    (Concrete.Decision.promiseSettle settleReq 1200)
    pendingAwaiterDocument

example : settledPending.2.2 = [] := by native_decide

example :
    ((settledPending.2.1.find? (·.suffix == "awaiter")).bind
      (·.task)).map (·.resumes) =
      some [ident "awaited"] := by
  native_decide

def call : Call :=
  { client := "client"
    id := 7
    requestedAt := 1000
    request := .promiseCreate createReq }

def candidate :=
  Concrete.externalCandidate (key := .origin "wf") appConfig call
    ([] : WorkflowDocument "wf")
    (Concrete.Decision.promiseCreate createReq 1000)
    .promiseCreate

def createdExecute : OutboxEntry :=
  { address := "worker", message := .execute (ident "task") 0 }

example :
    candidate.outputs.tail =
      [.message createdExecute] := by
  native_decide

example :
    ((candidate.document.find? (·.suffix == "task")).bind (·.task)).bind
        (·.retryTimeoutAt) =
      some 1100 := by
  native_decide

def dueTask : OriginObject "wf" :=
  { boundedPendingTask with
    suffix := "due"
    task := boundedPendingTask.task.map fun task =>
      { task with version := 2, retryTimeoutAt := some 900 } }

def getDueCall : Call :=
  { client := "client"
    id := 8
    requestedAt := 1000
    request := .promiseGet { id := ident "due" } }

def sweptCandidate :=
  Concrete.externalCandidate (key := .origin "wf") appConfig getDueCall
    [dueTask]
    (Concrete.Decision.promiseGet { id := ident "due" } 1000)
    .promiseGet

def dueExecute : OutboxEntry :=
  { address := "worker", message := .execute (ident "due") 2 }

/-- Due work is drained into the same candidate before its public handler. -/
example :
    sweptCandidate.outputs.tail =
      [.message dueExecute] := by
  native_decide

example :
    ((sweptCandidate.document.find? (·.suffix == "due")).bind (·.task)).bind
        (·.retryTimeoutAt) =
      some 1100 := by
  native_decide

def flight : Concrete.Flight :=
  { key := .origin "wf", transaction := .external call, address := "node" }

def writing :=
  Concrete.writeCandidate ({} : Concrete.Node) flight none candidate

/-- Candidate effects do not escape with the PUT; they remain selected until
the conditional write is acknowledged. -/
example :
    writing.send.any (fun entry => decide (entry.1 = Concrete.Pid.outside)) =
      false := by
  native_decide

example :
    (Concrete.finishFlight ({} : Concrete.Node)
      { flight with selected := candidate.outputs }).send =
      Concrete.sendOutputs candidate.outputs := by
  rfl

end Resonate.AtomicCheck
