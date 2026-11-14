import «abstract».External

/-! Timeout steps and the due work they fire. -/

namespace Resonate.Abstract

open ServerModel

/-- Write the object back as seen at `now`: a promise past its deadline is
stored settled. -/
def processPromiseTimeout (id : Ident) (now : Nat) : Handler Unit := do
  match ← readObject id now with
  | none => pure ()
  | some object =>
      if object.promise.state == .pending then setObject object
      else setSettled object object.promise now

/-- Read the awaited promise, drop the callback, and resume the awaiter. -/
def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.callbacks.contains req.awaiter then
        setObject { awaited with
          promise.callbacks := awaited.promise.callbacks.filter (· != req.awaiter) }
        resumeOne req.awaited req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.listeners.contains req.address then
        setObject { awaited with
          promise.listeners := awaited.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (awaited.promise.toRecord req.awaited))

def processLeaseTimeout (id : Ident) (now : Nat) : Handler Unit := do
  match ← readTask id now with
  | none => pure ()
  | some (object, task) =>
      match task.leaseTimeoutAt with
      | none => pure ()
      | some deadline =>
          if task.state == .acquired ∧ deadline ≤ now then
            dispatchTask object (task.unlease .pending none) now

def processRetryTimeout (id : Ident) (now : Nat) : Handler Unit := do
  match ← readTask id now with
  | none => pure ()
  | some (object, task) =>
      match task.retryTimeoutAt with
      | none => pure ()
      | some due =>
          if task.state == .pending ∧ due ≤ now then
            dispatchTask object task now

/-- One complete due-work pass for an object. Each operation has its own due
guard; settlement and lease expiry synchronously emit all newly due effects. -/
def sweepObject (id : Ident) (now : Nat) : Handler Unit := do
  processPromiseTimeout id now
  processLeaseTimeout id now
  processRetryTimeout id now

def originSuffixes (store : Store) (origin : String) : List String :=
  sortStrings <|
    (store.objects.filter (·.id.origin == origin)).map (·.id.suffix)

/-- Drain every currently stored object in one workflow document. -/
def sweepOrigin (origin : String) (now : Nat) : Handler Unit := do
  let store ← getStore
  (originSuffixes store origin).forM fun suffix =>
    sweepObject { origin, suffix } now

/-- Advance the schedule and return the occurrences it fired. Each occurrence
creates its promise in a later step. -/
def processSchedule (id : Ident) (now : Nat) : Handler (List WorkflowEntry) := do
  match ← getSchedule id with
  | none => return []
  | some schedule =>
      let times :=
        (occurrences schedule.cron schedule.nextRunAt now).filter (· ≤ now)
      if let some last := times.getLast? then
        setSchedule
          { schedule with
            lastRunAt := some last
            nextRunAt := nextCron schedule.cron last }
      return times.map fun time =>
        { request :=
            { id := expand schedule.promiseId id time
              timeoutAt := time + schedule.promiseTimeout
              param := schedule.promiseParam
              tags := schedule.promiseTags }
          instant := time }

/-- Run one piece of due work. Only a schedule returns continuations. -/
def processWork (item : WorkItem) (now : Nat) : Handler (List WorkflowEntry) :=
  match item with
  | .scheduleTimeout id => processSchedule id now
  | .promiseTimeout id => do processPromiseTimeout id now; return []
  | .callback req => do processCallback req now; return []
  | .listener req => do processListener req now; return []
  | .taskLeaseTimeout id => do processLeaseTimeout id now; return []
  | .taskRetryTimeout id => do processRetryTimeout id now; return []
  | .occurrence req time => do createIfAbsent req time; return []

/-- The internal steps an object can take. Each step's own guard decides
whether it does anything. -/
def objectWork (object : Object) : List WorkItem :=
  [.promiseTimeout object.id, .taskLeaseTimeout object.id,
    .taskRetryTimeout object.id]

end Resonate.Abstract
