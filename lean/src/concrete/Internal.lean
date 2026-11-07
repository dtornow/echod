import «concrete».External

/-! Independent concrete timeout and occurrence decisions. -/

namespace Resonate.Concrete.Decision

open ServerModel

def processPromiseTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← readObject id.suffix now with
  | none => pure ()
  | some object =>
      if object.promise.state == .pending then setObject object
      else setSettled object object.promise now

def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler (.origin req.awaited.origin) Unit := do
  if !req.awaited.sameOrigin req.awaiter then return ()
  match ← readObject req.awaited.suffix now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.callbacks.contains req.awaiter then
        setObject { awaited with
          promise.callbacks := awaited.promise.callbacks.filter (· != req.awaiter) }
        resumeOne awaited.id req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler (.origin req.awaited.origin) Unit := do
  match ← readObject req.awaited.suffix now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.listeners.contains req.address then
        setObject { awaited with
          promise.listeners := awaited.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (awaited.promise.toRecord awaited.id))

def processLeaseTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← readTask id.suffix now with
  | none => pure ()
  | some (object, task) =>
      match task.leaseTimeoutAt with
      | none => pure ()
      | some deadline =>
          if task.state == .acquired ∧ deadline ≤ now then
            dispatchTask object
              { task with
                state := .pending
                pid := none
                ttl := none
                leaseTimeoutAt := none }
              now

def processRetryTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← readTask id.suffix now with
  | none => pure ()
  | some (object, task) =>
      match task.retryTimeoutAt with
      | none => pure ()
      | some due =>
          if task.state == .pending ∧ due ≤ now then
            dispatchTask object task now

/-- One complete due-work pass for an object. -/
def sweepObject (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  processPromiseTimeout id now
  processLeaseTimeout id now
  processRetryTimeout id now

/-- Drain every currently stored object in one workflow document. -/
def sweepOrigin (origin : String) (now : Nat) :
    Handler (.origin origin) Unit := do
  let document ← get
  let suffixes := sortStrings (document.map (·.suffix))
  suffixes.forM fun suffix =>
    sweepObject { origin, suffix } now

def processSchedule (id : Ident) (now : Nat) :
    Handler (.schedule id) (List WorkItem) := do
  match ← getSchedule with
  | none => return []
  | some schedule =>
      let times :=
        (occurrences schedule.cron schedule.nextRunAt now).filter (· ≤ now)
      match times.getLast? with
      | some last =>
          setSchedule { schedule with
            lastRunAt := some last
            nextRunAt := nextCron schedule.cron last }
      | none => pure ()
      return times.map fun time =>
        .occurrence
          { id := expand schedule.promiseId schedule.id time
            timeoutAt := time + schedule.promiseTimeout
            param := schedule.promiseParam
            tags := schedule.promiseTags }
          time

def processOccurrence (req : PromiseCreateReq) (time : Nat) :
    Handler (.origin req.id.origin) Unit := do
  let _ ← readOrCreate req time

def originTaskWork {origin : String} (object : OriginObject origin)
    (now : Nat) : List WorkItem :=
  match object.task with
  | none => []
  | some task =>
      (match task.leaseTimeoutAt with
       | some due =>
           if task.state == .acquired ∧ due ≤ now ∧
               object.promise.state == .pending then
             [.taskLeaseTimeout object.id]
           else []
       | none => []) ++
      (match task.retryTimeoutAt with
       | some due =>
           if task.state == .pending ∧ due ≤ now ∧
               object.promise.state == .pending then
             [.taskRetryTimeout object.id]
           else []
       | none => [])

def originObjectWork {origin : String} (object : OriginObject origin)
    (now : Nat) : List WorkItem :=
  (if object.promise.state == .pending ∧ object.promise.timeoutAt ≤ now then
    [.promiseTimeout object.id]
  else []) ++ originTaskWork object now

def originWork (origin : String) (document : WorkflowDocument origin) (now : Nat) :
    List WorkItem :=
  document.flatMap fun object => originObjectWork object now

end Resonate.Concrete.Decision
