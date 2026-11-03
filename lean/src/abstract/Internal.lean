import «abstract».External

/-! Timeout steps and the due work they fire. -/

namespace Resonate.Abstract

open ServerModel

/-- Write the timed-out promise back. -/
def processPromiseTimeout (id : Ident) (now : Nat) : Handler Unit := do
  match ← getObject id with
  | none => pure ()
  | some object => setObject (object.project now)

/-- Wake the awaiter's task because `awaited` settled. -/
def resumeOne (awaited awaiter : Ident) (now : Nat) : Handler Unit := do
  match ← readTaskObject awaiter now with
  | none => pure ()
  | some object =>
      match object.task with
      | none => pure ()
      | some task =>
          match task.state with
          | .suspended =>
              setTask awaiter
                { task with
                  state := .pending
                  resumes := [awaited]
                  retryTimeoutAt := some now }
          | .pending | .acquired | .halted =>
              if !(task.resumes.contains awaited) then
                setTask awaiter
                  { task with resumes := task.resumes ++ [awaited] }
          | .fulfilled => pure ()

/-- Read the awaited promise, drop the callback, and resume the awaiter. -/
def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.callbacks.contains req.awaiter then
        setPromise req.awaited
          { awaited.promise with
            callbacks := awaited.promise.callbacks.filter (· != req.awaiter) }
        resumeOne req.awaited req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.listeners.contains req.address then
        setPromise req.awaited
          { awaited.promise with
            listeners := awaited.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (awaited.promise.toRecord req.awaited))

def processLeaseTimeout (id : Ident) (now : Nat) : Handler Unit := do
  match ← readTaskObject id now with
  | none => pure ()
  | some object =>
      match object.task with
      | none => pure ()
      | some task =>
          match task.leaseTimeoutAt with
          | none => pure ()
          | some deadline =>
              if task.state == .acquired ∧ deadline ≤ now ∧
                  object.promise.state == .pending then
                setTask id
                  { task with
                    state := .pending
                    pid := none
                    ttl := none
                    leaseTimeoutAt := none
                    retryTimeoutAt := some now }

def processRetryTimeout (id : Ident) (now : Nat) : Handler Unit := do
  match ← readTaskObject id now with
  | none => pure ()
  | some object =>
      match object.task with
      | none => pure ()
      | some task =>
          match task.retryTimeoutAt with
          | none => pure ()
          | some due =>
              if task.state == .pending ∧ due ≤ now ∧
                  object.promise.state == .pending then
                let env ← ask
                setTask id
                  { task with
                    retryTimeoutAt := some (now + env.config.retryTimeout) }
                setMessage
                  ((object.promise.tags.get? "resonate:target").getD "")
                  (.execute id task.version)

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
def processWork (item : WorkItem) (now : Nat) : Handler (List WorkflowEntry) := do
  match item with
  | .promiseTimeout id => processPromiseTimeout id now
  | .callback req => processCallback req now
  | .listener req => processListener req now
  | .taskLeaseTimeout id => processLeaseTimeout id now
  | .taskRetryTimeout id => processRetryTimeout id now
  | .scheduleTimeout id => return ← processSchedule id now
  | .occurrence req time => createIfAbsent req time
  return []

/-- Work an object makes due at `now`. -/
def objectWork (object : Object) (now : Nat) : List WorkItem :=
  let promise := object.promise
  let pending := promise.state == .pending
  (if pending ∧ promise.timeoutAt ≤ now then [.promiseTimeout object.id] else []) ++
  (if pending then [] else
    promise.callbacks.map (fun awaiter => .callback { awaited := object.id, awaiter }) ++
    promise.listeners.map (fun address => .listener { awaited := object.id, address })) ++
  (match object.task with
   | none => []
   | some task =>
       (match task.leaseTimeoutAt with
        | some due =>
            if task.state == .acquired ∧ due ≤ now ∧ pending then
              [.taskLeaseTimeout object.id] else []
        | none => []) ++
       (match task.retryTimeoutAt with
        | some due =>
            if task.state == .pending ∧ due ≤ now ∧ pending then
              [.taskRetryTimeout object.id] else []
        | none => []))

/-- Work a schedule makes due at `now`. -/
def scheduleWork (schedule : Schedule) (now : Nat) : List WorkItem :=
  if schedule.nextRunAt ≤ now then [.scheduleTimeout schedule.id] else []

end Resonate.Abstract
