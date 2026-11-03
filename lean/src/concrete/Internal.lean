import «concrete».External

/-! Independent concrete timeout and occurrence decisions. -/

namespace Resonate.Concrete.Decision

open ServerModel

def processPromiseTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← getObject id.suffix with
  | none => pure ()
  | some object => setObject (object.project now)

def resumeOne {origin : String} (awaited awaiter : Ident) (now : Nat) :
    Handler (.origin origin) Unit := do
  match ← readTask awaiter.suffix now with
  | none => pure ()
  | some (object, task) =>
      match task.state with
      | .suspended =>
          setTask object.suffix { task with
            state := .pending
            resumes := [awaited]
            retryTimeoutAt := some now }
      | .pending | .acquired | .halted =>
          if !(task.resumes.contains awaited) then
            setTask object.suffix
              { task with
                resumes := task.resumes ++ [awaited] }
      | .fulfilled => pure ()

def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler (.origin req.awaited.origin) Unit := do
  if !req.awaited.sameOrigin req.awaiter then return ()
  match ← readObject req.awaited.suffix now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.callbacks.contains req.awaiter then
        setPromise awaited.suffix
          { awaited.promise with
            callbacks := awaited.promise.callbacks.filter (· != req.awaiter) }
        resumeOne awaited.id req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler (.origin req.awaited.origin) Unit := do
  match ← readObject req.awaited.suffix now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.listeners.contains req.address then
        setPromise awaited.suffix
          { awaited.promise with
            listeners := awaited.promise.listeners.filter (· != req.address) }
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
            setTask object.suffix { task with
              state := .pending
              pid := none
              ttl := none
              leaseTimeoutAt := none
              retryTimeoutAt := some now }

def processRetryTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← readTask id.suffix now with
  | none => pure ()
  | some (object, task) =>
      match task.retryTimeoutAt with
      | none => pure ()
      | some due =>
          if task.state == .pending ∧ due ≤ now then
            let env ← ask
            setTask object.suffix { task with
              retryTimeoutAt := some (now + env.config.retryTimeout) }
            setMessage
              ((object.promise.tags.get? "resonate:target").getD "")
              (.execute object.id task.version)

def processSchedule (id : Ident) (now : Nat) :
    Handler (.schedule id) (List WorkItem) := do
  match ← getSchedule with
  | none => return []
  | some schedule =>
      let times :=
        (occurrences schedule.cron schedule.nextRunAt now).filter (· ≤ now)
      match times.getLast? with
      | some last =>
          setScheduleValue { schedule with
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
    Handler (.origin req.id.origin) Unit :=
  createIfAbsent req time

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

def originSettledWork {origin : String} (object : OriginObject origin) :
    List WorkItem :=
  if object.promise.state == .pending then [] else
    (object.promise.callbacks.map fun awaiter =>
      .callback { awaited := object.id, awaiter }) ++
    (object.promise.listeners.map fun address =>
      .listener { awaited := object.id, address })

def originObjectWork {origin : String} (object : OriginObject origin)
    (now : Nat) : List WorkItem :=
  (if object.promise.state == .pending ∧ object.promise.timeoutAt ≤ now then
    [.promiseTimeout object.id]
  else []) ++ originSettledWork object ++ originTaskWork object now

def originWork (origin : String) (document : OriginDocument origin) (now : Nat) :
    List WorkItem :=
  document.flatMap fun object => originObjectWork object now

end Resonate.Concrete.Decision
