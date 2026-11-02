import «abstract».External

namespace Resonate.Direct

open ServerModel

/-- Promise timeout materialisation changes only the promise's origin
document. -/
def processPromiseTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← getObject id.suffix with
  | none => pure ()
  | some object => setObject (object.project now)

def resumeOne {origin : String} (awaited awaiter : Ident) (now : Nat) :
    Handler (.origin origin) Unit := do
  match ← readTaskObject awaiter.suffix now with
  | none => pure ()
  | some object =>
      match object.task with
      | none => pure ()
      | some task =>
          match task.state with
          | .suspended =>
              setTask object.suffix
                { task with
                  state := .pending
                  resumes := [awaited]
                  retryTimeoutAt := some now }
          | .pending | .acquired | .halted =>
              if !(task.resumes.contains awaited) then
                setTask object.suffix
                  { task with resumes := task.resumes ++ [awaited] }
          | .fulfilled => pure ()

def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler (.origin req.awaited.origin) Unit := do
  -- Malformed pre-states cannot turn callback delivery into a cross-origin
  -- access; suffix lookup is used only after this guard.
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
  match ← readTaskObject id.suffix now with
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
                setTask object.suffix
                  { task with
                    state := .pending
                    pid := none
                    ttl := none
                    leaseTimeoutAt := none
                    retryTimeoutAt := some now }

def processRetryTimeout (id : Ident) (now : Nat) :
    Handler (.origin id.origin) Unit := do
  match ← readTaskObject id.suffix now with
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
                setTask object.suffix
                  { task with
                    retryTimeoutAt :=
                      some (now + env.config.retryTimeout) }
                setMessage
                  ((object.promise.tags.get? "resonate:target").getD "")
                  (.execute object.id task.version)

/-- A schedule-document step updates the schedule and returns origin work. It
does not execute any occurrence. -/
def processSchedule (id : Ident) (now : Nat) :
    Handler (.schedule id) (List WorkItem) := do
  match ← getSchedule with
  | none => return []
  | some schedule =>
      let times :=
        (occurrences schedule.cron schedule.nextRunAt now).filter (· ≤ now)
      match times.getLast? with
      | some last =>
          let next : Schedule :=
            { schedule with
              lastRunAt := some last
              nextRunAt := nextCron schedule.cron last }
          setScheduleValue next
      | none => pure ()
      return times.map fun time =>
        .occurrence
          { id := expand schedule.promiseId schedule.id time
            timeoutAt := time + schedule.promiseTimeout
            param := schedule.promiseParam
            tags := schedule.promiseTags }
          time

/-- Each occurrence is a separate origin-document transaction. -/
def processOccurrence (req : PromiseCreateReq) (time : Nat) :
    Handler (.origin req.id.origin) Unit :=
  createIfAbsent req time

/-- Execute one item selected from an origin document without permitting
cross-document access. The equality checks are redundant for items produced by
`originWork`, but make the fixed-key restriction explicit in the type. -/
def processOriginWorkItem (origin : String) (item : WorkItem) (now : Nat) :
    Handler (.origin origin) Unit :=
  match item with
  | .promiseTimeout id =>
      if h : id.origin = origin then h ▸ processPromiseTimeout id now
      else pure ()
  | .callback req =>
      if h : req.awaited.origin = origin then h ▸ processCallback req now
      else pure ()
  | .listener req =>
      if h : req.awaited.origin = origin then h ▸ processListener req now
      else pure ()
  | .taskLeaseTimeout id =>
      if h : id.origin = origin then h ▸ processLeaseTimeout id now
      else pure ()
  | .taskRetryTimeout id =>
      if h : id.origin = origin then h ▸ processRetryTimeout id now
      else pure ()
  | .scheduleTimeout _ | .occurrence _ _ => pure ()

def processOriginWorkItems (origin : String) (items : List WorkItem)
    (now : Nat) : Handler (.origin origin) Unit := do
  match items with
  | [] => pure ()
  | item :: rest =>
      processOriginWorkItem origin item now
      processOriginWorkItems origin rest now

/-- Task work discoverable from one fused origin row. -/
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

/-- Work discoverable from one fused origin row. -/
def originObjectWork {origin : String} (object : OriginObject origin)
    (now : Nat) : List WorkItem :=
  (if object.promise.state == .pending ∧ object.promise.timeoutAt ≤ now then
    [.promiseTimeout object.id]
  else []) ++
  originSettledWork object ++ originTaskWork object now

/-- Work discoverable in one origin document. The list order is stable and
newly enabled work is discovered only on a later Rover timeout. -/
def originWork (origin : String) (document : OriginDocument origin) (now : Nat) :
    List WorkItem :=
  document.flatMap fun object => originObjectWork object now

end Resonate.Direct
