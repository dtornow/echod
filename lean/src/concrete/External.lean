import «concrete».Machine

/-! Independent concrete decisions for public requests. -/

namespace Resonate.Concrete.Decision

open ServerModel

def promiseGet (req : PromiseGetReq) (now : Nat) :
    Handler (.origin req.id.origin) PromiseGetRes := do
  match ← readObject req.id.suffix now with
  | none => return { status := 404 }
  | some o =>
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseCreate {origin : String} (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin origin) PromiseCreateRes := do
  if req.tags.timerTargeted then
    return { status := 400, promise := none }
  let o ← readOrCreate req now
  return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseSettle {origin : String} (req : PromiseSettleReq) (now : Nat) :
    Handler (.origin origin) PromiseSettleRes := do
  if !req.state.settable then return { status := 400 }
  match ← readObject req.id.suffix now with
  | none => return { status := 404 }
  | some o =>
      if o.promise.state == .pending then
        let p := { o.promise with
          state := req.state
          value := req.value
          settledAt := some now }
        setSettled o p
        return { status := 200, promise := some (p.toRecord req.id) }
      return { status := 200, promise := some (o.promise.toRecord req.id) }

def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler (.origin req.awaited.origin) PromiseRegisterCallbackRes := do
  if req.awaited == req.awaiter then return { status := 400 }
  if !req.awaited.sameOrigin req.awaiter then return { status := 400 }
  match ← readObject req.awaited.suffix now with
  | none => return { status := 404 }
  | some awaited =>
      match ← readObject req.awaiter.suffix now with
      | none => return { status := 422 }
      | some awaiter =>
          if awaiter.promise.otype != .runnable then return { status := 422 }
          if !awaited.promise.otype.awaitable then return { status := 422 }
          if awaited.promise.state == .pending &&
              awaiter.promise.state == .pending then
            setObject { awaited with promise := awaited.promise.addCallback req.awaiter }
          return { status := 200, promise := some (awaited.promise.toRecord awaited.id) }

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler (.origin req.awaited.origin) PromiseRegisterListenerRes := do
  match ← readObject req.awaited.suffix now with
  | none => return { status := 404 }
  | some awaited =>
      if !awaited.promise.otype.awaitable then return { status := 422 }
      if awaited.promise.state == .pending then
        setObject { awaited with promise := awaited.promise.addListener req.address }
      return { status := 200, promise := some (awaited.promise.toRecord awaited.id) }

def promiseSearch (_req : PromiseSearchReq) (_now : Nat) :
    PromiseSearchRes :=
  { status := 501 }

def taskGet (req : TaskGetReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskGetRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      return { status := 200, task := some (t.toRecord o.id) }

def taskCreate (req : TaskCreateReq) (now : Nat) :
    Handler (.origin req.action.id.origin) TaskCreateRes := do
  let action := req.action
  if action.tags.otype != .runnable ∨ action.tags.timerTargeted then
    return { status := 400 }
  let o ← readOrCreate action now
  if o.promise.otype != .runnable then return { status := 422 }
  match o.task with
  | none => return { status := 409 }
  | some t =>
      if t.state == .fulfilled then
        return { status := 200, task := some (t.toRecord action.id),
                 promise := some (o.promise.toRecord action.id) }
      else if t.state == .pending then
        let next := { t with
          state := .acquired
          version := t.version + 1
          ttl := some req.ttl
          pid := some req.pid
          leaseTimeoutAt := some (now + req.ttl)
          retryTimeoutAt := none
          resumes := [] }
        setObject { o with task := some next }
        return { status := 200, task := some (next.toRecord action.id),
                 promise := some (o.promise.toRecord action.id) }
      return { status := 409 }

def taskAcquire (req : TaskAcquireReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskAcquireRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .pending then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let next := { t with
        state := .acquired
        version := t.version + 1
        ttl := some req.ttl
        pid := some req.pid
        leaseTimeoutAt := some (now + req.ttl)
        retryTimeoutAt := none
        resumes := [] }
      setObject { o with task := some next }
      return { status := 200, task := some (next.toRecord o.id), promise := some (o.promise.toRecord o.id) }

def taskFence (req : TaskFenceReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskFenceRes := do
  if req.action.targetId == req.id then return { status := 400 }
  if !req.action.targetId.sameOrigin req.id then return { status := 400 }
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      match req.action with
      | .create action =>
          let response ← promiseCreate action now
          return { status := 200, action := some (.create response) }
      | .settle action =>
          let response ← promiseSettle action now
          return { status := 200, action := some (.settle response) }

def heartbeatOne {origin : String} (pid : String) (ref : TaskRef) (now : Nat) :
    Handler (.origin origin) Unit := do
  match ← readTask ref.id.suffix now with
  | none => pure ()
  | some (o, t) =>
      if t.state == .acquired ∧ t.version == ref.version ∧
          t.pid == some pid then
        setObject { o with task := some { t with
            leaseTimeoutAt := some (now + t.ttl.getD 0) } }

def taskHeartbeat (origin : String) (req : TaskHeartbeatReq) (now : Nat) :
    Handler (.origin origin) TaskHeartbeatRes := do
  if req.tasks.any (fun ref => ref.id.origin != origin) then
    return { status := 400 }
  req.tasks.forM (heartbeatOne req.pid · now)
  return { status := 200 }

def addCallback {origin : String} (awaiter : Ident) (now : Nat)
    (action : PromiseRegisterCallbackReq) : Handler (.origin origin) Unit := do
  match ← readObject action.awaited.suffix now with
  | some awaited =>
      setObject { awaited with promise := awaited.promise.addCallback awaiter }
  | none => pure ()

def taskSuspend (req : TaskSuspendReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskSuspendRes := do
  if req.actions.isEmpty then return { status := 400 }
  if req.actions.any (·.awaited == req.id) then return { status := 400 }
  if req.actions.any (fun action => !action.awaited.sameOrigin req.id) then
    return { status := 400 }
  let awaitedIds := req.actions.map (·.awaited)
  if awaitedIds.eraseDups.length != awaitedIds.length then
    return { status := 400 }
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let awaited ← req.actions.mapM (readObject ·.awaited.suffix now)
      if !awaited.all (·.any (·.promise.otype.awaitable)) then
        return { status := 422 }
      if awaited.any (·.any (·.promise.state != .pending)) then
        setObject { o with task := some { t with resumes := [] } }
        return { status := 300 }
      req.actions.forM (addCallback req.id now)
      setObject { o with task := some { t with
        state := .suspended
        pid := none
        ttl := none
        leaseTimeoutAt := none
        retryTimeoutAt := none
        resumes := [] } }
      return { status := 200 }

def taskFulfill (req : TaskFulfillReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskFulfillRes := do
  if !req.action.id.sameOrigin req.id then return { status := 400 }
  if !req.action.state.settable then return { status := 400 }
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let p := { o.promise with
        state := req.action.state
        value := req.action.value
        settledAt := some now }
      setSettled o p
      return { status := 200, promise := some (p.toRecord o.id) }

def taskRelease (req : TaskReleaseReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskReleaseRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      setObject { o with task := some { t with
        state := .pending
        pid := none
        ttl := none
        leaseTimeoutAt := none
        retryTimeoutAt := some now } }
      return { status := 200 }

def taskHalt (req : TaskHaltReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskHaltRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state == .fulfilled then return { status := 409 }
      if t.state == .halted then return { status := 200 }
      setObject { o with task := some { t with
        state := .halted
        pid := none
        ttl := none
        leaseTimeoutAt := none
        retryTimeoutAt := none } }
      return { status := 200 }

def taskContinue (req : TaskContinueReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskContinueRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .halted then return { status := 409 }
      setObject { o with task := some { t with
          state := .pending
          retryTimeoutAt := some now } }
      return { status := 200 }

def taskSearch (_req : TaskSearchReq) (_now : Nat) : TaskSearchRes :=
  { status := 501 }

def scheduleGet (req : ScheduleGetReq) (_now : Nat) :
    Handler (.schedule req.id) ScheduleGetRes := do
  match ← getSchedule with
  | none => return { status := 404 }
  | some schedule =>
      return { status := 200, schedule := some schedule }

def scheduleCreate (req : ScheduleCreateReq) (now : Nat) :
    Handler (.schedule req.id) ScheduleCreateRes := do
  if req.promiseTags.timerTargeted then return { status := 400 }
  match ← getSchedule with
  | some schedule =>
      return { status := 200, schedule := some schedule }
  | none =>
      let schedule : Schedule :=
        { id := req.id,
          cron := req.cron,
          promiseId := req.promiseId,
          promiseTimeout := req.promiseTimeout,
          promiseParam := req.promiseParam,
          promiseTags := req.promiseTags,
          createdAt := now,
          nextRunAt := nextCron req.cron now,
          lastRunAt := none }
      setSchedule schedule
      return { status := 200, schedule := some schedule }

def scheduleDelete (req : ScheduleDeleteReq) (_now : Nat) :
    Handler (.schedule req.id) ScheduleDeleteRes := do
  match ← getSchedule with
  | none => return { status := 404 }
  | some _ =>
      delSchedule
      return { status := 200 }

def scheduleSearch (_req : ScheduleSearchReq) (_now : Nat) :
    ScheduleSearchRes :=
  { status := 501 }

end Resonate.Concrete.Decision
