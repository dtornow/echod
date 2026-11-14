import «abstract».Machine

namespace Resonate.Abstract

open ServerModel

def promiseGet (req : PromiseGetReq) (now : Nat) : Handler PromiseGetRes := do
  match ← readObject req.id now with
  | none => return { status := 404 }
  | some o =>
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseCreate (req : PromiseCreateReq) (now : Nat) :
    Handler PromiseCreateRes := do
  if req.tags.timerTargeted then
    return { status := 400, promise := none }
  let o ← readOrCreate req now
  return { status := 200, promise := some (o.promise.toRecord o.id) }

/-- Wake `awaiter` because `awaited` settled. -/
def settleResume (awaited awaiter : Ident) (now : Nat) : Handler Unit := do
  match ← readTask awaiter now with
  | none => pure ()
  | some (object, task) =>
      match task.state with
      | .suspended =>
          setObject { object with
            task := some { task with
              state := .pending
              resumes := [awaited]
              retryTimeoutAt := some now } }
      | .pending | .acquired | .halted =>
          if !(task.resumes.contains awaited) then
            setObject { object with
              task := some { task with resumes := task.resumes ++ [awaited] } }
      | .fulfilled => pure ()

/-- Drop one callback and resume its task. A pending promise has not settled. -/
def settleCallback (req : PromiseRegisterCallbackReq) (now : Nat) : Handler Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.callbacks.contains req.awaiter then
        setObject { awaited with
          promise.callbacks := awaited.promise.callbacks.filter (· != req.awaiter) }
        settleResume req.awaited req.awaiter now

/-- Drop one listener and tell it. -/
def settleListener (req : PromiseRegisterListenerReq) (now : Nat) : Handler Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.listeners.contains req.address then
        setObject { awaited with
          promise.listeners := awaited.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (awaited.promise.toRecord req.awaited))

def wasDue (id : Ident) (now : Nat) : Handler Bool := do
  match ← readObject id now with
  | none => return false
  | some object => return retryDue object.promise object.task now

/-- Offer a task this settlement woke. A retry that was already due stays. -/
def offerIfNew (awaiter : Ident) (due : Bool) (now : Nat) : Handler Unit := do
  if due then
    pure ()
  else
    match ← readTask awaiter now with
    | none => pure ()
    | some (object, task) =>
        match task.retryTimeoutAt with
        | none => pure ()
        | some due =>
            if task.state == .pending ∧ due ≤ now ∧ object.promise.state == .pending then
              let env ← ask
              setObject { object with
                task := some { task with retryTimeoutAt := some (now + env.config.retryTimeout) } }
              setMessage
                ((object.promise.tags.get? "resonate:target").getD "")
                (.execute awaiter task.version)
            else
              pure ()

/-- Resume the tasks registered on `id`, tell its listeners, and offer a task
this resume made due. -/
def resumeRegistered (id : Ident) (callbacks : List Ident) (listeners : List String)
    (now : Nat) : Handler Unit := do
  let mine := callbacks.filter (·.sameOrigin id)
  let dues ← mine.mapM (wasDue · now)
  mine.forM fun awaiter =>
    settleCallback { awaited := id, awaiter } now
  listeners.forM fun address =>
    settleListener { awaited := id, address } now
  (mine.zip dues).forM fun (awaiter, due) =>
    offerIfNew awaiter due now

def promiseSettle (req : PromiseSettleReq) (now : Nat) :
    Handler PromiseSettleRes := do
  if !req.state.settable then
    return { status := 400 }
  match ← readObject req.id now with
  | none => return { status := 404 }
  | some o =>
      if o.promise.state == .pending then
        let p := { o.promise with
          state := req.state
          value := req.value
          settledAt := some now }
        setSettled o p now
        resumeRegistered req.id p.callbacks p.listeners now
        return { status := 200, promise := some (p.toRecord req.id) }
      return { status := 200, promise := some (o.promise.toRecord req.id) }

/-- Read the awaited promise and the awaiter. Origins are compared on the
ids, and only the awaited promise is written. -/
def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    Handler PromiseRegisterCallbackRes := do
  if req.awaited == req.awaiter then return { status := 400 }
  if !req.awaited.sameOrigin req.awaiter then return { status := 400 }
  match ← readObject req.awaited now with
  | none => return { status := 404 }
  | some awaited =>
      match ← readObject req.awaiter now with
      | none => return { status := 422 }
      | some awaiter =>
          if awaiter.promise.otype != .runnable then return { status := 422 }
          if !awaited.promise.otype.awaitable then return { status := 422 }
          if awaited.promise.state == .pending &&
              awaiter.promise.state == .pending then
            setObject { awaited with promise := awaited.promise.addCallback req.awaiter }
          return { status := 200,
                   promise := some (awaited.promise.toRecord req.awaited) }

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler PromiseRegisterListenerRes := do
  match ← readObject req.awaited now with
  | none => return { status := 404 }
  | some awaited =>
      if !awaited.promise.otype.awaitable then return { status := 422 }
      if awaited.promise.state == .pending then
        setObject { awaited with promise := awaited.promise.addListener req.address }
      return { status := 200,
               promise := some (awaited.promise.toRecord req.awaited) }

def promiseSearch (_req : PromiseSearchReq) (_now : Nat) :
    PromiseSearchRes :=
  { status := 501 }

def taskGet (req : TaskGetReq) (now : Nat) : Handler TaskGetRes := do
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (_, t) => return { status := 200, task := some (t.toRecord req.id) }

def taskCreate (req : TaskCreateReq) (now : Nat) : Handler TaskCreateRes := do
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
        let next := t.acquire req.pid req.ttl now
        setObject { o with task := some next }
        return { status := 200, task := some (next.toRecord action.id),
                 promise := some (o.promise.toRecord action.id) }
      return { status := 409 }

def taskAcquire (req : TaskAcquireReq) (now : Nat) : Handler TaskAcquireRes := do
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .pending then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let next := t.acquire req.pid req.ttl now
      setObject { o with task := some next }
      return { status := 200, task := some (next.toRecord req.id),
               promise := some (o.promise.toRecord req.id) }

def taskFence (req : TaskFenceReq) (now : Nat) : Handler TaskFenceRes := do
  if req.action.targetId == req.id then return { status := 400 }
  if !req.action.targetId.sameOrigin req.id then return { status := 400 }
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (_, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      match req.action with
      | .create action =>
          let response ← promiseCreate action now
          return { status := 200, action := some (.create response) }
      | .settle action =>
          let response ← promiseSettle action now
          return { status := 200, action := some (.settle response) }

def heartbeatOne (pid : String) (ref : TaskRef) (now : Nat) : Handler Unit := do
  match ← readTask ref.id now with
  | none => pure ()
  | some (o, t) =>
      if t.state == .acquired ∧ t.version == ref.version ∧ t.pid == some pid then
        setObject { o with task := some { t with leaseTimeoutAt := some (now + t.ttl.getD 0) } }

/-- Every task in one heartbeat must share an origin. -/
def taskHeartbeat (req : TaskHeartbeatReq) (now : Nat) :
    Handler TaskHeartbeatRes := do
  match req.tasks with
  | [] => return { status := 200 }
  | first :: _ =>
      if !sameOriginRefs first.id.origin req.tasks then return { status := 400 }
      req.tasks.forM (heartbeatOne req.pid · now)
      return { status := 200 }

/-- Add `awaiter` to the callbacks of the awaited promise. -/
def addCallback (awaiter : Ident) (now : Nat)
    (action : PromiseRegisterCallbackReq) : Handler Unit := do
  match ← readObject action.awaited now with
  | some awaited =>
      setObject { awaited with promise := awaited.promise.addCallback awaiter }
  | none => pure ()

def taskSuspend (req : TaskSuspendReq) (now : Nat) : Handler TaskSuspendRes := do
  if req.actions.isEmpty then return { status := 400 }
  if req.actions.any (·.awaited == req.id) then return { status := 400 }
  if req.actions.any (fun action => !action.awaited.sameOrigin req.id) then
    return { status := 400 }
  let awaitedIds := req.actions.map (·.awaited)
  if awaitedIds.eraseDups.length != awaitedIds.length then
    return { status := 400 }
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let awaited ← req.actions.mapM (readObject ·.awaited now)
      if !awaited.all (·.any (·.promise.otype.awaitable)) then
        return { status := 422 }
      if awaited.any (·.any (·.promise.state != .pending)) then
        setObject { o with task := some { t with resumes := [] } }
        return { status := 300 }
      req.actions.forM (addCallback req.id now)
      setObject { o with task := some { t.unlease .suspended none with resumes := [] } }
      return { status := 200 }

def taskFulfill (req : TaskFulfillReq) (now : Nat) : Handler TaskFulfillRes := do
  if !req.action.id.sameOrigin req.id then return { status := 400 }
  if !req.action.state.settable then return { status := 400 }
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      let p :=
        { o.promise with
          state := req.action.state
          value := req.action.value
          settledAt := some now }
      setSettled o p now
      return { status := 200, promise := some (p.toRecord req.id) }

def taskRelease (req : TaskReleaseReq) (now : Nat) : Handler TaskReleaseRes := do
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .acquired then return { status := 409 }
      if t.version != req.version then return { status := 409 }
      setObject { o with task := some (t.unlease .pending (some now)) }
      return { status := 200 }

def taskHalt (req : TaskHaltReq) (now : Nat) : Handler TaskHaltRes := do
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state == .fulfilled then return { status := 409 }
      if t.state == .halted then return { status := 200 }
      setObject { o with task := some (t.unlease .halted none) }
      return { status := 200 }

def taskContinue (req : TaskContinueReq) (now : Nat) : Handler TaskContinueRes := do
  match ← readTask req.id now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .halted then return { status := 409 }
      setObject { o with task := some { t with state := .pending, retryTimeoutAt := some now } }
      return { status := 200 }

def taskSearch (_req : TaskSearchReq) (_now : Nat) : TaskSearchRes :=
  { status := 501 }

def scheduleGet (req : ScheduleGetReq) (_now : Nat) : Handler ScheduleGetRes := do
  match ← getSchedule req.id with
  | none => return { status := 404 }
  | some schedule =>
      return { status := 200, schedule := some schedule }

def scheduleCreate (req : ScheduleCreateReq) (now : Nat) :
    Handler ScheduleCreateRes := do
  if req.promiseTags.timerTargeted then return { status := 400 }
  match ← getSchedule req.id with
  | some schedule =>
      return { status := 200, schedule := some schedule }
  | none =>
      let schedule : Schedule :=
        { id := req.id, cron := req.cron, promiseId := req.promiseId,
          promiseTimeout := req.promiseTimeout,
          promiseParam := req.promiseParam, promiseTags := req.promiseTags,
          createdAt := now, nextRunAt := nextCron req.cron now,
          lastRunAt := none }
      setSchedule schedule
      return { status := 200, schedule := some schedule }

def scheduleDelete (req : ScheduleDeleteReq) (_now : Nat) :
    Handler ScheduleDeleteRes := do
  match ← getSchedule req.id with
  | none => return { status := 404 }
  | some _ =>
      deleteSchedule req.id
      return { status := 200 }

def scheduleSearch (_req : ScheduleSearchReq) (_now : Nat) :
    ScheduleSearchRes :=
  { status := 501 }

end Resonate.Abstract
