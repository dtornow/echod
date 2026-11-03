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

def promiseCreateAt {origin : String} (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin origin) PromiseCreateRes := do
  if req.tags.timerTargeted then
    return { status := 400, promise := none }
  match ← readObject req.id.suffix now with
  | some o =>
      return { status := 200, promise := some (o.promise.toRecord o.id) }
  | none =>
      let o ← createPromiseAt req.id.suffix req.timeoutAt now req.param req.tags
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseCreate (req : PromiseCreateReq) (now : Nat) :
    Handler (.origin req.id.origin) PromiseCreateRes :=
  promiseCreateAt req now

def promiseSettleAt {origin : String} (req : PromiseSettleReq) (now : Nat) :
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
        return { status := 200, promise := some (p.toRecord o.id) }
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseSettle (req : PromiseSettleReq) (now : Nat) :
    Handler (.origin req.id.origin) PromiseSettleRes :=
  promiseSettleAt req now

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
            setPromise awaited.suffix (awaited.promise.addCallback req.awaiter)
          return { status := 200, promise := some (awaited.promise.toRecord awaited.id) }

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) :
    Handler (.origin req.awaited.origin) PromiseRegisterListenerRes := do
  match ← readObject req.awaited.suffix now with
  | none => return { status := 404 }
  | some awaited =>
      if !awaited.promise.otype.awaitable then return { status := 422 }
      if awaited.promise.state == .pending then
        setPromise awaited.suffix (awaited.promise.addListener req.address)
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
  match ← readObject action.id.suffix now with
  | none =>
      if action.timeoutAt > now then
        let p : PromiseObject :=
          { state := .pending,
            param := action.param,
            tags := action.tags,
            timeoutAt := action.timeoutAt,
            createdAt := now }
        setPromise action.id.suffix p
        let t : TaskObject :=
          { state := .acquired,
            version := 1,
            ttl := some req.ttl,
            pid := some req.pid,
            leaseTimeoutAt := some (now + req.ttl) }
        setTask action.id.suffix t
        return { status := 200, task := some (t.toRecord action.id), promise := some (p.toRecord action.id) }
      else
        let p : PromiseObject :=
          { state := .rejectedTimedout,
            param := action.param,
            tags := action.tags,
            timeoutAt := action.timeoutAt,
            createdAt := action.timeoutAt,
            settledAt := some action.timeoutAt }
        setPromise action.id.suffix p
        let t : TaskObject := { state := .fulfilled, version := 0 }
        setTask action.id.suffix t
        return { status := 200, task := some (t.toRecord action.id), promise := some (p.toRecord action.id) }
  | some o =>
      if o.promise.otype != .runnable then return { status := 422 }
      match o.task with
      | none => return { status := 409 }
      | some t =>
          if t.state == .fulfilled then
            return { status := 200, task := some (t.toRecord o.id), promise := some (o.promise.toRecord o.id) }
          else if t.state == .pending then
            let next := { t with
              state := .acquired
              version := t.version + 1
              ttl := some req.ttl
              pid := some req.pid
              leaseTimeoutAt := some (now + req.ttl)
              retryTimeoutAt := none
              resumes := [] }
            setTask o.suffix next
            return { status := 200, task := some (next.toRecord o.id), promise := some (o.promise.toRecord o.id) }
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
      setTask o.suffix next
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
          let response ← promiseCreateAt action now
          return { status := 200, action := some (.create response) }
      | .settle action =>
          let response ← promiseSettleAt action now
          return { status := 200, action := some (.settle response) }

def heartbeatOne {origin : String} (pid : String) (ref : TaskRef) (now : Nat) :
    Handler (.origin origin) Unit := do
  match ← readTask ref.id.suffix now with
  | none => pure ()
  | some (o, t) =>
      if t.state == .acquired ∧ t.version == ref.version ∧
          t.pid == some pid then
        setTask o.suffix
          { t with
            leaseTimeoutAt := some (now + t.ttl.getD 0) }

def heartbeatAll {origin : String} (pid : String) (now : Nat) :
    List TaskRef → Handler (.origin origin) Unit
  | [] => pure ()
  | ref :: rest => do
      heartbeatOne pid ref now
      heartbeatAll pid now rest

def taskHeartbeat (origin : String) (req : TaskHeartbeatReq) (now : Nat) :
    Handler (.origin origin) TaskHeartbeatRes := do
  if req.tasks.any (fun ref => ref.id.origin != origin) then
    return { status := 400 }
  heartbeatAll req.pid now req.tasks
  return { status := 200 }

def checkAwaited {origin : String} (now : Nat) :
    List PromiseRegisterCallbackReq → Handler (.origin origin) (Option Bool)
  | [] => return some false
  | action :: rest => do
      match ← readObject action.awaited.suffix now with
      | none => return none
      | some awaited =>
          if !awaited.promise.otype.awaitable then return none
          match ← checkAwaited now rest with
          | none => return none
          | some settled =>
              return some (settled || awaited.promise.state != .pending)

def registerAwaited {origin : String} (awaiter : Ident) (now : Nat) :
    List PromiseRegisterCallbackReq → Handler (.origin origin) Unit
  | [] => pure ()
  | action :: rest => do
      match ← readObject action.awaited.suffix now with
      | some awaited =>
          setPromise awaited.suffix (awaited.promise.addCallback awaiter)
      | none => pure ()
      registerAwaited awaiter now rest

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
      match ← checkAwaited now req.actions with
      | none => return { status := 422 }
      | some true =>
          setTask o.suffix { t with
            resumes := [] }
          return { status := 300 }
      | some false =>
          registerAwaited req.id now req.actions
          setTask o.suffix { t with
            state := .suspended
            pid := none
            ttl := none
            leaseTimeoutAt := none
            retryTimeoutAt := none
            resumes := [] }
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
      setTask o.suffix { t with
        state := .pending
        pid := none
        ttl := none
        leaseTimeoutAt := none
        retryTimeoutAt := some now }
      return { status := 200 }

def taskHalt (req : TaskHaltReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskHaltRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state == .fulfilled then return { status := 409 }
      if t.state == .halted then return { status := 200 }
      setTask o.suffix { t with
        state := .halted
        pid := none
        ttl := none
        leaseTimeoutAt := none
        retryTimeoutAt := none }
      return { status := 200 }

def taskContinue (req : TaskContinueReq) (now : Nat) :
    Handler (.origin req.id.origin) TaskContinueRes := do
  match ← readTask req.id.suffix now with
  | none => return { status := 404 }
  | some (o, t) =>
      if t.state != .halted then return { status := 409 }
      setTask o.suffix
        { t with
          state := .pending
          retryTimeoutAt := some now }
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
      setScheduleValue schedule
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
