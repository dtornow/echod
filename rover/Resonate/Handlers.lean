import Resonate.Machine

namespace Resonate.Direct

open ServerModel

def promiseGet (req : PromiseGetReq) (now : Nat) : H PromiseGetRes := do
  match ← readObject req.id now with
  | none => return { status := 404 }
  | some o =>
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseCreate (req : PromiseCreateReq) (now : Nat) : H PromiseCreateRes := do
  if req.tags.timerTargeted then
    return { status := 400, promise := none }
  match ← readObject req.id now with
  | some o =>
      return { status := 200, promise := some (o.promise.toRecord o.id) }
  | none =>
      let o ← createPromise req now
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseSettle (req : PromiseSettleReq) (now : Nat) : H PromiseSettleRes := do
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
        setSettled o p
        return { status := 200, promise := some (p.toRecord o.id) }
      return { status := 200, promise := some (o.promise.toRecord o.id) }

def promiseRegisterCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    H PromiseRegisterCallbackRes := do
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
            setPromise awaited.id (awaited.promise.addCallback req.awaiter)
          return { status := 200,
                   promise := some (awaited.promise.toRecord awaited.id) }

def promiseRegisterListener (req : PromiseRegisterListenerReq) (now : Nat) :
    H PromiseRegisterListenerRes := do
  match ← readObject req.awaited now with
  | none => return { status := 404 }
  | some awaited =>
      if !awaited.promise.otype.awaitable then return { status := 422 }
      if awaited.promise.state == .pending then
        setPromise awaited.id (awaited.promise.addListener req.address)
      return { status := 200,
               promise := some (awaited.promise.toRecord awaited.id) }

def promiseSearch (_req : PromiseSearchReq) (_now : Nat) :
    H PromiseSearchRes :=
  pure { status := 501 }

def taskGet (req : TaskGetReq) (now : Nat) : H TaskGetRes := do
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          return { status := 200, task := some (t.toRecord o.id) }

def taskCreate (req : TaskCreateReq) (now : Nat) : H TaskCreateRes := do
  let action := req.action
  if action.tags.otype != .runnable ∨ action.tags.timerTargeted then
    return { status := 400 }
  match ← readObject action.id now with
  | none =>
      if action.timeoutAt > now then
        let p : PromiseObject :=
          { state := .pending, param := action.param, tags := action.tags,
            timeoutAt := action.timeoutAt, createdAt := now }
        setPromise action.id p
        let t : TaskObject :=
          { state := .acquired, version := 1, ttl := some req.ttl,
            pid := some req.pid, leaseTimeoutAt := some (now + req.ttl) }
        setTask action.id t
        return { status := 200, task := some (t.toRecord action.id),
                 promise := some (p.toRecord action.id) }
      else
        let p : PromiseObject :=
          { state := .rejectedTimedout, param := action.param,
            tags := action.tags, timeoutAt := action.timeoutAt,
            createdAt := action.timeoutAt, settledAt := some action.timeoutAt }
        setPromise action.id p
        let t : TaskObject := { state := .fulfilled, version := 0 }
        setTask action.id t
        return { status := 200, task := some (t.toRecord action.id),
                 promise := some (p.toRecord action.id) }
  | some o =>
      if o.promise.otype != .runnable then return { status := 422 }
      match o.task with
      | none => return { status := 409 }
      | some t =>
          if t.state == .fulfilled then
            return { status := 200, task := some (t.toRecord o.id),
                     promise := some (o.promise.toRecord o.id) }
          else if t.state == .pending then
            let next :=
              { t with
                state := .acquired
                version := t.version + 1
                ttl := some req.ttl
                pid := some req.pid
                leaseTimeoutAt := some (now + req.ttl)
                retryTimeoutAt := none
                resumes := [] }
            setTask o.id next
            return { status := 200, task := some (next.toRecord o.id),
                     promise := some (o.promise.toRecord o.id) }
          return { status := 409 }

def taskAcquire (req : TaskAcquireReq) (now : Nat) : H TaskAcquireRes := do
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state != .pending then return { status := 409 }
          if o.promise.state != .pending then return { status := 409 }
          if t.version != req.version then return { status := 409 }
          let next :=
            { t with
              state := .acquired
              version := t.version + 1
              ttl := some req.ttl
              pid := some req.pid
              leaseTimeoutAt := some (now + req.ttl)
              retryTimeoutAt := none
              resumes := [] }
          setTask o.id next
          return { status := 200, task := some (next.toRecord o.id),
                   promise := some (o.promise.toRecord o.id) }

def taskFence (req : TaskFenceReq) (now : Nat) : H TaskFenceRes := do
  if req.action.targetId == req.id then return { status := 400 }
  if !req.action.targetId.sameOrigin req.id then return { status := 400 }
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state != .acquired then return { status := 409 }
          if o.promise.state != .pending then return { status := 409 }
          if t.version != req.version then return { status := 409 }
          match req.action with
          | .create action =>
              let response ← promiseCreate action now
              return { status := 200, action := some (.create response) }
          | .settle action =>
              let response ← promiseSettle action now
              return { status := 200, action := some (.settle response) }

def heartbeatOne (pid : String) (ref : TaskRef) (now : Nat) : H Unit := do
  match ← readTaskObject ref.id now with
  | none => pure ()
  | some o =>
      match o.task with
      | none => pure ()
      | some t =>
          if t.state == .acquired ∧ t.version == ref.version ∧
              t.pid == some pid ∧ o.promise.state == .pending then
            setTask o.id
              { t with leaseTimeoutAt := some (now + t.ttl.getD 0) }

def heartbeatAll (pid : String) (now : Nat) : List TaskRef → H Unit
  | [] => pure ()
  | ref :: rest => do
      heartbeatOne pid ref now
      heartbeatAll pid now rest

def taskHeartbeat (req : TaskHeartbeatReq) (now : Nat) :
    H TaskHeartbeatRes := do
  heartbeatAll req.pid now req.tasks
  return { status := 200 }

def checkAwaited (now : Nat) :
    List PromiseRegisterCallbackReq → H (Option Bool)
  | [] => return some false
  | action :: rest => do
      match ← readObject action.awaited now with
      | none => return none
      | some awaited =>
          if !awaited.promise.otype.awaitable then return none
          match ← checkAwaited now rest with
          | none => return none
          | some settled =>
              return some (settled || awaited.promise.state != .pending)

def registerAwaited (awaiter : Ident) (now : Nat) :
    List PromiseRegisterCallbackReq → H Unit
  | [] => pure ()
  | action :: rest => do
      match ← readObject action.awaited now with
      | some awaited =>
          setPromise awaited.id (awaited.promise.addCallback awaiter)
      | none => pure ()
      registerAwaited awaiter now rest

def taskSuspend (req : TaskSuspendReq) (now : Nat) : H TaskSuspendRes := do
  if req.actions.isEmpty then return { status := 400 }
  if req.actions.any (·.awaited == req.id) then return { status := 400 }
  if req.actions.any (fun action => !action.awaited.sameOrigin req.id) then
    return { status := 400 }
  let awaitedIds := req.actions.map (·.awaited)
  if awaitedIds.eraseDups.length != awaitedIds.length then
    return { status := 400 }
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state != .acquired then return { status := 409 }
          if o.promise.state != .pending then return { status := 409 }
          if t.version != req.version then return { status := 409 }
          match ← checkAwaited now req.actions with
          | none => return { status := 422 }
          | some true =>
              setTask o.id { t with resumes := [] }
              return { status := 300 }
          | some false =>
              registerAwaited req.id now req.actions
              setTask o.id
                { t with
                  state := .suspended
                  pid := none
                  ttl := none
                  leaseTimeoutAt := none
                  retryTimeoutAt := none
                  resumes := [] }
              return { status := 200 }

def taskFulfill (req : TaskFulfillReq) (now : Nat) : H TaskFulfillRes := do
  if !req.action.state.settable then return { status := 400 }
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state != .acquired then return { status := 409 }
          if o.promise.state != .pending then return { status := 409 }
          if t.version != req.version then return { status := 409 }
          let p :=
            { o.promise with
              state := req.action.state
              value := req.action.value
              settledAt := some now }
          setSettled o p
          return { status := 200, promise := some (p.toRecord o.id) }

def taskRelease (req : TaskReleaseReq) (now : Nat) : H TaskReleaseRes := do
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state != .acquired then return { status := 409 }
          if o.promise.state != .pending then return { status := 409 }
          if t.version != req.version then return { status := 409 }
          setTask o.id
            { t with
              state := .pending
              pid := none
              ttl := none
              leaseTimeoutAt := none
              retryTimeoutAt := some now }
          return { status := 200 }

def taskHalt (req : TaskHaltReq) (now : Nat) : H TaskHaltRes := do
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state == .fulfilled then return { status := 409 }
          if t.state == .halted then return { status := 200 }
          setTask o.id
            { t with
              state := .halted
              pid := none
              ttl := none
              leaseTimeoutAt := none
              retryTimeoutAt := none }
          return { status := 200 }

def taskContinue (req : TaskContinueReq) (now : Nat) :
    H TaskContinueRes := do
  match ← readTaskObject req.id now with
  | none => return { status := 404 }
  | some o =>
      match o.task with
      | none => return { status := 404 }
      | some t =>
          if t.state != .halted then return { status := 409 }
          if o.promise.state != .pending then return { status := 409 }
          setTask o.id
            { t with
              state := .pending
              retryTimeoutAt := some now }
          return { status := 200 }

def taskSearch (_req : TaskSearchReq) (_now : Nat) : H TaskSearchRes :=
  pure { status := 501 }

def scheduleGet (req : ScheduleGetReq) (_now : Nat) : H ScheduleGetRes := do
  match ← getSchedule req.id with
  | none => return { status := 404 }
  | some schedule =>
      return { status := 200, schedule := some schedule }

def scheduleCreate (req : ScheduleCreateReq) (now : Nat) :
    H ScheduleCreateRes := do
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
    H ScheduleDeleteRes := do
  match ← getSchedule req.id with
  | none => return { status := 404 }
  | some schedule =>
      delSchedule schedule.id
      return { status := 200 }

def scheduleSearch (_req : ScheduleSearchReq) (_now : Nat) :
    H ScheduleSearchRes :=
  pure { status := 501 }

end Resonate.Direct
