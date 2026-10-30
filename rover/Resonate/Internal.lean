import Resonate.Handlers

namespace Resonate.Direct

open ServerModel
abbrev InternalStep := Abstraction.InternalStep

def resumeOne (awaited awaiter : Ident) (now : Nat) : H Unit := do
  match ← readTaskObject awaiter now with
  | none => pure ()
  | some o =>
      match o.task with
      | none => pure ()
      | some t =>
          match t.state with
          | .suspended =>
              setTask o.id
                { t with
                  state := .pending
                  resumes := [awaited]
                  retryTimeoutAt := some now }
          | .pending | .acquired | .halted =>
              if !(t.resumes.contains awaited) then
                setTask o.id
                  { t with resumes := t.resumes ++ [awaited] }
          | .fulfilled => pure ()

def processCallback (req : PromiseRegisterCallbackReq) (now : Nat) :
    H Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.callbacks.contains req.awaiter then
        setPromise awaited.id
          { awaited.promise with
            callbacks := awaited.promise.callbacks.filter (· != req.awaiter) }
        resumeOne awaited.id req.awaiter now

def processListener (req : PromiseRegisterListenerReq) (now : Nat) :
    H Unit := do
  match ← readObject req.awaited now with
  | none => pure ()
  | some awaited =>
      if awaited.promise.state == .pending then pure ()
      else if awaited.promise.listeners.contains req.address then
        setPromise awaited.id
          { awaited.promise with
            listeners := awaited.promise.listeners.filter (· != req.address) }
        setMessage req.address (.unblock (awaited.promise.toRecord awaited.id))

def processLeaseTimeout (req : TaskLeaseTimeoutReq) (now : Nat) :
    H Unit := do
  match ← readTaskObject req.id now with
  | none => pure ()
  | some o =>
      match o.task with
      | none => pure ()
      | some t =>
          match t.leaseTimeoutAt with
          | none => pure ()
          | some deadline =>
              if t.state == .acquired ∧ deadline ≤ now ∧
                  o.promise.state == .pending then
                setTask o.id
                  { t with
                    state := .pending
                    pid := none
                    ttl := none
                    leaseTimeoutAt := none
                    retryTimeoutAt := some now }

def processRetryTimeout (req : TaskRetryTimeoutReq) (now : Nat) :
    H Unit := do
  match ← readTaskObject req.id now with
  | none => pure ()
  | some o =>
      match o.task with
      | none => pure ()
      | some t =>
          match t.retryTimeoutAt with
          | none => pure ()
          | some due =>
              if t.state == .pending ∧ due ≤ now ∧
                  o.promise.state == .pending then
                let config ← ask
                setTask o.id
                  { t with
                    retryTimeoutAt := some (now + config.config.retryTimeout) }
                setMessage
                  ((o.promise.tags.get? "resonate:target").getD "")
                  (.execute o.id t.version)

def fireOccurrence (schedule : Schedule) (time : Nat) : H Unit :=
  createIfAbsent
    { id := expand schedule.promiseId schedule.id time,
      timeoutAt := time + schedule.promiseTimeout,
      param := schedule.promiseParam, tags := schedule.promiseTags }
    time

def fireAll (schedule : Schedule) : List Nat → H Unit
  | [] => pure ()
  | time :: rest => do
      fireOccurrence schedule time
      fireAll schedule rest

def processSchedule (req : ScheduleTimeoutReq) (now : Nat) : H Unit := do
  match ← getSchedule req.schedule with
  | none => pure ()
  | some schedule =>
      let times :=
        (occurrences schedule.cron schedule.nextRunAt now).filter (· ≤ now)
      fireAll schedule times
      match times.getLast? with
      | some last =>
          setSchedule
            { schedule with
              lastRunAt := some last
              nextRunAt := nextCron schedule.cron last }
      | none => pure ()

def handleInternal : InternalStep → Nat → H Unit
  | .promiseTimeout req, now =>
      modify fun state =>
        { state with objects := state.objects.map fun object =>
            if object.id == req.id then object.project now else object }
  | .callback req, now => processCallback req now
  | .listener req, now => processListener req now
  | .taskLeaseTimeout req, now => processLeaseTimeout req now
  | .taskRetryTimeout req, now => processRetryTimeout req now
  | .scheduleTimeout req, now => processSchedule req now

/-- Run a fixed list of process-local work in order. Reader+State+Writer bind
makes each handler observe earlier writes and preserves emission order. -/
def handleInternals (steps : List InternalStep) (now : Nat) : H Unit :=
  match steps with
  | [] => pure ()
  | step :: rest => do
      handleInternal step now
      handleInternals rest now

/-- Work enabled in one projected-state snapshot. Handlers may enable later
work, but it is absent from this list until the next timeout. -/
def internalSteps (state : State) (now : Nat) : List InternalStep :=
  let objects := state.objects.flatMap fun o =>
    (if o.promise.state == .pending then [] else
      (o.promise.callbacks.map fun awaiter =>
        Abstraction.InternalStep.callback { awaited := o.id, awaiter }) ++
      (o.promise.listeners.map fun address =>
        Abstraction.InternalStep.listener { awaited := o.id, address })) ++
    (match o.task with
     | none => []
     | some task =>
         (match task.leaseTimeoutAt with
          | some due =>
              if task.state == .acquired ∧ due ≤ now ∧
                  o.promise.state == .pending then
                [Abstraction.InternalStep.taskLeaseTimeout { id := o.id }]
              else []
          | none => []) ++
         (match task.retryTimeoutAt with
          | some due =>
              if task.state == .pending ∧ due ≤ now ∧
                  o.promise.state == .pending then
                [Abstraction.InternalStep.taskRetryTimeout { id := o.id }]
              else []
          | none => []))
  objects ++ state.schedules.map fun schedule =>
    Abstraction.InternalStep.scheduleTimeout { schedule := schedule.id }

end Resonate.Direct
