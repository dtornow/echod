// The document a Resonate message carries: an origin's objects, or a schedule.

module Temp {
  datatype Opt<T> = None | Some(value: T)

  type Tag = (string, string)
  type Tags = seq<Tag>

  datatype Value = Value(headers: Tags, data: Opt<string>)

  datatype PromiseState =
    | Pending
    | Resolved
    | Rejected
    | RejectedCanceled
    | RejectedTimedout

  datatype TaskState = Pending | Acquired | Suspended | Halted | Fulfilled

  datatype Promise = Promise(
    state: PromiseState,
    param: Value,
    value: Value,
    tags: Tags,
    timeoutAt: nat,
    createdAt: nat,
    settledAt: Opt<nat>,
    callbacks: set<string>,
    listeners: set<string>)

  datatype Task = Task(
    state: TaskState,
    version: nat,
    pid: Opt<string>,
    ttl: Opt<nat>,
    leaseTimeoutAt: Opt<nat>,
    retryTimeoutAt: Opt<nat>,
    resumes: seq<string>)

  datatype Obj = Obj(promise: Promise, task: Opt<Task>)

  datatype Sched = Sched(
    id: string,
    cron: string,
    promiseId: string,
    promiseTimeout: nat,
    promiseParam: Value,
    promiseTags: Tags,
    nextRunAt: nat,
    lastRunAt: Opt<nat>,
    createdAt: nat)

  datatype Doc = Origin(stamp: nat, objects: map<string, Obj>) | Schedule(stamp: nat, slot: Opt<Sched>)

  datatype CreateReq = CreateReq(id: string, timeoutAt: nat, param: Value, tags: Tags)
  datatype SettleReq = SettleReq(id: string, state: PromiseState, value: Value)
  datatype CallbackReq = CallbackReq(awaited: string, awaiter: string)
  datatype ListenerReq = ListenerReq(awaited: string, address: string)
  datatype TaskRef = TaskRef(id: string, version: nat)
  datatype FenceAction = FenceCreate(create: CreateReq) | FenceSettle(settle: SettleReq)
  datatype FenceInner =
    | FenceCreated(status: nat, promise: Opt<Promise>)
    | FenceSettled(status: nat, promise: Opt<Promise>)
  datatype Request =
    | PromiseGet(id: string)
    | PromiseCreate(create: CreateReq)
    | PromiseSettle(settle: SettleReq)
    | PromiseRegisterCallback(callback: CallbackReq)
    | PromiseRegisterListener(listener: ListenerReq)
    | TaskGet(id: string)
    | TaskCreate(pid: string, ttl: nat, create: CreateReq)
    | TaskAcquire(id: string, version: nat, pid: string, ttl: nat)
    | TaskRelease(id: string, version: nat)
    | TaskFulfill(id: string, version: nat, settle: SettleReq)
    | TaskHalt(id: string)
    | TaskContinue(id: string)
    | TaskHeartbeat(pid: string, refs: seq<TaskRef>)
    | TaskSuspend(id: string, version: nat, suspend: seq<CallbackReq>)
    | TaskFence(id: string, version: nat, fence: FenceAction)
    | TaskFenceCheck(id: string, version: nat)
  datatype Answer =
    | Answer(status: nat, promise: Opt<Promise>)
    | Claim(status: nat, task: Opt<Task>, promise: Opt<Promise>)
    | Status(status: nat)
    | Fenced(status: nat, action: Opt<FenceInner>)
  datatype Applied = Applied(doc: Doc, answer: Answer, notes: seq<Note>)

  datatype Occurrence = Occurrence(promise: string, at: nat, timeout: nat, param: Value, tags: Tags)
  datatype Note = Execute(id: string, version: nat) | Unblock(address: string, id: string, promise: Promise)
  datatype Ran = Ran(doc: Doc, born: seq<Occurrence>, notes: seq<Note>)
  datatype Passed = Passed(objects: map<string, Obj>, notes: seq<Note>)

}
