include "../framework/order.dfy"

// One node handler, the document half of `spec_handle`.
//
// A document is an origin's objects, or a schedule, and the stamp of the
// step that wrote it: the processing time. `WellFormed` is the catalogue
// for that document at that instant: the promise rows, the task rows, and,
// when the document is a schedule, the schedule rows. A document the
// handler leaves is caught up at its stamp. No promise is still pending
// with a deadline at or before that processing time; the sweep timed every
// one of those out before the call ran, and the call does not put one back.
// Before the handler, the document is swept at that instant. Every promise
// whose deadline has passed is timed out first. A timeout leaves that
// promise's callbacks in place, and the next pass applies them: every
// callback on a settled promise, least id first. Listeners are told the
// same way. A lease and a
// retry still due on a promise that is still pending come after that. A
// schedule is its next run. The promise calls then see that document.
// Get answers from the projection and does not write it back. Create refuses
// a timer that is also targeted. An id already present is answered as it
// stands, projected at `now`, and not written back. A new id is inserted,
// and a schedule document becomes an origin to hold it. Settle writes only
// a promise the projection still shows as pending, fulfills its task, and
// resumes the tasks registered on it. A listener of that promise is told,
// and a task resumed at this instant is offered, in that same step.
// A callback is recorded only while both promises are still pending, and
// only for another id of the same origin. A listener is recorded only while
// the promise is still pending. A schedule is opened into an empty origin
// before a lookup. The task calls read that same projection. Create reads
// or creates the promise, then takes a pending task. Acquire takes a
// pending task. Release, halt, and continue park it. Fulfill settles the
// task's own promise and fulfills the task, and does not resume what was
// registered on it. A fence that settles uses Settle, so that resume
// happens there. Suspend records the task on each awaited promise, then
// parks it. A heartbeat extends the lease of each acquired task it names.
// The sweep and the handler each leave a well-formed document well-formed.

module Node {
  import opened Keys
  datatype Opt<T> = None | Some(value: T)

  type Tag = (string, string)
  type Tags = seq<Tag>

  datatype Value = Value(headers: Tags, data: Opt<string>)

  function Empty(): Value { Value([], None) }

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

  // The cron engine. The sweep uses one fact: the next run is later.
  function {:axiom} NextCron(cron: string, at: nat): nat
    ensures NextCron(cron, at) > at

  // The id a schedule template expands to at an instant.
  function Expand(template: string, id: string, at: nat): string

  // Everything before the first `:`, or the whole string when there is none.
  function OriginOf(s: string): string
    decreases |s|
  {
    if |s| == 0 then ""
    else if s[0] == ':' then ""
    else [s[0]] + OriginOf(s[1..])
  }

  predicate TagIs(tags: Tags, key: string, value: string)
    decreases |tags|
  {
    if |tags| == 0 then false
    else if tags[0].0 == key then tags[0].1 == value
    else TagIs(tags[1..], key, value)
  }

  predicate TagKey(tags: Tags, key: string)
    decreases |tags|
  {
    if |tags| == 0 then false
    else if tags[0].0 == key then true
    else TagKey(tags[1..], key)
  }

  predicate Timer(tags: Tags) { TagIs(tags, "resonate:timer", "true") }
  predicate Targeted(tags: Tags) { TagKey(tags, "resonate:target") }
  predicate External(tags: Tags) { TagIs(tags, "resonate:external", "true") }
  predicate Global(tags: Tags) { TagIs(tags, "resonate:scope", "global") }
  predicate Awaitable(tags: Tags) { Targeted(tags) || Timer(tags) || External(tags) || Global(tags) }

  predicate Settable(state: PromiseState) {
    state == PromiseState.Resolved || state == PromiseState.Rejected || state == PromiseState.RejectedCanceled
  }

  ghost predicate Distinct(xs: seq<string>) {
    forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
  }

  ghost predicate Cleared(t: Task) {
    t.pid.None? && t.ttl.None? && t.retryTimeoutAt.None?
  }

  // The promise rows of the catalogue, for one promise at one `now`.
  // Callbacks and listeners are sets, so a duplicate cannot be stored.
  ghost predicate PromiseOk(p: Promise, now: nat) {
    && p.createdAt <= p.timeoutAt
    && (p.settledAt.Some? ==> p.settledAt.value <= p.timeoutAt)
    && (p.settledAt.Some? ==> p.createdAt <= p.settledAt.value)
    && ((p.state != PromiseState.Pending) == p.settledAt.Some?)
    && (p.state == PromiseState.Pending ==> p.createdAt < p.timeoutAt)
    && (p.state == PromiseState.Pending ==> p.value.data.None?)
    && (p.settledAt == Some(p.timeoutAt) ==> p.value.data.None?)
    && (p.state == PromiseState.RejectedTimedout ==> p.settledAt == Some(p.timeoutAt))
    && p.createdAt <= now
    && (p.settledAt.Some? ==> p.settledAt.value <= now)
  }

  ghost predicate TaskOk(task: Opt<Task>) {
    match task
    case None => true
    case Some(t) =>
      && ((t.state == TaskState.Acquired) == t.pid.Some?)
      && ((t.state == TaskState.Acquired) == t.ttl.Some?)
      && ((t.state == TaskState.Pending) == t.retryTimeoutAt.Some?)
      && (t.state == TaskState.Fulfilled ==> Cleared(t))
      && (t.state == TaskState.Suspended ==> Cleared(t))
      && (t.state == TaskState.Halted ==> Cleared(t))
      && (t.state == TaskState.Suspended ==> |t.resumes| == 0)
      && Distinct(t.resumes)
      && (t.state == TaskState.Acquired ==> t.version > 0)
  }

  ghost predicate ScheduleOk(s: Sched) {
    && s.createdAt <= s.nextRunAt
    && (s.lastRunAt.Some? ==> s.createdAt <= s.lastRunAt.value)
    && (s.lastRunAt.Some? ==> s.lastRunAt.value < s.nextRunAt)
  }

  ghost predicate ObjectOk(id: string, o: Obj, now: nat) {
    && PromiseOk(o.promise, now)
    && TaskOk(o.task)
    && id !in o.promise.callbacks
    && (forall awaiter :: awaiter in o.promise.callbacks ==> OriginOf(id) == OriginOf(awaiter))
  }

  ghost predicate MapOk(objects: map<string, Obj>, now: nat) {
    forall id :: id in objects ==> ObjectOk(id, objects[id], now)
  }

  ghost predicate WellFormed(doc: Doc, now: nat) {
    match doc
    case Origin(_, objects) => MapOk(objects, now)
    case Schedule(_, slot) => slot.Some? ==> ScheduleOk(slot.value)
  }

  // No promise deadline at or before `now` is still pending.
  ghost predicate OnTime(objects: map<string, Obj>, now: nat) {
    forall id :: id in objects ==>
      objects[id].promise.state == PromiseState.Pending ==> now < objects[id].promise.timeoutAt
  }

  // Written at the processing time, with every due promise deadline timed out.
  ghost predicate CaughtUp(doc: Doc, now: nat) {
    doc.stamp == now && OnTime(ObjectsOf(doc), now)
  }

  function ObjectsOf(doc: Doc): map<string, Obj> {
    match doc
    case Origin(_, objects) => objects
    case Schedule(_, _) => map[]
  }

  function NewPromise(timeout: nat, now: nat, param: Value, tags: Tags): (p: Promise)
    ensures PromiseOk(p, now)
    ensures p.callbacks == {}
    ensures p.state == PromiseState.Pending ==> now < p.timeoutAt
  {
    if timeout > now then
      Promise(PromiseState.Pending, param, Empty(), tags, timeout, now, None, {}, {})
    else if Timer(tags) then
      Promise(PromiseState.Resolved, param, Empty(), tags, timeout, timeout, Some(timeout), {}, {})
    else
      Promise(PromiseState.RejectedTimedout, param, Empty(), tags, timeout, timeout, Some(timeout), {}, {})
  }

  // The offer time is `now`. A `resonate:delay` tag is not read yet.
  function NewTask(timeout: nat, now: nat): (t: Task)
    ensures TaskOk(Some(t))
  {
    if timeout > now then
      Task(TaskState.Pending, 0, None, None, None, Some(now), [])
    else
      Task(TaskState.Fulfilled, 0, None, None, None, None, [])
  }

  function NewObj(timeout: nat, now: nat, param: Value, tags: Tags, runnable: bool): (o: Obj)
    ensures PromiseOk(o.promise, now) && TaskOk(o.task) && o.promise.callbacks == {}
  {
    Obj(NewPromise(timeout, now, param, tags), if runnable then Some(NewTask(timeout, now)) else None)
  }

  // A pending promise whose deadline has passed is answered as settled.
  // The stored promise is left as it was.
  function ProjectPromise(p: Promise, now: nat): Promise {
    if p.state == PromiseState.Pending && now >= p.timeoutAt then
      Promise(
        if Timer(p.tags) then PromiseState.Resolved else PromiseState.RejectedTimedout,
        p.param, p.value, p.tags, p.timeoutAt, p.createdAt,
        Some(p.timeoutAt), p.callbacks, p.listeners)
    else
      p
  }

  function Fulfill(t: Task): Task {
    Task(TaskState.Fulfilled, t.version, None, None, None, None, [])
  }

  function Project(o: Obj, now: nat): Obj {
    var promise := ProjectPromise(o.promise, now);
    var task :=
      if promise.state == PromiseState.Pending then o.task
      else
        match o.task
        case None => None
        case Some(t) => if t.state == TaskState.Fulfilled then Some(t) else Some(Fulfill(t));
    Obj(promise, task)
  }

  lemma InsertOk(doc: Doc, id: string, obj: Obj, now: nat)
    requires WellFormed(doc, now)
    requires PromiseOk(obj.promise, now) && TaskOk(obj.task) && obj.promise.callbacks == {}
    requires id !in ObjectsOf(doc)
    ensures WellFormed(Origin(doc.stamp, ObjectsOf(doc)[id := obj]), now)
  {
    var objects := ObjectsOf(doc);
    var placed := objects[id := obj];
    forall k | k in placed
      ensures ObjectOk(k, placed[k], now)
    {
      if k == id {
        assert placed[k] == obj;
        assert id !in obj.promise.callbacks;
      } else {
        assert k in objects && placed[k] == objects[k];
        match doc
        case Origin(_, os) =>
          assert os == objects;
        case Schedule(_, _) =>
          assert objects == map[];
          assert false;
      }
    }
  }

  function Create(doc: Doc, req: CreateReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if Timer(req.tags) && Targeted(req.tags) then
      Applied(doc, Answer(400, None), [])
    else
      var objects := ObjectsOf(doc);
      if req.id in objects then
        var seen := Project(objects[req.id], now);
        Applied(doc, Answer(200, Some(seen.promise)), [])
      else
        var obj := NewObj(req.timeoutAt, now, req.param, req.tags, Targeted(req.tags));
        var doc' := Origin(now, objects[req.id := obj]);
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) { InsertOk(doc, req.id, obj, now); }
        }
        Applied(doc', Answer(200, Some(obj.promise)), [])
  }

  // A schedule has no rows. Looking one up is the empty origin.
  function Opened(doc: Doc): (r: Doc)
    ensures r.stamp == doc.stamp
    ensures ObjectsOf(r) == ObjectsOf(doc)
  {
    Origin(doc.stamp, ObjectsOf(doc))
  }

  function Get(doc: Doc, id: string, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if id !in objects then Applied(shown, Answer(404, None), [])
    else Applied(shown, Answer(200, Some(Project(objects[id], now).promise)), [])
  }

  function Settled(o: Obj, state: PromiseState, value: Value, now: nat): Obj {
    var promise := o.promise.(state := state, value := value, settledAt := Some(now));
    var task :=
      match o.task
      case None => None
      case Some(t) => if t.state == TaskState.Fulfilled then Some(t) else Some(Fulfill(t));
    Obj(promise, task)
  }

  function Settle(doc: Doc, req: SettleReq, now: nat, retry: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if !Settable(req.state) then Applied(doc, Answer(400, None), [])
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      if req.id !in objects then Applied(shown, Answer(404, None), [])
      else
        var seen := Project(objects[req.id], now);
        if seen.promise.state != PromiseState.Pending then
          Applied(shown, Answer(200, Some(seen.promise)), [])
        else
          var obj := Settled(seen, req.state, req.value, now);
          var placed := objects[req.id := obj];
          var resumed := Callbacks(placed, req.id, now);
          var told := Listeners(resumed, req.id);
          var waiting := obj.promise.callbacks;
          SortedProps(waiting);
          var ids := Sorted(waiting);
          forall i, j | 0 <= i < j < |ids|
            ensures ids[i] != ids[j]
          {
            assert Lt(ids[i], ids[j]);
          }
          var armed := Offer(placed, told.objects, ids, now, retry);
          var doc' := Origin(now, armed.objects);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              StillPending(objects[req.id], now);
              SettledOk(req.id, seen, req.state, req.value, now);
              ReplaceOk(objects, req.id, obj, now);
              CallbacksOk(placed, req.id, now);
              ListenersOk(resumed, req.id, now);
              assert placed.Keys == resumed.Keys == told.objects.Keys;
              OfferOk(placed, told.objects, ids, now, retry);
            }
          }
          assert CaughtUp(doc, now) ==> CaughtUp(doc', now) by {
            if CaughtUp(doc, now) {
              assert shown.stamp == doc.stamp;
              assert ObjectsOf(shown) == ObjectsOf(doc);
              assert OnTime(objects, now);
              ReplaceOnTime(objects, req.id, obj, now);
              CallbacksClock(placed, req.id, now);
              ClockOnTime(placed, resumed, now);
              ListenersClock(resumed, req.id);
              ClockOnTime(resumed, told.objects, now);
              assert placed.Keys == told.objects.Keys;
              OfferClock(placed, told.objects, ids, now, retry);
              ClockOnTime(told.objects, armed.objects, now);
            }
          }
          Applied(doc', Answer(200, Some(obj.promise)), told.notes + armed.notes)
  }

  function AddCallback(o: Obj, awaiter: string): Obj {
    if awaiter in o.promise.callbacks then o
    else Obj(o.promise.(callbacks := o.promise.callbacks + {awaiter}), o.task)
  }

  function RegisterCallback(doc: Doc, req: CallbackReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if req.awaited == req.awaiter || OriginOf(req.awaited) != OriginOf(req.awaiter) then
      Applied(doc, Answer(400, None), [])
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      if req.awaited !in objects then Applied(shown, Answer(404, None), [])
      else if req.awaiter !in objects then Applied(shown, Answer(422, None), [])
      else
        var awaited := Project(objects[req.awaited], now);
        var awaiter := Project(objects[req.awaiter], now);
        if !Targeted(awaiter.promise.tags) || !Awaitable(awaited.promise.tags) then
          Applied(shown, Answer(422, None), [])
        else if awaited.promise.state == PromiseState.Pending && awaiter.promise.state == PromiseState.Pending then
          var obj := AddCallback(awaited, req.awaiter);
          var doc' := Origin(now, objects[req.awaited := obj]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              StillPending(objects[req.awaited], now);
              AddCallbackOk(req.awaited, awaited, req.awaiter, now);
              ReplaceOk(objects, req.awaited, obj, now);
            }
          }
          Applied(doc', Answer(200, Some(awaited.promise)), [])
        else
          Applied(shown, Answer(200, Some(awaited.promise)), [])
  }

  function AddListener(o: Obj, address: string): Obj {
    if address in o.promise.listeners then o
    else Obj(o.promise.(listeners := o.promise.listeners + {address}), o.task)
  }

  function RegisterListener(doc: Doc, req: ListenerReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if req.awaited !in objects then Applied(shown, Answer(404, None), [])
    else
      var awaited := Project(objects[req.awaited], now);
      if !Awaitable(awaited.promise.tags) then
        Applied(shown, Answer(422, None), [])
      else if awaited.promise.state == PromiseState.Pending then
        var obj := AddListener(awaited, req.address);
        var doc' := Origin(now, objects[req.awaited := obj]);
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) {
            StillPending(objects[req.awaited], now);
            AddListenerOk(req.awaited, awaited, req.address, now);
            ReplaceOk(objects, req.awaited, obj, now);
          }
        }
        Applied(doc', Answer(200, Some(awaited.promise)), [])
      else
        Applied(shown, Answer(200, Some(awaited.promise)), [])
  }

  // The task taken by `pid` for `ttl`, from `now`. The version moves, and
  // the resumes of the previous attempt are dropped.
  function ToAcquired(t: Task, pid: string, ttl: nat, now: nat): Task {
    Task(TaskState.Acquired, t.version + 1, Some(pid), Some(ttl), Some(now + ttl), None, [])
  }

  function ToHalted(t: Task): Task {
    Task(TaskState.Halted, t.version, None, None, None, None, t.resumes)
  }

  function ToSuspended(t: Task): Task {
    Task(TaskState.Suspended, t.version, None, None, None, None, [])
  }

  function ToPending(t: Task, now: nat): Task {
    t.(state := TaskState.Pending, retryTimeoutAt := Some(now))
  }

  function TtlOf(t: Task): nat {
    if t.ttl.Some? then t.ttl.value else 0
  }

  datatype Held = HeldOk(obj: Obj) | HeldMissing | HeldStale

  // The task `id` at `version`, acquired, its promise still pending.
  function Hold(objects: map<string, Obj>, id: string, version: nat, now: nat): Held {
    if id !in objects then HeldMissing
    else
      var obj := Project(objects[id], now);
      match obj.task
      case None => HeldMissing
      case Some(t) =>
        if t.state == TaskState.Acquired && t.version == version && obj.promise.state == PromiseState.Pending then
          HeldOk(obj)
        else
          HeldStale
  }

  function PromiseStatus(a: Answer): nat {
    match a
    case Answer(status, _) => status
    case Claim(status, _, _) => status
    case Status(status) => status
    case Fenced(status, _) => status
  }

  function PromiseBody(a: Answer): Opt<Promise> {
    match a
    case Answer(_, promise) => promise
    case Claim(_, _, promise) => promise
    case Status(_) => None
    case Fenced(_, _) => None
  }

  predicate BadSuspend(actions: seq<CallbackReq>, id: string) {
    exists i :: 0 <= i < |actions| && (actions[i].awaited == id || OriginOf(actions[i].awaited) != OriginOf(id))
  }

  predicate DistinctAwaited(actions: seq<CallbackReq>) {
    forall i, j :: 0 <= i < j < |actions| ==> actions[i].awaited != actions[j].awaited
  }

  predicate MissingAwaited(objects: map<string, Obj>, actions: seq<CallbackReq>) {
    exists i :: 0 <= i < |actions| && actions[i].awaited !in objects
  }

  predicate Unawaitable(objects: map<string, Obj>, actions: seq<CallbackReq>) {
    exists i :: 0 <= i < |actions| && actions[i].awaited in objects && !Awaitable(objects[actions[i].awaited].promise.tags)
  }

  predicate AnySettled(objects: map<string, Obj>, actions: seq<CallbackReq>, now: nat) {
    exists i :: 0 <= i < |actions| &&
      actions[i].awaited in objects &&
      Project(objects[actions[i].awaited], now).promise.state != PromiseState.Pending
  }

  predicate OneOrigin(refs: seq<TaskRef>)
    requires |refs| > 0
  {
    forall i :: 0 <= i < |refs| ==> OriginOf(refs[i].id) == OriginOf(refs[0].id)
  }

  function AddSuspends(objects: map<string, Obj>, awaiter: string, actions: seq<CallbackReq>, i: nat): (r: map<string, Obj>)
    requires i <= |actions|
    ensures r.Keys == objects.Keys
    decreases |actions| - i
  {
    if i == |actions| then objects
    else
      var awaited := actions[i].awaited;
      if awaited !in objects then AddSuspends(objects, awaiter, actions, i + 1)
      else AddSuspends(objects[awaited := AddCallback(objects[awaited], awaiter)], awaiter, actions, i + 1)
  }

  function Extend(objects: map<string, Obj>, pid: string, refs: seq<TaskRef>, i: nat, now: nat): (r: map<string, Obj>)
    requires i <= |refs|
    ensures r.Keys == objects.Keys
    decreases |refs| - i
  {
    if i == |refs| then objects
    else
      var id := refs[i].id;
      if id !in objects then Extend(objects, pid, refs, i + 1, now)
      else
        var seen := Project(objects[id], now);
        match seen.task
        case None => Extend(objects, pid, refs, i + 1, now)
        case Some(t) =>
          if t.state == TaskState.Acquired && t.version == refs[i].version && t.pid == Some(pid) then
            var next := Obj(seen.promise, Some(t.(leaseTimeoutAt := Some(now + TtlOf(t)))));
            Extend(objects[id := next], pid, refs, i + 1, now)
          else
            Extend(objects, pid, refs, i + 1, now)
  }

  function GetTask(doc: Doc, id: string, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if id !in objects then Applied(shown, Claim(404, None, None), [])
    else
      var seen := Project(objects[id], now);
      match seen.task
      case None => Applied(shown, Claim(404, None, None), [])
      case Some(t) => Applied(shown, Claim(200, Some(t), None), [])
  }

  function CreateTask(doc: Doc, pid: string, ttl: nat, action: CreateReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if !Targeted(action.tags) || Timer(action.tags) then
      Applied(doc, Claim(400, None, None), [])
    else
      var done := Create(doc, action, now);
      var objects := ObjectsOf(done.doc);
      if action.id !in objects then
        Applied(done.doc, Claim(422, None, None), [])
      else
        var seen := Project(objects[action.id], now);
        if !Targeted(seen.promise.tags) then
          Applied(done.doc, Claim(422, None, None), [])
        else
          match seen.task
          case None => Applied(done.doc, Claim(409, None, None), [])
          case Some(t) =>
            if t.state == TaskState.Fulfilled then
              Applied(done.doc, Claim(200, Some(t), Some(seen.promise)), [])
            else if t.state == TaskState.Pending && seen.promise.state == PromiseState.Pending then
              var u := ToAcquired(t, pid, ttl, now);
              var obj := Obj(seen.promise, Some(u));
              var doc' := Origin(now, objects[action.id := obj]);
              assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
                if WellFormed(doc, now) {
                  assert WellFormed(done.doc, now);
                  OriginMap(done.doc, action.id, now);
                  StillPending(objects[action.id], now);
                  assert seen == objects[action.id];
                  AcquireOk(t, pid, ttl, now);
                  assert obj.promise == objects[action.id].promise;
                  ReplaceOk(objects, action.id, obj, now);
                }
              }
              Applied(doc', Claim(200, Some(u), Some(obj.promise)), [])
            else
              Applied(done.doc, Claim(409, None, None), [])
  }

  function AcquireTask(doc: Doc, id: string, version: nat, pid: string, ttl: nat, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if id !in objects then Applied(shown, Claim(404, None, None), [])
    else
      var seen := Project(objects[id], now);
      match seen.task
      case None => Applied(shown, Claim(404, None, None), [])
      case Some(t) =>
        if t.state != TaskState.Pending || t.version != version || seen.promise.state != PromiseState.Pending then
          Applied(shown, Claim(409, None, None), [])
        else
          var u := ToAcquired(t, pid, ttl, now);
          var obj := Obj(seen.promise, Some(u));
          var doc' := Origin(now, objects[id := obj]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              assert WellFormed(shown, now);
              assert MapOk(objects, now);
              StillPending(objects[id], now);
              assert seen == objects[id];
              AcquireOk(t, pid, ttl, now);
              assert obj.promise == objects[id].promise;
              ReplaceOk(objects, id, obj, now);
            }
          }
          Applied(doc', Claim(200, Some(u), Some(obj.promise)), [])
  }

  function ReleaseTask(doc: Doc, id: string, version: nat, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    match Hold(objects, id, version, now)
    case HeldMissing => Applied(shown, Status(404), [])
    case HeldStale => Applied(shown, Status(409), [])
    case HeldOk(obj) =>
      var t := obj.task.value;
      var u := Unlease(t, now);
      var next := Obj(obj.promise, Some(u));
      var doc' := Origin(now, objects[id := next]);
      assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
        if WellFormed(doc, now) {
          assert WellFormed(shown, now);
          assert MapOk(objects, now);
          HeldFacts(objects, id, version, now);
          assert obj == objects[id];
          UnleaseOk(t, now);
          assert next.promise == objects[id].promise;
          ReplaceOk(objects, id, next, now);
        }
      }
      Applied(doc', Status(200), [])
  }

  function FulfillTask(doc: Doc, id: string, version: nat, action: SettleReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if !Settable(action.state) then Applied(doc, Answer(400, None), [])
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      match Hold(objects, id, version, now)
      case HeldMissing => Applied(shown, Answer(404, None), [])
      case HeldStale => Applied(shown, Answer(409, None), [])
      case HeldOk(obj) =>
        var settled := Settled(obj, action.state, action.value, now);
        var doc' := Origin(now, objects[id := settled]);
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) {
            assert WellFormed(shown, now);
            assert MapOk(objects, now);
            HeldFacts(objects, id, version, now);
            assert obj == objects[id];
            SettledOk(id, obj, action.state, action.value, now);
            ReplaceOk(objects, id, settled, now);
          }
        }
        Applied(doc', Answer(200, Some(settled.promise)), [])
  }

  function HaltTask(doc: Doc, id: string, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if id !in objects then Applied(shown, Status(404), [])
    else
      var seen := Project(objects[id], now);
      match seen.task
      case None => Applied(shown, Status(404), [])
      case Some(t) =>
        if t.state == TaskState.Fulfilled then Applied(shown, Status(409), [])
        else if t.state == TaskState.Halted then Applied(shown, Status(200), [])
        else
          var u := ToHalted(t);
          var obj := Obj(seen.promise, Some(u));
          var doc' := Origin(now, objects[id := obj]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              assert WellFormed(shown, now);
              assert MapOk(objects, now);
              Stored(objects[id], now, t);
              assert seen == objects[id];
              HaltOk(t);
              assert obj.promise == objects[id].promise;
              ReplaceOk(objects, id, obj, now);
            }
          }
          Applied(doc', Status(200), [])
  }

  function ContinueTask(doc: Doc, id: string, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if id !in objects then Applied(shown, Status(404), [])
    else
      var seen := Project(objects[id], now);
      match seen.task
      case None => Applied(shown, Status(404), [])
      case Some(t) =>
        if t.state != TaskState.Halted || seen.promise.state != PromiseState.Pending then
          Applied(shown, Status(409), [])
        else
          var u := ToPending(t, now);
          var obj := Obj(seen.promise, Some(u));
          var doc' := Origin(now, objects[id := obj]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              assert WellFormed(shown, now);
              assert MapOk(objects, now);
              StillPending(objects[id], now);
              assert seen == objects[id];
              ContinueOk(t, now);
              assert obj.promise == objects[id].promise;
              ReplaceOk(objects, id, obj, now);
            }
          }
          Applied(doc', Status(200), [])
  }

  function Heartbeat(doc: Doc, pid: string, refs: seq<TaskRef>, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if |refs| == 0 then Applied(doc, Status(200), [])
    else if !OneOrigin(refs) then Applied(doc, Status(400), [])
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      var next := Extend(objects, pid, refs, 0, now);
      var doc' := Origin(now, next);
      assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
        if WellFormed(doc, now) {
          assert WellFormed(shown, now);
          assert MapOk(objects, now);
          ExtendOk(objects, pid, refs, 0, now);
        }
      }
      assert CaughtUp(doc, now) ==> CaughtUp(doc', now) by {
        if CaughtUp(doc, now) {
          assert shown.stamp == doc.stamp;
          assert ObjectsOf(shown) == ObjectsOf(doc);
          ExtendClock(objects, pid, refs, 0, now);
          ClockOnTime(objects, next, now);
        }
      }
      Applied(doc', Status(200), [])
  }

  function SuspendTask(doc: Doc, id: string, version: nat, actions: seq<CallbackReq>, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    if |actions| == 0 || BadSuspend(actions, id) || !DistinctAwaited(actions) then
      Applied(doc, Status(400), [])
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      match Hold(objects, id, version, now)
      case HeldMissing => Applied(shown, Status(404), [])
      case HeldStale => Applied(shown, Status(409), [])
      case HeldOk(obj) =>
        if MissingAwaited(objects, actions) || Unawaitable(objects, actions) then
          Applied(shown, Status(422), [])
        else if AnySettled(objects, actions, now) then
          var t := obj.task.value;
          var next := Obj(obj.promise, Some(t.(resumes := [])));
          var doc' := Origin(now, objects[id := next]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              assert WellFormed(shown, now);
              assert MapOk(objects, now);
              HeldFacts(objects, id, version, now);
              assert obj == objects[id];
              DropResumesOk(t);
              assert next.promise == objects[id].promise;
              ReplaceOk(objects, id, next, now);
            }
          }
          Applied(doc', Status(300), [])
        else
          var placed := AddSuspends(objects, id, actions, 0);
          var t := obj.task.value;
          var next := Obj(obj.promise, Some(ToSuspended(t)));
          var doc' := Origin(now, placed[id := next]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              assert WellFormed(shown, now);
              assert MapOk(objects, now);
              HeldFacts(objects, id, version, now);
              assert obj == objects[id];
              SuspendReady(objects, id, actions, now);
              AddSuspendsOk(objects, id, actions, 0, now);
              assert placed[id] == objects[id];
              SuspendOk(t);
              assert next.promise == placed[id].promise;
              ReplaceOk(placed, id, next, now);
            }
          }
          assert CaughtUp(doc, now) ==> CaughtUp(doc', now) by {
            if CaughtUp(doc, now) {
              assert shown.stamp == doc.stamp;
              assert ObjectsOf(shown) == ObjectsOf(doc);
              assert OnTime(objects, now);
              AddSuspendsClock(objects, id, actions, 0);
              ClockOnTime(objects, placed, now);
              assert next.promise.state == obj.promise.state;
              assert next.promise.timeoutAt == obj.promise.timeoutAt;
              ReplaceOnTime(placed, id, next, now);
            }
          }
          Applied(doc', Status(200), [])
  }

  function Fence(doc: Doc, id: string, version: nat, action: FenceAction, now: nat, retry: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var target := match action case FenceCreate(req) => req.id case FenceSettle(req) => req.id;
    if target == id || OriginOf(target) != OriginOf(id) then
      Applied(doc, Fenced(400, None), [])
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      match Hold(objects, id, version, now)
      case HeldMissing => Applied(shown, Fenced(404, None), [])
      case HeldStale => Applied(shown, Fenced(409, None), [])
      case HeldOk(_) =>
        match action
        case FenceCreate(req) =>
          var done := Create(shown, req, now);
          assert WellFormed(doc, now) ==> WellFormed(done.doc, now) by {
            if WellFormed(doc, now) { assert WellFormed(shown, now); }
          }
          Applied(done.doc, Fenced(200, Some(FenceCreated(PromiseStatus(done.answer), PromiseBody(done.answer)))), [])
        case FenceSettle(req) =>
          var done := Settle(shown, req, now, retry);
          assert WellFormed(doc, now) ==> WellFormed(done.doc, now) by {
            if WellFormed(doc, now) { assert WellFormed(shown, now); }
          }
          Applied(done.doc, Fenced(200, Some(FenceSettled(PromiseStatus(done.answer), PromiseBody(done.answer)))), done.notes)
  }

  function FenceCheck(doc: Doc, id: string, version: nat, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(doc, now) ==> CaughtUp(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    match Hold(objects, id, version, now)
    case HeldMissing => Applied(shown, Status(404), [])
    case HeldStale => Applied(shown, Status(409), [])
    case HeldOk(_) => Applied(shown, Status(200), [])
  }

  function Unlease(t: Task, at: nat): Task {
    Task(TaskState.Pending, t.version, None, None, None, Some(at), t.resumes)
  }

  function Rearm(t: Task, at: nat): Task {
    t.(retryTimeoutAt := Some(at))
  }

  function DropCallback(o: Obj, awaiter: string): Obj
    requires awaiter in o.promise.callbacks
  {
    Obj(o.promise.(callbacks := o.promise.callbacks - {awaiter}), o.task)
  }

  function DropListener(o: Obj, address: string): Obj
    requires address in o.promise.listeners
  {
    Obj(o.promise.(listeners := o.promise.listeners - {address}), o.task)
  }

  // Wake `awaiter` from `awaited`, read through its projection at `now`.
  function Resume(objects: map<string, Obj>, awaiter: string, awaited: string, since: nat, now: nat): map<string, Obj> {
    if awaiter !in objects then objects
    else
      var seen := Project(objects[awaiter], now);
      match seen.task
      case None => objects
      case Some(t) =>
        if t.state == TaskState.Suspended then
          var woken := Task(TaskState.Pending, t.version, None, None, None, Some(since), [awaited]);
          objects[awaiter := Obj(objects[awaiter].promise, Some(woken))]
        else if t.state == TaskState.Fulfilled then objects
        else if awaited in t.resumes then objects
        else objects[awaiter := Obj(objects[awaiter].promise, Some(t.(resumes := t.resumes + [awaited])))]
  }

  datatype Noted = Noted(obj: Obj, notes: seq<Note>)

  function Deadline(o: Obj, now: nat): Obj {
    if o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now then Project(o, now) else o
  }

  function Lease(o: Obj, now: nat): Obj {
    if o.promise.state != PromiseState.Pending then o
    else
      match o.task
      case Some(t) =>
        if t.state == TaskState.Acquired && t.leaseTimeoutAt.Some? && t.leaseTimeoutAt.value <= now then
          Obj(o.promise, Some(Unlease(t, now)))
        else o
      case None => o
  }

  predicate DueRetry(o: Obj, now: nat) {
    && o.promise.state == PromiseState.Pending
    && (match o.task
        case Some(t) => t.state == TaskState.Pending && t.retryTimeoutAt.Some? && t.retryTimeoutAt.value <= now
        case None => false)
  }

  function RetryOf(o: Obj, id: string, now: nat, retry: nat): Noted {
    if o.promise.state != PromiseState.Pending then Noted(o, [])
    else
      match o.task
      case Some(t) =>
        if t.state == TaskState.Pending && t.retryTimeoutAt.Some? && t.retryTimeoutAt.value <= now then
          Noted(Obj(o.promise, Some(Rearm(t, now + retry))), [Execute(id, t.version)])
        else Noted(o, [])
      case None => Noted(o, [])
  }

  lemma ResumePromise(objects: map<string, Obj>, awaiter: string, awaited: string, since: nat, now: nat)
    ensures var after := Resume(objects, awaiter, awaited, since, now);
      after.Keys == objects.Keys &&
      (forall k :: k in objects ==> after[k].promise == objects[k].promise)
  {
    if awaiter in objects {
      var stored := objects[awaiter];
      var seen := Project(stored, now);
      match seen.task
      case None =>
      case Some(t) =>
        if t.state == TaskState.Suspended {
          var woken := Task(TaskState.Pending, t.version, None, None, None, Some(since), [awaited]);
          var after := objects[awaiter := Obj(stored.promise, Some(woken))];
          forall k | k in objects
            ensures after[k].promise == objects[k].promise
          {
            if k == awaiter { assert after[k].promise == stored.promise; }
          }
        } else if t.state == TaskState.Fulfilled {
        } else if awaited in t.resumes {
        } else {
          var placed := Obj(stored.promise, Some(t.(resumes := t.resumes + [awaited])));
          var after := objects[awaiter := placed];
          forall k | k in objects
            ensures after[k].promise == objects[k].promise
          {
            if k == awaiter { assert after[k].promise == stored.promise; }
          }
        }
    }
  }

  // The callbacks of one object, least id first.
  function Callbacks(objects: map<string, Obj>, id: string, now: nat): (r: map<string, Obj>)
    ensures r.Keys == objects.Keys
    decreases if id in objects && objects[id].promise.state != PromiseState.Pending then |objects[id].promise.callbacks| else 0
  {
    if id !in objects then objects
    else if objects[id].promise.state == PromiseState.Pending || objects[id].promise.callbacks == {} then objects
    else
      var o := objects[id];
      var awaiter := MinKey(o.promise.callbacks);
      var since := if o.promise.settledAt.Some? then o.promise.settledAt.value else 0;
      var objects' := objects[id := DropCallback(o, awaiter)];
      var resumed := Resume(objects', awaiter, id, since, now);
      ResumePromise(objects', awaiter, id, since, now);
      assert id in resumed && resumed[id].promise.callbacks == objects'[id].promise.callbacks;
      assert |resumed[id].promise.callbacks| + 1 == |o.promise.callbacks|;
      Callbacks(resumed, id, now)
  }

  // The listeners of one object, least id first.
  function Listeners(objects: map<string, Obj>, id: string): (s: Passed)
    ensures s.objects.Keys == objects.Keys
    decreases if id in objects && objects[id].promise.state != PromiseState.Pending then |objects[id].promise.listeners| else 0
  {
    if id !in objects then Passed(objects, [])
    else if objects[id].promise.state == PromiseState.Pending || objects[id].promise.listeners == {} then Passed(objects, [])
    else
      var o := objects[id];
      var address := MinKey(o.promise.listeners);
      var dropped := DropListener(o, address);
      var objects' := objects[id := dropped];
      var rest := Listeners(objects', id);
      Passed(rest.objects, [Unblock(address, id, o.promise)] + rest.notes)
  }

  lemma TailKeys(objects: map<string, Obj>, objects': map<string, Obj>, keys: seq<string>)
    requires |keys| > 0
    requires objects'.Keys == objects.Keys
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures var tail := keys[1..];
      (forall k :: k in tail ==> k in objects') &&
      (forall i, j | 0 <= i < j < |tail| :: tail[i] != tail[j])
  {
    var tail := keys[1..];
    forall k | k in tail
      ensures k in objects'
    {
      assert k in objects;
    }
    forall i, j | 0 <= i < j < |tail|
      ensures tail[i] != tail[j]
    {
      assert tail[i] == keys[i + 1] && tail[j] == keys[j + 1];
    }
  }

  // Every promise whose deadline has passed, keys in order.
  function Timeouts(objects: map<string, Obj>, keys: seq<string>, now: nat): (r: map<string, Obj>)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures r.Keys == objects.Keys
    decreases |keys|
  {
    if |keys| == 0 then objects
    else
      var id := keys[0];
      var objects' := objects[id := Deadline(objects[id], now)];
      TailKeys(objects, objects', keys);
      Timeouts(objects', keys[1..], now)
  }

  // The callbacks a settled promise holds, every key, after the timeouts.
  function ApplyCallbacks(objects: map<string, Obj>, keys: seq<string>, now: nat): (r: map<string, Obj>)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures r.Keys == objects.Keys
    decreases |keys|
  {
    if |keys| == 0 then objects
    else
      var woken := Callbacks(objects, keys[0], now);
      TailKeys(objects, woken, keys);
      ApplyCallbacks(woken, keys[1..], now)
  }

  function ApplyListeners(objects: map<string, Obj>, keys: seq<string>): (s: Passed)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures s.objects.Keys == objects.Keys
    decreases |keys|
  {
    if |keys| == 0 then Passed(objects, [])
    else
      var told := Listeners(objects, keys[0]);
      TailKeys(objects, told.objects, keys);
      var rest := ApplyListeners(told.objects, keys[1..]);
      Passed(rest.objects, told.notes + rest.notes)
  }

  function Leases(objects: map<string, Obj>, keys: seq<string>, now: nat): (r: map<string, Obj>)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures r.Keys == objects.Keys
    decreases |keys|
  {
    if |keys| == 0 then objects
    else
      var id := keys[0];
      var objects' := objects[id := Lease(objects[id], now)];
      TailKeys(objects, objects', keys);
      Leases(objects', keys[1..], now)
  }

  function Retries(objects: map<string, Obj>, keys: seq<string>, now: nat, retry: nat): (s: Passed)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures s.objects.Keys == objects.Keys
    decreases |keys|
  {
    if |keys| == 0 then Passed(objects, [])
    else
      var id := keys[0];
      var armed := RetryOf(objects[id], id, now, retry);
      var objects' := objects[id := armed.obj];
      TailKeys(objects, objects', keys);
      var rest := Retries(objects', keys[1..], now, retry);
      Passed(rest.objects, armed.notes + rest.notes)
  }

  // Offer a task this settlement woke. A retry the sweep already armed stays where it is.
  function Offer(before: map<string, Obj>, objects: map<string, Obj>, ids: seq<string>, now: nat, retry: nat): (s: Passed)
    requires before.Keys == objects.Keys
    requires forall i, j | 0 <= i < j < |ids| :: ids[i] != ids[j]
    ensures s.objects.Keys == objects.Keys
    decreases |ids|
  {
    if |ids| == 0 then Passed(objects, [])
    else
      var id := ids[0];
      var tail := ids[1..];
      forall i, j | 0 <= i < j < |tail|
        ensures tail[i] != tail[j]
      {
        assert tail[i] == ids[i + 1] && tail[j] == ids[j + 1];
      }
      if id in objects && DueRetry(objects[id], now) && !DueRetry(before[id], now) then
        var armed := RetryOf(objects[id], id, now, retry);
        var objects' := objects[id := armed.obj];
        var rest := Offer(before, objects', tail, now, retry);
        Passed(rest.objects, armed.notes + rest.notes)
      else
        Offer(before, objects, tail, now, retry)
  }

  ghost predicate ClockSame(a: map<string, Obj>, b: map<string, Obj>) {
    && a.Keys == b.Keys
    && (forall id :: id in a ==>
         b[id].promise.state == a[id].promise.state &&
         b[id].promise.timeoutAt == a[id].promise.timeoutAt)
  }

  lemma ClockOnTime(a: map<string, Obj>, b: map<string, Obj>, now: nat)
    requires OnTime(a, now)
    requires ClockSame(a, b)
    ensures OnTime(b, now)
  {
  }

  lemma DeadlineOnTime(o: Obj, now: nat)
    ensures var d := Deadline(o, now);
      d.promise.state == PromiseState.Pending ==> now < d.promise.timeoutAt
  {
    if o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now {
      var d := Project(o, now);
      assert d.promise == ProjectPromise(o.promise, now);
      assert d.promise.state != PromiseState.Pending;
    }
  }

  lemma TimeoutsKeeps(objects: map<string, Obj>, keys: seq<string>, now: nat, id: string)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    requires id in objects
    requires id !in keys
    ensures Timeouts(objects, keys, now)[id] == objects[id]
    decreases |keys|
  {
    if |keys| != 0 {
      var head := keys[0];
      var objects' := objects[head := Deadline(objects[head], now)];
      var tail := keys[1..];
      assert id != head;
      assert objects'[id] == objects[id];
      if id in tail {
        assert id in keys;
        assert false;
      }
      TailKeys(objects, objects', keys);
      TimeoutsKeeps(objects', tail, now, id);
    }
  }

  lemma TimeoutsOnTime(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures var r := Timeouts(objects, keys, now);
      forall id :: id in keys ==>
        r[id].promise.state == PromiseState.Pending ==> now < r[id].promise.timeoutAt
    decreases |keys|
  {
    if |keys| != 0 {
      var head := keys[0];
      var due := Deadline(objects[head], now);
      DeadlineOnTime(objects[head], now);
      var objects' := objects[head := due];
      var tail := keys[1..];
      assert head !in tail by {
        if head in tail {
          var i :| 0 <= i < |tail| && tail[i] == head;
          assert tail[i] == keys[i + 1];
          assert keys[i + 1] != keys[0];
        }
      }
      TailKeys(objects, objects', keys);
      TimeoutsOnTime(objects', tail, now);
      var r := Timeouts(objects, keys, now);
      assert r == Timeouts(objects', tail, now);
      TimeoutsKeeps(objects', tail, now, head);
      assert r[head] == due;
    }
  }

  lemma CallbacksClock(objects: map<string, Obj>, id: string, now: nat)
    ensures ClockSame(objects, Callbacks(objects, id, now))
    decreases if id in objects && objects[id].promise.state != PromiseState.Pending then |objects[id].promise.callbacks| else 0
  {
    if id in objects && objects[id].promise.state != PromiseState.Pending && objects[id].promise.callbacks != {} {
      var o := objects[id];
      var awaiter := MinKey(o.promise.callbacks);
      var dropped := DropCallback(o, awaiter);
      var objects' := objects[id := dropped];
      var since := if o.promise.settledAt.Some? then o.promise.settledAt.value else 0;
      var resumed := Resume(objects', awaiter, id, since, now);
      ResumePromise(objects', awaiter, id, since, now);
      assert dropped.promise.state == o.promise.state && dropped.promise.timeoutAt == o.promise.timeoutAt;
      forall k | k in objects
        ensures resumed[k].promise.state == objects[k].promise.state && resumed[k].promise.timeoutAt == objects[k].promise.timeoutAt
      {
        assert resumed[k].promise == objects'[k].promise;
        if k == id {
          assert objects'[k].promise.state == o.promise.state;
        } else {
          assert objects'[k] == objects[k];
        }
      }
      CallbacksClock(resumed, id, now);
    }
  }

  lemma ListenersClock(objects: map<string, Obj>, id: string)
    ensures ClockSame(objects, Listeners(objects, id).objects)
    decreases if id in objects && objects[id].promise.state != PromiseState.Pending then |objects[id].promise.listeners| else 0
  {
    if id in objects && objects[id].promise.state != PromiseState.Pending && objects[id].promise.listeners != {} {
      var o := objects[id];
      var address := MinKey(o.promise.listeners);
      var dropped := DropListener(o, address);
      var objects' := objects[id := dropped];
      assert dropped.promise.state == o.promise.state && dropped.promise.timeoutAt == o.promise.timeoutAt;
      ListenersClock(objects', id);
    }
  }

  lemma ApplyCallbacksClock(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures ClockSame(objects, ApplyCallbacks(objects, keys, now))
    decreases |keys|
  {
    if |keys| != 0 {
      CallbacksClock(objects, keys[0], now);
      var woken := Callbacks(objects, keys[0], now);
      TailKeys(objects, woken, keys);
      ApplyCallbacksClock(woken, keys[1..], now);
    }
  }

  lemma ApplyListenersClock(objects: map<string, Obj>, keys: seq<string>)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures ClockSame(objects, ApplyListeners(objects, keys).objects)
    decreases |keys|
  {
    if |keys| != 0 {
      ListenersClock(objects, keys[0]);
      var told := Listeners(objects, keys[0]);
      TailKeys(objects, told.objects, keys);
      ApplyListenersClock(told.objects, keys[1..]);
    }
  }

  lemma LeasePromise(o: Obj, now: nat)
    ensures Lease(o, now).promise == o.promise
  {
  }

  lemma LeasesClock(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures ClockSame(objects, Leases(objects, keys, now))
    decreases |keys|
  {
    if |keys| != 0 {
      var id := keys[0];
      LeasePromise(objects[id], now);
      var objects' := objects[id := Lease(objects[id], now)];
      TailKeys(objects, objects', keys);
      LeasesClock(objects', keys[1..], now);
    }
  }

  lemma RetryPromise(o: Obj, id: string, now: nat, retry: nat)
    ensures RetryOf(o, id, now, retry).obj.promise == o.promise
  {
  }

  lemma RetriesClock(objects: map<string, Obj>, keys: seq<string>, now: nat, retry: nat)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures ClockSame(objects, Retries(objects, keys, now, retry).objects)
    decreases |keys|
  {
    if |keys| != 0 {
      var id := keys[0];
      RetryPromise(objects[id], id, now, retry);
      var objects' := objects[id := RetryOf(objects[id], id, now, retry).obj];
      TailKeys(objects, objects', keys);
      RetriesClock(objects', keys[1..], now, retry);
    }
  }

  lemma OfferClock(before: map<string, Obj>, objects: map<string, Obj>, ids: seq<string>, now: nat, retry: nat)
    requires before.Keys == objects.Keys
    requires forall i, j | 0 <= i < j < |ids| :: ids[i] != ids[j]
    ensures ClockSame(objects, Offer(before, objects, ids, now, retry).objects)
    decreases |ids|
  {
    if |ids| != 0 {
      var id := ids[0];
      var tail := ids[1..];
      forall i, j | 0 <= i < j < |tail|
        ensures tail[i] != tail[j]
      {
        assert tail[i] == ids[i + 1] && tail[j] == ids[j + 1];
      }
      if id in objects && DueRetry(objects[id], now) && !DueRetry(before[id], now) {
        RetryPromise(objects[id], id, now, retry);
        var armed := RetryOf(objects[id], id, now, retry);
        var objects' := objects[id := armed.obj];
        OfferClock(before, objects', tail, now, retry);
      } else {
        OfferClock(before, objects, tail, now, retry);
      }
    }
  }

  lemma ExtendClock(objects: map<string, Obj>, pid: string, refs: seq<TaskRef>, i: nat, now: nat)
    requires i <= |refs|
    ensures ClockSame(objects, Extend(objects, pid, refs, i, now))
    decreases |refs| - i
  {
    if i < |refs| {
      var id := refs[i].id;
      if id in objects {
        var seen := Project(objects[id], now);
        match seen.task
        case None =>
          ExtendClock(objects, pid, refs, i + 1, now);
        case Some(t) =>
          if t.state == TaskState.Acquired && t.version == refs[i].version && t.pid == Some(pid) {
            Stored(objects[id], now, t);
            var next := Obj(seen.promise, Some(t.(leaseTimeoutAt := Some(now + TtlOf(t)))));
            assert seen == objects[id];
            assert next.promise == objects[id].promise;
            ExtendClock(objects[id := next], pid, refs, i + 1, now);
          } else {
            ExtendClock(objects, pid, refs, i + 1, now);
          }
      } else {
        ExtendClock(objects, pid, refs, i + 1, now);
      }
    }
  }

  lemma AddSuspendsClock(objects: map<string, Obj>, awaiter: string, actions: seq<CallbackReq>, i: nat)
    requires i <= |actions|
    ensures ClockSame(objects, AddSuspends(objects, awaiter, actions, i))
    decreases |actions| - i
  {
    if i < |actions| {
      var awaited := actions[i].awaited;
      if awaited in objects {
        var added := AddCallback(objects[awaited], awaiter);
        assert added.promise.state == objects[awaited].promise.state;
        assert added.promise.timeoutAt == objects[awaited].promise.timeoutAt;
        AddSuspendsClock(objects[awaited := added], awaiter, actions, i + 1);
      } else {
        AddSuspendsClock(objects, awaiter, actions, i + 1);
      }
    }
  }

  lemma ReplaceOnTime(objects: map<string, Obj>, id: string, o: Obj, now: nat)
    requires OnTime(objects, now)
    requires id in objects
    requires o.promise.state == PromiseState.Pending ==> now < o.promise.timeoutAt
    ensures OnTime(objects[id := o], now)
  {
    var placed := objects[id := o];
    forall k | k in placed
      ensures placed[k].promise.state == PromiseState.Pending ==> now < placed[k].promise.timeoutAt
    {
      if k != id {
        assert placed[k] == objects[k];
      }
    }
  }

  lemma InsertOnTime(objects: map<string, Obj>, id: string, o: Obj, now: nat)
    requires OnTime(objects, now)
    requires id !in objects
    requires o.promise.state == PromiseState.Pending ==> now < o.promise.timeoutAt
    ensures OnTime(objects[id := o], now)
  {
    var placed := objects[id := o];
    forall k | k in placed
      ensures placed[k].promise.state == PromiseState.Pending ==> now < placed[k].promise.timeoutAt
    {
      if k != id {
        assert k in objects && placed[k] == objects[k];
      }
    }
  }

  function Sweep(doc: Doc, now: nat, retry: nat): (s: Ran)
    ensures WellFormed(doc, now) ==> WellFormed(s.doc, now)
    ensures CaughtUp(s.doc, now)
  {
    match doc
    case Schedule(_, Some(sched)) =>
      if sched.nextRunAt <= now then
        var at := sched.nextRunAt;
        var born := Occurrence(Expand(sched.promiseId, sched.id, at), at, sched.promiseTimeout, sched.promiseParam, sched.promiseTags);
        var sched' := sched.(lastRunAt := Some(at), nextRunAt := NextCron(sched.cron, at));
        var doc' := Schedule(now, Some(sched'));
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) { AdvanceOk(sched); }
        }
        Ran(doc', [born], [])
      else
        var kept := Schedule(now, Some(sched));
        assert WellFormed(doc, now) ==> WellFormed(kept, now);
        Ran(kept, [], [])
    case Origin(_, objects) =>
      SortedProps(objects.Keys);
      var keys := Sorted(objects.Keys);
      forall i, j | 0 <= i < j < |keys|
        ensures keys[i] != keys[j]
      {
        assert Lt(keys[i], keys[j]);
      }
      var timed := Timeouts(objects, keys, now);
      TimeoutsOnTime(objects, keys, now);
      forall id | id in timed
        ensures timed[id].promise.state == PromiseState.Pending ==> now < timed[id].promise.timeoutAt
      {
        assert id in keys;
      }
      var woken := ApplyCallbacks(timed, keys, now);
      ApplyCallbacksClock(timed, keys, now);
      ClockOnTime(timed, woken, now);
      var told := ApplyListeners(woken, keys);
      ApplyListenersClock(woken, keys);
      ClockOnTime(woken, told.objects, now);
      var returned := Leases(told.objects, keys, now);
      LeasesClock(told.objects, keys, now);
      ClockOnTime(told.objects, returned, now);
      var armed := Retries(returned, keys, now, retry);
      RetriesClock(returned, keys, now, retry);
      ClockOnTime(returned, armed.objects, now);
      assert WellFormed(doc, now) ==> WellFormed(Origin(now, armed.objects), now) by {
        if WellFormed(doc, now) {
          TimeoutsOk(objects, keys, now);
          ApplyCallbacksOk(timed, keys, now);
          ApplyListenersOk(woken, keys, now);
          LeasesOk(told.objects, keys, now);
          RetriesOk(returned, keys, now, retry);
        }
      }
      Ran(Origin(now, armed.objects), [], told.notes + armed.notes)
    case Schedule(_, None) => Ran(Schedule(now, None), [], [])
  }

  lemma CallbacksOk(objects: map<string, Obj>, id: string, now: nat)
    requires MapOk(objects, now)
    ensures MapOk(Callbacks(objects, id, now), now)
    decreases if id in objects && objects[id].promise.state != PromiseState.Pending then |objects[id].promise.callbacks| else 0
  {
    if id in objects && objects[id].promise.state != PromiseState.Pending && objects[id].promise.callbacks != {} {
      var o := objects[id];
      var awaiter := MinKey(o.promise.callbacks);
      var since := if o.promise.settledAt.Some? then o.promise.settledAt.value else 0;
      DropCallbackOk(id, o, awaiter, now);
      var objects' := objects[id := DropCallback(o, awaiter)];
      ReplaceOk(objects, id, DropCallback(o, awaiter), now);
      var resumed := Resume(objects', awaiter, id, since, now);
      ResumeOk(objects', awaiter, id, since, now);
      ResumePromise(objects', awaiter, id, since, now);
      CallbacksOk(resumed, id, now);
    }
  }

  lemma ListenersOk(objects: map<string, Obj>, id: string, now: nat)
    requires MapOk(objects, now)
    ensures MapOk(Listeners(objects, id).objects, now)
    decreases if id in objects && objects[id].promise.state != PromiseState.Pending then |objects[id].promise.listeners| else 0
  {
    if id in objects && objects[id].promise.state != PromiseState.Pending && objects[id].promise.listeners != {} {
      var o := objects[id];
      var address := MinKey(o.promise.listeners);
      var dropped := DropListener(o, address);
      assert dropped.promise.state == o.promise.state;
      assert dropped.promise.callbacks == o.promise.callbacks;
      assert dropped.task == o.task;
      ReplaceOk(objects, id, dropped, now);
      ListenersOk(objects[id := dropped], id, now);
    }
  }

  lemma TimeoutsOk(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires MapOk(objects, now)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures MapOk(Timeouts(objects, keys, now), now)
    decreases |keys|
  {
    if |keys| != 0 {
      var id := keys[0];
      var o := objects[id];
      var due := Deadline(o, now);
      if o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now {
        ProjectOk(id, o, now);
      }
      assert ObjectOk(id, due, now);
      var objects' := objects[id := due];
      ReplaceOk(objects, id, due, now);
      TailKeys(objects, objects', keys);
      TimeoutsOk(objects', keys[1..], now);
    }
  }

  lemma ApplyCallbacksOk(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires MapOk(objects, now)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures MapOk(ApplyCallbacks(objects, keys, now), now)
    decreases |keys|
  {
    if |keys| != 0 {
      CallbacksOk(objects, keys[0], now);
      var woken := Callbacks(objects, keys[0], now);
      TailKeys(objects, woken, keys);
      ApplyCallbacksOk(woken, keys[1..], now);
    }
  }

  lemma ApplyListenersOk(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires MapOk(objects, now)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures MapOk(ApplyListeners(objects, keys).objects, now)
    decreases |keys|
  {
    if |keys| != 0 {
      ListenersOk(objects, keys[0], now);
      var told := Listeners(objects, keys[0]);
      TailKeys(objects, told.objects, keys);
      ApplyListenersOk(told.objects, keys[1..], now);
    }
  }

  lemma LeasesOk(objects: map<string, Obj>, keys: seq<string>, now: nat)
    requires MapOk(objects, now)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures MapOk(Leases(objects, keys, now), now)
    decreases |keys|
  {
    if |keys| != 0 {
      var id := keys[0];
      var o := objects[id];
      var returned := Lease(o, now);
      if o.promise.state == PromiseState.Pending {
        match o.task
        case Some(t) =>
          if t.state == TaskState.Acquired && t.leaseTimeoutAt.Some? && t.leaseTimeoutAt.value <= now {
            UnleaseOk(t, now);
            assert returned == Obj(o.promise, Some(Unlease(t, now)));
          }
        case None =>
      }
      assert ObjectOk(id, returned, now);
      var objects' := objects[id := returned];
      ReplaceOk(objects, id, returned, now);
      TailKeys(objects, objects', keys);
      LeasesOk(objects', keys[1..], now);
    }
  }

  lemma RetriesOk(objects: map<string, Obj>, keys: seq<string>, now: nat, retry: nat)
    requires MapOk(objects, now)
    requires forall k :: k in keys ==> k in objects
    requires forall i, j | 0 <= i < j < |keys| :: keys[i] != keys[j]
    ensures MapOk(Retries(objects, keys, now, retry).objects, now)
    decreases |keys|
  {
    if |keys| != 0 {
      var id := keys[0];
      var o := objects[id];
      var armed := RetryOf(o, id, now, retry);
      if o.promise.state == PromiseState.Pending {
        match o.task
        case Some(t) =>
          if t.state == TaskState.Pending && t.retryTimeoutAt.Some? && t.retryTimeoutAt.value <= now {
            RearmOk(t, now + retry);
          }
        case None =>
      }
      assert ObjectOk(id, armed.obj, now);
      var objects' := objects[id := armed.obj];
      ReplaceOk(objects, id, armed.obj, now);
      TailKeys(objects, objects', keys);
      RetriesOk(objects', keys[1..], now, retry);
    }
  }

  lemma OfferOk(before: map<string, Obj>, objects: map<string, Obj>, ids: seq<string>, now: nat, retry: nat)
    requires MapOk(objects, now)
    requires before.Keys == objects.Keys
    requires forall i, j | 0 <= i < j < |ids| :: ids[i] != ids[j]
    ensures MapOk(Offer(before, objects, ids, now, retry).objects, now)
    decreases |ids|
  {
    if |ids| != 0 {
      var id := ids[0];
      var tail := ids[1..];
      forall i, j | 0 <= i < j < |tail|
        ensures tail[i] != tail[j]
      {
        assert tail[i] == ids[i + 1] && tail[j] == ids[j + 1];
      }
      if id in objects && DueRetry(objects[id], now) && !DueRetry(before[id], now) {
        var o := objects[id];
        match o.task
        case Some(t) =>
          assert t.state == TaskState.Pending && t.retryTimeoutAt.Some?;
          var armed := RetryOf(o, id, now, retry);
          RearmOk(t, now + retry);
          assert armed.obj.promise == o.promise && armed.obj.task == Some(Rearm(t, now + retry));
          ReplaceOk(objects, id, armed.obj, now);
          var objects' := objects[id := armed.obj];
          OfferOk(before, objects', tail, now, retry);
        case None =>
      }
    }
  }

  lemma AdvanceOk(s: Sched)
    requires ScheduleOk(s)
    ensures var at := s.nextRunAt;
      var s' := s.(lastRunAt := Some(at), nextRunAt := NextCron(s.cron, at));
      ScheduleOk(s')
  {
    var at := s.nextRunAt;
    var next := NextCron(s.cron, at);
    var s' := s.(lastRunAt := Some(at), nextRunAt := next);
    assert s'.createdAt <= at;
    assert at < next;
    assert s'.createdAt <= next;
    assert s'.lastRunAt.value < s'.nextRunAt;
  }

  lemma FulfillOk(t: Task)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(Fulfill(t)))
  {
  }

  lemma ProjectPromiseOk(p: Promise, now: nat)
    requires PromiseOk(p, now)
    requires p.state == PromiseState.Pending && p.timeoutAt <= now
    ensures PromiseOk(ProjectPromise(p, now), now)
  {
    var p' := ProjectPromise(p, now);
    assert p.createdAt < p.timeoutAt;
    assert p.value.data.None?;
    assert p'.settledAt == Some(p.timeoutAt);
    assert p'.createdAt == p.createdAt && p'.timeoutAt == p.timeoutAt && p'.value == p.value;
  }

  lemma ProjectOk(id: string, o: Obj, now: nat)
    requires ObjectOk(id, o, now)
    requires o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now
    ensures ObjectOk(id, Project(o, now), now)
  {
    var seen := Project(o, now);
    ProjectPromiseOk(o.promise, now);
    assert seen.promise == ProjectPromise(o.promise, now);
    assert seen.promise.callbacks == o.promise.callbacks;
    match o.task
    case None =>
    case Some(t) =>
      if t.state != TaskState.Fulfilled { FulfillOk(t); }
  }

  lemma UnleaseOk(t: Task, at: nat)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(Unlease(t, at)))
  {
  }

  lemma RearmOk(t: Task, at: nat)
    requires TaskOk(Some(t))
    requires t.state == TaskState.Pending && t.retryTimeoutAt.Some?
    ensures TaskOk(Some(Rearm(t, at)))
  {
  }

  lemma DistinctPush(xs: seq<string>, x: string)
    requires Distinct(xs) && x !in xs
    ensures Distinct(xs + [x])
  {
    forall i, j | 0 <= i < j < |xs + [x]|
      ensures (xs + [x])[i] != (xs + [x])[j]
    {
      if j == |xs| {
        assert (xs + [x])[j] == x;
        assert (xs + [x])[i] == xs[i];
      }
    }
  }

  lemma ReplaceOk(objects: map<string, Obj>, id: string, o: Obj, now: nat)
    requires MapOk(objects, now)
    requires id in objects
    requires ObjectOk(id, o, now)
    ensures MapOk(objects[id := o], now)
  {
    var placed := objects[id := o];
    forall k | k in placed
      ensures ObjectOk(k, placed[k], now)
    {
      if k == id {
        assert placed[k] == o;
      } else {
        assert k in objects && placed[k] == objects[k];
      }
    }
  }

  lemma DropCallbackOk(id: string, o: Obj, awaiter: string, now: nat)
    requires ObjectOk(id, o, now)
    requires awaiter in o.promise.callbacks
    ensures var dropped := DropCallback(o, awaiter);
      ObjectOk(id, dropped, now) && awaiter != id
  {
    var dropped := DropCallback(o, awaiter);
    assert id !in o.promise.callbacks;
    forall a | a in dropped.promise.callbacks
      ensures OriginOf(id) == OriginOf(a)
    {
      assert a in o.promise.callbacks;
    }
  }

  lemma ResumeOk(objects: map<string, Obj>, awaiter: string, awaited: string, since: nat, now: nat)
    requires MapOk(objects, now)
    ensures MapOk(Resume(objects, awaiter, awaited, since, now), now)
  {
    if awaiter in objects {
      var seen := Project(objects[awaiter], now);
      match seen.task
      case None =>
      case Some(t) =>
        if t.state == TaskState.Suspended {
          var woken := Task(TaskState.Pending, t.version, None, None, None, Some(since), [awaited]);
          var placed := Obj(objects[awaiter].promise, Some(woken));
          assert Distinct([awaited]);
          ReplaceOk(objects, awaiter, placed, now);
        } else if t.state == TaskState.Fulfilled {
        } else if awaited in t.resumes {
        } else {
          DistinctPush(t.resumes, awaited);
          var placed := Obj(objects[awaiter].promise, Some(t.(resumes := t.resumes + [awaited])));
          ReplaceOk(objects, awaiter, placed, now);
        }
    }
  }

  lemma OpenOk(doc: Doc, now: nat)
    requires WellFormed(doc, now)
    ensures WellFormed(Opened(doc), now)
  {
    match doc
    case Origin(_, _) =>
      assert Opened(doc) == doc;
    case Schedule(_, _) =>
      assert ObjectsOf(doc) == map[];
  }

  // A projection that is still pending did not fire, so it is the stored row.
  lemma StillPending(o: Obj, now: nat)
    requires Project(o, now).promise.state == PromiseState.Pending
    ensures Project(o, now) == o
    ensures o.promise.state == PromiseState.Pending
    ensures now < o.promise.timeoutAt
  {
    var seen := Project(o, now);
    var p := o.promise;
    if p.state == PromiseState.Pending && now >= p.timeoutAt {
      var projected := ProjectPromise(p, now);
      assert projected.state != PromiseState.Pending;
      assert seen.promise == projected;
      assert false;
    }
    assert ProjectPromise(p, now) == p;
    assert seen.promise == p;
    assert p.state == PromiseState.Pending;
    assert now < p.timeoutAt;
    assert seen.task == o.task;
  }

  lemma SettledOk(id: string, o: Obj, state: PromiseState, value: Value, now: nat)
    requires ObjectOk(id, o, now)
    requires o.promise.state == PromiseState.Pending
    requires now < o.promise.timeoutAt
    requires Settable(state)
    ensures ObjectOk(id, Settled(o, state, value, now), now)
  {
    var obj := Settled(o, state, value, now);
    var p := obj.promise;
    assert p.createdAt == o.promise.createdAt && p.timeoutAt == o.promise.timeoutAt;
    assert p.createdAt <= p.timeoutAt;
    assert p.settledAt == Some(now);
    assert now <= p.timeoutAt;
    assert p.createdAt <= now;
    assert state != PromiseState.Pending && state != PromiseState.RejectedTimedout;
    assert p.state == state;
    assert p.settledAt != Some(p.timeoutAt);
    assert p.callbacks == o.promise.callbacks;
    assert id !in p.callbacks;
    if o.task.Some? && o.task.value.state != TaskState.Fulfilled {
      FulfillOk(o.task.value);
    }
  }

  lemma AddCallbackOk(id: string, o: Obj, awaiter: string, now: nat)
    requires ObjectOk(id, o, now)
    requires awaiter != id
    requires OriginOf(id) == OriginOf(awaiter)
    ensures ObjectOk(id, AddCallback(o, awaiter), now)
  {
    if awaiter !in o.promise.callbacks {
      var added := AddCallback(o, awaiter);
      assert added.promise.callbacks == o.promise.callbacks + {awaiter};
      assert id !in added.promise.callbacks;
      forall a | a in added.promise.callbacks
        ensures OriginOf(id) == OriginOf(a)
      {
        if a != awaiter {
          assert a in o.promise.callbacks;
        }
      }
    }
  }

  lemma AddListenerOk(id: string, o: Obj, address: string, now: nat)
    requires ObjectOk(id, o, now)
    ensures ObjectOk(id, AddListener(o, address), now)
  {
    var added := AddListener(o, address);
    assert added.promise.state == o.promise.state;
    assert added.promise.callbacks == o.promise.callbacks;
    assert added.promise.timeoutAt == o.promise.timeoutAt;
    assert added.promise.createdAt == o.promise.createdAt;
    assert added.promise.settledAt == o.promise.settledAt;
    assert added.promise.value == o.promise.value;
    assert added.task == o.task;
  }

  lemma OriginMap(doc: Doc, id: string, now: nat)
    requires WellFormed(doc, now)
    requires id in ObjectsOf(doc)
    ensures doc.Origin?
    ensures MapOk(ObjectsOf(doc), now)
  {
    match doc
    case Origin(_, objects) =>
    case Schedule(_, _) =>
      assert ObjectsOf(doc) == map[];
      assert false;
  }

  lemma AcquireOk(t: Task, pid: string, ttl: nat, now: nat)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(ToAcquired(t, pid, ttl, now)))
  {
  }

  lemma HaltOk(t: Task)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(ToHalted(t)))
  {
  }

  lemma SuspendOk(t: Task)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(ToSuspended(t)))
  {
    assert Distinct([]);
  }

  lemma ContinueOk(t: Task, now: nat)
    requires TaskOk(Some(t))
    requires t.state == TaskState.Halted
    ensures TaskOk(Some(ToPending(t, now)))
  {
    assert Cleared(t);
  }

  lemma DropResumesOk(t: Task)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(t.(resumes := [])))
  {
    assert Distinct([]);
  }

  lemma LeaseOk(t: Task, at: nat)
    requires TaskOk(Some(t))
    ensures TaskOk(Some(t.(leaseTimeoutAt := Some(at))))
  {
  }

  // A projected task that is not fulfilled is the stored row, still pending.
  lemma Stored(o: Obj, now: nat, t: Task)
    requires Project(o, now).task == Some(t)
    requires t.state != TaskState.Fulfilled
    ensures Project(o, now) == o
    ensures o.promise.state == PromiseState.Pending
    ensures now < o.promise.timeoutAt
    ensures o.task == Some(t)
  {
    var seen := Project(o, now);
    if seen.promise.state != PromiseState.Pending {
      match o.task
      case None =>
        assert seen.task.None?;
        assert false;
      case Some(u) =>
        if u.state == TaskState.Fulfilled {
          assert seen.task == Some(u);
          assert false;
        } else {
          assert seen.task == Some(Fulfill(u));
          assert Fulfill(u).state == TaskState.Fulfilled;
          assert false;
        }
    }
    StillPending(o, now);
  }

  lemma HeldFacts(objects: map<string, Obj>, id: string, version: nat, now: nat)
    requires MapOk(objects, now)
    requires Hold(objects, id, version, now).HeldOk?
    ensures var obj := Hold(objects, id, version, now).obj;
      && id in objects
      && obj == objects[id]
      && obj.promise.state == PromiseState.Pending
      && now < obj.promise.timeoutAt
      && obj.task.Some?
      && obj.task.value.state == TaskState.Acquired
      && obj.task.value.version == version
      && obj.task.value.ttl.Some?
      && ObjectOk(id, obj, now)
  {
    if id !in objects {
      assert Hold(objects, id, version, now) == HeldMissing;
      assert false;
    }
    var seen := Project(objects[id], now);
    match seen.task
    case None =>
      assert Hold(objects, id, version, now) == HeldMissing;
      assert false;
    case Some(t) =>
      if !(t.state == TaskState.Acquired && t.version == version && seen.promise.state == PromiseState.Pending) {
        assert Hold(objects, id, version, now) == HeldStale;
        assert false;
      }
      assert Hold(objects, id, version, now) == HeldOk(seen);
      Stored(objects[id], now, t);
      assert seen == objects[id];
      assert TaskOk(Some(t));
      assert t.ttl.Some?;
  }

  lemma ProjectIfPending(o: Obj, now: nat)
    requires o.promise.state == PromiseState.Pending
    requires now < o.promise.timeoutAt
    ensures Project(o, now) == o
  {
    assert ProjectPromise(o.promise, now) == o.promise;
  }

  lemma SuspendReady(objects: map<string, Obj>, awaiter: string, actions: seq<CallbackReq>, now: nat)
    requires !BadSuspend(actions, awaiter)
    requires !MissingAwaited(objects, actions)
    requires !AnySettled(objects, actions, now)
    ensures forall k :: 0 <= k < |actions| ==>
      actions[k].awaited in objects &&
      actions[k].awaited != awaiter &&
      OriginOf(actions[k].awaited) == OriginOf(awaiter) &&
      Project(objects[actions[k].awaited], now).promise.state == PromiseState.Pending
  {
    forall k | 0 <= k < |actions|
      ensures actions[k].awaited in objects
      ensures actions[k].awaited != awaiter
      ensures OriginOf(actions[k].awaited) == OriginOf(awaiter)
      ensures Project(objects[actions[k].awaited], now).promise.state == PromiseState.Pending
    {
      if actions[k].awaited !in objects {
        assert MissingAwaited(objects, actions);
        assert false;
      }
      if actions[k].awaited == awaiter || OriginOf(actions[k].awaited) != OriginOf(awaiter) {
        assert BadSuspend(actions, awaiter);
        assert false;
      }
      if Project(objects[actions[k].awaited], now).promise.state != PromiseState.Pending {
        assert AnySettled(objects, actions, now);
        assert false;
      }
    }
  }

  lemma AddSuspendsOk(objects: map<string, Obj>, awaiter: string, actions: seq<CallbackReq>, i: nat, now: nat)
    requires i <= |actions|
    requires MapOk(objects, now)
    requires forall k :: i <= k < |actions| ==>
      actions[k].awaited in objects &&
      actions[k].awaited != awaiter &&
      OriginOf(actions[k].awaited) == OriginOf(awaiter) &&
      Project(objects[actions[k].awaited], now).promise.state == PromiseState.Pending
    ensures MapOk(AddSuspends(objects, awaiter, actions, i), now)
    ensures awaiter in objects ==> AddSuspends(objects, awaiter, actions, i)[awaiter] == objects[awaiter]
    decreases |actions| - i
  {
    if i < |actions| {
      var awaited := actions[i].awaited;
      assert awaited in objects;
      assert awaited != awaiter;
      var stored := objects[awaited];
      assert Project(stored, now).promise.state == PromiseState.Pending;
      StillPending(stored, now);
      AddCallbackOk(awaited, stored, awaiter, now);
      var added := AddCallback(stored, awaiter);
      assert added.promise.state == stored.promise.state;
      assert added.promise.timeoutAt == stored.promise.timeoutAt;
      ProjectIfPending(added, now);
      ReplaceOk(objects, awaited, added, now);
      var objects' := objects[awaited := added];
      forall k | i + 1 <= k < |actions|
        ensures actions[k].awaited in objects'
        ensures actions[k].awaited != awaiter
        ensures OriginOf(actions[k].awaited) == OriginOf(awaiter)
        ensures Project(objects'[actions[k].awaited], now).promise.state == PromiseState.Pending
      {
        var id := actions[k].awaited;
        assert id in objects;
        if id == awaited {
          assert objects'[id] == added;
          assert Project(added, now) == added;
        } else {
          assert objects'[id] == objects[id];
        }
      }
      if awaiter in objects {
        assert objects'[awaiter] == objects[awaiter];
      }
      AddSuspendsOk(objects', awaiter, actions, i + 1, now);
    }
  }

  lemma ExtendOk(objects: map<string, Obj>, pid: string, refs: seq<TaskRef>, i: nat, now: nat)
    requires i <= |refs|
    requires MapOk(objects, now)
    ensures MapOk(Extend(objects, pid, refs, i, now), now)
    decreases |refs| - i
  {
    if i < |refs| {
      var id := refs[i].id;
      if id in objects {
        var seen := Project(objects[id], now);
        match seen.task
        case None =>
          ExtendOk(objects, pid, refs, i + 1, now);
        case Some(t) =>
          if t.state == TaskState.Acquired && t.version == refs[i].version && t.pid == Some(pid) {
            Stored(objects[id], now, t);
            assert objects[id].task == Some(t);
            assert TaskOk(Some(t));
            assert t.ttl.Some?;
            assert TtlOf(t) == t.ttl.value;
            var at := now + TtlOf(t);
            LeaseOk(t, at);
            var bumped := t.(leaseTimeoutAt := Some(at));
            var next := Obj(seen.promise, Some(bumped));
            assert seen == objects[id];
            assert next.promise == objects[id].promise;
            assert next.promise.callbacks == objects[id].promise.callbacks;
            ReplaceOk(objects, id, next, now);
            ExtendOk(objects[id := next], pid, refs, i + 1, now);
          } else {
            ExtendOk(objects, pid, refs, i + 1, now);
          }
      } else {
        ExtendOk(objects, pid, refs, i + 1, now);
      }
    }
  }

  function Handle(doc: Doc, request: Request, now: nat, retry: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
    ensures CaughtUp(r.doc, now)
  {
    var swept := Sweep(doc, now, retry);
    assert WellFormed(doc, now) ==> WellFormed(swept.doc, now);
    var done :=
      match request
      case PromiseGet(id) => Get(swept.doc, id, now)
      case PromiseCreate(create) => Create(swept.doc, create, now)
      case PromiseSettle(settle) => Settle(swept.doc, settle, now, retry)
      case PromiseRegisterCallback(callback) => RegisterCallback(swept.doc, callback, now)
      case PromiseRegisterListener(listener) => RegisterListener(swept.doc, listener, now)
      case TaskGet(id) => GetTask(swept.doc, id, now)
      case TaskCreate(pid, ttl, create) => CreateTask(swept.doc, pid, ttl, create, now)
      case TaskAcquire(id, version, pid, ttl) => AcquireTask(swept.doc, id, version, pid, ttl, now)
      case TaskRelease(id, version) => ReleaseTask(swept.doc, id, version, now)
      case TaskFulfill(id, version, settle) => FulfillTask(swept.doc, id, version, settle, now)
      case TaskHalt(id) => HaltTask(swept.doc, id, now)
      case TaskContinue(id) => ContinueTask(swept.doc, id, now)
      case TaskHeartbeat(pid, refs) => Heartbeat(swept.doc, pid, refs, now)
      case TaskSuspend(id, version, suspend) => SuspendTask(swept.doc, id, version, suspend, now)
      case TaskFence(id, version, fence) => Fence(swept.doc, id, version, fence, now, retry)
      case TaskFenceCheck(id, version) => FenceCheck(swept.doc, id, version, now);
    Applied(done.doc, done.answer, swept.notes + done.notes)
  }

  lemma HandlerPreservesWellFormed(doc: Doc, request: Request, now: nat, retry: nat)
    requires WellFormed(doc, now)
    ensures var r := Handle(doc, request, now, retry);
      && WellFormed(r.doc, now)
      && r.doc.stamp == now
      && OnTime(ObjectsOf(r.doc), now)
  {
  }
}
