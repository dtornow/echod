// One node handler, the document half of `spec_handle`.
//
// A document is an origin's objects, or a schedule. `WellFormed` is the
// catalogue for that document: the promise rows, the task rows, and, when
// the document is a schedule, the schedule rows. Promise create is the first
// handler. A timer that is also targeted is refused. An id already present
// is answered as it stands, projected at `now`, and not written back. A new
// id is inserted, and a schedule document becomes an origin to hold it.
// Whichever arm runs, a well-formed document stays well-formed.

module Node {
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

  datatype Doc = Origin(objects: map<string, Obj>) | Schedule(slot: Opt<Sched>)

  datatype CreateReq = CreateReq(id: string, timeoutAt: nat, param: Value, tags: Tags)
  datatype Request = PromiseCreate(req: CreateReq)
  datatype Answer = Answer(status: nat, promise: Opt<Promise>)
  datatype Applied = Applied(doc: Doc, answer: Answer)

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

  ghost predicate WellFormed(doc: Doc, now: nat) {
    match doc
    case Origin(objects) =>
      forall id :: id in objects ==> ObjectOk(id, objects[id], now)
    case Schedule(slot) =>
      slot.Some? ==> ScheduleOk(slot.value)
  }

  function ObjectsOf(doc: Doc): map<string, Obj> {
    match doc
    case Origin(objects) => objects
    case Schedule(_) => map[]
  }

  function NewPromise(timeout: nat, now: nat, param: Value, tags: Tags): (p: Promise)
    ensures PromiseOk(p, now)
    ensures p.callbacks == {}
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
    ensures WellFormed(Origin(ObjectsOf(doc)[id := obj]), now)
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
        case Origin(os) =>
          assert os == objects;
        case Schedule(_) =>
          assert objects == map[];
          assert false;
      }
    }
  }

  function Create(doc: Doc, req: CreateReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    if Timer(req.tags) && Targeted(req.tags) then
      Applied(doc, Answer(400, None))
    else
      var objects := ObjectsOf(doc);
      if req.id in objects then
        var seen := Project(objects[req.id], now);
        Applied(doc, Answer(200, Some(seen.promise)))
      else
        var obj := NewObj(req.timeoutAt, now, req.param, req.tags, Targeted(req.tags));
        var doc' := Origin(objects[req.id := obj]);
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) { InsertOk(doc, req.id, obj, now); }
        }
        Applied(doc', Answer(200, Some(obj.promise)))
  }

  function Handle(doc: Doc, request: Request, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    match request
    case PromiseCreate(req) => Create(doc, req, now)
  }

  lemma HandlerPreservesWellFormed(doc: Doc, request: Request, now: nat)
    requires WellFormed(doc, now)
    ensures WellFormed(Handle(doc, request, now).doc, now)
  {
  }
}
