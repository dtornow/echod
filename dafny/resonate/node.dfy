include "../framework/order.dfy"

// One node handler, the document half of `spec_handle`.
//
// A document is an origin's objects, or a schedule. `WellFormed` is the
// catalogue for that document: the promise rows, the task rows, and, when
// the document is a schedule, the schedule rows. Before the handler, the
// document is swept at that instant: due steps until one changes nothing,
// or `SweepSteps` of them have run. Promise create then sees that document.
// A timer that is also targeted is refused. An id already present is
// answered as it stands, projected at `now`, and not written back. A new id
// is inserted, and a schedule document becomes an origin to hold it. The
// sweep and the handler each leave a well-formed document well-formed.

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

  datatype Doc = Origin(objects: map<string, Obj>) | Schedule(slot: Opt<Sched>)

  datatype CreateReq = CreateReq(id: string, timeoutAt: nat, param: Value, tags: Tags)
  datatype Request = PromiseCreate(req: CreateReq)
  datatype Answer = Answer(status: nat, promise: Opt<Promise>)
  datatype Applied = Applied(doc: Doc, answer: Answer)

  datatype Occurrence = Occurrence(promise: string, at: nat, timeout: nat, param: Value, tags: Tags)
  datatype Note = Execute(id: string, version: nat) | Unblock(address: string, id: string, promise: Promise)
  datatype Ran = Ran(doc: Doc, born: seq<Occurrence>, notes: seq<Note>)
  datatype Stepped = Stepped(objects: map<string, Obj>, notes: seq<Note>)

  // How many due steps one sweep runs. A document with more due is left
  // with a deadline still due.
  const SweepSteps: nat := 256

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
    case Origin(objects) => MapOk(objects, now)
    case Schedule(slot) => slot.Some? ==> ScheduleOk(slot.value)
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

  predicate PromiseDue(o: Obj, now: nat) {
    if o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now then true
    else if o.promise.state != PromiseState.Pending && (o.promise.callbacks != {} || o.promise.listeners != {}) then
      var at := if o.promise.settledAt.Some? then o.promise.settledAt.value else 0;
      at <= now
    else false
  }

  predicate LeaseDue(o: Obj, now: nat) {
    match o.task
    case Some(t) =>
      o.promise.state == PromiseState.Pending && t.state == TaskState.Acquired &&
      t.leaseTimeoutAt.Some? && t.leaseTimeoutAt.value <= now
    case None => false
  }

  predicate RetryDue(o: Obj, now: nat) {
    match o.task
    case Some(t) =>
      o.promise.state == PromiseState.Pending && t.state == TaskState.Pending &&
      t.retryTimeoutAt.Some? && t.retryTimeoutAt.value <= now
    case None => false
  }

  predicate Due(o: Obj, now: nat) {
    PromiseDue(o, now) || LeaseDue(o, now) || RetryDue(o, now)
  }

  function DueKeys(objects: map<string, Obj>, now: nat): set<string> {
    set id | id in objects && Due(objects[id], now)
  }

  function FirstDue(objects: map<string, Obj>, now: nat): (r: Opt<string>)
    ensures r.Some? ==> r.value in objects && Due(objects[r.value], now)
  {
    var keys := DueKeys(objects, now);
    if keys == {} then None
    else
      var id := MinKey(keys);
      assert id in keys;
      Some(id)
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

  function StepObject(objects: map<string, Obj>, id: string, now: nat, retry: nat): Stepped
    requires id in objects
  {
    var o := objects[id];
    if o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now then
      Stepped(objects[id := Project(o, now)], [])
    else if o.promise.state == PromiseState.Pending then
      match o.task
      case Some(t) =>
        if t.state == TaskState.Acquired && t.leaseTimeoutAt.Some? && t.leaseTimeoutAt.value <= now then
          Stepped(objects[id := Obj(o.promise, Some(Unlease(t, now)))], [])
        else if t.state == TaskState.Pending && t.retryTimeoutAt.Some? && t.retryTimeoutAt.value <= now then
          Stepped(objects[id := Obj(o.promise, Some(Rearm(t, now + retry)))], [Execute(id, t.version)])
        else
          Stepped(objects, [])
      case None => Stepped(objects, [])
    else if o.promise.callbacks != {} then
      // One id per awaiter. The step takes the least.
      var awaiter := MinKey(o.promise.callbacks);
      var since := if o.promise.settledAt.Some? then o.promise.settledAt.value else 0;
      var objects' := objects[id := DropCallback(o, awaiter)];
      Stepped(Resume(objects', awaiter, id, since, now), [])
    else if o.promise.listeners != {} then
      var address := MinKey(o.promise.listeners);
      var dropped := DropListener(o, address);
      Stepped(objects[id := dropped], [Unblock(address, id, o.promise)])
    else
      Stepped(objects, [])
  }

  function RunDue(doc: Doc, now: nat, retry: nat): Ran {
    match doc
    case Schedule(Some(s)) =>
      if s.nextRunAt <= now then
        var at := s.nextRunAt;
        var born := Occurrence(Expand(s.promiseId, s.id, at), at, s.promiseTimeout, s.promiseParam, s.promiseTags);
        var s' := s.(lastRunAt := Some(at), nextRunAt := NextCron(s.cron, at));
        Ran(Schedule(Some(s')), [born], [])
      else
        Ran(doc, [], [])
    case Origin(objects) =>
      (match FirstDue(objects, now)
       case None => Ran(doc, [], [])
       case Some(id) =>
         var stepped := StepObject(objects, id, now, retry);
         Ran(Origin(stepped.objects), [], stepped.notes))
    case Schedule(None) => Ran(doc, [], [])
  }

  function Sweep(doc: Doc, now: nat, retry: nat, limit: nat): (s: Ran)
    ensures WellFormed(doc, now) ==> WellFormed(s.doc, now)
    decreases limit
  {
    if limit == 0 then Ran(doc, [], [])
    else
      var ran := RunDue(doc, now, retry);
      if ran.doc == doc then Ran(doc, [], [])
      else
        var rest := Sweep(ran.doc, now, retry, limit - 1);
        assert WellFormed(doc, now) ==> WellFormed(rest.doc, now) by {
          if WellFormed(doc, now) {
            RunDueOk(doc, now, retry);
          }
        }
        Ran(rest.doc, ran.born + rest.born, ran.notes + rest.notes)
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

  lemma StepOk(objects: map<string, Obj>, id: string, now: nat, retry: nat)
    requires MapOk(objects, now) && id in objects
    ensures MapOk(StepObject(objects, id, now, retry).objects, now)
  {
    var o := objects[id];
    if o.promise.state == PromiseState.Pending && o.promise.timeoutAt <= now {
      ProjectOk(id, o, now);
      ReplaceOk(objects, id, Project(o, now), now);
    } else if o.promise.state == PromiseState.Pending {
      match o.task
      case Some(t) =>
        if t.state == TaskState.Acquired && t.leaseTimeoutAt.Some? && t.leaseTimeoutAt.value <= now {
          UnleaseOk(t, now);
          var placed := Obj(o.promise, Some(Unlease(t, now)));
          ReplaceOk(objects, id, placed, now);
        } else if t.state == TaskState.Pending && t.retryTimeoutAt.Some? && t.retryTimeoutAt.value <= now {
          RearmOk(t, now + retry);
          var placed := Obj(o.promise, Some(Rearm(t, now + retry)));
          ReplaceOk(objects, id, placed, now);
        }
      case None =>
    } else if o.promise.callbacks != {} {
      var awaiter := MinKey(o.promise.callbacks);
      var since := if o.promise.settledAt.Some? then o.promise.settledAt.value else 0;
      DropCallbackOk(id, o, awaiter, now);
      var objects' := objects[id := DropCallback(o, awaiter)];
      ReplaceOk(objects, id, DropCallback(o, awaiter), now);
      ResumeOk(objects', awaiter, id, since, now);
    } else if o.promise.listeners != {} {
      var address := MinKey(o.promise.listeners);
      var dropped := DropListener(o, address);
      assert dropped.promise.state == o.promise.state;
      assert dropped.promise.callbacks == o.promise.callbacks;
      ReplaceOk(objects, id, dropped, now);
    }
  }

  lemma RunDueOk(doc: Doc, now: nat, retry: nat)
    requires WellFormed(doc, now)
    ensures WellFormed(RunDue(doc, now, retry).doc, now)
  {
    match doc
    case Schedule(Some(s)) =>
      if s.nextRunAt <= now {
        AdvanceOk(s);
      }
    case Origin(objects) =>
      var due := FirstDue(objects, now);
      if due.Some? {
        StepOk(objects, due.value, now, retry);
      }
    case Schedule(None) =>
  }

  function Handle(doc: Doc, request: Request, now: nat, retry: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    var swept := Sweep(doc, now, retry, SweepSteps);
    match request
    case PromiseCreate(req) =>
      var r := Create(swept.doc, req, now);
      assert WellFormed(doc, now) ==> WellFormed(r.doc, now) by {
        if WellFormed(doc, now) {
          assert WellFormed(swept.doc, now);
        }
      }
      r
  }

  lemma HandlerPreservesWellFormed(doc: Doc, request: Request, now: nat, retry: nat)
    requires WellFormed(doc, now)
    ensures WellFormed(Handle(doc, request, now, retry).doc, now)
  {
  }
}
