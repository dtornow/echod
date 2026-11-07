include "../framework/order.dfy"

// One node handler, the document half of `spec_handle`.
//
// A document is an origin's objects, or a schedule. `WellFormed` is the
// catalogue for that document: the promise rows, the task rows, and, when
// the document is a schedule, the schedule rows. Before the handler, the
// document is swept at that instant. Every promise whose deadline has
// passed is timed out first. A timeout leaves that promise's callbacks in
// place, and the next pass applies them: every callback on a settled
// promise, least id first. Listeners are told the same way. A lease and a
// retry still due on a promise that is still pending come after that. A
// schedule is its next run. The promise calls then see that document.
// Get answers from the projection and does not write it back. Create refuses
// a timer that is also targeted. An id already present is answered as it
// stands, projected at `now`, and not written back. A new id is inserted,
// and a schedule document becomes an origin to hold it. Settle writes only
// a promise the projection still shows as pending, and fulfills its task.
// A callback is recorded only while both promises are still pending, and
// only for another id of the same origin. A listener is recorded only while
// the promise is still pending. A schedule is opened into an empty origin
// before get, settle, and the two registrations look it up. The sweep and
// the handler each leave a well-formed document well-formed.

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
  datatype SettleReq = SettleReq(id: string, state: PromiseState, value: Value)
  datatype CallbackReq = CallbackReq(awaited: string, awaiter: string)
  datatype ListenerReq = ListenerReq(awaited: string, address: string)
  datatype Request =
    | PromiseGet(id: string)
    | PromiseCreate(create: CreateReq)
    | PromiseSettle(settle: SettleReq)
    | PromiseRegisterCallback(callback: CallbackReq)
    | PromiseRegisterListener(listener: ListenerReq)
  datatype Answer = Answer(status: nat, promise: Opt<Promise>)
  datatype Applied = Applied(doc: Doc, answer: Answer)

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

  // A schedule has no rows. Looking one up is the empty origin.
  function Opened(doc: Doc): Doc {
    Origin(ObjectsOf(doc))
  }

  function Get(doc: Doc, id: string, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if id !in objects then Applied(shown, Answer(404, None))
    else Applied(shown, Answer(200, Some(Project(objects[id], now).promise)))
  }

  function Settled(o: Obj, state: PromiseState, value: Value, now: nat): Obj {
    var promise := o.promise.(state := state, value := value, settledAt := Some(now));
    var task :=
      match o.task
      case None => None
      case Some(t) => if t.state == TaskState.Fulfilled then Some(t) else Some(Fulfill(t));
    Obj(promise, task)
  }

  function Settle(doc: Doc, req: SettleReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    if !Settable(req.state) then Applied(doc, Answer(400, None))
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      if req.id !in objects then Applied(shown, Answer(404, None))
      else
        var seen := Project(objects[req.id], now);
        if seen.promise.state != PromiseState.Pending then
          Applied(shown, Answer(200, Some(seen.promise)))
        else
          var obj := Settled(seen, req.state, req.value, now);
          var doc' := Origin(objects[req.id := obj]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              StillPending(objects[req.id], now);
              SettledOk(req.id, seen, req.state, req.value, now);
              ReplaceOk(objects, req.id, obj, now);
            }
          }
          Applied(doc', Answer(200, Some(obj.promise)))
  }

  function AddCallback(o: Obj, awaiter: string): Obj {
    if awaiter in o.promise.callbacks then o
    else Obj(o.promise.(callbacks := o.promise.callbacks + {awaiter}), o.task)
  }

  function RegisterCallback(doc: Doc, req: CallbackReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    if req.awaited == req.awaiter || OriginOf(req.awaited) != OriginOf(req.awaiter) then
      Applied(doc, Answer(400, None))
    else
      var shown := Opened(doc);
      assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
        if WellFormed(doc, now) { OpenOk(doc, now); }
      }
      var objects := ObjectsOf(shown);
      if req.awaited !in objects then Applied(shown, Answer(404, None))
      else if req.awaiter !in objects then Applied(shown, Answer(422, None))
      else
        var awaited := Project(objects[req.awaited], now);
        var awaiter := Project(objects[req.awaiter], now);
        if !Targeted(awaiter.promise.tags) || !Awaitable(awaited.promise.tags) then
          Applied(shown, Answer(422, None))
        else if awaited.promise.state == PromiseState.Pending && awaiter.promise.state == PromiseState.Pending then
          var obj := AddCallback(awaited, req.awaiter);
          var doc' := Origin(objects[req.awaited := obj]);
          assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
            if WellFormed(doc, now) {
              StillPending(objects[req.awaited], now);
              AddCallbackOk(req.awaited, awaited, req.awaiter, now);
              ReplaceOk(objects, req.awaited, obj, now);
            }
          }
          Applied(doc', Answer(200, Some(awaited.promise)))
        else
          Applied(shown, Answer(200, Some(awaited.promise)))
  }

  function AddListener(o: Obj, address: string): Obj {
    if address in o.promise.listeners then o
    else Obj(o.promise.(listeners := o.promise.listeners + {address}), o.task)
  }

  function RegisterListener(doc: Doc, req: ListenerReq, now: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    var shown := Opened(doc);
    assert WellFormed(doc, now) ==> WellFormed(shown, now) by {
      if WellFormed(doc, now) { OpenOk(doc, now); }
    }
    var objects := ObjectsOf(shown);
    if req.awaited !in objects then Applied(shown, Answer(404, None))
    else
      var awaited := Project(objects[req.awaited], now);
      if !Awaitable(awaited.promise.tags) then
        Applied(shown, Answer(422, None))
      else if awaited.promise.state == PromiseState.Pending then
        var obj := AddListener(awaited, req.address);
        var doc' := Origin(objects[req.awaited := obj]);
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) {
            StillPending(objects[req.awaited], now);
            AddListenerOk(req.awaited, awaited, req.address, now);
            ReplaceOk(objects, req.awaited, obj, now);
          }
        }
        Applied(doc', Answer(200, Some(awaited.promise)))
      else
        Applied(shown, Answer(200, Some(awaited.promise)))
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

  function Sweep(doc: Doc, now: nat, retry: nat): (s: Ran)
    ensures WellFormed(doc, now) ==> WellFormed(s.doc, now)
  {
    match doc
    case Schedule(Some(sched)) =>
      if sched.nextRunAt <= now then
        var at := sched.nextRunAt;
        var born := Occurrence(Expand(sched.promiseId, sched.id, at), at, sched.promiseTimeout, sched.promiseParam, sched.promiseTags);
        var sched' := sched.(lastRunAt := Some(at), nextRunAt := NextCron(sched.cron, at));
        var doc' := Schedule(Some(sched'));
        assert WellFormed(doc, now) ==> WellFormed(doc', now) by {
          if WellFormed(doc, now) { AdvanceOk(sched); }
        }
        Ran(doc', [born], [])
      else
        Ran(doc, [], [])
    case Origin(objects) =>
      SortedProps(objects.Keys);
      var keys := Sorted(objects.Keys);
      forall i, j | 0 <= i < j < |keys|
        ensures keys[i] != keys[j]
      {
        assert Lt(keys[i], keys[j]);
      }
      var timed := Timeouts(objects, keys, now);
      var woken := ApplyCallbacks(timed, keys, now);
      var told := ApplyListeners(woken, keys);
      var returned := Leases(told.objects, keys, now);
      var armed := Retries(returned, keys, now, retry);
      assert WellFormed(doc, now) ==> WellFormed(Origin(armed.objects), now) by {
        if WellFormed(doc, now) {
          TimeoutsOk(objects, keys, now);
          ApplyCallbacksOk(timed, keys, now);
          ApplyListenersOk(woken, keys, now);
          LeasesOk(told.objects, keys, now);
          RetriesOk(returned, keys, now, retry);
        }
      }
      Ran(Origin(armed.objects), [], told.notes + armed.notes)
    case Schedule(None) => Ran(doc, [], [])
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
    case Origin(_) =>
      assert Opened(doc) == doc;
    case Schedule(_) =>
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

  function Handle(doc: Doc, request: Request, now: nat, retry: nat): (r: Applied)
    ensures WellFormed(doc, now) ==> WellFormed(r.doc, now)
  {
    var swept := Sweep(doc, now, retry);
    assert WellFormed(doc, now) ==> WellFormed(swept.doc, now);
    match request
    case PromiseGet(id) => Get(swept.doc, id, now)
    case PromiseCreate(req) => Create(swept.doc, req, now)
    case PromiseSettle(req) => Settle(swept.doc, req, now)
    case PromiseRegisterCallback(req) => RegisterCallback(swept.doc, req, now)
    case PromiseRegisterListener(req) => RegisterListener(swept.doc, req, now)
  }

  lemma HandlerPreservesWellFormed(doc: Doc, request: Request, now: nat, retry: nat)
    requires WellFormed(doc, now)
    ensures WellFormed(Handle(doc, request, now, retry).doc, now)
  {
  }
}
