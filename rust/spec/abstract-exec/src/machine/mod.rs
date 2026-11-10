//! Verified executable realization of the abstract protocol transitions.
#![cfg_attr(not(verus_keep_ghost), allow(unused_imports))]
use vstd::prelude::*;
use echod_types::*;
use crate::trusted::*;
use crate::view::*;
pub use echod_abstract_spec::machine::*;
pub use echod_abstract_spec::{Dispatch, ServerConfig};

verus! {
/// Executable handlers bound to a passive specification configuration.
pub(crate) struct Machine<'a>(pub(crate) &'a ServerConfig);

/// The first value of `key`, which is how a tag list is read: `spec_first`.
fn first_of(tags: &Tags, key: &str) -> (r: Option<String>)
    ensures
        r is None <==> spec_first(*tags, key@, 0) is None,
        r is Some ==> spec_first(*tags, key@, 0) == Some(r->0@),
{
    let mut i: usize = 0;
    while i < tags.len()
        invariant
            i <= tags.len(),
            spec_first(*tags, key@, 0) == spec_first(*tags, key@, i as int),
        decreases tags.len() - i,
    {
        if tags[i].0.as_str() == key {
            return Some(tags[i].1.clone());
        }
        i += 1;
    }
    None
}

fn has_target(tags: &Tags) -> (r: bool)
    ensures
        r == spec_has_target(*tags),
{
    proof {
        reveal_strlit("resonate:target");
        assert("resonate:target"@ =~= tag_target());
    }
    first_of(tags, "resonate:target").is_some()
}

fn is_true(tags: &Tags, key: &str) -> (r: bool)
    ensures
        r == (spec_first(*tags, key@, 0) == Some(tag_true())),
{
    proof {
        reveal_strlit("true");
        assert("true"@ =~= tag_true());
    }
    match first_of(tags, key) {
        Some(v) => v.as_str() == "true",
        None => false,
    }
}

fn is_timer(tags: &Tags) -> (r: bool)
    ensures
        r == spec_is_timer(*tags),
{
    proof {
        reveal_strlit("resonate:timer");
        assert("resonate:timer"@ =~= tag_timer());
    }
    is_true(tags, "resonate:timer")
}

fn is_external_tag(tags: &Tags) -> (r: bool)
    ensures
        r == spec_is_external_tag(*tags),
{
    proof {
        reveal_strlit("resonate:external");
        assert("resonate:external"@ =~= tag_external());
    }
    is_true(tags, "resonate:external")
}

fn is_global(tags: &Tags) -> (r: bool)
    ensures
        r == spec_is_global(*tags),
{
    proof {
        reveal_strlit("resonate:scope");
        reveal_strlit("global");
        assert("resonate:scope"@ =~= tag_scope());
        assert("global"@ =~= tag_global());
    }
    match first_of(tags, "resonate:scope") {
        Some(v) => v.as_str() == "global",
        None => false,
    }
}

/// `resonate:delay`, when it is a number of milliseconds: `spec_delay`.
fn delay_of(tags: &Tags) -> (r: Option<u64>)
    ensures
        r == spec_delay(*tags),
{
    proof {
        reveal_strlit("resonate:delay");
        assert("resonate:delay"@ =~= tag_delay());
    }
    match first_of(tags, "resonate:delay") {
        Some(text) => parse_u64(&text),
        None => None,
    }
}

/// Decimal digits to a number, `None` on anything else or on overflow:
/// `spec_parse_u64`, what `str::parse::<u64>` accepts.
fn parse_u64(text: &String) -> (r: Option<u64>)
    ensures
        r == spec_parse_u64(text@),
{
    let chars = chars_of(text);
    parse_chars(&chars, Ghost(text@))
}

#[verifier::external_body]
fn chars_of(text: &String) -> (r: Vec<char>)
    ensures
        r@ == text@,
{
    text.chars().collect()
}

fn parse_chars(chars: &Vec<char>, _text: Ghost<Seq<char>>) -> (r: Option<u64>)
    requires
        chars@ == _text@,
    ensures
        r == spec_parse_u64(_text@),
{
    if chars.len() == 0 {
        return None;
    }
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(_text@.skip(0) =~= _text@);
    }
    while i < chars.len()
        invariant
            i <= chars.len(),
            chars@ == _text@,
            _text@.len() > 0,
            spec_parse_u64(_text@) == spec_parse_acc(_text@.skip(i as int), acc),
        decreases chars.len() - i,
    {
        let c = chars[i];
        if c < '0' || c > '9' {
            return None;
        }
        let d = (c as u64) - ('0' as u64);
        if acc > (u64::MAX - d) / 10 {
            return None;
        }
        proof {
            assert(_text@.skip(i as int).drop_first() =~= _text@.skip(i as int + 1));
        }
        acc = acc * 10 + d;
        i += 1;
    }
    proof {
        assert(_text@.skip(i as int) =~= Seq::<char>::empty());
    }
    Some(acc)
}


#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Promise {
    pub state: PromiseState,
    pub value: Value,
    pub param: Value,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
    /// Awaiter ids to resume when this promise settles.
    pub callbacks: PSet,
    /// Addresses to send an `unblock` to when this promise settles.
    pub listeners: PSet,
}

impl Promise {
    /// Awaitable: Lean's `otype.awaitable`, everything but an internal promise.
    pub fn external(&self) -> (r: bool)
        ensures
            r == spec_external(self@),
    {
        has_target(&self.tags)
            || is_global(&self.tags)
            || is_external_tag(&self.tags)
            || is_timer(&self.tags)
    }

    /// The promise as a read at `now` sees it. A pending promise past its
    /// deadline is settled at the deadline: `spec_project_promise`.
    pub(crate) fn project(&self, now: Time) -> (r: Promise)
        ensures
            r@ == spec_project_promise(self@, now),
    {
        if self.state == PromiseState::Pending && now >= self.timeout_at {
            let mut q = copy(self);
            q.state = if is_timer(&self.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
            q.settled_at = Some(self.timeout_at);
            q
        } else {
            copy(self)
        }
    }

    /// The record a reply carries: `spec_promise_record`.
    pub(crate) fn to_record(&self, id: &Id) -> (r: PromiseRecord)
        ensures
            r == spec_promise_record(*id, self@),
            r.state == self.state,
            r.timeout_at == self.timeout_at,
            r.created_at == self.created_at,
            r.settled_at == self.settled_at,
    {
        let param = self.param.dup();
        let value = self.value.dup();
        let tags = echod_types::clone_tags(&self.tags);
        proof {
            lemma_value_ext(param, self.param);
            lemma_value_ext(value, self.value);
            lemma_tags_ext(tags, self.tags);
        }
        PromiseRecord {
            id: id.clone(),
            state: self.state,
            param,
            value,
            tags,
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Task {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<String>,
    pub ttl: Option<Time>,
    /// When the lease started (or was last extended); its end is `acquired_at + ttl`.
    pub acquired_at: Time,
    /// When a pending task is next offered to a worker (Lean's `retryTimeoutAt`).
    pub retry_timeout_at: Option<Time>,
    /// The awaited promises that settled since the task last ran (Lean's `resumes`).
    pub resumes: Vec<Id>,
}

impl Task {
    fn fulfill(&mut self)
        ensures
            final(self)@ == spec_fulfill(old(self)@),
    {
        self.state = TaskState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        proof {
            broadcast use group_views;
        }
    }

    fn acquire(&mut self, version: u64, pid: String, ttl: Time, now: Time)
        ensures
            final(self)@ == spec_acquire(old(self)@, version, pid@, ttl, now),
    {
        self.state = TaskState::Acquired;
        self.version = version;
        self.pid = Some(pid);
        self.ttl = Some(ttl);
        self.acquired_at = now;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        proof {
            broadcast use group_views;
        }
    }

    /// Lean's `unlease`: `state`, no lease, next offer at `retry`.
    fn unlease(&mut self, state: TaskState, retry: Option<Time>)
        ensures
            final(self)@ == spec_unlease(old(self)@, state, retry),
    {
        self.state = state;
        self.pid = None;
        self.ttl = None;
        self.acquired_at = 0;
        self.retry_timeout_at = retry;
    }

    pub fn lease_timeout_at(&self) -> (r: Time)
        ensures
            r == spec_lease_at(self@),
    {
        match self.ttl {
            Some(ttl) => self.acquired_at.saturating_add(ttl),
            None => self.acquired_at,
        }
    }

    /// The task as its promise reads. A settled promise fulfills the task:
    /// `spec_project_task`.
    pub(crate) fn project(&self, promise: &Promise) -> (r: Task)
        ensures
            r@ == spec_project_task(self@, promise@),
    {
        if promise.state != PromiseState::Pending && self.state != TaskState::Fulfilled {
            let mut u = copy(self);
            u.fulfill();
            u
        } else {
            copy(self)
        }
    }

    /// The record a reply carries: `spec_task_record`.
    pub(crate) fn to_record(&self, id: &Id) -> (r: TaskRecord)
        ensures
            r == spec_task_record(*id, self@),
    {
        let resumes: u64 = if self.resumes.len() as u64 > u64::MAX { u64::MAX } else { self.resumes.len() as u64 };
        let pid = copy(&self.pid);
        proof {
            broadcast use group_views;
            if self.pid is Some {
                lemma_string_of(self.pid->0);
            }
        }
        TaskRecord { id: id.clone(), state: self.state, version: self.version, resumes, ttl: self.ttl, pid }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Store {
    pub promises: PMap<Promise>,
    pub tasks: PMap<Task>,
    pub schedules: PMap<Schedule>,
}

pub open spec fn exec_promise_ok(p: Promise) -> bool {
    times_ok(p.created_at, p.settled_at, p.timeout_at)
}

pub open spec fn exec_server_ok(s: Store) -> bool {
    forall|k: Seq<char>| #[trigger] s.promises@.contains_key(k)
        ==> exec_promise_ok(s.promises@[k])
}

/// Lean's `newObject`. `at` is when the promise is created: the clock for a
/// request, the occurrence instant for a schedule. A deadline already past
/// `now` is born settled. `runnable` adds the task, offered at `at` or at
/// its delay.
fn new_object(timeout_at: Time, at: Time, now: Time, param: &Value, tags: &Tags, runnable: bool) -> (born: (Promise, Option<Task>))
    ensures
        exec_promise_ok(born.0),
        born.0.timeout_at == timeout_at,
        born.0@ == spec_new_object(timeout_at, at, now, *param, *tags, runnable).0,
        match born.1 {
            Some(t) => spec_new_object(timeout_at, at, now, *param, *tags, runnable).1 == Some(t@),
            None => spec_new_object(timeout_at, at, now, *param, *tags, runnable).1 is None,
        },
{
    broadcast use group_views;
    let live_now = timeout_at > now;
    let live_at = timeout_at > at;
    let state = if live_now {
        PromiseState::Pending
    } else if is_timer(tags) {
        PromiseState::Resolved
    } else {
        PromiseState::RejectedTimedout
    };
    let param_copy = param.dup();
    let tags_copy = echod_types::clone_tags(tags);
    let empty = Value::empty();
    proof {
        lemma_value_ext(param_copy, *param);
        lemma_tags_ext(tags_copy, *tags);
        assert(exists|v: Value| v@ == echod_types::AValue::empty());
        lemma_value_ext(empty, spec_empty_value());
    }
    let promise = Promise {
        state,
        value: empty,
        param: param_copy,
        timeout_at,
        created_at: if live_at { at } else { timeout_at },
        settled_at: if live_now { None } else { Some(timeout_at) },
        tags: tags_copy,
        callbacks: PSet::empty(),
        listeners: PSet::empty(),
    };
    let task = if runnable {
        let due = match delay_of(tags) {
            Some(d) => if d > at { d } else { at },
            None => at,
        };
        let task_state = if live_now { TaskState::Pending } else { TaskState::Fulfilled };
        let retry_timeout_at = if live_now { Some(due) } else { None };
        Some(Task { state: task_state, version: 0, pid: None, ttl: None, acquired_at: 0, retry_timeout_at, resumes: Vec::new() })
    } else {
        None
    };
    proof {
        assert(promise.created_at <= timeout_at);
        assert(promise.settled_at == if live_now { None } else { Some(timeout_at) });
        assert(exec_promise_ok(promise));
    }
    (promise, task)
}

fn copy_store(s: &Store) -> (r: Store)
    ensures
        r.promises@ == s.promises@,
        r.tasks@ == s.tasks@,
        r.schedules@ == s.schedules@,
        r@ == s@,
{
    Store { promises: s.promises.copy(), tasks: s.tasks.copy(), schedules: s.schedules.copy() }
}

pub(crate) fn promise_res(status: u16, promise: Option<PromiseRecord>) -> (r: Response)
    ensures
        r == spec_promise_res(status, promise),
{
    Response::Promise(PromiseRes { status, promise })
}

pub(crate) fn schedule_res(status: u16, schedule: Option<Schedule>) -> (r: Response)
    ensures
        r == spec_schedule_res(status, schedule),
{
    Response::Schedule(ScheduleRes { status, schedule })
}

fn status_res(status: u16) -> (r: Response)
    ensures
        r == spec_status_res(status),
{
    Response::Status(StatusRes { status })
}

pub(crate) fn task_get_res(status: u16, task: Option<TaskRecord>) -> (r: Response)
    ensures
        r == spec_task_get_res(status, task),
{
    Response::TaskGet(TaskGetRes { status, task })
}

fn claim_res(status: u16, task: Option<TaskRecord>, promise: Option<PromiseRecord>) -> (r: Response)
    ensures
        r == spec_claim_res(status, task, promise),
{
    Response::TaskClaim(TaskClaimRes { status, task, promise })
}

fn fence_res(status: u16, action: Option<TaskFenceInnerRes>) -> (r: Response)
    ensures
        r == spec_fence_res(status, action),
{
    Response::TaskFence(TaskFenceRes { status, action })
}

/// The reply when a request is shed or the store does not answer. The shape
/// follows the request, and the status is 503.
pub(crate) fn unavailable(request: &Request) -> (response: Response)
    ensures
        response == spec_unavailable(*request),
{
    match request {
        Request::PromiseGet(_) | Request::PromiseCreate(_) | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_) | Request::PromiseRegisterListener(_) => {
            promise_res(503, None)
        },
        Request::ScheduleGet(_) | Request::ScheduleCreate(_) => schedule_res(503, None),
        Request::ScheduleDelete(_) | Request::TaskRelease(_) | Request::TaskHalt(_)
        | Request::TaskContinue(_) | Request::TaskHeartbeat(_) | Request::TaskSuspend(_)
        | Request::TaskFenceCheck(_) => status_res(503),
        Request::TaskGet(_) => task_get_res(503, None),
        Request::TaskCreate(_) | Request::TaskAcquire(_) => claim_res(503, None, None),
        Request::TaskFulfill(_) => promise_res(503, None),
        Request::TaskFence(_) => fence_res(503, None),
    }
}

/// One due item. A timeout runs exactly one. The schedule item appends an
/// `Occurrence` to the queue; that is the only work a step starts.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Work {
    PromiseTimeout(Id),
    Callback { awaited: Id, awaiter: Id },
    Listener { awaited: Id, address: String },
    TaskLeaseTimeout(Id),
    TaskRetryTimeout(Id),
    /// Record the run and queue its occurrence. `promise` is the id that
    /// occurrence will create, so the step's footprint can name it.
    ScheduleTimeout { id: Id, promise: Id },
    /// A promise to create as of `at`, queued by the schedule item.
    Occurrence { promise: Id, at: Time, timeout: Time, param: Value, tags: Tags },
}

/// One possible effect of a request: the response, the next state, the work it
/// starts, the dispatches it sends. As `echod_rover::ExternalOutcome`.
pub struct Out {
    pub resp: Response,
    pub next: Store,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    /// What this outcome does, for coverage. Changes nothing.
    pub marks: Vec<&'static str>,
}

/// The effect of one work item. As `echod_rover::InternalOutcome`. `not_due`
/// means the handler did nothing, so the step is not a timeout choice.
pub struct InOut {
    pub next: Store,
    pub work: Vec<Work>,
    pub send: Vec<Dispatch>,
    pub marks: Vec<&'static str>,
    pub not_due: bool,
}

fn one(o: Out) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0] == o,
        outs_v(r@) == seq![o@],
{
    let mut v = Vec::new();
    v.push(o);
    proof {
        broadcast use group_views;
    }
    v
}

/// A mark: the name of a branch of the spec, for coverage. Every mark goes
/// through `mk` with a string literal, so a test can list them from this module.
pub(crate) fn mk(name: &'static str) -> &'static str {
    name
}

fn marked(name: &'static str) -> Vec<&'static str> {
    let mut v = Vec::new();
    v.push(name);
    v
}

/// One outcome that answers `resp` and changes nothing: `spec_out`.
pub(crate) fn status(resp: Response, mark: &'static str, s: &Store) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == resp,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,
        outs_v(r@) == spec_out(resp, s@),
{
    broadcast use group_views;
    let work: Vec<Work> = Vec::new();
    let send: Vec<Dispatch> = Vec::new();
    let r = one(Out { resp, next: copy_store(s), work, send, marks: marked(mark) });
    proof {
        assert(works(work@) =~= Seq::empty());
        assert(sends(send@) =~= Seq::empty());
    }
    r
}

/// The same as `status`; the mark says the request found what it named.
pub(crate) fn echo(res: Response, mark: &'static str, s: &Store) -> (r: Vec<Out>)
    ensures
        r.len() == 1,
        r[0].resp == res,
        r[0].next.promises@ == s.promises@,
        r[0].next.tasks@ == s.tasks@,
        r[0].next.schedules@ == s.schedules@,
        outs_v(r@) == spec_out(res, s@),
{
    status(res, mark, s)
}

/// Settles `id` and fulfills its task, if any: `spec_settle`.
fn settle(s: &mut Store, id: &Id, state: PromiseState, value: &Value, at: Time)
    ensures
        final(s)@ == spec_settle(old(s)@, id@, state, *value, at),
{
    broadcast use group_views;
    let ghost s0 = *s;

    match s.promises.get(id) {
        Some(p) => {
            let mut q = copy(p);
            q.state = state;
            let v = value.dup();
            proof {
                lemma_value_ext(v, *value);
            }
            q.value = v;
            q.settled_at = Some(at);
            assert(q@ == (PromiseV { state, value: *value, settled_at: Some(at), ..s0@.promises[id@] }));
            s.promises.insert(id.clone(), q);
            assert(s.promises@ == s0.promises@.insert(id@, q));
            assert(s.promises@.map_values(|p: Promise| p@) == s0.promises@.map_values(|p: Promise| p@).insert(id@, q@));
        },
        None => {},
    }

    assert(s@.tasks == s0@.tasks);
    let ghost s1 = *s;
    if s.promises.contains_key(id) {
        match s.tasks.get(id) {
            Some(t) => {
                if t.state != TaskState::Fulfilled {
                    let mut u = copy(t);
                    u.fulfill();
                    s.tasks.insert(id.clone(), u);
                    assert(s.tasks@.map_values(|t: Task| t@) =~= s1.tasks@.map_values(|t: Task| t@).insert(id@, u@));
                }
            },
            None => {},
        }
    }
    proof {
        if !s0.promises@.contains_key(id@) {
            assert(s@ == s0@);
        } else {
            assert(s@ =~= spec_settle(s0@, id@, state, *value, at));
        }
    }
}

fn contains(ids: &Vec<Id>, id: &Id) -> (r: bool)
    ensures
        r == strs(ids@).contains(id@),
{
    let mut i = 0;
    while i < ids.len()
        invariant
            i <= ids.len(),
            forall|j: int| 0 <= j < i ==> strs(ids@)[j] != id@,
        decreases ids.len() - i,
    {
        if ids[i] == *id {
            assert(strs(ids@)[i as int] == id@);
            return true;
        }
        i += 1;
    }
    false
}


} // verus!

pub mod external;
pub mod internal;
pub use external::*;
pub use internal::*;
