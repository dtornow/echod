//! One object at an instant: projection, the task's view of its promise, and
//! the small edits every handler makes. Spec first, exec after, each exec
//! function proven equal to its spec.

use vstd::prelude::*;

use crate::tags::OType;
use crate::types::MAX_TIME;
use crate::types::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

#[cfg(verus_keep_ghost)]
impl APromise {
    pub open spec fn is_timer(self) -> bool {
        crate::tags::is_timer(self.tags)
    }

    pub open spec fn otype(self) -> OType {
        crate::tags::otype(self.tags)
    }

    /// `PromiseObject.project`: a pending promise past its deadline is settled
    /// by its deadline — resolved if it is a timer, timed out otherwise.
    pub open spec fn project_promise(self, now: nat) -> APromise {
        if self.state == PromiseState::Pending && self.timeout_at <= now {
            if self.is_timer() {
                APromise { state: PromiseState::Resolved, settled_at: Some(self.timeout_at), ..self }
            } else {
                APromise { state: PromiseState::RejectedTimedout, settled_at: Some(self.timeout_at), ..self }
            }
        } else {
            self
        }
    }

    /// `Object.project`: the promise projected, and the task viewed through it.
    pub open spec fn project(self, now: nat) -> APromise {
        let p = self.project_promise(now);
        APromise {
            task: match self.task {
                Some(t) => Some(t.view_through(p)),
                None => None,
            },
            ..p
        }
    }

    pub open spec fn add_callback(self, awaiter: Seq<char>) -> APromise {
        if self.callbacks.contains(awaiter) {
            self
        } else {
            APromise { callbacks: self.callbacks.push(awaiter), ..self }
        }
    }

    pub open spec fn add_listener(self, address: Seq<char>) -> APromise {
        if self.listeners.contains(address) {
            self
        } else {
            APromise { listeners: self.listeners.push(address), ..self }
        }
    }

    pub open spec fn remove_callback(self, awaiter: Seq<char>) -> APromise {
        APromise { callbacks: without(self.callbacks, awaiter), ..self }
    }

    pub open spec fn remove_listener(self, address: Seq<char>) -> APromise {
        APromise { listeners: without(self.listeners, address), ..self }
    }

    /// `setSettled`: the promise settled by a client at `now`, and its task
    /// fulfilled if it has one that is not.
    pub open spec fn settle(self, state: PromiseState, value: AValue, now: nat) -> APromise {
        APromise {
            state: state,
            value: value,
            settled_at: Some(now as u64),
            task: match self.task {
                Some(t) => Some(if t.state != TaskState::Fulfilled { t.fulfill() } else { t }),
                None => None,
            },
            ..self
        }
    }

    pub open spec fn with_task(self, t: ATask) -> APromise {
        APromise { task: Some(t), ..self }
    }
}

#[cfg(verus_keep_ghost)]
impl ATask {
    /// `task.create` on a pending task, `task.acquire`.
    pub open spec fn acquire(self, pid: Seq<char>, ttl: nat, now: nat) -> ATask {
        ATask {
            state: TaskState::Acquired,
            version: (self.version + 1) as u64,
            ttl: Some(ttl as u64),
            pid: Some(pid),
            lease_timeout_at: Some((now + ttl) as u64),
            retry_timeout_at: None,
            resumes: Seq::empty(),
        }
    }

    /// `task.release`, and the lease timeout.
    pub open spec fn release(self, now: nat) -> ATask {
        ATask {
            state: TaskState::Pending,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: Some(now as u64),
            ..self
        }
    }

    pub open spec fn halt(self) -> ATask {
        ATask {
            state: TaskState::Halted,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: None,
            ..self
        }
    }

    pub open spec fn continue_(self, now: nat) -> ATask {
        ATask { state: TaskState::Pending, retry_timeout_at: Some(now as u64), ..self }
    }

    pub open spec fn suspend(self) -> ATask {
        ATask {
            state: TaskState::Suspended,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: None,
            resumes: Seq::empty(),
            ..self
        }
    }

    pub open spec fn clear_resumes(self) -> ATask {
        ATask { resumes: Seq::empty(), ..self }
    }

    pub open spec fn heartbeat(self, now: nat) -> ATask {
        ATask { lease_timeout_at: Some((now + crate::properties::opt_or_zero(self.ttl)) as u64), ..self }
    }

    /// `resumeOne` on a suspended task.
    pub open spec fn wake(self, awaited: Seq<char>, now: nat) -> ATask {
        ATask { state: TaskState::Pending, resumes: seq![awaited], retry_timeout_at: Some(now as u64), ..self }
    }

    /// `resumeOne` on a task that is not suspended.
    pub open spec fn buffer(self, awaited: Seq<char>) -> ATask {
        if self.resumes.contains(awaited) { self } else { ATask { resumes: self.resumes.push(awaited), ..self } }
    }

    pub open spec fn rearm(self, now: nat, retry_timeout: nat) -> ATask {
        ATask { retry_timeout_at: Some((now + retry_timeout) as u64), ..self }
    }
}

#[cfg(verus_keep_ghost)]
impl ATask {
    /// `TaskObject.fulfill`.
    pub open spec fn fulfill(self) -> ATask {
        ATask {
            state: TaskState::Fulfilled,
            pid: None,
            ttl: None,
            lease_timeout_at: None,
            retry_timeout_at: None,
            resumes: Seq::empty(),
            ..self
        }
    }

    /// `TaskObject.view`: a task whose promise is settled is fulfilled.
    pub open spec fn view_through(self, p: APromise) -> ATask {
        if p.state != PromiseState::Pending && self.state != TaskState::Fulfilled {
            self.fulfill()
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------
// Executable
// ---------------------------------------------------------------------------

pub fn seq_contains(v: &Vec<String>, x: &String) -> (r: bool)
    ensures r == v.deep_view().contains(x@),
{
    let ghost s = v.deep_view();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            s == v.deep_view(),
            forall|j: int| 0 <= j < i ==> s[j] != x@,
        decreases v@.len() - i,
    {
        if v[i] == *x {
            assert(s[i as int] == x@);
            return true;
        }
        i += 1;
    }
    false
}

/// `v` with `x` appended; the deep view is the view pushed.
pub fn push_string(v: &mut Vec<String>, x: String)
    ensures final(v).deep_view() == old(v).deep_view().push(x@),
{
    let ghost s = old(v).deep_view();
    v.push(x);
    assert(v.deep_view() =~= s.push(x@));
}

/// `s` without every occurrence of `x`, in order.
pub open spec fn without(s: Seq<Seq<char>>, x: Seq<char>) -> Seq<Seq<char>>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s.last() == x {
        without(s.drop_last(), x)
    } else {
        without(s.drop_last(), x).push(s.last())
    }
}

/// What `without` keeps: everything but `x`.
pub proof fn lemma_without_contains(s: Seq<Seq<char>>, x: Seq<char>, y: Seq<char>)
    ensures
        without(s, x).contains(y) <==> (s.contains(y) && y != x),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        lemma_without_contains(init, x, y);
        assert(s.contains(y) <==> (init.contains(y) || s.last() == y)) by {
            if s.contains(y) {
                let i = choose|i: int| 0 <= i < s.len() && s[i] == y;
                if i < s.len() - 1 {
                    assert(init[i] == y);
                }
            }
            if init.contains(y) {
                let i = choose|i: int| 0 <= i < init.len() && init[i] == y;
                assert(s[i] == y);
            }
            if s.last() == y {
                assert(s[s.len() - 1] == y);
            }
        }
        if s.last() != x {
            let w = without(init, x);
            assert(w.push(s.last()).contains(y) <==> (w.contains(y) || s.last() == y)) by {
                if w.push(s.last()).contains(y) {
                    let i = choose|i: int| 0 <= i < w.push(s.last()).len() && w.push(s.last())[i] == y;
                    if i < w.len() {
                        assert(w[i] == y);
                    }
                }
                if w.contains(y) {
                    let i = choose|i: int| 0 <= i < w.len() && w[i] == y;
                    assert(w.push(s.last())[i] == y);
                }
                if s.last() == y {
                    assert(w.push(s.last())[w.len() as int] == y);
                }
            }
        }
    }
}

/// `without` keeps a duplicate-free sequence duplicate-free.
pub proof fn lemma_without_no_dups(s: Seq<Seq<char>>, x: Seq<char>)
    requires
        crate::properties::no_dups(s),
    ensures
        crate::properties::no_dups(without(s, x)),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        let init = s.drop_last();
        assert(crate::properties::no_dups(init)) by {
            assert forall|i: int, j: int| 0 <= i < init.len() && 0 <= j < init.len() && init[i] == init[j]
                implies i == j by {
                assert(s[i] == init[i]);
                assert(s[j] == init[j]);
            }
        }
        lemma_without_no_dups(init, x);
        if s.last() != x {
            let w = without(init, x);
            assert(!w.contains(s.last())) by {
                lemma_without_contains(init, x, s.last());
                if init.contains(s.last()) {
                    let i = choose|i: int| 0 <= i < init.len() && init[i] == s.last();
                    assert(s[i] == s[s.len() - 1]);
                }
            }
            assert forall|i: int, j: int| 0 <= i < w.push(s.last()).len() && 0 <= j < w.push(s.last()).len()
                && w.push(s.last())[i] == w.push(s.last())[j] implies i == j by {
                if i < w.len() && j < w.len() {
                } else if i < w.len() {
                    assert(w[i] == s.last());
                } else if j < w.len() {
                    assert(w[j] == s.last());
                }
            }
        }
    }
}

/// `v` without every occurrence of `x`.
pub fn remove_string(v: &Vec<String>, x: &String) -> (r: Vec<String>)
    ensures r.deep_view() == without(v.deep_view(), x@),
{
    let ghost s = v.deep_view();
    let mut r: Vec<String> = Vec::new();
    let mut i: usize = 0;
    assert(r.deep_view() =~= Seq::<Seq<char>>::empty());
    assert(s.take(0) =~= Seq::<Seq<char>>::empty());
    while i < v.len()
        invariant
            i <= v@.len(),
            s == v.deep_view(),
            r.deep_view() == without(s.take(i as int), x@),
        decreases v@.len() - i,
    {
        let ghost before = r.deep_view();
        assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
        assert(s.take(i as int).push(s[i as int]).drop_last() =~= s.take(i as int));
        if v[i] != *x {
            assert(s[i as int] != x@);
            let y = v[i].clone();
            r.push(y);
            assert(r.deep_view() =~= before.push(s[i as int]));
        } else {
            assert(s[i as int] == x@);
        }
        i += 1;
    }
    assert(s.take(v@.len() as int) =~= s);
    r
}

impl Promise {
    pub fn is_timer(&self) -> (r: bool)
        ensures r == self@.is_timer(),
    {
        crate::tags::exec_is_timer(&self.tags)
    }

    pub fn otype(&self) -> (r: OType)
        ensures r == self@.otype(),
    {
        crate::tags::exec_otype(&self.tags)
    }

    /// `Object.project`, in place.
    pub fn project(&mut self, now: u64)
        ensures final(self)@ == old(self)@.project(now as nat),
    {
        if self.state == PromiseState::Pending && self.timeout_at <= now {
            if self.is_timer() {
                self.state = PromiseState::Resolved;
            } else {
                self.state = PromiseState::RejectedTimedout;
            }
            self.settled_at = Some(self.timeout_at);
        }
        let settled = self.state != PromiseState::Pending;
        match &mut self.task {
            Some(t) => {
                if settled && t.state != TaskState::Fulfilled {
                    t.fulfill();
                }
            }
            None => {}
        }
    }

    pub fn add_callback(&mut self, awaiter: &String)
        ensures final(self)@ == old(self)@.add_callback(awaiter@),
    {
        if !seq_contains(&self.callbacks, awaiter) {
            push_string(&mut self.callbacks, awaiter.clone());
        }
    }

    pub fn add_listener(&mut self, address: &String)
        ensures final(self)@ == old(self)@.add_listener(address@),
    {
        if !seq_contains(&self.listeners, address) {
            push_string(&mut self.listeners, address.clone());
        }
    }


    pub fn remove_callback(&mut self, awaiter: &String)
        ensures final(self)@ == old(self)@.remove_callback(awaiter@),
    {
        self.callbacks = remove_string(&self.callbacks, awaiter);
    }

    pub fn remove_listener(&mut self, address: &String)
        ensures final(self)@ == old(self)@.remove_listener(address@),
    {
        self.listeners = remove_string(&self.listeners, address);
    }

    /// `setSettled`.
    pub fn settle(&mut self, state: PromiseState, value: Value, now: u64)
        ensures final(self)@ == old(self)@.settle(state, value@, now as nat),
    {
        self.state = state;
        self.value = value;
        self.settled_at = Some(now);
        match &mut self.task {
            Some(t) => {
                if t.state != TaskState::Fulfilled {
                    t.fulfill();
                }
            }
            None => {}
        }
    }

    /// Apply `f` to the task, which must be there.
    pub fn task_acquire(&mut self, pid: &String, ttl: u64, now: u64)
        requires
            old(self).task is Some,
            now + ttl <= u64::MAX,
            old(self).task.unwrap().version < u64::MAX,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().acquire(pid@, ttl as nat, now as nat)),
    {
        match &mut self.task {
            Some(t) => {
                t.state = TaskState::Acquired;
                t.version = t.version + 1;
                t.ttl = Some(ttl);
                t.pid = Some(pid.clone());
                t.lease_timeout_at = Some(now + ttl);
                t.retry_timeout_at = None;
                t.resumes = Vec::new();
                assert(t.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
            }
            None => {}
        }
    }

    pub fn task_release(&mut self, now: u64)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().release(now as nat)),
    {
        match &mut self.task {
            Some(t) => {
                t.state = TaskState::Pending;
                t.pid = None;
                t.ttl = None;
                t.lease_timeout_at = None;
                t.retry_timeout_at = Some(now);
            }
            None => {}
        }
    }

    pub fn task_halt(&mut self)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().halt()),
    {
        match &mut self.task {
            Some(t) => {
                t.state = TaskState::Halted;
                t.pid = None;
                t.ttl = None;
                t.lease_timeout_at = None;
                t.retry_timeout_at = None;
            }
            None => {}
        }
    }

    pub fn task_continue(&mut self, now: u64)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().continue_(now as nat)),
    {
        match &mut self.task {
            Some(t) => {
                t.state = TaskState::Pending;
                t.retry_timeout_at = Some(now);
            }
            None => {}
        }
    }

    pub fn task_suspend(&mut self)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().suspend()),
    {
        match &mut self.task {
            Some(t) => {
                t.state = TaskState::Suspended;
                t.pid = None;
                t.ttl = None;
                t.lease_timeout_at = None;
                t.retry_timeout_at = None;
                t.resumes = Vec::new();
                assert(t.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
            }
            None => {}
        }
    }

    pub fn task_clear_resumes(&mut self)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().clear_resumes()),
    {
        match &mut self.task {
            Some(t) => {
                t.resumes = Vec::new();
                assert(t.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
            }
            None => {}
        }
    }

    pub fn task_heartbeat(&mut self, now: u64)
        requires
            old(self).task is Some,
            now + crate::properties::opt_or_zero(old(self).task.unwrap().ttl) <= u64::MAX,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().heartbeat(now as nat)),
    {
        match &mut self.task {
            Some(t) => {
                let ttl = match t.ttl { Some(x) => x, None => 0 };
                t.lease_timeout_at = Some(now + ttl);
            }
            None => {}
        }
    }

    pub fn task_wake(&mut self, awaited: &String, now: u64)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().wake(awaited@, now as nat)),
    {
        match &mut self.task {
            Some(t) => {
                t.state = TaskState::Pending;
                let mut v: Vec<String> = Vec::new();
                v.push(awaited.clone());
                assert(v.deep_view() =~= seq![awaited@]);
                t.resumes = v;
                t.retry_timeout_at = Some(now);
            }
            None => {}
        }
    }

    pub fn task_buffer(&mut self, awaited: &String)
        requires old(self).task is Some,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().buffer(awaited@)),
    {
        match &mut self.task {
            Some(t) => {
                if !seq_contains(&t.resumes, awaited) {
                    push_string(&mut t.resumes, awaited.clone());
                }
            }
            None => {}
        }
    }

    pub fn task_rearm(&mut self, now: u64, retry_timeout: u64)
        requires old(self).task is Some, now + retry_timeout <= u64::MAX,
        ensures final(self)@ == old(self)@.with_task(old(self)@.task.unwrap().rearm(now as nat, retry_timeout as nat)),
    {
        match &mut self.task {
            Some(t) => {
                t.retry_timeout_at = Some(now + retry_timeout);
            }
            None => {}
        }
    }

    /// `toRecord`.
    pub fn to_record(&self) -> (r: PromiseRecord)
        ensures r@ == self@.to_record(),
    {
        PromiseRecord {
            id: self.id.clone(),
            state: self.state,
            param: self.param.dup(),
            value: self.value.dup(),
            tags: clone_tags(&self.tags),
            timeout_at: self.timeout_at,
            created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }
}

impl Task {
    pub fn fulfill(&mut self)
        ensures final(self)@ == old(self)@.fulfill(),
    {
        self.state = TaskState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.lease_timeout_at = None;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        assert(self.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
    }

    pub fn to_record(&self, id: &String) -> (r: TaskRecord)
        ensures r@ == self@.to_record(id@),
    {
        TaskRecord {
            id: id.clone(),
            state: self.state,
            version: self.version,
            resumes: self.resumes.len() as u64,
            ttl: self.ttl,
            pid: match &self.pid {
                Some(p) => Some(p.clone()),
                None => None,
            },
        }
    }
}

pub fn clone_tags(t: &Tags) -> (r: Tags)
    ensures r.deep_view() == t.deep_view(),
{
    let ghost s = t.deep_view();
    let mut r: Tags = Vec::new();
    let mut i: usize = 0;
    assert(r.deep_view() =~= s.take(0));
    while i < t.len()
        invariant
            i <= t@.len(),
            s == t.deep_view(),
            r.deep_view() == s.take(i as int),
        decreases t@.len() - i,
    {
        let ghost before = r.deep_view();
        r.push((t[i].0.clone(), t[i].1.clone()));
        assert(r.deep_view() =~= before.push(s[i as int]));
        assert(s.take(i as int + 1) =~= s.take(i as int).push(s[i as int]));
        i += 1;
    }
    assert(s.take(t@.len() as int) =~= s);
    r
}

impl Value {
    pub fn dup(&self) -> (r: Value)
        ensures r@ == self@,
    {
        Value {
            headers: clone_tags(&self.headers),
            data: match &self.data {
                Some(d) => Some(d.clone()),
                None => None,
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Birth
// ---------------------------------------------------------------------------

/// The dispatch instant of a new task: `resonate:delay` if present, never
/// before `now`.
pub open spec fn first_dispatch(tags: ATags, now: nat) -> nat {
    match crate::tags::tags_get(tags, "resonate:delay"@) {
        Some(d) => if crate::ident::spec_parse_nat(d) > now { crate::ident::spec_parse_nat(d) } else { now },
        None => now,
    }
}

/// `createPromise`: the object `promise.create` writes for a fresh id.
pub open spec fn spec_create(req: APromiseCreateReq, now: nat) -> APromise {
    let runnable = crate::tags::otype(req.tags) == OType::Runnable;
    if req.timeout_at > now {
        APromise {
            id: req.id,
            state: PromiseState::Pending,
            tags: req.tags,
            param: req.param,
            value: AValue::empty(),
            timeout_at: req.timeout_at,
            created_at: now as u64,
            settled_at: None,
            callbacks: Seq::empty(),
            listeners: Seq::empty(),
            task: if runnable {
                Some(ATask {
                    state: TaskState::Pending,
                    version: 0,
                    ttl: None,
                    pid: None,
                    lease_timeout_at: None,
                    retry_timeout_at: Some(first_dispatch(req.tags, now) as u64),
                    resumes: Seq::empty(),
                })
            } else {
                None
            },
        }
    } else {
        APromise {
            id: req.id,
            state: if crate::tags::is_timer(req.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            tags: req.tags,
            param: req.param,
            value: AValue::empty(),
            timeout_at: req.timeout_at,
            created_at: req.timeout_at,
            settled_at: Some(req.timeout_at),
            callbacks: Seq::empty(),
            listeners: Seq::empty(),
            task: if runnable { Some(fulfilled_task()) } else { None },
        }
    }
}

/// A task born fulfilled: version 0, everything cleared.
pub open spec fn fulfilled_task() -> ATask {
    ATask {
        state: TaskState::Fulfilled,
        version: 0,
        ttl: None,
        pid: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Seq::empty(),
    }
}

/// The object `task.create` writes for a fresh id whose deadline is ahead:
/// born pending and acquired at version 1.
pub open spec fn spec_create_acquired(req: APromiseCreateReq, pid: Seq<char>, ttl: nat, now: nat) -> APromise {
    APromise {
        id: req.id,
        state: PromiseState::Pending,
        tags: req.tags,
        param: req.param,
        value: AValue::empty(),
        timeout_at: req.timeout_at,
        created_at: now as u64,
        settled_at: None,
        callbacks: Seq::empty(),
        listeners: Seq::empty(),
        task: Some(ATask {
            state: TaskState::Acquired,
            version: 1,
            ttl: Some(ttl as u64),
            pid: Some(pid),
            lease_timeout_at: Some((now + ttl) as u64),
            retry_timeout_at: None,
            resumes: Seq::empty(),
        }),
    }
}

fn empty_task_fulfilled() -> (t: Task)
    ensures t@ == fulfilled_task(),
{
    let t = Task {
        state: TaskState::Fulfilled,
        version: 0,
        ttl: None,
        pid: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Vec::new(),
    };
    assert(t.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
    t
}

/// `createPromise`, executable.
pub fn create_promise(req: &PromiseCreateReq, now: u64) -> (p: Promise)
    ensures p@ == spec_create(req@, now as nat),
{
    let runnable = crate::tags::exec_otype(&req.tags) == OType::Runnable;
    let mut p = Promise {
        id: req.id.clone(),
        state: PromiseState::Pending,
        tags: clone_tags(&req.tags),
        param: req.param.dup(),
        value: Value::empty(),
        timeout_at: req.timeout_at,
        created_at: now as u64,
        settled_at: None,
        callbacks: Vec::new(),
        listeners: Vec::new(),
        task: None,
    };
    assert(p.callbacks.deep_view() =~= Seq::<Seq<char>>::empty());
    assert(p.listeners.deep_view() =~= Seq::<Seq<char>>::empty());
    if req.timeout_at > now {
        if runnable {
            let due = match crate::tags::tag_find(&req.tags, "resonate:delay") {
                Some(i) => {
                    let d = crate::ident::parse_nat(&req.tags[i].1);
                    if d > now { d } else { now }
                }
                None => now,
            };
            let t = Task {
                state: TaskState::Pending,
                version: 0,
                ttl: None,
                pid: None,
                lease_timeout_at: None,
                retry_timeout_at: Some(due),
                resumes: Vec::new(),
            };
            assert(t.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
            p.task = Some(t);
        }
    } else {
        p.state = if crate::tags::exec_is_timer(&req.tags) { PromiseState::Resolved } else { PromiseState::RejectedTimedout };
        p.created_at = req.timeout_at;
        p.settled_at = Some(req.timeout_at);
        if runnable {
            p.task = Some(empty_task_fulfilled());
        }
    }
    p
}

/// `task.create`'s live path, executable.
pub fn create_promise_acquired(req: &PromiseCreateReq, pid: &String, ttl: u64, now: u64) -> (p: Promise)
    requires req.timeout_at <= MAX_TIME, now <= MAX_TIME, ttl <= MAX_TIME,
    ensures p@ == spec_create_acquired(req@, pid@, ttl as nat, now as nat),
{
    let t = Task {
        state: TaskState::Acquired,
        version: 1,
        ttl: Some(ttl),
        pid: Some(pid.clone()),
        lease_timeout_at: Some(now + ttl),
        retry_timeout_at: None,
        resumes: Vec::new(),
    };
    assert(t.resumes.deep_view() =~= Seq::<Seq<char>>::empty());
    let p = Promise {
        id: req.id.clone(),
        state: PromiseState::Pending,
        tags: clone_tags(&req.tags),
        param: req.param.dup(),
        value: Value::empty(),
        timeout_at: req.timeout_at,
        created_at: now as u64,
        settled_at: None,
        callbacks: Vec::new(),
        listeners: Vec::new(),
        task: Some(t),
    };
    assert(p.callbacks.deep_view() =~= Seq::<Seq<char>>::empty());
    assert(p.listeners.deep_view() =~= Seq::<Seq<char>>::empty());
    p
}

} // verus!
