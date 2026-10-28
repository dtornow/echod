//! Abstract state, writer effects, projection, and effect commit.
//!
//! Handlers read one immutable `State` and emit an ordered `Vec<Effect>`.
//! Consequently a handler cannot observe its own writes, matching Lean's
//! reader/writer monad. `apply_all` is the transaction commit.

use vstd::contrib::{make_spec_type, self_view};
use vstd::prelude::*;
use crate::types::*;

verus! {

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct PromiseObject {
    pub state: PromiseState,
    pub param: Value,
    pub value: Value,
    pub tags: Tags,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Vec<Ident>,
    pub listeners: Vec<Text>,
}

#[cfg(verus_keep_ghost)]
pub type APromiseObject = PromiseObjectSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct TaskObject {
    pub state: TaskState,
    pub version: u64,
    pub ttl: Option<u64>,
    pub pid: Option<Text>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Vec<Ident>,
}

#[cfg(verus_keep_ghost)]
pub type ATaskObject = TaskObjectSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Object {
    pub id: Ident,
    pub promise: PromiseObject,
    pub task: Option<TaskObject>,
}

#[cfg(verus_keep_ghost)]
pub type AObject = ObjectSpec;

#[self_view]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum MessageKind {
    Execute,
    Unblock,
}

/// Executable tagged representation of Lean's `Message` sum.
#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Message {
    pub kind: MessageKind,
    pub task_id: Option<Ident>,
    pub version: u64,
    pub promise: Option<PromiseRecord>,
}

#[cfg(verus_keep_ghost)]
pub type AMessage = MessageSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct OutboxEntry {
    pub address: Text,
    pub message: Message,
}

#[cfg(verus_keep_ghost)]
pub type AOutboxEntry = OutboxEntrySpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct State {
    pub objects: Vec<Object>,
    pub schedules: Vec<Schedule>,
    pub outbox: Vec<OutboxEntry>,
}

#[cfg(verus_keep_ghost)]
pub type AState = StateSpec;

#[derive(Clone, Copy)]
pub struct Config {
    pub retry_timeout: u64,
}

impl Config {
    pub fn lean_default() -> Config {
        Config { retry_timeout: 5000 }
    }

    pub fn bounded(&self) -> bool {
        self.retry_timeout <= MAX_TIME
    }
}

pub enum Effect {
    SetPromise(Ident, PromiseObject),
    SetTask(Ident, TaskObject),
    SetSchedule(Schedule),
    DeleteSchedule(Ident),
    SetMessage(Text, Message),
}

#[cfg(verus_keep_ghost)]
pub enum AEffect {
    SetPromise(AIdent, APromiseObject),
    SetTask(AIdent, ATaskObject),
    SetSchedule(ASchedule),
    DeleteSchedule(AIdent),
    SetMessage(AText, AMessage),
}

#[cfg(verus_keep_ghost)]
impl DeepView for Effect {
    type V = AEffect;

    open spec fn deep_view(&self) -> AEffect {
        match self {
            Effect::SetPromise(id, p) => AEffect::SetPromise(id.deep_view(), p.deep_view()),
            Effect::SetTask(id, t) => AEffect::SetTask(id.deep_view(), t.deep_view()),
            Effect::SetSchedule(s) => AEffect::SetSchedule(s.deep_view()),
            Effect::DeleteSchedule(id) => AEffect::DeleteSchedule(id.deep_view()),
            Effect::SetMessage(address, message) =>
                AEffect::SetMessage(address.deep_view(), message.deep_view()),
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Effect {
    type V = AEffect;
    open spec fn view(&self) -> AEffect { self.deep_view() }
}

pub struct Transition<R> {
    pub response: R,
    pub effects: Vec<Effect>,
}

pub struct ReadResult {
    pub object: Option<Object>,
    pub effects: Vec<Effect>,
}

pub open spec fn spec_add_callback(
    promise: APromiseObject, id: AIdent,
) -> APromiseObject {
    if promise.callbacks.contains(id) {
        promise
    } else {
        APromiseObject { callbacks: promise.callbacks.push(id), ..promise }
    }
}

pub open spec fn spec_add_listener(
    promise: APromiseObject, address: AText,
) -> APromiseObject {
    if promise.listeners.contains(address) {
        promise
    } else {
        APromiseObject {
            listeners: promise.listeners.push(address),
            ..promise
        }
    }
}

impl State {
    pub fn new() -> State {
        State { objects: Vec::new(), schedules: Vec::new(), outbox: Vec::new() }
    }

    pub fn find_object(&self, id: &Ident) -> (r: Option<usize>)
        ensures match r {
            Some(i) => i < self.objects@.len()
                && spec_find_object(self.objects.deep_view(), id@)
                    == Some(self.objects[i as int]@),
            None => spec_find_object(self.objects.deep_view(), id@) is None,
        },
    {
        let mut i: usize = 0;
        while i < self.objects.len()
            invariant
                i <= self.objects@.len(),
                spec_find_object(self.objects.deep_view(), id@)
                    == spec_find_object_at(self.objects.deep_view(), id@, i as nat),
            decreases self.objects@.len() - i,
        {
            if ident_eq(&self.objects[i].id, id) {
                assert(spec_find_object_at(
                    self.objects.deep_view(), id@, i as nat,
                ) == Some(self.objects[i as int]@));
                return Some(i);
            }
            assert(spec_find_object_at(
                self.objects.deep_view(), id@, i as nat,
            ) == spec_find_object_at(
                self.objects.deep_view(), id@, i as nat + 1,
            ));
            i += 1;
        }
        assert(spec_find_object_at(
            self.objects.deep_view(), id@, i as nat,
        ) is None);
        None
    }

    pub fn find_schedule(&self, id: &Ident) -> (r: Option<usize>)
        ensures match r {
            Some(i) => i < self.schedules@.len()
                && spec_find_schedule(self.schedules.deep_view(), id@)
                    == Some(self.schedules[i as int]@),
            None => spec_find_schedule(self.schedules.deep_view(), id@) is None,
        },
    {
        let mut i: usize = 0;
        while i < self.schedules.len()
            invariant
                i <= self.schedules@.len(),
                spec_find_schedule(self.schedules.deep_view(), id@)
                    == spec_find_schedule_at(
                        self.schedules.deep_view(), id@, i as nat,
                    ),
            decreases self.schedules@.len() - i,
        {
            if ident_eq(&self.schedules[i].id, id) {
                assert(spec_find_schedule_at(
                    self.schedules.deep_view(), id@, i as nat,
                ) == Some(self.schedules[i as int]@));
                return Some(i);
            }
            assert(spec_find_schedule_at(
                self.schedules.deep_view(), id@, i as nat,
            ) == spec_find_schedule_at(
                self.schedules.deep_view(), id@, i as nat + 1,
            ));
            i += 1;
        }
        assert(spec_find_schedule_at(
            self.schedules.deep_view(), id@, i as nat,
        ) is None);
        None
    }
}

impl PromiseObject {
    pub fn dup(&self) -> (r: PromiseObject)
        ensures r@ == self@,
    {
        let mut callbacks = Vec::new();
        let mut i: usize = 0;
        while i < self.callbacks.len()
            invariant
                i <= self.callbacks@.len(),
                callbacks.deep_view() == self.callbacks.deep_view().take(i as int),
            decreases self.callbacks@.len() - i,
        {
            let ghost before = callbacks.deep_view();
            let next = self.callbacks[i].dup();
            callbacks.push(next);
            assert(callbacks.deep_view()
                =~= before.push(self.callbacks.deep_view()[i as int]));
            assert(self.callbacks.deep_view().take(i as int + 1)
                =~= self.callbacks.deep_view().take(i as int)
                    .push(self.callbacks.deep_view()[i as int]));
            i += 1;
        }
        assert(self.callbacks.deep_view().take(self.callbacks@.len() as int)
            =~= self.callbacks.deep_view());
        let mut listeners = Vec::new();
        i = 0;
        while i < self.listeners.len()
            invariant
                i <= self.listeners@.len(),
                listeners.deep_view() == self.listeners.deep_view().take(i as int),
            decreases self.listeners@.len() - i,
        {
            let ghost before = listeners.deep_view();
            let next = self.listeners[i].dup();
            listeners.push(next);
            assert(listeners.deep_view()
                =~= before.push(self.listeners.deep_view()[i as int]));
            assert(self.listeners.deep_view().take(i as int + 1)
                =~= self.listeners.deep_view().take(i as int)
                    .push(self.listeners.deep_view()[i as int]));
            i += 1;
        }
        assert(self.listeners.deep_view().take(self.listeners@.len() as int)
            =~= self.listeners.deep_view());
        PromiseObject {
            state: self.state, param: self.param.dup(), value: self.value.dup(),
            tags: dup_tags(&self.tags), timeout_at: self.timeout_at,
            created_at: self.created_at, settled_at: self.settled_at,
            callbacks, listeners,
        }
    }

    pub fn to_record(&self, id: &Ident) -> (r: PromiseRecord)
        ensures r@ == (APromiseRecord {
            id: id@,
            state: self@.state,
            param: self@.param,
            value: self@.value,
            tags: self@.tags,
            timeout_at: self@.timeout_at,
            created_at: self@.created_at,
            settled_at: self@.settled_at,
        }),
    {
        PromiseRecord {
            id: id.dup(), state: self.state, param: self.param.dup(),
            value: self.value.dup(), tags: dup_tags(&self.tags),
            timeout_at: self.timeout_at, created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }

    pub fn is_timer(&self) -> (r: bool)
        ensures r == spec_tags_is_timer(self@.tags),
    {
        tags_is_timer(&self.tags)
    }
    pub fn otype(&self) -> (r: OType)
        ensures r == spec_otype(self@.tags),
    {
        tags_otype(&self.tags)
    }

    pub fn project(mut self, now: u64) -> (r: PromiseObject)
        ensures r@ == spec_project_promise(self@, now),
    {
        let ghost original = self@;
        if self.state == PromiseState::Pending && self.timeout_at <= now {
            self.state = if self.is_timer() {
                PromiseState::Resolved
            } else {
                PromiseState::RejectedTimedout
            };
            self.settled_at = Some(self.timeout_at);
        }
        assert(self@.param == original.param);
        assert(self@.value == original.value);
        assert(self@.tags == original.tags);
        assert(self@.callbacks == original.callbacks);
        assert(self@.listeners == original.listeners);
        assert(self@.state == spec_project_promise(original, now).state);
        assert(self@.timeout_at == spec_project_promise(original, now).timeout_at);
        assert(self@.created_at == spec_project_promise(original, now).created_at);
        assert(self@.settled_at == spec_project_promise(original, now).settled_at);
        assert(self@.param == spec_project_promise(original, now).param);
        assert(self@.value == spec_project_promise(original, now).value);
        assert(self@.tags == spec_project_promise(original, now).tags);
        assert(self@.callbacks == spec_project_promise(original, now).callbacks);
        assert(self@.listeners == spec_project_promise(original, now).listeners);
        assert(self@ == spec_project_promise(original, now));
        self
    }

    pub fn add_callback(mut self, id: &Ident) -> (r: PromiseObject)
        ensures r@ == spec_add_callback(self@, id@),
    {
        let ghost original = self@;
        let mut found = false;
        let mut i: usize = 0;
        while i < self.callbacks.len()
            invariant
                self@ == original,
                i <= self.callbacks@.len(),
                found == original.callbacks.take(i as int).contains(id@),
            decreases self.callbacks@.len() - i,
        {
            if ident_eq(&self.callbacks[i], id) { found = true; }
            proof {
                vstd::seq_lib::lemma_seq_contains_after_push(
                    original.callbacks.take(i as int),
                    original.callbacks[i as int],
                    id@,
                );
            }
            assert(original.callbacks.take(i as int + 1)
                =~= original.callbacks.take(i as int)
                    .push(original.callbacks[i as int]));
            i += 1;
        }
        assert(original.callbacks.take(original.callbacks.len() as int)
            =~= original.callbacks);
        if !found {
            let next = id.dup();
            self.callbacks.push(next);
            assert(self@.callbacks =~= original.callbacks.push(id@));
        }
        assert(self@ == spec_add_callback(original, id@));
        self
    }

    pub fn add_listener(mut self, address: &Text) -> (r: PromiseObject)
        ensures r@ == spec_add_listener(self@, address@),
    {
        let ghost original = self@;
        let mut found = false;
        let mut i: usize = 0;
        while i < self.listeners.len()
            invariant
                self@ == original,
                i <= self.listeners@.len(),
                found == original.listeners.take(i as int).contains(address@),
            decreases self.listeners@.len() - i,
        {
            if text_eq(&self.listeners[i], address) { found = true; }
            proof {
                vstd::seq_lib::lemma_seq_contains_after_push(
                    original.listeners.take(i as int),
                    original.listeners[i as int],
                    address@,
                );
            }
            assert(original.listeners.take(i as int + 1)
                =~= original.listeners.take(i as int)
                    .push(original.listeners[i as int]));
            i += 1;
        }
        assert(original.listeners.take(original.listeners.len() as int)
            =~= original.listeners);
        if !found {
            let next = address.dup();
            self.listeners.push(next);
            assert(self@.listeners =~= original.listeners.push(address@));
        }
        assert(self@ == spec_add_listener(original, address@));
        self
    }

    pub fn remove_callback(mut self, id: &Ident) -> (r: PromiseObject)
        ensures r@ == (APromiseObject {
            callbacks: spec_without_ident(self@.callbacks, id@),
            ..self@
        }),
    {
        let ghost original = self@;
        let mut callbacks = Vec::new();
        let mut i: usize = 0;
        while i < self.callbacks.len()
            invariant
                self@ == original,
                i <= self.callbacks@.len(),
                callbacks.deep_view()
                    == spec_without_ident(original.callbacks.take(i as int), id@),
            decreases self.callbacks@.len() - i,
        {
            if !ident_eq(&self.callbacks[i], id) {
                callbacks.push(self.callbacks[i].dup());
            }
            proof {
                lemma_without_ident_push(
                    original.callbacks.take(i as int), original.callbacks[i as int], id@,
                );
            }
            assert(original.callbacks.take(i as int + 1)
                =~= original.callbacks.take(i as int).push(original.callbacks[i as int]));
            assert(spec_without_ident(original.callbacks.take(i as int + 1), id@)
                =~= if original.callbacks[i as int] == id@ {
                    spec_without_ident(original.callbacks.take(i as int), id@)
                } else {
                    spec_without_ident(original.callbacks.take(i as int), id@)
                        .push(original.callbacks[i as int])
                });
            i += 1;
        }
        assert(original.callbacks.take(original.callbacks.len() as int)
            =~= original.callbacks);
        self.callbacks = callbacks;
        self
    }

    pub fn remove_listener(mut self, address: &Text) -> (r: PromiseObject)
        ensures r@ == (APromiseObject {
            listeners: spec_without_text(self@.listeners, address@),
            ..self@
        }),
    {
        let ghost original = self@;
        let mut listeners = Vec::new();
        let mut i: usize = 0;
        while i < self.listeners.len()
            invariant
                self@ == original,
                i <= self.listeners@.len(),
                listeners.deep_view()
                    == spec_without_text(original.listeners.take(i as int), address@),
            decreases self.listeners@.len() - i,
        {
            if !text_eq(&self.listeners[i], address) {
                listeners.push(self.listeners[i].dup());
            }
            proof {
                lemma_without_text_push(
                    original.listeners.take(i as int), original.listeners[i as int], address@,
                );
            }
            assert(original.listeners.take(i as int + 1)
                =~= original.listeners.take(i as int).push(original.listeners[i as int]));
            assert(spec_without_text(original.listeners.take(i as int + 1), address@)
                =~= if original.listeners[i as int] == address@ {
                    spec_without_text(original.listeners.take(i as int), address@)
                } else {
                    spec_without_text(original.listeners.take(i as int), address@)
                        .push(original.listeners[i as int])
                });
            i += 1;
        }
        assert(original.listeners.take(original.listeners.len() as int)
            =~= original.listeners);
        self.listeners = listeners;
        self
    }
}

impl TaskObject {
    pub fn dup(&self) -> (r: TaskObject)
        ensures r.deep_view() == self.deep_view(),
    {
        let mut resumes = Vec::new();
        let mut i: usize = 0;
        while i < self.resumes.len()
            invariant
                i <= self.resumes@.len(),
                resumes.deep_view() == self.resumes.deep_view().take(i as int),
            decreases self.resumes@.len() - i,
        {
            let ghost before = resumes.deep_view();
            let next = self.resumes[i].dup();
            resumes.push(next);
            assert(resumes.deep_view()
                =~= before.push(self.resumes.deep_view()[i as int]));
            assert(self.resumes.deep_view().take(i as int + 1)
                =~= self.resumes.deep_view().take(i as int)
                    .push(self.resumes.deep_view()[i as int]));
            i += 1;
        }
        assert(self.resumes.deep_view().take(self.resumes@.len() as int)
            =~= self.resumes.deep_view());
        TaskObject {
            state: self.state, version: self.version, ttl: self.ttl,
            pid: match &self.pid { Some(x) => Some(x.dup()), None => None },
            lease_timeout_at: self.lease_timeout_at,
            retry_timeout_at: self.retry_timeout_at, resumes,
        }
    }

    pub fn to_record(&self, id: &Ident) -> (r: TaskRecord)
        ensures r@ == crate::task_spec::spec_task_record(self@, id@),
    {
        TaskRecord {
            id: id.dup(), state: self.state, version: self.version,
            resumes: self.resumes.len() as u64, ttl: self.ttl,
            pid: match &self.pid { Some(x) => Some(x.dup()), None => None },
        }
    }

    pub fn fulfill(mut self) -> (r: TaskObject)
        ensures r.deep_view() == spec_fulfill_task(self.deep_view()),
    {
        let ghost original = self.deep_view();
        self.state = TaskState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.lease_timeout_at = None;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        assert(self.deep_view().state == spec_fulfill_task(original).state);
        assert(self.deep_view().version == spec_fulfill_task(original).version);
        assert(self.deep_view().ttl == spec_fulfill_task(original).ttl);
        assert(self.deep_view().pid == spec_fulfill_task(original).pid);
        assert(self.deep_view().lease_timeout_at
            == spec_fulfill_task(original).lease_timeout_at);
        assert(self.deep_view().retry_timeout_at
            == spec_fulfill_task(original).retry_timeout_at);
        assert(self.deep_view().resumes == spec_fulfill_task(original).resumes);
        assert(self.deep_view() == spec_fulfill_task(original));
        self
    }

    pub fn view(self, promise: &PromiseObject) -> (r: TaskObject)
        ensures r.deep_view() == if promise@.state != PromiseState::Pending
            && self.deep_view().state != TaskState::Fulfilled {
            spec_fulfill_task(self.deep_view())
        } else {
            self.deep_view()
        },
    {
        if promise.state != PromiseState::Pending && self.state != TaskState::Fulfilled {
            self.fulfill()
        } else {
            self
        }
    }
}

impl Object {
    pub fn dup(&self) -> (r: Object)
        ensures r@ == self@,
    {
        Object {
            id: self.id.dup(), promise: self.promise.dup(),
            task: match &self.task { Some(t) => Some(t.dup()), None => None },
        }
    }

    pub fn project(mut self, now: u64) -> (r: Object)
        ensures r@ == spec_project_object(self@, now),
    {
        self.promise = self.promise.project(now);
        self.task = match self.task {
            Some(t) => Some(t.view(&self.promise)),
            None => None,
        };
        self
    }
}

// The generated `…Spec` twins are the proof vocabulary. These definitions
// encode the central projection rules independently of executable mutation.
#[cfg(verus_keep_ghost)]
impl APromiseObject {
    pub open spec fn projected_state(self, now: nat) -> PromiseState {
        if self.state == PromiseState::Pending && self.timeout_at as nat <= now {
            if spec_tags_is_timer(self.tags) {
                PromiseState::Resolved
            } else {
                PromiseState::RejectedTimedout
            }
        } else {
            self.state
        }
    }
}

/// Ghost twin of first-match timer classification.
pub open spec fn spec_tag_key_timer(k: Seq<char>) -> bool {
    k =~= seq!['r','e','s','o','n','a','t','e',':','t','i','m','e','r']
}

pub open spec fn spec_text_true(x: AText) -> bool {
    x.chars =~= seq!['t','r','u','e']
}

pub open spec fn spec_timer_value(tags: ATags) -> Option<AText>
    decreases tags.len(),
{
    if tags.len() == 0 {
        None
    } else if spec_tag_key_timer(tags[0].key.chars) {
        Some(tags[0].value)
    } else {
        spec_timer_value(tags.drop_first())
    }
}

pub open spec fn spec_tags_is_timer(tags: ATags) -> bool {
    spec_is_timer(tags)
}

/// Pure Abstract projection used by executable correctness contracts.
pub open spec fn spec_project_promise(p: APromiseObject, now: u64) -> APromiseObject {
    if p.state == PromiseState::Pending && p.timeout_at <= now {
        APromiseObject {
            state: if spec_tags_is_timer(p.tags) {
                PromiseState::Resolved
            } else {
                PromiseState::RejectedTimedout
            },
            settled_at: Some(p.timeout_at),
            ..p
        }
    } else {
        p
    }
}

pub open spec fn spec_fulfill_task(t: ATaskObject) -> ATaskObject {
    ATaskObject {
        state: TaskState::Fulfilled,
        ttl: None,
        pid: None,
        lease_timeout_at: None,
        retry_timeout_at: None,
        resumes: Seq::empty(),
        ..t
    }
}

pub open spec fn spec_project_object(o: AObject, now: u64) -> AObject {
    let promise = spec_project_promise(o.promise, now);
    let task = match o.task {
        Some(t) => Some(if promise.state != PromiseState::Pending
            && t.state != TaskState::Fulfilled {
            spec_fulfill_task(t)
        } else {
            t
        }),
        None => None,
    };
    AObject { promise, task, ..o }
}

pub open spec fn spec_without_ident(xs: Seq<AIdent>, id: AIdent) -> Seq<AIdent>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if xs.last() == id {
        spec_without_ident(xs.drop_last(), id)
    } else {
        spec_without_ident(xs.drop_last(), id).push(xs.last())
    }
}

pub open spec fn spec_without_text(xs: Seq<AText>, x: AText) -> Seq<AText>
    decreases xs.len(),
{
    if xs.len() == 0 {
        Seq::empty()
    } else if xs.last() == x {
        spec_without_text(xs.drop_last(), x)
    } else {
        spec_without_text(xs.drop_last(), x).push(xs.last())
    }
}

pub proof fn lemma_without_ident_push(xs: Seq<AIdent>, x: AIdent, id: AIdent)
    ensures spec_without_ident(xs.push(x), id)
        == if x == id {
            spec_without_ident(xs, id)
        } else {
            spec_without_ident(xs, id).push(x)
        },
    decreases xs.len(),
{
    assert(xs.push(x).drop_last() =~= xs);
    assert(xs.push(x).last() == x);
}

pub proof fn lemma_without_text_push(xs: Seq<AText>, x: AText, removed: AText)
    ensures spec_without_text(xs.push(x), removed)
        == if x == removed {
            spec_without_text(xs, removed)
        } else {
            spec_without_text(xs, removed).push(x)
        },
    decreases xs.len(),
{
    assert(xs.push(x).drop_last() =~= xs);
    assert(xs.push(x).last() == x);
}

// Pure ghost commit twin. These list functions deliberately use head/tail
// recursion, so proofs see the same stable filters and prepend order as Lean.

#[cfg(verus_keep_ghost)]
pub open spec fn spec_find_object_at(
    rows: Seq<AObject>, id: AIdent, start: nat,
) -> Option<AObject>
    decreases rows.len() - start,
{
    if start >= rows.len() {
        None
    } else if rows[start as int].id == id {
        Some(rows[start as int])
    } else {
        spec_find_object_at(rows, id, start + 1)
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_find_object(rows: Seq<AObject>, id: AIdent) -> Option<AObject> {
    spec_find_object_at(rows, id, 0)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_find_schedule_at(
    rows: Seq<ASchedule>, id: AIdent, start: nat,
) -> Option<ASchedule>
    decreases rows.len() - start,
{
    if start >= rows.len() {
        None
    } else if rows[start as int].id == id {
        Some(rows[start as int])
    } else {
        spec_find_schedule_at(rows, id, start + 1)
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_find_schedule(
    rows: Seq<ASchedule>, id: AIdent,
) -> Option<ASchedule> {
    spec_find_schedule_at(rows, id, 0)
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_read_object(
    state: AState, id: AIdent, now: u64,
) -> Option<AObject> {
    match spec_find_object(state.objects, id) {
        Some(o) => Some(spec_project_object(o, now)),
        None => None,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_read_effects(
    state: AState, id: AIdent, now: u64, materialize: bool,
) -> Seq<AEffect> {
    match spec_find_object(state.objects, id) {
        None => Seq::empty(),
        Some(old) => {
            let projected = spec_project_object(old, now);
            let promise = if materialize && projected.promise.state != old.promise.state {
                seq![AEffect::SetPromise(id, projected.promise)]
            } else {
                Seq::empty()
            };
            let task = if materialize {
                match (old.task, projected.task) {
                    (Some(a), Some(b)) if a.state != b.state =>
                        seq![AEffect::SetTask(id, b)],
                    _ => Seq::empty(),
                }
            } else {
                Seq::empty()
            };
            promise + task
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_read_task_object(
    state: AState, id: AIdent, now: u64,
) -> Option<AObject> {
    match spec_find_object(state.objects, id) {
        Some(o) if o.task is Some => spec_read_object(state, id, now),
        _ => None,
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_read_task_effects(
    state: AState, id: AIdent, now: u64, materialize: bool,
) -> Seq<AEffect> {
    match spec_find_object(state.objects, id) {
        Some(o) if o.task is Some => spec_read_effects(state, id, now, materialize),
        _ => Seq::empty(),
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_without_object(rows: Seq<AObject>, id: AIdent) -> Seq<AObject>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else if rows[0].id == id {
        spec_without_object(rows.drop_first(), id)
    } else {
        seq![rows[0]] + spec_without_object(rows.drop_first(), id)
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_set_task(rows: Seq<AObject>, id: AIdent, task: ATaskObject) -> Seq<AObject>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        let head = if rows[0].id == id {
            AObject { task: Some(task), ..rows[0] }
        } else {
            rows[0]
        };
        seq![head] + spec_set_task(rows.drop_first(), id, task)
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_without_schedule(rows: Seq<ASchedule>, id: AIdent) -> Seq<ASchedule>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else if rows[0].id == id {
        spec_without_schedule(rows.drop_first(), id)
    } else {
        seq![rows[0]] + spec_without_schedule(rows.drop_first(), id)
    }
}

#[cfg(verus_keep_ghost)]
pub enum AOutboxKey {
    Execute(AIdent),
    Notify(AIdent, AText),
    Invalid,
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_outbox_key(entry: AOutboxEntry) -> AOutboxKey {
    match entry.message.kind {
        MessageKind::Execute => match entry.message.task_id {
            Some(id) => AOutboxKey::Execute(id),
            None => AOutboxKey::Invalid,
        },
        MessageKind::Unblock => match entry.message.promise {
            Some(p) => AOutboxKey::Notify(p.id, entry.address),
            None => AOutboxKey::Invalid,
        },
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_without_outbox(
    rows: Seq<AOutboxEntry>, key: AOutboxKey,
) -> Seq<AOutboxEntry>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else if spec_outbox_key(rows[0]) == key {
        spec_without_outbox(rows.drop_first(), key)
    } else {
        seq![rows[0]] + spec_without_outbox(rows.drop_first(), key)
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_effect(state: AState, effect: AEffect) -> AState {
    match effect {
        AEffect::SetPromise(id, promise) => {
            let task = match spec_find_object(state.objects, id) {
                Some(old) => old.task,
                None => None,
            };
            AState {
                objects: seq![AObject { id, promise, task }]
                    + spec_without_object(state.objects, id),
                ..state
            }
        }
        AEffect::SetTask(id, task) =>
            AState { objects: spec_set_task(state.objects, id, task), ..state },
        AEffect::SetSchedule(schedule) =>
            AState {
                schedules: seq![schedule]
                    + spec_without_schedule(state.schedules, schedule.id),
                ..state
            },
        AEffect::DeleteSchedule(id) =>
            AState { schedules: spec_without_schedule(state.schedules, id), ..state },
        AEffect::SetMessage(address, message) => {
            let entry = AOutboxEntry { address, message };
            AState {
                outbox: seq![entry]
                    + spec_without_outbox(state.outbox, spec_outbox_key(entry)),
                ..state
            }
        }
    }
}

#[cfg(verus_keep_ghost)]
pub open spec fn spec_apply_all(state: AState, effects: Seq<AEffect>) -> AState
    decreases effects.len(),
{
    if effects.len() == 0 {
        state
    } else {
        spec_apply_all(spec_apply_effect(state, effects[0]), effects.drop_first())
    }
}

/// Append all effects in `tail` after `head`, retaining Lean list order.
pub fn append_effects(
    mut head: Vec<Effect>, mut tail: Vec<Effect>,
) -> (r: Vec<Effect>)
    ensures r.deep_view() == head.deep_view() + tail.deep_view(),
{
    let ghost original_head = head.deep_view();
    let ghost original_tail = tail.deep_view();
    while tail.len() > 0
        invariant
            head.deep_view() + tail.deep_view() == original_head + original_tail,
        decreases tail@.len(),
    {
        let e = tail.remove(0);
        head.push(e);
    }
    assert(tail.deep_view() =~= Seq::<AEffect>::empty());
    head
}

pub fn push_effect(out: &mut Vec<Effect>, effect: Effect)
    ensures
        final(out).deep_view()
            == old(out).deep_view().push(effect.deep_view()),
{
    let ghost before = out.deep_view();
    let ghost added = effect.deep_view();
    out.push(effect);
    assert(final(out).deep_view() =~= before.push(added));
}

pub fn read_object(
    state: &State, id: &Ident, now: u64, materialize: bool,
) -> (r: ReadResult)
    ensures
        r.object.deep_view() == spec_read_object(state@, id@, now),
        r.effects.deep_view() == spec_read_effects(state@, id@, now, materialize),
{
    match state.find_object(id) {
        None => ReadResult { object: None, effects: Vec::new() },
        Some(i) => {
            let old = &state.objects[i];
            let projected = old.dup().project(now);
            let mut effects = Vec::new();
            if materialize {
                if projected.promise.state != old.promise.state {
                    effects.push(Effect::SetPromise(id.dup(), projected.promise.dup()));
                }
                match (&old.task, &projected.task) {
                    (Some(a), Some(b)) => {
                        if a.state != b.state {
                            effects.push(Effect::SetTask(id.dup(), b.dup()));
                        }
                    }
                    _ => {}
                }
            }
            ReadResult { object: Some(projected), effects }
        }
    }
}

pub fn read_task_object(
    state: &State, id: &Ident, now: u64, materialize: bool,
) -> (r: ReadResult)
    ensures
        r.object.deep_view() == spec_read_task_object(state@, id@, now),
        r.effects.deep_view() == spec_read_task_effects(state@, id@, now, materialize),
{
    match state.find_object(id) {
        None => ReadResult { object: None, effects: Vec::new() },
        Some(i) => match &state.objects[i].task {
            None => ReadResult { object: None, effects: Vec::new() },
            Some(_) => read_object(state, id, now, materialize),
        },
    }
}

pub open spec fn spec_set_settled_effects(
    object: AObject, promise: APromiseObject,
) -> Seq<AEffect> {
    let first = seq![AEffect::SetPromise(object.id, promise)];
    if promise.state != PromiseState::Pending {
        match object.task {
            Some(task) if task.state != TaskState::Fulfilled =>
                first.push(AEffect::SetTask(
                    object.id,
                    spec_fulfill_task(task),
                )),
            _ => first,
        }
    } else {
        first
    }
}

pub fn set_settled_effects(
    o: &Object, p: &PromiseObject,
) -> (r: Vec<Effect>)
    ensures r.deep_view() == spec_set_settled_effects(o@, p@),
{
    let mut out = Vec::new();
    out.push(Effect::SetPromise(o.id.dup(), p.dup()));
    if p.state != PromiseState::Pending {
        match &o.task {
            Some(t) => {
                if t.state != TaskState::Fulfilled {
                    out.push(Effect::SetTask(o.id.dup(), t.dup().fulfill()));
                }
            }
            None => {}
        }
    }
    out
}

pub fn checked_add(a: u64, b: u64) -> (r: u64)
    ensures r == if b <= u64::MAX - a { (a + b) as u64 } else { u64::MAX },
{
    if b <= u64::MAX - a { a + b } else { u64::MAX }
}

pub struct Created {
    pub object: Object,
    pub effects: Vec<Effect>,
}

pub open spec fn spec_created_promise(
    req: APromiseCreateReq, now: u64,
) -> APromiseObject {
    if req.timeout_at > now {
        APromiseObject {
            state: PromiseState::Pending,
            param: req.param,
            value: AValue { headers: Seq::empty(), data: None },
            tags: req.tags,
            timeout_at: req.timeout_at,
            created_at: now,
            settled_at: None,
            callbacks: Seq::empty(),
            listeners: Seq::empty(),
        }
    } else {
        APromiseObject {
            state: if spec_is_timer(req.tags) {
                PromiseState::Resolved
            } else {
                PromiseState::RejectedTimedout
            },
            param: req.param,
            value: AValue { headers: Seq::empty(), data: None },
            tags: req.tags,
            timeout_at: req.timeout_at,
            created_at: req.timeout_at,
            settled_at: Some(req.timeout_at),
            callbacks: Seq::empty(),
            listeners: Seq::empty(),
        }
    }
}

pub open spec fn spec_created_task(
    promise: APromiseObject, now: u64,
) -> Option<ATaskObject> {
    if spec_otype(promise.tags) != OType::Runnable {
        None
    } else if promise.state == PromiseState::Pending {
        let due = match spec_tag_value(promise.tags, 4) {
            Some(d) => {
                let parsed = spec_parse_nat_bounded(d);
                if parsed > now { parsed } else { now }
            }
            None => now,
        };
        Some(ATaskObject {
            state: TaskState::Pending,
            version: 0,
            ttl: None,
            pid: None,
            lease_timeout_at: None,
            retry_timeout_at: Some(due),
            resumes: Seq::empty(),
        })
    } else {
        Some(ATaskObject {
            state: TaskState::Fulfilled,
            version: 0,
            ttl: None,
            pid: None,
            lease_timeout_at: None,
            retry_timeout_at: None,
            resumes: Seq::empty(),
        })
    }
}

pub open spec fn spec_create_promise_effects(
    req: APromiseCreateReq, now: u64,
) -> Seq<AEffect> {
    let promise = spec_created_promise(req, now);
    let base = seq![AEffect::SetPromise(req.id, promise)];
    match spec_created_task(promise, now) {
        Some(task) => base.push(AEffect::SetTask(req.id, task)),
        None => base,
    }
}

pub fn create_promise(req: PromiseCreateReq, now: u64) -> (r: Created)
    ensures
        r.object@ == (AObject {
            id: req@.id,
            promise: spec_created_promise(req@, now),
            task: spec_created_task(spec_created_promise(req@, now), now),
        }),
        r.effects.deep_view() == spec_create_promise_effects(req@, now),
{
    let ghost request = req@;
    let id = req.id;
    let promise = if req.timeout_at > now {
        PromiseObject {
            state: PromiseState::Pending, param: req.param, value: Value::empty(),
            tags: req.tags, timeout_at: req.timeout_at, created_at: now,
            settled_at: None, callbacks: Vec::new(), listeners: Vec::new(),
        }
    } else {
        let timer = tags_is_timer(&req.tags);
        PromiseObject {
            state: if timer { PromiseState::Resolved } else { PromiseState::RejectedTimedout },
            param: req.param, value: Value::empty(), tags: req.tags,
            timeout_at: req.timeout_at, created_at: req.timeout_at,
            settled_at: Some(req.timeout_at), callbacks: Vec::new(), listeners: Vec::new(),
        }
    };
    assert(promise@.state == spec_created_promise(request, now).state);
    assert(promise@.param == spec_created_promise(request, now).param);
    assert(promise@.value == spec_created_promise(request, now).value);
    assert(promise@.tags == spec_created_promise(request, now).tags);
    assert(promise@.timeout_at == spec_created_promise(request, now).timeout_at);
    assert(promise@.created_at == spec_created_promise(request, now).created_at);
    assert(promise@.settled_at == spec_created_promise(request, now).settled_at);
    assert(promise@.callbacks == spec_created_promise(request, now).callbacks);
    assert(promise@.listeners == spec_created_promise(request, now).listeners);
    assert(promise@ == spec_created_promise(request, now));
    let mut effects = Vec::new();
    effects.push(Effect::SetPromise(id.dup(), promise.dup()));
    let task = if promise.otype() == OType::Runnable {
        let t = if promise.state == PromiseState::Pending {
            let due = match tag_value(&promise.tags, 4) {
                Some(d) => {
                    let parsed = parse_nat_bounded(&d);
                    if parsed > now { parsed } else { now }
                }
                None => now,
            };
            TaskObject {
                state: TaskState::Pending, version: 0, ttl: None, pid: None,
                lease_timeout_at: None, retry_timeout_at: Some(due), resumes: Vec::new(),
            }
        } else {
            TaskObject {
                state: TaskState::Fulfilled, version: 0, ttl: None, pid: None,
                lease_timeout_at: None, retry_timeout_at: None, resumes: Vec::new(),
            }
        };
        effects.push(Effect::SetTask(id.dup(), t.dup()));
        Some(t)
    } else {
        None
    };
    assert(task.deep_view() == spec_created_task(promise@, now));
    assert(effects.deep_view() == spec_create_promise_effects(request, now));
    let r = Created { object: Object { id, promise, task }, effects };
    assert(r.object@.id == request.id);
    assert(r.object@.promise == spec_created_promise(request, now));
    assert(r.object@.task == spec_created_task(spec_created_promise(request, now), now));
    assert(r.object@ == (AObject {
        id: request.id,
        promise: spec_created_promise(request, now),
        task: spec_created_task(spec_created_promise(request, now), now),
    }));
    r
}

fn message_same_key(a: &OutboxEntry, address: &Text, msg: &Message) -> bool {
    if a.message.kind != msg.kind { return false; }
    match msg.kind {
        MessageKind::Execute => match (&a.message.task_id, &msg.task_id) {
            (Some(x), Some(y)) => ident_eq(x, y),
            _ => false,
        },
        MessageKind::Unblock => match (&a.message.promise, &msg.promise) {
            (Some(x), Some(y)) => ident_eq(&x.id, &y.id) && text_eq(&a.address, address),
            _ => false,
        },
    }
}

/// Apply one writer effect. Upserts prepend exactly as Lean's
/// `new :: old.filter`, while task writes map in place.
pub fn apply_effect(mut state: State, effect: Effect) -> State {
    match effect {
        Effect::SetPromise(id, promise) => {
            let task = match state.find_object(&id) {
                Some(i) => {
                    let old = state.objects.remove(i);
                    old.task
                }
                None => None,
            };
            let mut i: usize = 0;
            while i < state.objects.len()
                decreases state.objects@.len() - i,
            {
                if ident_eq(&state.objects[i].id, &id) {
                    state.objects.remove(i);
                } else {
                    i += 1;
                }
            }
            state.objects.insert(0, Object { id, promise, task });
        }
        Effect::SetTask(id, task) => {
            let mut i: usize = 0;
            while i < state.objects.len()
                decreases state.objects@.len() - i,
            {
                if ident_eq(&state.objects[i].id, &id) {
                    state.objects[i].task = Some(task.dup());
                }
                i += 1;
            }
        }
        Effect::SetSchedule(schedule) => {
            let mut i: usize = 0;
            while i < state.schedules.len()
                decreases state.schedules@.len() - i,
            {
                if ident_eq(&state.schedules[i].id, &schedule.id) {
                    state.schedules.remove(i);
                } else {
                    i += 1;
                }
            }
            state.schedules.insert(0, schedule);
        }
        Effect::DeleteSchedule(id) => {
            let mut i: usize = 0;
            while i < state.schedules.len()
                decreases state.schedules@.len() - i,
            {
                if ident_eq(&state.schedules[i].id, &id) {
                    state.schedules.remove(i);
                } else {
                    i += 1;
                }
            }
        }
        Effect::SetMessage(address, message) => {
            let mut i: usize = 0;
            while i < state.outbox.len()
                decreases state.outbox@.len() - i,
            {
                if message_same_key(&state.outbox[i], &address, &message) {
                    state.outbox.remove(i);
                } else {
                    i += 1;
                }
            }
            state.outbox.insert(0, OutboxEntry { address, message });
        }
    }
    state
}

pub fn apply_all(mut state: State, mut effects: Vec<Effect>) -> State {
    while effects.len() > 0
        decreases effects@.len(),
    {
        state = apply_effect(state, effects.remove(0));
    }
    state
}

} // verus!
