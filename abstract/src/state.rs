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

impl State {
    pub fn new() -> State {
        State { objects: Vec::new(), schedules: Vec::new(), outbox: Vec::new() }
    }

    pub fn find_object(&self, id: &Ident) -> (r: Option<usize>)
        ensures match r { Some(i) => i < self.objects@.len(), None => true },
    {
        let mut i: usize = 0;
        while i < self.objects.len()
            invariant i <= self.objects@.len(),
            decreases self.objects@.len() - i,
        {
            if ident_eq(&self.objects[i].id, id) { return Some(i); }
            i += 1;
        }
        None
    }

    pub fn find_schedule(&self, id: &Ident) -> (r: Option<usize>)
        ensures match r { Some(i) => i < self.schedules@.len(), None => true },
    {
        let mut i: usize = 0;
        while i < self.schedules.len()
            invariant i <= self.schedules@.len(),
            decreases self.schedules@.len() - i,
        {
            if ident_eq(&self.schedules[i].id, id) { return Some(i); }
            i += 1;
        }
        None
    }
}

impl PromiseObject {
    pub fn dup(&self) -> PromiseObject {
        let mut callbacks = Vec::new();
        let mut i: usize = 0;
        while i < self.callbacks.len()
            decreases self.callbacks@.len() - i,
        {
            callbacks.push(self.callbacks[i].dup());
            i += 1;
        }
        let mut listeners = Vec::new();
        i = 0;
        while i < self.listeners.len()
            decreases self.listeners@.len() - i,
        {
            listeners.push(self.listeners[i].dup());
            i += 1;
        }
        PromiseObject {
            state: self.state, param: self.param.dup(), value: self.value.dup(),
            tags: dup_tags(&self.tags), timeout_at: self.timeout_at,
            created_at: self.created_at, settled_at: self.settled_at,
            callbacks, listeners,
        }
    }

    pub fn to_record(&self, id: &Ident) -> PromiseRecord {
        PromiseRecord {
            id: id.dup(), state: self.state, param: self.param.dup(),
            value: self.value.dup(), tags: dup_tags(&self.tags),
            timeout_at: self.timeout_at, created_at: self.created_at,
            settled_at: self.settled_at,
        }
    }

    pub fn is_timer(&self) -> bool { tags_is_timer(&self.tags) }
    pub fn otype(&self) -> OType { tags_otype(&self.tags) }

    pub fn project(mut self, now: u64) -> PromiseObject {
        if self.state == PromiseState::Pending && self.timeout_at <= now {
            self.state = if self.is_timer() {
                PromiseState::Resolved
            } else {
                PromiseState::RejectedTimedout
            };
            self.settled_at = Some(self.timeout_at);
        }
        self
    }

    pub fn add_callback(mut self, id: &Ident) -> PromiseObject {
        let mut found = false;
        let mut i: usize = 0;
        while i < self.callbacks.len()
            decreases self.callbacks@.len() - i,
        {
            if ident_eq(&self.callbacks[i], id) { found = true; }
            i += 1;
        }
        if !found { self.callbacks.push(id.dup()); }
        self
    }

    pub fn add_listener(mut self, address: &Text) -> PromiseObject {
        let mut found = false;
        let mut i: usize = 0;
        while i < self.listeners.len()
            decreases self.listeners@.len() - i,
        {
            if text_eq(&self.listeners[i], address) { found = true; }
            i += 1;
        }
        if !found { self.listeners.push(address.dup()); }
        self
    }

    pub fn remove_callback(mut self, id: &Ident) -> PromiseObject {
        let mut i: usize = 0;
        while i < self.callbacks.len()
            decreases self.callbacks@.len() - i,
        {
            if ident_eq(&self.callbacks[i], id) {
                self.callbacks.remove(i);
            } else {
                i += 1;
            }
        }
        self
    }

    pub fn remove_listener(mut self, address: &Text) -> PromiseObject {
        let mut i: usize = 0;
        while i < self.listeners.len()
            decreases self.listeners@.len() - i,
        {
            if text_eq(&self.listeners[i], address) {
                self.listeners.remove(i);
            } else {
                i += 1;
            }
        }
        self
    }
}

impl TaskObject {
    pub fn dup(&self) -> TaskObject {
        let mut resumes = Vec::new();
        let mut i: usize = 0;
        while i < self.resumes.len()
            decreases self.resumes@.len() - i,
        {
            resumes.push(self.resumes[i].dup());
            i += 1;
        }
        TaskObject {
            state: self.state, version: self.version, ttl: self.ttl,
            pid: match &self.pid { Some(x) => Some(x.dup()), None => None },
            lease_timeout_at: self.lease_timeout_at,
            retry_timeout_at: self.retry_timeout_at, resumes,
        }
    }

    pub fn to_record(&self, id: &Ident) -> TaskRecord {
        TaskRecord {
            id: id.dup(), state: self.state, version: self.version,
            resumes: self.resumes.len() as u64, ttl: self.ttl,
            pid: match &self.pid { Some(x) => Some(x.dup()), None => None },
        }
    }

    pub fn fulfill(mut self) -> TaskObject {
        self.state = TaskState::Fulfilled;
        self.pid = None;
        self.ttl = None;
        self.lease_timeout_at = None;
        self.retry_timeout_at = None;
        self.resumes = Vec::new();
        self
    }

    pub fn view(self, promise: &PromiseObject) -> TaskObject {
        if promise.state != PromiseState::Pending && self.state != TaskState::Fulfilled {
            self.fulfill()
        } else {
            self
        }
    }
}

impl Object {
    pub fn dup(&self) -> Object {
        Object {
            id: self.id.dup(), promise: self.promise.dup(),
            task: match &self.task { Some(t) => Some(t.dup()), None => None },
        }
    }

    pub fn project(mut self, now: u64) -> Object {
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
pub open spec fn spec_tag_key_timer(k: Seq<u8>) -> bool {
    k =~= seq![114u8,101u8,115u8,111u8,110u8,97u8,116u8,101u8,58u8,116u8,105u8,109u8,101u8,114u8]
}

pub open spec fn spec_text_true(x: AText) -> bool {
    x.bytes =~= seq![116u8,114u8,117u8,101u8]
}

pub open spec fn spec_timer_value(tags: ATags) -> Option<AText>
    decreases tags.len(),
{
    if tags.len() == 0 {
        None
    } else if spec_tag_key_timer(tags[0].key.bytes) {
        Some(tags[0].value)
    } else {
        spec_timer_value(tags.drop_first())
    }
}

pub open spec fn spec_tags_is_timer(tags: ATags) -> bool {
    match spec_timer_value(tags) {
        Some(value) => spec_text_true(value),
        None => false,
    }
}

// Pure ghost commit twin. These list functions deliberately use head/tail
// recursion, so proofs see the same stable filters and prepend order as Lean.

#[cfg(verus_keep_ghost)]
pub open spec fn spec_find_object(rows: Seq<AObject>, id: AIdent) -> Option<AObject>
    decreases rows.len(),
{
    if rows.len() == 0 {
        None
    } else if rows[0].id == id {
        Some(rows[0])
    } else {
        spec_find_object(rows.drop_first(), id)
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
pub fn append_effects(mut head: Vec<Effect>, mut tail: Vec<Effect>) -> Vec<Effect> {
    while tail.len() > 0
        decreases tail@.len(),
    {
        let e = tail.remove(0);
        head.push(e);
    }
    head
}

pub fn read_object(state: &State, id: &Ident, now: u64, materialize: bool) -> ReadResult {
    match state.find_object(id) {
        None => ReadResult { object: None, effects: Vec::new() },
        Some(i) => {
            let old = &state.objects[i];
            let projected = old.dup().project(now);
            let mut effects = Vec::new();
            if materialize && projected.promise.state != old.promise.state {
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
            ReadResult { object: Some(projected), effects }
        }
    }
}

pub fn read_task_object(state: &State, id: &Ident, now: u64, materialize: bool) -> ReadResult {
    match state.find_object(id) {
        None => ReadResult { object: None, effects: Vec::new() },
        Some(i) => match &state.objects[i].task {
            None => ReadResult { object: None, effects: Vec::new() },
            Some(_) => read_object(state, id, now, materialize),
        },
    }
}

pub fn set_settled_effects(o: &Object, p: &PromiseObject) -> Vec<Effect> {
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

pub fn checked_add(a: u64, b: u64) -> u64 {
    if b <= u64::MAX - a { a + b } else { u64::MAX }
}

pub struct Created {
    pub object: Object,
    pub effects: Vec<Effect>,
}

pub fn create_promise(req: PromiseCreateReq, now: u64) -> Created {
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
    Created { object: Object { id, promise, task }, effects }
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
