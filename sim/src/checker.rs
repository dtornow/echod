//! Bounded finite-trace search over the workspace Abstract machine.
//!
//! Calls may linearize in any order between Invoke and Return.  At every
//! observed clock instant, all productive Abstract internal actions may run
//! in any order.  Addressed `SetMessage` effects are queued and matched by
//! Receive observations.  Thus an `Ok` is an executable witness.  `Ko` is
//! returned only after the finite closure is exhausted; any budget or width
//! truncation yields `Unknown`.

use std::collections::{BTreeMap, BTreeSet, HashSet, VecDeque};
use std::sync::Arc;

use echod_abstract::state::{MessageKind, OutboxEntry};
use echod_abstract::{
    apply_all, handle_external, handle_internal, Config, Effect, ExternalAction, Ident,
    InternalAction, Occurrence, PromiseRegisterCallbackReq, PromiseRegisterListenerReq,
    PromiseState, PromiseTimeoutReq, ScheduleTimeoutReq, State, TaskLeaseTimeoutReq,
    TaskRetryTimeoutReq, TaskState,
};

use crate::bus::Sent;
use crate::history::Entry;
use crate::wire::{
    action_kind, clone_action, decode_response, ident, ident_string, model_response_view,
    text_string, ResponseView,
};

pub enum Event {
    Invoke { call: u64, req: Arc<ExternalAction> },
    Return { call: u64, response: ResponseView },
    Receive { message: OutboxEntry },
    Clock { at: u64 },
}

pub type Trace = Vec<Event>;
pub const DEFAULT_MAX_WIDTH: usize = 512;

/// The trace, from what the run recorded.
pub fn trace(entries: &[Entry], marks: &[u64], sent: &[Sent]) -> Trace {
    // (instant, rank, event): at one instant, returns and receives before
    // invokes, so a call never returns before it is invoked in the trace
    // order and a message is received where the clock had already reached.
    // The clock moves to every observed instant, plus the nodes' own step
    // marks. Receive instants matter: a retry dispatch resets its next
    // deadline from the instant the internal action ran.
    let mut items: Vec<(u64, u8, u64, Event)> = Vec::new();
    for e in entries {
        items.push((
            e.now,
            2,
            e.id,
            Event::Invoke {
                call: e.id,
                req: Arc::clone(&e.req),
            },
        ));
        if let Some((status, data)) = &e.outcome {
            let kind = action_kind(&e.req);
            items.push((
                e.ret.max(e.now),
                3,
                e.id,
                Event::Return {
                    call: e.id,
                    response: decode_response(kind, *status, data),
                },
            ));
        }
    }
    for (i, s) in sent.iter().enumerate() {
        items.push((
            s.at,
            1,
            i as u64,
            Event::Receive {
                message: s.msg.clone(),
            },
        ));
    }
    items.sort_by_key(|(t, rank, id, _)| (*t, *rank, *id));
    let mut marks = marks.to_vec();
    marks.sort_unstable();
    let mut out = Vec::new();
    let mut clock: Option<u64> = None;
    let mut mi = 0;
    for (t, _rank, _, e) in items {
        // the nodes' own instants up to here, then this one if it is an invoke
        while mi < marks.len() && marks[mi] <= t {
            if clock.is_none_or(|c| marks[mi] > c) {
                out.push(Event::Clock { at: marks[mi] });
                clock = Some(marks[mi]);
            }
            mi += 1;
        }
        if clock.is_none_or(|c| t > c) {
            out.push(Event::Clock { at: t });
            clock = Some(t);
        }
        out.push(e);
    }
    out
}

/// The Abstract state is a product over connected object ids. Multi-object
/// actions join their ids; independent components are checked separately.
/// Schedule actions retain a global catalogue and use the unfactored checker.
fn partition_trace(trace: &Trace) -> Option<Vec<(String, Trace, Vec<usize>)>> {
    let mut call_ids = BTreeMap::new();
    let mut parents = BTreeMap::new();
    for event in trace {
        match event {
            Event::Invoke { call, req } => {
                let ids = action_ids(req)?;
                let first = ids.first()?.clone();
                for id in &ids {
                    parents.entry(id.clone()).or_insert_with(|| id.clone());
                    union(&mut parents, &first, id);
                }
                call_ids.insert(*call, first);
            }
            Event::Receive { message } => {
                let id = message_id(message)?;
                parents.entry(id.clone()).or_insert(id);
            }
            _ => {}
        }
    }
    let calls: BTreeMap<u64, String> = call_ids
        .into_iter()
        .map(|(call, id)| (call, root(&parents, &id)))
        .collect();
    let keys: BTreeSet<String> = parents.keys().map(|id| root(&parents, id)).collect();
    if keys.len() <= 1 {
        return None;
    }
    let mut out: BTreeMap<String, (Trace, Vec<usize>)> = keys
        .into_iter()
        .map(|key| (key, (Vec::new(), Vec::new())))
        .collect();
    for (index, event) in trace.iter().enumerate() {
        match event {
            Event::Clock { at } => {
                for (partition, indices) in out.values_mut() {
                    partition.push(Event::Clock { at: *at });
                    indices.push(index);
                }
            }
            Event::Invoke { call, req } => {
                let key = calls.get(call)?;
                let (partition, indices) = out.get_mut(key)?;
                partition.push(Event::Invoke {
                    call: *call,
                    req: Arc::clone(req),
                });
                indices.push(index);
            }
            Event::Return { call, response } => {
                let key = calls.get(call)?;
                let (partition, indices) = out.get_mut(key)?;
                partition.push(Event::Return {
                    call: *call,
                    response: response.clone(),
                });
                indices.push(index);
            }
            Event::Receive { message } => {
                let key = root(&parents, &message_id(message)?);
                let (partition, indices) = out.get_mut(&key)?;
                partition.push(Event::Receive {
                    message: message.clone(),
                });
                indices.push(index);
            }
        }
    }
    Some(
        out.into_iter()
            .map(|(key, (partition, indices))| (key, partition, indices))
            .collect(),
    )
}

fn action_ids(action: &ExternalAction) -> Option<Vec<String>> {
    let one = |id: &Ident| Some(vec![ident_string(id)]);
    match action {
        ExternalAction::ScheduleGet(_)
        | ExternalAction::ScheduleCreate(_)
        | ExternalAction::ScheduleDelete(_)
        | ExternalAction::ScheduleSearch(_)
        | ExternalAction::PromiseSearch(_)
        | ExternalAction::TaskSearch(_) => None,
        ExternalAction::PromiseGet(q) => one(&q.id),
        ExternalAction::PromiseCreate(q) => one(&q.id),
        ExternalAction::PromiseSettle(q) => one(&q.id),
        ExternalAction::PromiseRegisterCallback(q) => {
            Some(vec![ident_string(&q.awaited), ident_string(&q.awaiter)])
        }
        ExternalAction::PromiseRegisterListener(q) => one(&q.awaited),
        ExternalAction::TaskGet(q) => one(&q.id),
        ExternalAction::TaskCreate(q) => one(&q.action.id),
        ExternalAction::TaskAcquire(q) => one(&q.id),
        ExternalAction::TaskFence(q) => {
            let target = match &q.action {
                echod_abstract::TaskFenceAction::Create(x) => &x.id,
                echod_abstract::TaskFenceAction::Settle(x) => &x.id,
            };
            Some(vec![ident_string(&q.id), ident_string(target)])
        }
        ExternalAction::TaskHeartbeat(q) => {
            let ids: Vec<String> = q.tasks.iter().map(|task| ident_string(&task.id)).collect();
            (!ids.is_empty()).then_some(ids)
        }
        ExternalAction::TaskSuspend(q) => {
            let mut ids = vec![ident_string(&q.id)];
            ids.extend(q.actions.iter().map(|action| ident_string(&action.awaited)));
            Some(ids)
        }
        ExternalAction::TaskFulfill(q) => one(&q.id),
        ExternalAction::TaskRelease(q) => one(&q.id),
        ExternalAction::TaskHalt(q) => one(&q.id),
        ExternalAction::TaskContinue(q) => one(&q.id),
    }
}

fn message_id(message: &OutboxEntry) -> Option<String> {
    message
        .message
        .task_id
        .as_ref()
        .map(ident_string)
        .or_else(|| {
            message
                .message
                .promise
                .as_ref()
                .map(|p| ident_string(&p.id))
        })
}

fn root(parents: &BTreeMap<String, String>, id: &str) -> String {
    let mut current = id;
    while let Some(parent) = parents.get(current) {
        if parent == current {
            break;
        }
        current = parent;
    }
    current.to_string()
}

fn union(parents: &mut BTreeMap<String, String>, a: &str, b: &str) {
    let left = root(parents, a);
    let right = root(parents, b);
    if left != right {
        let (low, high) = if left < right {
            (left, right)
        } else {
            (right, left)
        };
        parents.insert(high, low);
    }
}

#[derive(Debug)]
pub enum Verdict {
    /// Explained: how many nodes the search visited.
    Ok { explored: usize },
    /// No execution explains the event at `index`.
    Ko(Violation),
    /// The checker gave up before deciding.
    Unknown(Violation),
}

#[derive(Debug)]
pub struct Violation {
    pub index: usize,
    pub event: String,
    pub reason: String,
    pub profile: Vec<String>,
    pub explored: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Candidate {
    state: State,
    now: u64,
    /// Earliest instant at which this exact semantic state exists.
    floor: u64,
    pending: BTreeSet<u64>,
    done: BTreeMap<u64, ResponseView>,
    emitted: VecDeque<OutboxEntry>,
}

impl Candidate {
    fn initial() -> Self {
        Self {
            state: State::new(),
            now: 0,
            floor: 0,
            pending: BTreeSet::new(),
            done: BTreeMap::new(),
            emitted: VecDeque::new(),
        }
    }
}

struct Search<'a> {
    calls: BTreeMap<u64, Arc<ExternalAction>>,
    config: Config,
    fire_within: u64,
    budget: u64,
    explored: u64,
    max_width: Option<usize>,
    incomplete: bool,
    unsupported: Option<String>,
    trace: &'a Trace,
    position: usize,
    dead_profile: Vec<String>,
}

/// Check existential finite-trace semantics against the executable Abstract
/// machine.  Both external materialization choices are searched.
pub fn check(trace: &Trace, retry_timeout: u64, fire_within: u64, budget: u64) -> Verdict {
    let Some(partitions) = partition_trace(trace) else {
        return check_one(trace, retry_timeout, fire_within, budget);
    };
    let mut explored = 0usize;
    for (key, partition, indices) in partitions {
        let remaining = budget.saturating_sub(explored as u64);
        match check_one(&partition, retry_timeout, fire_within, remaining) {
            Verdict::Ok { explored: n } => explored += n,
            Verdict::Ko(mut violation) => {
                violation.index = indices[violation.index];
                violation.profile.push(format!("partition {key}"));
                return Verdict::Ko(violation);
            }
            Verdict::Unknown(mut violation) => {
                violation.index = indices[violation.index];
                violation.profile.push(format!("partition {key}"));
                return Verdict::Unknown(violation);
            }
        }
    }
    Verdict::Ok { explored }
}

fn check_one(trace: &Trace, retry_timeout: u64, fire_within: u64, budget: u64) -> Verdict {
    let max_width = std::env::var("ECHOD_SIM_WIDTH")
        .ok()
        .and_then(|v| v.parse().ok())
        .filter(|n| *n > 0)
        .or(Some(DEFAULT_MAX_WIDTH));
    let mut search = Search {
        calls: BTreeMap::new(),
        config: Config { retry_timeout },
        fire_within,
        budget,
        explored: 0,
        max_width,
        incomplete: false,
        unsupported: None,
        trace,
        position: 0,
        dead_profile: Vec::new(),
    };
    let progress: Option<usize> = std::env::var("ECHOD_SIM_PROGRESS")
        .ok()
        .and_then(|v| v.parse().ok())
        .filter(|n| *n > 0);
    let started = std::time::Instant::now();
    let mut profiles = vec![Candidate::initial()];
    for (index, event) in trace.iter().enumerate() {
        search.position = index;
        if let Event::Invoke { call, req } = event {
            if search.calls.insert(*call, Arc::clone(req)).is_some() {
                let violation = Violation {
                    index,
                    event: event_name(event),
                    reason: format!("call {call} was invoked more than once"),
                    profile: search.profile(index),
                    explored: search.explored,
                };
                return Verdict::Ko(violation);
            }
        }
        if progress.is_some_and(|n| index % n == 0) {
            eprintln!(
                "event {index}: {:.1?} explored {} width {}",
                started.elapsed(),
                search.explored,
                profiles.len()
            );
        }
        let mut next = if matches!(event, Event::Return { .. } | Event::Receive { .. }) {
            search.matching(profiles, event)
        } else {
            if matches!(event, Event::Clock { .. }) {
                profiles = search.external_closure(profiles);
            }
            let mut observed = Vec::new();
            let mut observed_keys = HashSet::new();
            for candidate in profiles {
                if let Some(candidate) = search.observe(candidate, event) {
                    push_candidate(&mut observed, &mut observed_keys, candidate);
                }
            }
            observed
        };
        next.retain(|candidate| search.viable(candidate));
        if let Some(width) = search.max_width {
            if next.len() > width {
                next = fair_truncate(next, width);
                search.incomplete = true;
            }
        }
        if next.is_empty() {
            let reason = search.unsupported.clone().unwrap_or_else(|| {
                if search.explored >= search.budget {
                    format!("semantic search budget {} exhausted", search.budget)
                } else if search.incomplete {
                    "semantic search profile was truncated".into()
                } else {
                    "no Abstract execution admits this observation".into()
                }
            });
            let violation = Violation {
                index,
                event: event_name(event),
                reason,
                profile: search.profile(index),
                explored: search.explored,
            };
            return if search.incomplete
                || search.explored >= search.budget
                || search.unsupported.is_some()
            {
                Verdict::Unknown(violation)
            } else {
                Verdict::Ko(violation)
            };
        }
        profiles = next;
    }
    Verdict::Ok {
        explored: search.explored as usize,
    }
}

impl Search<'_> {
    /// Completed calls and already-emitted messages are immutable. Discard a
    /// profile as soon as either disagrees with its future observation.
    fn viable(&self, candidate: &Candidate) -> bool {
        for (call, response) in &candidate.done {
            if let Some(expected) = self.trace[self.position..]
                .iter()
                .find_map(|event| match event {
                    Event::Return { call: c, response } if c == call => Some(response),
                    _ => None,
                })
            {
                if expected != response {
                    return false;
                }
            }
        }
        let mut receives: Vec<&OutboxEntry> = self.trace[self.position..]
            .iter()
            .filter_map(|event| match event {
                Event::Receive { message } => Some(message),
                _ => None,
            })
            .collect();
        for emitted in &candidate.emitted {
            let Some(index) = receives.iter().position(|message| *message == emitted) else {
                return false;
            };
            receives.remove(index);
        }
        true
    }

    /// Explore every productive action before a clock mark. Retry and lease
    /// actions cannot be deferred because their execution instant determines
    /// a later deadline. Origin factoring bounds this closure.
    fn external_closure(&mut self, seeds: Vec<Candidate>) -> Vec<Candidate> {
        let mut all = Vec::new();
        let mut keys = HashSet::new();
        let mut queue = VecDeque::new();
        for seed in seeds {
            if push_candidate(&mut all, &mut keys, seed.clone()) {
                queue.push_back(seed);
            }
        }
        while let Some(candidate) = queue.pop_front() {
            if self.explored >= self.budget {
                self.incomplete = true;
                break;
            }
            for next in self.successors(&candidate) {
                self.explored += 1;
                if self.explored > self.budget {
                    self.incomplete = true;
                    break;
                }
                if push_candidate(&mut all, &mut keys, next.clone()) {
                    if self.max_width.is_some_and(|w| all.len() >= w) {
                        self.incomplete = true;
                    } else {
                        queue.push_back(next);
                    }
                }
            }
            if self.explored >= self.budget {
                self.incomplete = true;
                break;
            }
        }
        all
    }

    /// Search epsilon actions only until the next observation is admitted.
    /// No action after that observation is enumerated.
    fn matching(&mut self, seeds: Vec<Candidate>, event: &Event) -> Vec<Candidate> {
        self.dead_profile = seeds
            .iter()
            .take(6)
            .map(|candidate| candidate_summary(candidate, event))
            .collect();
        let mut matched = Vec::new();
        let mut matched_keys = HashSet::new();
        let mut seen = HashSet::new();
        let mut queue = VecDeque::new();
        for seed in seeds {
            if seen.insert(format!("{seed:?}")) {
                queue.push_back(seed);
            }
        }
        while let Some(candidate) = queue.pop_front() {
            if let Some(observed) = self.observe(candidate.clone(), event) {
                push_candidate(&mut matched, &mut matched_keys, observed);
                continue;
            }
            match event {
                Event::Return { call, .. } if candidate.done.contains_key(call) => continue,
                _ => {}
            }
            if self.explored >= self.budget {
                self.incomplete = true;
                break;
            }
            let mut successors = self.successors(&candidate);
            successors.sort_by_key(|next| (!admits(next, event)) as u8);
            for next in successors {
                self.explored += 1;
                if self.explored > self.budget {
                    self.incomplete = true;
                    break;
                }
                if seen.insert(format!("{next:?}")) {
                    if self.max_width.is_some_and(|w| queue.len() >= w) {
                        self.incomplete = true;
                    } else {
                        queue.push_back(next);
                    }
                }
            }
        }
        matched
    }

    fn successors(&mut self, candidate: &Candidate) -> Vec<Candidate> {
        let mut out = Vec::new();
        let mut keys = HashSet::new();
        self.push_external_successors(candidate, &mut out, &mut keys);
        for action in internal_actions(&candidate.state, candidate.now) {
            for at in internal_times(&candidate.state, &action, candidate.floor, candidate.now) {
                let effects =
                    handle_internal(&candidate.state, clone_internal(&action), at, &self.config);
                if effects.is_empty() {
                    continue;
                }
                let mut next = candidate.clone();
                append_messages(&mut next.emitted, &effects);
                next.state = canonical(apply_all(next.state, effects));
                next.floor = next.floor.max(at);
                if next != *candidate {
                    push_candidate(&mut out, &mut keys, next);
                }
            }
        }
        out
    }

    fn push_external_successors(
        &self,
        candidate: &Candidate,
        out: &mut Vec<Candidate>,
        keys: &mut HashSet<String>,
    ) {
        for call in &candidate.pending {
            let Some(action) = self.calls.get(call) else {
                continue;
            };
            for materialize in [false, true] {
                let step = handle_external(
                    &candidate.state,
                    clone_action(action),
                    candidate.now,
                    materialize,
                );
                let response = model_response_view(&step.response);
                let mut next = candidate.clone();
                append_messages(&mut next.emitted, &step.effects);
                next.state = canonical(apply_all(next.state, step.effects));
                next.floor = candidate.now;
                next.pending.remove(call);
                next.done.insert(*call, response);
                push_candidate(out, keys, next);
            }
        }
    }

    fn observe(&mut self, mut candidate: Candidate, event: &Event) -> Option<Candidate> {
        match event {
            Event::Clock { at } => {
                if *at < candidate.now || schedules_overdue(&candidate.state, *at, self.fire_within)
                {
                    return None;
                }
                candidate.now = *at;
                Some(candidate)
            }
            Event::Invoke { call, req } => {
                let _ = req;
                if candidate.pending.contains(call) || candidate.done.contains_key(call) {
                    return None;
                }
                candidate.pending.insert(*call);
                Some(candidate)
            }
            Event::Return { call, response } => {
                if candidate.done.get(call) != Some(response) {
                    return None;
                }
                candidate.done.remove(call);
                Some(candidate)
            }
            Event::Receive { message } => {
                let index = candidate
                    .emitted
                    .iter()
                    .position(|emitted| emitted == message)?;
                if candidate.emitted.remove(index).is_none() {
                    return None;
                }
                Some(candidate)
            }
        }
    }

    fn profile(&self, index: usize) -> Vec<String> {
        let mut profile = vec![
            format!("processed {index}/{} observations", self.trace.len()),
            format!(
                "explored {} semantic successors (budget {})",
                self.explored, self.budget
            ),
        ];
        profile.extend(self.dead_profile.iter().cloned());
        profile
    }
}

fn append_messages(out: &mut VecDeque<OutboxEntry>, effects: &[Effect]) {
    for effect in effects {
        if let Effect::SetMessage(address, message) = effect {
            out.push_back(OutboxEntry {
                address: address.dup(),
                message: message.clone(),
            });
        }
    }
}

fn canonical(mut state: State) -> State {
    state.objects.sort_by_key(|o| ident_string(&o.id));
    state.schedules.sort_by_key(|s| ident_string(&s.id));
    state.outbox.sort_by_key(|e| {
        let id = e
            .message
            .task_id
            .as_ref()
            .map(ident_string)
            .or_else(|| e.message.promise.as_ref().map(|p| ident_string(&p.id)))
            .unwrap_or_default();
        (
            text_string(&e.address),
            e.message.kind == MessageKind::Unblock,
            id,
        )
    });
    state
}

fn internal_actions(state: &State, now: u64) -> Vec<InternalAction> {
    let mut out = Vec::new();
    for object in &state.objects {
        let settled =
            object.promise.state != PromiseState::Pending || object.promise.timeout_at <= now;
        if object.promise.state == PromiseState::Pending && object.promise.timeout_at <= now {
            out.push(InternalAction::PromiseTimeout(PromiseTimeoutReq {
                id: object.id.dup(),
            }));
        }
        if settled {
            for awaiter in &object.promise.callbacks {
                out.push(InternalAction::Callback(PromiseRegisterCallbackReq {
                    awaited: object.id.dup(),
                    awaiter: awaiter.dup(),
                }));
            }
            for address in &object.promise.listeners {
                out.push(InternalAction::Listener(PromiseRegisterListenerReq {
                    awaited: object.id.dup(),
                    address: address.dup(),
                }));
            }
        }
        if let Some(task) = &object.task {
            if task.state == TaskState::Acquired
                && task.lease_timeout_at.is_some_and(|at| at <= now)
            {
                out.push(InternalAction::TaskLeaseTimeout(TaskLeaseTimeoutReq {
                    id: object.id.dup(),
                }));
            }
            if task.state == TaskState::Pending && task.retry_timeout_at.is_some_and(|at| at <= now)
            {
                out.push(InternalAction::TaskRetryTimeout(TaskRetryTimeoutReq {
                    id: object.id.dup(),
                }));
            }
        }
    }
    for schedule in &state.schedules {
        if schedule.next_run_at <= now {
            let at = schedule.next_run_at;
            let schedule_id = ident_string(&schedule.id);
            let template = ident_string(&schedule.promise_id);
            let promise_id = template
                .replace("{{.id}}", &schedule_id)
                .replace("{{.timestamp}}", &at.to_string());
            let cron = text_string(&schedule.cron);
            let next_run_at = resonate_core::util::compute_next_cron(&cron, at as i64)
                .max(at.saturating_add(1) as i64) as u64;
            out.push(InternalAction::ScheduleTimeout(ScheduleTimeoutReq {
                schedule: schedule.id.dup(),
                occurrences: vec![Occurrence {
                    at,
                    promise_id: ident(&promise_id),
                }],
                next_run_at,
            }));
        }
    }
    out
}

/// Internal effects may be delivered after the semantic action. Search both
/// the enabling deadline and the latest observed instant; this represents
/// internal timing nondeterminism without moving the observation clock.
fn internal_times(state: &State, action: &InternalAction, floor: u64, now: u64) -> Vec<u64> {
    let due = match action {
        InternalAction::PromiseTimeout(q) => state
            .objects
            .iter()
            .find(|o| ident_string(&o.id) == ident_string(&q.id))
            .map(|o| o.promise.timeout_at),
        InternalAction::Callback(q) => state
            .objects
            .iter()
            .find(|o| ident_string(&o.id) == ident_string(&q.awaited))
            .and_then(|o| o.promise.settled_at.or(Some(o.promise.timeout_at))),
        InternalAction::Listener(q) => state
            .objects
            .iter()
            .find(|o| ident_string(&o.id) == ident_string(&q.awaited))
            .and_then(|o| o.promise.settled_at.or(Some(o.promise.timeout_at))),
        InternalAction::TaskLeaseTimeout(q) => state
            .objects
            .iter()
            .find(|o| ident_string(&o.id) == ident_string(&q.id))
            .and_then(|o| o.task.as_ref()?.lease_timeout_at),
        InternalAction::TaskRetryTimeout(q) => state
            .objects
            .iter()
            .find(|o| ident_string(&o.id) == ident_string(&q.id))
            .and_then(|o| o.task.as_ref()?.retry_timeout_at),
        InternalAction::ScheduleTimeout(q) => state
            .schedules
            .iter()
            .find(|s| ident_string(&s.id) == ident_string(&q.schedule))
            .map(|s| s.next_run_at),
    };
    match due {
        Some(due) if floor <= due && due < now => vec![due, now],
        _ => vec![now],
    }
}

fn clone_internal(action: &InternalAction) -> InternalAction {
    match action {
        InternalAction::PromiseTimeout(q) => {
            InternalAction::PromiseTimeout(PromiseTimeoutReq { id: q.id.dup() })
        }
        InternalAction::Callback(q) => InternalAction::Callback(PromiseRegisterCallbackReq {
            awaited: q.awaited.dup(),
            awaiter: q.awaiter.dup(),
        }),
        InternalAction::Listener(q) => InternalAction::Listener(PromiseRegisterListenerReq {
            awaited: q.awaited.dup(),
            address: q.address.dup(),
        }),
        InternalAction::TaskLeaseTimeout(q) => {
            InternalAction::TaskLeaseTimeout(TaskLeaseTimeoutReq { id: q.id.dup() })
        }
        InternalAction::TaskRetryTimeout(q) => {
            InternalAction::TaskRetryTimeout(TaskRetryTimeoutReq { id: q.id.dup() })
        }
        InternalAction::ScheduleTimeout(q) => InternalAction::ScheduleTimeout(ScheduleTimeoutReq {
            schedule: q.schedule.dup(),
            occurrences: q
                .occurrences
                .iter()
                .map(|o| Occurrence {
                    at: o.at,
                    promise_id: o.promise_id.dup(),
                })
                .collect(),
            next_run_at: q.next_run_at,
        }),
    }
}

fn schedules_overdue(state: &State, at: u64, fire_within: u64) -> bool {
    state
        .schedules
        .iter()
        .any(|s| s.next_run_at.saturating_add(fire_within) < at)
}

fn admits(candidate: &Candidate, event: &Event) -> bool {
    match event {
        Event::Return { call, response } => candidate.done.get(call) == Some(response),
        Event::Receive { message } => candidate.emitted.contains(message),
        Event::Clock { at } => *at >= candidate.now,
        Event::Invoke { call, .. } => {
            !candidate.pending.contains(call) && !candidate.done.contains_key(call)
        }
    }
}

fn candidate_summary(candidate: &Candidate, event: &Event) -> String {
    if let Event::Receive { message } = event {
        let id = message
            .message
            .task_id
            .as_ref()
            .or_else(|| message.message.promise.as_ref().map(|p| &p.id));
        if let Some(id) = id {
            let object = candidate
                .state
                .objects
                .iter()
                .find(|object| ident_string(&object.id) == ident_string(id));
            return format!(
                "now={} floor={} target={} object={object:?} emitted={:?}",
                candidate.now,
                candidate.floor,
                ident_string(id),
                candidate.emitted.front()
            );
        }
    }
    format!(
        "now={} floor={} pending={:?} done={:?} emitted={:?}",
        candidate.now,
        candidate.floor,
        candidate.pending,
        candidate.done.keys().collect::<Vec<_>>(),
        candidate.emitted.front()
    )
}

fn push_candidate(
    values: &mut Vec<Candidate>,
    keys: &mut HashSet<String>,
    value: Candidate,
) -> bool {
    let key = format!("{value:?}");
    if keys.insert(key) {
        values.push(value);
        true
    } else {
        false
    }
}

/// Keep representatives of every call phase instead of allowing the first
/// (usually "not linearized yet") phase to consume the whole width budget.
fn fair_truncate(values: Vec<Candidate>, width: usize) -> Vec<Candidate> {
    let mut groups: BTreeMap<String, VecDeque<Candidate>> = BTreeMap::new();
    for candidate in values {
        let key = format!(
            "{:?}|{:?}|{}",
            candidate.pending,
            candidate.done.keys().collect::<Vec<_>>(),
            candidate.emitted.len()
        );
        groups.entry(key).or_default().push_back(candidate);
    }
    let mut out = Vec::new();
    while out.len() < width {
        let mut advanced = false;
        for group in groups.values_mut() {
            if let Some(candidate) = group.pop_front() {
                out.push(candidate);
                advanced = true;
                if out.len() == width {
                    break;
                }
            }
        }
        if !advanced {
            break;
        }
    }
    out
}

fn event_name(event: &Event) -> String {
    match event {
        Event::Invoke { call, req } => format!("call {call} invoke {}", action_kind(req)),
        Event::Return { call, response } => format!("call {call} return {response:?}"),
        Event::Receive { message } => format!("receive {message:?}"),
        Event::Clock { at } => format!("clock {at}"),
    }
}

/// The trace as a client saw it, one event per line, up to event `upto`.
pub fn show(trace: &Trace, upto: usize) -> String {
    let mut out = String::new();
    for (i, event) in trace.iter().enumerate().take(upto + 1) {
        out.push_str(&format!("{i:>5}  {}\n", event_name(event)));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::{clone_action, ident, text};
    use echod_abstract::{PromiseCreateReq, PromiseGetReq, ScheduleCreateReq, Tag, Value};

    fn empty(status: u16) -> ResponseView {
        ResponseView {
            status,
            promise: None,
            task: None,
            schedule: None,
        }
    }

    #[test]
    fn distinguishes_ok_ko_and_budget_unknown() {
        let get = Arc::new(ExternalAction::PromiseGet(PromiseGetReq {
            id: ident("o:1"),
        }));
        let ok = vec![
            Event::Clock { at: 10 },
            Event::Invoke {
                call: 1,
                req: Arc::clone(&get),
            },
            Event::Return {
                call: 1,
                response: empty(404),
            },
        ];
        assert!(matches!(check(&ok, 100, 100, 100), Verdict::Ok { .. }));

        let ko = vec![
            Event::Clock { at: 10 },
            Event::Invoke {
                call: 1,
                req: Arc::clone(&get),
            },
            Event::Return {
                call: 1,
                response: empty(200),
            },
        ];
        assert!(matches!(check(&ko, 100, 100, 100), Verdict::Ko(_)));
        assert!(matches!(check(&ok, 100, 100, 0), Verdict::Unknown(_)));
    }

    #[test]
    fn searches_concurrent_call_order() {
        let create = ExternalAction::PromiseCreate(PromiseCreateReq {
            id: ident("o:1"),
            timeout_at: 100,
            param: Value::empty(),
            tags: Vec::new(),
        });
        let get = ExternalAction::PromiseGet(PromiseGetReq { id: ident("o:1") });
        let state = State::new();
        let get_response = handle_external(&state, clone_action(&get), 10, false);
        let create_response = handle_external(&state, clone_action(&create), 10, false);
        let trace = vec![
            Event::Clock { at: 10 },
            Event::Invoke {
                call: 1,
                req: Arc::new(create),
            },
            Event::Invoke {
                call: 2,
                req: Arc::new(get),
            },
            Event::Return {
                call: 2,
                response: model_response_view(&get_response.response),
            },
            Event::Return {
                call: 1,
                response: model_response_view(&create_response.response),
            },
        ];
        assert!(matches!(check(&trace, 100, 100, 1_000), Verdict::Ok { .. }));
    }

    #[test]
    fn searches_schedule_occurrence_witnesses() {
        let schedule = ExternalAction::ScheduleCreate(ScheduleCreateReq {
            id: ident("tick"),
            cron: text("*/1 * * * * *"),
            promise_id: ident("o:tick-{{.timestamp}}"),
            promise_timeout: 5_000,
            promise_param: Value::empty(),
            promise_tags: vec![Tag {
                key: text("resonate:target"),
                value: text("sim://worker"),
            }],
            next_run_at: 2_000,
        });
        let get = ExternalAction::PromiseGet(PromiseGetReq {
            id: ident("o:tick-2000"),
        });
        let create = handle_external(&State::new(), clone_action(&schedule), 1_000, false);
        let mut state = apply_all(State::new(), create.effects);
        state = apply_all(
            state.clone(),
            handle_internal(
                &state,
                InternalAction::ScheduleTimeout(ScheduleTimeoutReq {
                    schedule: ident("tick"),
                    occurrences: vec![Occurrence {
                        at: 2_000,
                        promise_id: ident("o:tick-2000"),
                    }],
                    next_run_at: 3_000,
                }),
                2_000,
                &Config { retry_timeout: 100 },
            ),
        );
        let get_response = handle_external(&state, clone_action(&get), 2_000, false);
        let trace = vec![
            Event::Clock { at: 1_000 },
            Event::Invoke {
                call: 1,
                req: Arc::new(schedule),
            },
            Event::Return {
                call: 1,
                response: model_response_view(&create.response),
            },
            Event::Clock { at: 2_000 },
            Event::Invoke {
                call: 2,
                req: Arc::new(get),
            },
            Event::Return {
                call: 2,
                response: model_response_view(&get_response.response),
            },
        ];
        assert!(matches!(
            check(&trace, 100, 1_000, 10_000),
            Verdict::Ok { .. }
        ));
    }
}
