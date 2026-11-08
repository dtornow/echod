//! A flight on one document, executed: the step it decides, and the
//! sequence of store calls that commits it, each decision a pure function
//! that ensures it computes `flight_spec`.
//!
//! `decide` is the concrete model's step on the document. `Sequence` is the
//! commit: from the verified plan, one `advance` per store answer, each
//! returning the next call to make, or the end. `handler_docs` names the
//! keys, builds the bytes, makes the calls, and brings the answers back;
//! it takes no decision of its own.

use vstd::prelude::*;

use echod_concrete::store::{StoreError, StoreRes};
use echod_concrete::{
    create_occurrence, fire_schedule, request_transition, sweep, DocumentBody, Outbound, Pending,
};
use echod_types::{Request, Response};

use super::commit::Commit;
use super::node::*;

#[cfg(verus_keep_ghost)]
use super::commit_spec::*;
#[cfg(verus_keep_ghost)]
use super::flight_spec::*;
#[cfg(verus_keep_ghost)]
use echod_concrete::node::{notes_v, pend_v, NoteV, PendingV};

verus! {

// ---------------------------------------------------------------------------
// The step
// ---------------------------------------------------------------------------

/// What a flight does to its document.
pub enum Job {
    Request(Request),
    Sweep,
    Fire,
    Occurrence(Pending),
}

#[cfg(verus_keep_ghost)]
impl View for Job {
    type V = AJob;
    open spec fn view(&self) -> AJob {
        match self {
            Job::Request(request) => AJob::Request(*request),
            Job::Sweep => AJob::Sweep,
            Job::Fire => AJob::Fire,
            Job::Occurrence(pending) => AJob::Occurrence(pending@),
        }
    }
}

/// What a step left: the document, its answer, the occurrences it queued,
/// and the notes to send once the document is committed.
pub struct Decided {
    pub doc: DocumentBody,
    pub response: Option<Response>,
    pub born: Vec<Pending>,
    pub notes: Vec<Outbound>,
}

/// The step: the concrete model's, by the job.
pub fn decide(job: Job, doc: DocumentBody, now: u64, retry_timeout: u64) -> (r: Decided)
    ensures
        (r.doc@, r.response, pend_v(r.born@), notes_v(r.notes@)) == spec_step(job@, doc@, now, retry_timeout),
{
    proof {
        assert(pend_v(Seq::<Pending>::empty()) =~= Seq::<PendingV>::empty());
        assert(notes_v(Seq::<Outbound>::empty()) =~= Seq::<NoteV>::empty());
    }
    match job {
        Job::Request(request) => {
            let (doc, response, born, notes) =
                request_transition(doc, &request, now, retry_timeout);
            Decided { doc, response: Some(response), born, notes }
        },
        Job::Sweep => {
            let (doc, born, notes) = sweep(doc, now, retry_timeout);
            Decided { doc, response: None, born, notes }
        },
        Job::Fire => {
            let (doc, born) = fire_schedule(doc, now);
            Decided { doc, response: None, born, notes: Vec::new() }
        },
        Job::Occurrence(pending) => {
            let doc = create_occurrence(doc, &pending, now);
            Decided { doc, response: None, born: Vec::new(), notes: Vec::new() }
        },
    }
}

// ---------------------------------------------------------------------------
// The commit
// ---------------------------------------------------------------------------

/// The key that fired the flight, and the node that armed it.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
#[cfg_attr(not(verus_keep_ghost), derive(Debug))]
pub struct FiredKey {
    pub key: Key,
    pub by: String,
}

#[cfg(verus_keep_ghost)]
impl View for FiredKey {
    type V = AFired;
    open spec fn view(&self) -> AFired {
        AFired { key: self.key@, by: self.by@ }
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for FiredKey {
    type V = AFired;
    open spec fn deep_view(&self) -> AFired {
        self.view()
    }
}

#[cfg(verus_keep_ghost)]
impl DeepView for Sequence {
    type V = ASequence;
    open spec fn deep_view(&self) -> ASequence {
        self.view()
    }
}

pub open spec fn opt_fired(o: Option<FiredKey>) -> Option<AFired> {
    match o {
        Some(f) => Some(f@),
        None => None,
    }
}

pub open spec fn opt_seq(o: Option<String>) -> Option<Seq<char>> {
    match o {
        Some(s) => Some(s@),
        None => None,
    }
}

pub open spec fn answer_v(step: AStep, o: Option<&StoreRes>) -> AAnswer {
    match (step, o) {
        (_, None) => AAnswer::Fresh,
        (AStep::PuttingKey(_), Some(StoreRes::Put { result: Ok(()) }))
        | (AStep::DeletingPrevious(_), Some(StoreRes::Del { result: Ok(()) }))
        | (AStep::DeletingFired(_), Some(StoreRes::Del { result: Ok(()) })) => AAnswer::Done,
        (AStep::Writing { .. }, Some(StoreRes::PutIfMatch { result: Ok(tag) }))
        | (AStep::Writing { .. }, Some(StoreRes::PutIfNoneMatch { result: Ok(tag) }))
        | (AStep::Writing { .. }, Some(StoreRes::AppIfMatch { result: Ok(tag) })) => AAnswer::Written(tag.0@),
        (AStep::PuttingKey(_), Some(StoreRes::Put { result: Err(e) }))
        | (AStep::DeletingPrevious(_), Some(StoreRes::Del { result: Err(e) }))
        | (AStep::DeletingFired(_), Some(StoreRes::Del { result: Err(e) }))
        | (AStep::Writing { .. }, Some(StoreRes::PutIfMatch { result: Err(e) }))
        | (AStep::Writing { .. }, Some(StoreRes::PutIfNoneMatch { result: Err(e) }))
        | (AStep::Writing { .. }, Some(StoreRes::AppIfMatch { result: Err(e) })) => AAnswer::Failed(*e),
        (_, Some(_)) => AAnswer::Other,
    }
}

/// Where the commit stands: which call it waits on.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum Step {
    Start,
    PuttingKey(Key),
    Writing { idle: bool },
    DeletingPrevious(Key),
    DeletingFired(Key),
    Over,
}

#[cfg(verus_keep_ghost)]
impl View for Step {
    type V = AStep;
    open spec fn view(&self) -> AStep {
        match self {
            Step::Start => AStep::Start,
            Step::PuttingKey(k) => AStep::PuttingKey(k@),
            Step::Writing { idle } => AStep::Writing { idle: *idle },
            Step::DeletingPrevious(k) => AStep::DeletingPrevious(k@),
            Step::DeletingFired(k) => AStep::DeletingFired(k@),
            Step::Over => AStep::Over,
        }
    }
}

/// What the shell is asked to do next.
pub enum Act {
    /// Put the key, empty; arm the wheel at its instant once it lands.
    PutKey(Key),
    /// Write the document under `cond`: `PutIfMatch` on that version,
    /// `PutIfNoneMatch` when none was loaded. `idle` rewrites the same rows
    /// at a new version.
    Write { cond: Option<String>, idle: bool },
    /// Delete the key `by` armed.
    DeleteKey { key: Key, by: String },
    /// The commit is over; whether the fired key was deleted.
    Done { deleted: bool },
}

#[cfg(verus_keep_ghost)]
impl View for Act {
    type V = AAct;
    open spec fn view(&self) -> AAct {
        match self {
            Act::PutKey(k) => AAct::PutKey(k@),
            Act::Write { cond, idle } => AAct::Write { cond: opt_seq(*cond), idle: *idle },
            Act::DeleteKey { key, by } => AAct::DeleteKey { key: key@, by: by@ },
            Act::Done { deleted } => AAct::Done { deleted: *deleted },
        }
    }
}

pub enum Outcome {
    Act(Act),
    /// The store failed the call; `None` is an answer of another shape.
    Failed(Option<StoreError>),
}

#[cfg(verus_keep_ghost)]
impl View for Outcome {
    type V = AOutcome;
    open spec fn view(&self) -> AOutcome {
        match self {
            Outcome::Act(a) => AOutcome::Act(a@),
            Outcome::Failed(e) => AOutcome::Failed(*e),
        }
    }
}

/// `StoreError::clone`, with its meaning stated.
#[verifier::external_body]
fn copy_error(e: &StoreError) -> (r: StoreError)
    ensures r == *e,
{
    e.clone()
}

fn copy_opt_string(o: &Option<String>) -> (r: Option<String>)
    ensures opt_seq(r) == opt_seq(*o),
{
    match o {
        Some(s) => Some(clone_string(s)),
        None => None,
    }
}

fn copy_step(s: &Step) -> (r: Step)
    ensures r@ == s@,
{
    match s {
        Step::Start => Step::Start,
        Step::PuttingKey(k) => Step::PuttingKey(clone_key(k)),
        Step::Writing { idle } => Step::Writing { idle: *idle },
        Step::DeletingPrevious(k) => Step::DeletingPrevious(clone_key(k)),
        Step::DeletingFired(k) => Step::DeletingFired(clone_key(k)),
        Step::Over => Step::Over,
    }
}

/// The commit of one step on one document.
#[derive(Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct Sequence {
    pub origin: String,
    /// The version loaded; after the write, the version written.
    pub etag: Option<String>,
    /// Whether the document differs from what was loaded.
    pub changed: bool,
    /// The key whose firing began the flight, if any.
    pub fired: Option<FiredKey>,
    /// The token the key armed, if one is, carries.
    pub token: u64,
    pub plan: Commit,
    pub step: Step,
}

#[cfg(verus_keep_ghost)]
impl View for Sequence {
    type V = ASequence;
    open spec fn view(&self) -> ASequence {
        ASequence {
            origin: self.origin@,
            etag: opt_seq(self.etag),
            changed: self.changed,
            fired: opt_fired(self.fired),
            token: self.token as nat,
            plan: self.plan@,
            step: self.step@,
        }
    }
}

impl Sequence {
    /// A commit before its first call: `spec_new`, the verified plan for it.
    pub fn new(core: &NodeCore, origin: &str, etag: Option<&String>, deadline: Option<u64>, changed: bool, fired: Option<FiredKey>, token: u64) -> (s: Sequence)
        ensures
            s@ == spec_new(core@, origin@, opt_str(etag), opt_nat(deadline), changed, opt_fired(fired), token as nat),
    {
        let fired_key = match &fired {
            Some(f) => Some(clone_key(&f.key)),
            None => None,
        };
        let plan = core.prepare(origin, etag, deadline, changed, fired_key);
        let etag = match etag {
            Some(e) => Some(clone_string(e)),
            None => None,
        };
        Sequence { origin: origin.to_string(), etag, changed, fired, token, plan, step: Step::Start }
    }

    /// Whether the commit waits on a store call.
    pub fn waiting(&self) -> (r: bool)
        ensures r == !(self@.step is Start || self@.step is Over),
    {
        match &self.step {
            Step::Start | Step::Over => false,
            _ => true,
        }
    }

    /// One decision: `spec_advance`. `answer` is the store's answer to the
    /// call the commit waits on, if it waits on one.
    pub fn advance(&mut self, core: &mut NodeCore, answer: Option<&StoreRes>) -> (r: Outcome)
        ensures
            (final(self)@, final(core)@, r@) == spec_advance(old(self)@, old(core)@, answer_v(old(self)@.step, answer)),
    {
        let step = copy_step(&self.step);
        match step {
            Step::Start => {
                if self.changed {
                    let arm = match self.plan.deadline {
                        Some(at) => if self.plan.rearm { Some(at) } else { None },
                        None => None,
                    };
                    match arm {
                        Some(at) => {
                            let key = Key { origin: clone_string(&self.origin), at, token: self.token };
                            self.step = Step::PuttingKey(clone_key(&key));
                            Outcome::Act(Act::PutKey(key))
                        },
                        None => {
                            self.step = Step::Writing { idle: false };
                            Outcome::Act(Act::Write { cond: copy_opt_string(&self.etag), idle: false })
                        },
                    }
                } else if self.fired.is_some() {
                    self.step = Step::Writing { idle: true };
                    Outcome::Act(Act::Write { cond: copy_opt_string(&self.etag), idle: true })
                } else {
                    self.step = Step::Over;
                    Outcome::Act(Act::Done { deleted: false })
                }
            },
            Step::PuttingKey(key) => match answer {
                Some(StoreRes::Put { result: Ok(()) }) => {
                    proof { assert(answer_v(old(self)@.step, answer) == AAnswer::Done); }
                    self.plan.armed(key);
                    self.step = Step::Writing { idle: false };
                    Outcome::Act(Act::Write { cond: copy_opt_string(&self.etag), idle: false })
                },
                Some(StoreRes::Put { result: Err(e) }) => {
                    proof { assert(answer_v(old(self)@.step, answer) == AAnswer::Failed(*e)); }
                    self.step = Step::Over;
                    Outcome::Failed(Some(copy_error(e)))
                },
                _ => {
                    self.step = Step::Over;
                    Outcome::Failed(None)
                },
            },
            Step::Writing { idle } => match answer {
                Some(StoreRes::PutIfMatch { result: Ok(tag) })
                | Some(StoreRes::PutIfNoneMatch { result: Ok(tag) })
                | Some(StoreRes::AppIfMatch { result: Ok(tag) }) => {
                    proof { assert(answer_v(old(self)@.step, answer) == AAnswer::Written(tag.0@)); }
                    self.etag = Some(clone_string(&tag.0));
                    if idle {
                        self.collect(core)
                    } else {
                        match self.plan.to_disarm() {
                            Some(previous) => {
                                self.step = Step::DeletingPrevious(clone_key(&previous));
                                Outcome::Act(Act::DeleteKey { key: previous, by: clone_string(&core.id) })
                            },
                            None => {
                                core.finish(&self.plan, &tag.0);
                                self.collect(core)
                            },
                        }
                    }
                },
                Some(StoreRes::PutIfMatch { result: Err(e) })
                | Some(StoreRes::PutIfNoneMatch { result: Err(e) })
                | Some(StoreRes::AppIfMatch { result: Err(e) }) => {
                    proof { assert(answer_v(old(self)@.step, answer) == AAnswer::Failed(*e)); }
                    self.step = Step::Over;
                    Outcome::Failed(Some(copy_error(e)))
                },
                _ => {
                    self.step = Step::Over;
                    Outcome::Failed(None)
                },
            },
            Step::DeletingPrevious(_) => {
                let tag = match &self.etag {
                    Some(t) => clone_string(t),
                    None => String::new(),
                };
                core.finish(&self.plan, &tag);
                self.collect(core)
            },
            Step::DeletingFired(_) => match answer {
                Some(StoreRes::Del { result: Ok(()) }) => {
                    proof { assert(answer_v(old(self)@.step, answer) == AAnswer::Done); }
                    self.step = Step::Over;
                    Outcome::Act(Act::Done { deleted: true })
                },
                _ => {
                    self.step = Step::Over;
                    Outcome::Act(Act::Done { deleted: false })
                },
            },
            Step::Over => Outcome::Act(Act::Done { deleted: false }),
        }
    }

    /// After the write: `spec_collect`, the key fired collected behind it.
    fn collect(&mut self, core: &mut NodeCore) -> (r: Outcome)
        ensures
            (final(self)@, final(core)@, r@) == spec_collect(old(self)@, old(core)@),
    {
        match &self.fired {
            Some(f) => {
                let key = clone_key(&f.key);
                let by = clone_string(&f.by);
                core.collected(self.origin.as_str(), &key);
                self.step = Step::DeletingFired(clone_key(&key));
                Outcome::Act(Act::DeleteKey { key, by })
            },
            None => {
                self.step = Step::Over;
                Outcome::Act(Act::Done { deleted: false })
            },
        }
    }
}

} // verus!
