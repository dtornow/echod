//! A flight on one document, as a specification: the step it decides, and
//! the sequence of store calls that commits it.
//!
//! The step is the concrete model's (`spec_handle`, `spec_sweep`,
//! `spec_run_due`, `spec_occurrence`); `lemma_step_is_decide` reads it off
//! the model's `spec_decide`. The commit is this design's own: a deadline
//! key is armed before the document is written, the key it replaced is
//! removed after, and the key whose firing began the flight is collected
//! last, behind a write that fences every commit that armed it. `flight.rs`
//! ensures it computes these.

use vstd::prelude::*;

use echod_concrete::node::{
    notes_v, pend_v, spec_decide, spec_occurrence, spec_request_transition, spec_run_due,
    spec_sweep, DocumentBodyV, FlightV, JobV, NodeV, NoteV, PendingV,
};
use echod_concrete::store::{StoreError, StoreReq, StoreRes};
use echod_concrete::model::{Message, Pid};
use echod_types::Response;

use super::commit_spec::*;
use super::node_spec::*;

verus! {

// ---------------------------------------------------------------------------
// The step
// ---------------------------------------------------------------------------

/// What a flight does to its document.
pub enum AJob {
    /// A request: `spec_handle`.
    Request(echod_types::Request),
    /// A fired key: `spec_sweep`, every due step up to a limit.
    Sweep,
    /// A schedule's key: `spec_run_due`, the occurrence due and the schedule advanced.
    Fire,
    /// That occurrence, born in its origin: `spec_occurrence`.
    Occurrence(PendingV),
}

/// The document a step leaves, its answer, the occurrences it queued, and
/// the notes it will send once the document is committed.
pub open spec fn spec_step(job: AJob, doc: DocumentBodyV, now: u64, retry_timeout: u64, limit: nat) -> (DocumentBodyV, Option<Response>, Seq<PendingV>, Seq<NoteV>) {
    match job {
        AJob::Request(request) => {
            let (next, response, born, notes) =
                spec_request_transition(doc, request, now, retry_timeout, limit);
            (next, Some(response), born, notes)
        },
        AJob::Sweep => {
            let (next, born, notes) = spec_sweep(doc, now, retry_timeout, limit);
            (next, None, born, notes)
        },
        AJob::Fire => spec_run_due(doc, now, retry_timeout),
        AJob::Occurrence(pending) => (spec_occurrence(doc, pending, now), None, Seq::empty(), Seq::empty()),
    }
}

/// The model's job as this flight's: one due step is `Fire`.
pub open spec fn job_of(job: JobV) -> AJob {
    match job {
        JobV::External(request) => AJob::Request(request),
        JobV::Due => AJob::Fire,
        JobV::Occurrence(pending) => AJob::Occurrence(pending),
    }
}

/// For model-native due and occurrence jobs, `spec_decide` writes the
/// document `spec_step` leaves. Request jobs use the stronger process-level
/// pre/handler/post transition and are verified directly by
/// [`super::flight::decide`], rather than by Rover's raw-handler step.
pub proof fn lemma_step_is_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV, limit: nat)
    requires
        !(flight.job is External),
        match flight.etag {
            Some(chars) => chars.len() <= usize::MAX as int,
            None => true,
        },
    ensures
        ({
            let (next, reply, born, notify) = spec_step(job_of(flight.job), doc, flight.now, node.retry_timeout, limit);
            let (after, sent) = spec_decide(node, flight, doc);
            match after.flight {
                Some(open) => {
                    &&& open.writing
                    &&& open.decided == Some(echod_concrete::node::spec_encode_body(next))
                    &&& sent.len() == 1
                    &&& match sent[0].1 {
                        Message::StoreReq { request, .. } => match flight.etag {
                            Some(chars) => request matches StoreReq::PutIfMatch { etag, .. } && etag.0@ == chars,
                            None => request is PutIfNoneMatch,
                        },
                        _ => false,
                    }
                },
                None => after.flight is None,
            }
        }),
{
    let (after, sent) = spec_decide(node, flight, doc);
    match after.flight {
        Some(open) => {
            match flight.etag {
                Some(chars) => echod_concrete::interpret::lemma_string_view(chars),
                None => {},
            }
        },
        None => {},
    }
}

// ---------------------------------------------------------------------------
// The commit: the sequence of store calls
// ---------------------------------------------------------------------------

/// The key that fired the flight, and the node that armed it.
pub struct AFired {
    pub key: AKey,
    pub by: Seq<char>,
}

/// Where the commit stands: which call it waits on.
pub enum AStep {
    Start,
    PuttingKey(AKey),
    Writing { idle: bool },
    DeletingPrevious(AKey),
    DeletingFired(AKey),
    Over,
}

/// The commit of one step on one document.
pub struct ASequence {
    pub origin: Origin,
    /// The version loaded; after the write, the version written.
    pub etag: Option<Seq<char>>,
    /// Whether the document differs from what was loaded.
    pub changed: bool,
    pub fired: Option<AFired>,
    /// The token the key armed, if one is, carries.
    pub token: nat,
    pub plan: ACommit,
    pub step: AStep,
}

/// What the shell is asked to do next.
pub enum AAct {
    /// Put the key, empty, and arm the wheel at its instant once it lands.
    PutKey(AKey),
    /// Write the document, conditionally on `cond`: `PutIfMatch` on that
    /// version, `PutIfNoneMatch` when none was loaded. `idle` is a rewrite of
    /// the same rows at a new version, so a fired key can be collected behind it.
    Write { cond: Option<Seq<char>>, idle: bool },
    /// Delete the key `by` armed.
    DeleteKey { key: AKey, by: Seq<char> },
    /// The commit is over; whether the fired key was deleted.
    Done { deleted: bool },
}

/// The store's answer to the call the commit waits on, as the commit reads it.
pub enum AAnswer {
    /// No call was waited on.
    Fresh,
    Done,
    Written(Seq<char>),
    Failed(StoreError),
    /// An answer of another shape.
    Other,
}

pub enum AOutcome {
    Act(AAct),
    /// The store failed the call; `None` is an answer of another shape.
    Failed(Option<StoreError>),
}

pub open spec fn answer_v(step: AStep, o: Option<StoreRes>) -> AAnswer {
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
        | (AStep::Writing { .. }, Some(StoreRes::AppIfMatch { result: Err(e) })) => AAnswer::Failed(e),
        (_, Some(_)) => AAnswer::Other,
    }
}

/// A commit before its first call: the verified plan for it.
pub open spec fn spec_new(n: ANode, origin: Origin, etag: Option<Seq<char>>, deadline: Option<nat>, changed: bool, fired: Option<AFired>, token: nat) -> ASequence {
    let fired_key = match fired { Some(f) => Some(f.key), None => None };
    ASequence {
        origin,
        etag,
        changed,
        fired,
        token,
        plan: spec_prepare(n, origin, etag, deadline, changed, fired_key),
        step: AStep::Start,
    }
}

/// After the write: the key fired is collected, behind it.
pub open spec fn spec_collect(s: ASequence, n: ANode) -> (ASequence, ANode, AOutcome) {
    match s.fired {
        Some(f) => (
            ASequence { step: AStep::DeletingFired(f.key), ..s },
            spec_collected(n, s.origin, f.key),
            AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }),
        ),
        None => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: false })),
    }
}

/// One decision of the commit: given the answer to the call it waited on,
/// the next call, or the end.
///
/// (1) The key for the new deadline, before the state that arms it.
/// (2) The document. A document that did not change under a fired key is
///     rewritten at a new version, so that no commit in flight that armed
///     the key can land on the version it loaded.
/// (3) The key replaced, or no longer needed; best effort.
/// (4) The key kept, remembered with the version written.
/// (5) The key fired: the write that just landed fences every commit that
///     armed it and has not written yet.
pub open spec fn spec_advance(s: ASequence, n: ANode, answer: AAnswer) -> (ASequence, ANode, AOutcome) {
    match s.step {
        AStep::Start => {
            if s.changed {
                match s.plan.deadline {
                    Some(at) if s.plan.rearm => {
                        let key = AKey { origin: s.origin, at, token: s.token };
                        (ASequence { step: AStep::PuttingKey(key), ..s }, n, AOutcome::Act(AAct::PutKey(key)))
                    },
                    _ => (ASequence { step: AStep::Writing { idle: false }, ..s }, n, AOutcome::Act(AAct::Write { cond: s.etag, idle: false })),
                }
            } else if s.fired is Some {
                (ASequence { step: AStep::Writing { idle: true }, ..s }, n, AOutcome::Act(AAct::Write { cond: s.etag, idle: true }))
            } else {
                (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: false }))
            }
        },
        AStep::PuttingKey(key) => match answer {
            AAnswer::Done => (
                ASequence { step: AStep::Writing { idle: false }, plan: spec_armed(s.plan, key), ..s },
                n,
                AOutcome::Act(AAct::Write { cond: s.etag, idle: false }),
            ),
            AAnswer::Failed(e) => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(Some(e))),
            _ => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(None)),
        },
        AStep::Writing { idle } => match answer {
            AAnswer::Written(tag) => {
                let s = ASequence { etag: Some(tag), ..s };
                if idle {
                    spec_collect(s, n)
                } else {
                    match spec_to_disarm(s.plan) {
                        Some(previous) => (
                            ASequence { step: AStep::DeletingPrevious(previous), ..s },
                            n,
                            AOutcome::Act(AAct::DeleteKey { key: previous, by: n.id }),
                        ),
                        None => spec_collect(s, spec_finish(n, s.plan, tag)),
                    }
                }
            },
            AAnswer::Failed(e) => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(Some(e))),
            _ => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Failed(None)),
        },
        AStep::DeletingPrevious(_) => {
            let tag = match s.etag { Some(t) => t, None => Seq::empty() };
            spec_collect(s, spec_finish(n, s.plan, tag))
        },
        AStep::DeletingFired(_) => match answer {
            AAnswer::Done => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: true })),
            _ => (ASequence { step: AStep::Over, ..s }, n, AOutcome::Act(AAct::Done { deleted: false })),
        },
        AStep::Over => (s, n, AOutcome::Act(AAct::Done { deleted: false })),
    }
}

// ---------------------------------------------------------------------------
// The sequence as a whole
// ---------------------------------------------------------------------------

/// The answer a store that serves every call gives to the call a step waits on.
pub open spec fn spec_served(s: ASequence, tag: Seq<char>) -> AAnswer {
    match s.step {
        AStep::Start => AAnswer::Fresh,
        AStep::Writing { .. } => AAnswer::Written(tag),
        _ => AAnswer::Done,
    }
}

/// The acts of a commit against a store that serves every call, up to `k` decisions.
pub open spec fn spec_run(s: ASequence, n: ANode, tag: Seq<char>, k: nat) -> (Seq<AAct>, ASequence, ANode)
    decreases k,
{
    if k == 0 || s.step is Over {
        (Seq::empty(), s, n)
    } else {
        match spec_advance(s, n, spec_served(s, tag)) {
            (s2, n2, AOutcome::Act(act)) => {
                let (acts, s3, n3) = spec_run(s2, n2, tag, (k - 1) as nat);
                (seq![act] + acts, s3, n3)
            },
            (s2, n2, AOutcome::Failed(_)) => (Seq::empty(), s2, n2),
        }
    }
}

/// The key a commit arms, if it arms one.
pub open spec fn spec_arms(s: ASequence) -> Option<AKey> {
    match s.plan.deadline {
        Some(at) if s.changed && s.plan.rearm => Some(AKey { origin: s.origin, at, token: s.token }),
        _ => None,
    }
}

/// The plan once the key is armed.
pub open spec fn spec_plan_after(s: ASequence) -> ACommit {
    match spec_arms(s) {
        Some(key) => spec_armed(s.plan, key),
        None => s.plan,
    }
}

/// The calls a commit makes, in order, against a store that serves every
/// call: the key armed, the document written under the version loaded, the
/// key replaced removed, the key fired collected.
pub open spec fn spec_calls(s: ASequence, n: ANode) -> Seq<AAct> {
    let arm = match spec_arms(s) { Some(key) => seq![AAct::PutKey(key)], None => Seq::empty() };
    let write = if s.changed || s.fired is Some { seq![AAct::Write { cond: s.etag, idle: !s.changed }] } else { Seq::empty() };
    let disarm = match spec_to_disarm(spec_plan_after(s)) {
        Some(previous) if s.changed => seq![AAct::DeleteKey { key: previous, by: n.id }],
        _ => Seq::empty(),
    };
    let collect = match s.fired {
        Some(f) => seq![AAct::DeleteKey { key: f.key, by: f.by }],
        None => Seq::empty(),
    };
    let done = seq![AAct::Done { deleted: s.fired is Some }];
    arm + write + disarm + collect + done
}

/// The node once the commit is over: the key kept is remembered with the
/// version written, and the fired key, if it was the one remembered, forgotten.
pub open spec fn spec_node_after(s: ASequence, n: ANode, tag: Seq<char>) -> ANode {
    let n = if s.changed { spec_finish(n, spec_plan_after(s), tag) } else { n };
    match s.fired {
        Some(f) => spec_collected(n, s.origin, f.key),
        None => n,
    }
}

/// The sequence: from `Start`, against a store that serves every call, a
/// commit makes exactly `spec_calls`, in that order, and leaves the node as
/// `spec_node_after`.
pub proof fn lemma_sequence(s: ASequence, n: ANode, tag: Seq<char>)
    requires
        s.step is Start,
    ensures
        ({
            let (acts, last, after) = spec_run(s, n, tag, 6);
            &&& acts == spec_calls(s, n)
            &&& last.step is Over
            &&& after == spec_node_after(s, n, tag)
        }),
{
    let (acts, last, after) = spec_run(s, n, tag, 6);
    lemma_sequence_cases(s, n, tag);
}

proof fn lemma_sequence_cases(s: ASequence, n: ANode, tag: Seq<char>)
    requires
        s.step is Start,
    ensures
        spec_run(s, n, tag, 6).0 == spec_calls(s, n),
        spec_run(s, n, tag, 6).1.step is Over,
        spec_run(s, n, tag, 6).2 == spec_node_after(s, n, tag),
{
    reveal_with_fuel(spec_run, 7);
    let e = Seq::<AAct>::empty();
    if s.changed {
        let (s1, n1, o1) = spec_advance(s, n, AAnswer::Fresh);
        match spec_arms(s) {
            Some(key) => {
                assert(o1 == AOutcome::Act(AAct::PutKey(key)));
                let (s2, n2, o2) = spec_advance(s1, n1, AAnswer::Done);
                assert(s2.plan == spec_armed(s.plan, key));
                lemma_written(s2, n2, tag);
                let (acts, last, after) = spec_run(s2, n2, tag, 4);
                assert(spec_run(s, n, tag, 6).0 =~= seq![AAct::PutKey(key)] + (seq![AAct::Write { cond: s.etag, idle: false }] + acts));
                assert(spec_calls(s, n) =~= seq![AAct::PutKey(key)] + (seq![AAct::Write { cond: s.etag, idle: false }] + acts));
            },
            None => {
                assert(o1 == AOutcome::Act(AAct::Write { cond: s.etag, idle: false }));
                lemma_written(s1, n1, tag);
                let (acts, last, after) = spec_run(s1, n1, tag, 5);
                assert(spec_run(s, n, tag, 6).0 =~= seq![AAct::Write { cond: s.etag, idle: false }] + acts);
                assert(spec_calls(s, n) =~= seq![AAct::Write { cond: s.etag, idle: false }] + acts);
            },
        }
    } else if s.fired is Some {
        let f = s.fired->Some_0;
        let (s1, n1, o1) = spec_advance(s, n, AAnswer::Fresh);
        assert(o1 == AOutcome::Act(AAct::Write { cond: s.etag, idle: true }));
        let (s2, n2, o2) = spec_advance(s1, n1, AAnswer::Written(tag));
        assert(o2 == AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }));
        assert(n2 == spec_collected(n, s.origin, f.key));
        let (s3, n3, o3) = spec_advance(s2, n2, AAnswer::Done);
        assert(o3 == AOutcome::Act(AAct::Done { deleted: true }));
        assert(spec_run(s, n, tag, 6).0 =~= seq![AAct::Write { cond: s.etag, idle: true }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
        assert(spec_calls(s, n) =~= seq![AAct::Write { cond: s.etag, idle: true }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
    } else {
        let (s1, n1, o1) = spec_advance(s, n, AAnswer::Fresh);
        assert(o1 == AOutcome::Act(AAct::Done { deleted: false }));
        assert(spec_run(s, n, tag, 6).0 =~= seq![AAct::Done { deleted: false }]);
        assert(spec_calls(s, n) =~= seq![AAct::Done { deleted: false }]);
    }
}

/// From `Writing { idle: false }` on, with `plan` the plan the write runs
/// under: the key replaced is removed, the kept key remembered, the fired
/// key collected.
proof fn lemma_written(s: ASequence, n: ANode, tag: Seq<char>)
    requires
        s.step == (AStep::Writing { idle: false }),
        s.changed,
    ensures
        ({
            let disarm = match spec_to_disarm(s.plan) {
                Some(previous) => seq![AAct::DeleteKey { key: previous, by: n.id }],
                None => Seq::<AAct>::empty(),
            };
            let collect = match s.fired {
                Some(f) => seq![AAct::DeleteKey { key: f.key, by: f.by }],
                None => Seq::<AAct>::empty(),
            };
            let after = match s.fired {
                Some(f) => spec_collected(spec_finish(n, s.plan, tag), s.origin, f.key),
                None => spec_finish(n, s.plan, tag),
            };
            &&& spec_run(s, n, tag, 4).0 == disarm + collect + seq![AAct::Done { deleted: s.fired is Some }]
            &&& spec_run(s, n, tag, 5).0 == spec_run(s, n, tag, 4).0
            &&& spec_run(s, n, tag, 4).1.step is Over
            &&& spec_run(s, n, tag, 5).1.step is Over
            &&& spec_run(s, n, tag, 4).2 == after
            &&& spec_run(s, n, tag, 5).2 == after
        }),
{
    reveal_with_fuel(spec_run, 6);
    let (s1, n1, o1) = spec_advance(s, n, AAnswer::Written(tag));
    assert(s1.etag == Some(tag));
    match spec_to_disarm(s.plan) {
        Some(previous) => {
            assert(o1 == AOutcome::Act(AAct::DeleteKey { key: previous, by: n.id }));
            let (s2, n2, o2) = spec_advance(s1, n1, AAnswer::Done);
            assert(n2 == spec_finish(n, s.plan, tag) || s.fired is Some);
            match s.fired {
                Some(f) => {
                    assert(o2 == AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }));
                    let (s3, n3, o3) = spec_advance(s2, n2, AAnswer::Done);
                    assert(o3 == AOutcome::Act(AAct::Done { deleted: true }));
                    assert(spec_run(s, n, tag, 4).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(spec_run(s, n, tag, 5).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(seq![AAct::DeleteKey { key: previous, by: n.id }] + seq![AAct::DeleteKey { key: f.key, by: f.by }] + seq![AAct::Done { deleted: true }] =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                },
                None => {
                    assert(o2 == AOutcome::Act(AAct::Done { deleted: false }));
                    assert(spec_run(s, n, tag, 4).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::Done { deleted: false }]);
                    assert(spec_run(s, n, tag, 5).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::Done { deleted: false }]);
                    assert(seq![AAct::DeleteKey { key: previous, by: n.id }] + Seq::<AAct>::empty() + seq![AAct::Done { deleted: false }] =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::Done { deleted: false }]);
                },
            }
        },
        None => {
            match s.fired {
                Some(f) => {
                    assert(o1 == AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }));
                    assert(n1 == spec_collected(spec_finish(n, s.plan, tag), s.origin, f.key));
                    let (s2, n2, o2) = spec_advance(s1, n1, AAnswer::Done);
                    assert(o2 == AOutcome::Act(AAct::Done { deleted: true }));
                    assert(spec_run(s, n, tag, 4).0 =~= seq![AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(spec_run(s, n, tag, 5).0 =~= seq![AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(Seq::<AAct>::empty() + seq![AAct::DeleteKey { key: f.key, by: f.by }] + seq![AAct::Done { deleted: true }] =~= seq![AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                },
                None => {
                    assert(o1 == AOutcome::Act(AAct::Done { deleted: false }));
                    assert(n1 == spec_finish(n, s.plan, tag));
                    assert(spec_run(s, n, tag, 4).0 =~= seq![AAct::Done { deleted: false }]);
                    assert(spec_run(s, n, tag, 5).0 =~= seq![AAct::Done { deleted: false }]);
                    assert(Seq::<AAct>::empty() + Seq::<AAct>::empty() + seq![AAct::Done { deleted: false }] =~= seq![AAct::Done { deleted: false }]);
                },
            }
        },
    }
}

} // verus!
