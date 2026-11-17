//! property_proof definitions for the concrete model.
#![allow(unused_imports)]
use vstd::prelude::*;
use crate::state::ProductionTargetData;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
use crate::state::{ChangeV, PartialV, FoldedV, DocumentBodyV, Message, Proc, NoteV, JobV, FlightV, CachedV, NodeV, Etag, StoreReq, StoreRes, EntryV, StoreV};
use crate::state::{ProductionPromiseData, ProductionTaskData, ProductionObjectData, ProductionDocumentData, ProductionDebugData, ProductionAnswerData, ProductionDispatchData, ProductionEffectData, ProductionNoteData};
#[cfg(verus_keep_ghost)]
use crate::handler::{on_event, spec_apply_changes, spec_apply_document, spec_compose, spec_string, spec_bytes, spec_node, spec_store, spec_note_key, spec_note_relevant, spec_keyed_notes, spec_encode_body, spec_read, spec_owns, spec_cached, spec_body_is_empty, spec_keep, spec_remember, spec_forget, spec_request, spec_timeout, spec_store_reply, spec_flight, spec_begin, spec_decide, spec_commit, spec_origin_key, spec_empty_body, spec_key, spec_handle, spec_run_due, spec_occurrence, spec_min_key, least_key, spec_sorted, spec_earliest_key, spec_earliest_from, spec_earliest_in, spec_utf8_ok, spec_prefix, spec_etag, spec_find, spec_insert_at, spec_before, spec_put, spec_remove_at, spec_bump, spec_apply};
use crate::rover::{Pid, Config, spec_nodes, spec_initial_node, spec_world};
#[cfg(verus_keep_ghost)]
use crate::property_claim::{keys_strictly_sorted, document_object_order, document_keys_unique, document_key_ownership, store_entries_ordered, store_entries_unique, store_versions_positive, process_layout, state_properties, transition_properties, step_properties, property_claim};
use rover_spec::rover::comm::Time;

use crate::state::{AKey, AArmed, AEntry, ANode, ACommit, AJob, AFired, AStep, ASequence, AAct, AAnswer, AOutcome};
use crate::handler::{spec_production_owner, spec_production_fresh, spec_production_acts, spec_production_read_config, spec_production_filled, spec_production_forget, spec_production_set_armed, spec_production_collected, spec_production_prepare, spec_production_armed, spec_production_to_disarm, spec_production_keep, spec_production_finish, production_opt_nat, production_opt_str, spec_production_step, production_job_of, production_answer_v, spec_production_new, spec_production_collect, spec_production_advance, spec_production_served, spec_production_run, spec_production_arms, spec_production_plan_after, spec_production_calls, spec_production_node_after};
use crate::state::ProductionCacheEntryV;
use crate::handler::spec_production_cache_find;
verus! {
pub proof fn lemma_production_lift_target_actual(data: ProductionTargetData)
    ensures crate::handler::production_lift_target(data.deep_view()) == data,
{
    assert(exists|x: ProductionTargetData| x.deep_view() == data.deep_view());
    let chosen = crate::handler::production_lift_target(data.deep_view());
    match (chosen, data) {
        (ProductionTargetData::Origin(a), ProductionTargetData::Origin(b)) |
        (ProductionTargetData::Schedule(a), ProductionTargetData::Schedule(b)) => axiom_string_ext(a, b),
        _ => {},
    }
}

pub proof fn lemma_production_opt_string_ext(a: Option<String>, b: Option<String>)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    if let (Some(x), Some(y)) = (a, b) { axiom_string_ext(x, y); }
}

pub proof fn lemma_production_strings_ext(a: Vec<String>, b: Vec<String>)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    assert(a.deep_view().len() == a@.len());
    assert(b.deep_view().len() == b@.len());
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] a[i] == b[i] by {
        assert(a.deep_view()[i] == a[i]@);
        assert(b.deep_view()[i] == b[i]@);
        axiom_string_ext(a[i], b[i]);
    }
    assert(a@ =~= b@);
    axiom_vec_ext(a, b);
}

pub proof fn lemma_production_schedule_ext(a: Schedule, b: Schedule)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    axiom_string_ext(a.id, b.id);
    axiom_string_ext(a.cron, b.cron);
    axiom_string_ext(a.promise_id, b.promise_id);
    lemma_value_ext(a.promise_param, b.promise_param);
    lemma_tags_ext(a.promise_tags, b.promise_tags);
}

pub proof fn lemma_production_record_ext(a: PromiseRecord, b: PromiseRecord)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    axiom_string_ext(a.id, b.id);
    lemma_value_ext(a.param, b.param);
    lemma_value_ext(a.value, b.value);
    lemma_tags_ext(a.tags, b.tags);
}

pub proof fn lemma_production_opt_record_ext(a: Option<PromiseRecord>, b: Option<PromiseRecord>)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    if let (Some(x), Some(y)) = (a, b) { lemma_production_record_ext(x, y); }
}

pub proof fn lemma_production_opt_task_ext(a: Option<TaskRecord>, b: Option<TaskRecord>)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    if let (Some(x), Some(y)) = (a, b) {
        axiom_string_ext(x.id, y.id);
        lemma_production_opt_string_ext(x.pid, y.pid);
    }
}

pub proof fn lemma_production_response_ext(a: Response, b: Response)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    match (a, b) {
        (Response::Promise(x), Response::Promise(y)) => lemma_production_opt_record_ext(x.promise, y.promise),
        (Response::Schedule(x), Response::Schedule(y)) => {
            if let (Some(x), Some(y)) = (x.schedule, y.schedule) { lemma_production_schedule_ext(x, y); }
        },
        (Response::TaskGet(x), Response::TaskGet(y)) => lemma_production_opt_task_ext(x.task, y.task),
        (Response::TaskClaim(x), Response::TaskClaim(y)) => {
            lemma_production_opt_task_ext(x.task, y.task);
            lemma_production_opt_record_ext(x.promise, y.promise);
        },
        (Response::TaskFence(x), Response::TaskFence(y)) => {
            match (x.action, y.action) {
                (Some(TaskFenceInnerRes::Create(p)), Some(TaskFenceInnerRes::Create(q))) |
                (Some(TaskFenceInnerRes::Settle(p)), Some(TaskFenceInnerRes::Settle(q))) =>
                    lemma_production_opt_record_ext(p.promise, q.promise),
                _ => {},
            }
        },
        _ => {},
    }
}

pub proof fn lemma_production_object_ext(a: ProductionObjectData, b: ProductionObjectData)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    lemma_production_strings_ext(a.promise.callbacks, b.promise.callbacks);
    lemma_production_strings_ext(a.promise.listeners, b.promise.listeners);
    if let (Some(x), Some(y)) = (a.task, b.task) {
        lemma_production_opt_string_ext(x.pid, y.pid);
        lemma_production_strings_ext(x.resumes, y.resumes);
    }
}

pub proof fn lemma_production_document_ext(a: ProductionDocumentData, b: ProductionDocumentData)
    requires
        a.deep_view() == b.deep_view(),
        crate::property_claim::production_document_canonical(a),
        crate::property_claim::production_document_canonical(b),
    ensures a == b,
{
    match (a, b) {
        (ProductionDocumentData::Workflow(x), ProductionDocumentData::Workflow(y)) => {
            let xm = crate::handler::production_document_data_rows(x.deep_view());
            let ym = crate::handler::production_document_data_rows(y.deep_view());
            assert(xm == ym);
            let xk = x@.map_values(|e: (String, ProductionObjectData)| e.0@);
            let yk = y@.map_values(|e: (String, ProductionObjectData)| e.0@);
            assert(xk == crate::handler::spec_sorted_present(xm));
            assert(yk == crate::handler::spec_sorted_present(ym));
            assert(xk == yk);
            assert(x.len() == y.len());
            assert forall|i: int| 0 <= i < x.len() implies #[trigger] x[i] == y[i] by {
                assert(xk[i] == x[i].0@);
                assert(yk[i] == y[i].0@);
                assert(xm[x[i].0@] == x[i].1.deep_view());
                assert(ym[y[i].0@] == y[i].1.deep_view());
                axiom_string_ext(x[i].0, y[i].0);
                lemma_production_object_ext(x[i].1, y[i].1);
            }
            assert(x@ =~= y@);
            axiom_vec_ext(x, y);
        },
        (ProductionDocumentData::Schedule(x), ProductionDocumentData::Schedule(y)) => {},
        _ => {},
    }
}

pub proof fn lemma_production_debug_ext(a: ProductionDebugData, b: ProductionDebugData)
    requires
        a.deep_view() == b.deep_view(),
        crate::property_claim::production_debug_canonical(a),
        crate::property_claim::production_debug_canonical(b),
    ensures a == b,
{
    match (a, b) {
        (ProductionDebugData::Message(x), ProductionDebugData::Message(y)) => axiom_string_ext(x, y),
        (ProductionDebugData::Snap { origins: x, schedules: s }, ProductionDebugData::Snap { origins: y, schedules: t }) => {
            assert(x.deep_view() == y.deep_view());
            assert(x.deep_view().len() == x.len());
            assert(y.deep_view().len() == y.len());
            assert forall|i: int| 0 <= i < x.len() implies #[trigger] x[i] == y[i] by {
                assert(x.deep_view()[i] == x[i].deep_view());
                assert(y.deep_view()[i] == y[i].deep_view());
                lemma_production_document_ext(x[i], y[i]);
            }
            assert(x@ =~= y@);
            axiom_vec_ext(x, y);
            assert(s.deep_view() == t.deep_view());
            assert(s.deep_view().len() == s.len());
            assert(t.deep_view().len() == t.len());
            assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] == t[i] by {
                assert(s.deep_view()[i] == s[i].deep_view());
                assert(t.deep_view()[i] == t[i].deep_view());
                lemma_production_schedule_ext(s[i], t[i]);
            }
            assert(s@ =~= t@);
            axiom_vec_ext(s, t);
        },
        _ => {},
    }
}

pub proof fn lemma_production_store_request_ext(a: StoreReq, b: StoreReq)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    match (a, b) {
        (StoreReq::GetIfNoneMatch { etag: x, .. }, StoreReq::GetIfNoneMatch { etag: y, .. }) |
        (StoreReq::PutIfMatch { etag: x, .. }, StoreReq::PutIfMatch { etag: y, .. }) |
        (StoreReq::AppIfMatch { etag: x, .. }, StoreReq::AppIfMatch { etag: y, .. }) =>
            axiom_string_ext(x.0, y.0),
        _ => {},
    }
    match (a, b) {
        (StoreReq::Get { key: x }, StoreReq::Get { key: y }) |
        (StoreReq::Del { key: x }, StoreReq::Del { key: y }) |
        (StoreReq::GetIfNoneMatch { key: x, .. }, StoreReq::GetIfNoneMatch { key: y, .. }) |
        (StoreReq::List { prefix: x, .. }, StoreReq::List { prefix: y, .. }) |
        (StoreReq::ListPrefixes { prefix: x }, StoreReq::ListPrefixes { prefix: y }) => axiom_string_ext(x, y),
        (StoreReq::Put { key: x, body: p }, StoreReq::Put { key: y, body: q }) |
        (StoreReq::PutIfMatch { key: x, body: p, .. }, StoreReq::PutIfMatch { key: y, body: q, .. }) |
        (StoreReq::PutIfNoneMatch { key: x, body: p }, StoreReq::PutIfNoneMatch { key: y, body: q }) |
        (StoreReq::AppIfMatch { key: x, body: p, .. }, StoreReq::AppIfMatch { key: y, body: q, .. }) => {
            axiom_string_ext(x, y);
            axiom_vec_ext(p, q);
        },
        _ => {},
    }
}

pub proof fn lemma_production_note_ext(a: ProductionNoteData, b: ProductionNoteData)
    requires a.deep_view() == b.deep_view(),
    ensures a == b,
{
    match (a, b) {
        (ProductionNoteData::SweepBegin { target: x, .. }, ProductionNoteData::SweepBegin { target: y, .. }) |
        (ProductionNoteData::AdvanceBegin { schedule: x, .. }, ProductionNoteData::AdvanceBegin { schedule: y, .. }) |
        (ProductionNoteData::Raced { target: x, .. }, ProductionNoteData::Raced { target: y, .. }) |
        (ProductionNoteData::KeyUnparseable { key: x }, ProductionNoteData::KeyUnparseable { key: y }) |
        (ProductionNoteData::RefreshFailed { error: x }, ProductionNoteData::RefreshFailed { error: y }) |
        (ProductionNoteData::ListingFailed { error: x }, ProductionNoteData::ListingFailed { error: y }) |
        (ProductionNoteData::MessageUndeliverable { address: x }, ProductionNoteData::MessageUndeliverable { address: y }) =>
            axiom_string_ext(x, y),
        (ProductionNoteData::FireBegin { origin: x, promise_id: p, row: r, .. }, ProductionNoteData::FireBegin { origin: y, promise_id: q, row: s, .. }) => {
            axiom_string_ext(x, y);
            axiom_string_ext(p, q);
            lemma_production_schedule_ext(*r, *s);
        },
        (ProductionNoteData::ConfigurationRead { members: x, .. }, ProductionNoteData::ConfigurationRead { members: y, .. }) |
        (ProductionNoteData::ConfigurationWritten { members: x, .. }, ProductionNoteData::ConfigurationWritten { members: y, .. }) =>
            lemma_production_strings_ext(x, y),
        (ProductionNoteData::KeyNotDeleted { key: x, error: p }, ProductionNoteData::KeyNotDeleted { key: y, error: q }) |
        (ProductionNoteData::FireFailed { key: x, error: p }, ProductionNoteData::FireFailed { key: y, error: q }) => {
            axiom_string_ext(x, y);
            axiom_string_ext(p, q);
        },
        _ => {},
    }
}

pub proof fn lemma_production_effect_ext(a: ProductionEffectData, b: ProductionEffectData)
    requires
        a.deep_view() == b.deep_view(),
        crate::property_claim::production_effect_canonical(a),
        crate::property_claim::production_effect_canonical(b),
    ensures a == b,
{
    match (a, b) {
        (ProductionEffectData::Reply { response: x, .. }, ProductionEffectData::Reply { response: y, .. }) => {
            match (x, y) {
                (Err(x), Err(y)) => axiom_string_ext(x, y),
                (Ok(ProductionAnswerData::Step { kind: k, corr: c, action_kind: a, response: r, why: w }),
                 Ok(ProductionAnswerData::Step { kind: l, corr: d, action_kind: b, response: s, why: z })) => {
                    axiom_string_ext(k, l); axiom_string_ext(c, d);
                    lemma_production_opt_string_ext(a, b); lemma_production_opt_string_ext(w, z);
                    lemma_production_response_ext(r, s);
                },
                (Ok(ProductionAnswerData::Debug { kind: k, corr: c, body: r, .. }),
                 Ok(ProductionAnswerData::Debug { kind: l, corr: d, body: s, .. })) => {
                    axiom_string_ext(k, l); axiom_string_ext(c, d);
                    lemma_production_debug_ext(r, s);
                },
                _ => {},
            }
        },
        (ProductionEffectData::Store { request: x, .. }, ProductionEffectData::Store { request: y, .. }) =>
            lemma_production_store_request_ext(x, y),
        (ProductionEffectData::Send { address: x, message: p }, ProductionEffectData::Send { address: y, message: q }) => {
            axiom_string_ext(x, y);
            match (p, q) {
                (ProductionDispatchData::Execute { task_id: x, .. }, ProductionDispatchData::Execute { task_id: y, .. }) => axiom_string_ext(x, y),
                (ProductionDispatchData::Unblock(x), ProductionDispatchData::Unblock(y)) => lemma_production_record_ext(x, y),
                _ => {},
            }
        },
        (ProductionEffectData::Note(x), ProductionEffectData::Note(y)) => lemma_production_note_ext(x, y),
        _ => {},
    }
}

pub proof fn lemma_production_lift_actual(data: ProductionEffectData)
    requires crate::property_claim::production_effect_canonical(data),
    ensures crate::handler::production_lift_effect(data.deep_view()) == data,
{
    assert(exists|x: ProductionEffectData| x.deep_view() == data.deep_view()
        && crate::property_claim::production_effect_canonical(x));
    let chosen = crate::handler::production_lift_effect(data.deep_view());
    lemma_production_effect_ext(chosen, data);
}

pub proof fn lemma_production_replay_prefix(
    config: crate::state::ProductionConfigV,
    loops: bool,
    left: Seq<crate::state::ProductionEventV>,
    right: Seq<crate::state::ProductionEventV>,
    count: nat,
)
    requires count <= left.len(), count <= right.len(), left.take(count as int) == right.take(count as int),
    ensures crate::handler::production_replay_state(config, loops, left, count)
        == crate::handler::production_replay_state(config, loops, right, count),
    decreases count,
{
    if count > 0 {
        assert(left.take((count - 1) as int) =~= right.take((count - 1) as int));
        assert(left.take(count as int)[count - 1] == left[count - 1]);
        assert(right.take(count as int)[count - 1] == right[count - 1]);
        assert(left[count - 1] == right[count - 1]);
        lemma_production_replay_prefix(config, loops, left, right, (count - 1) as nat);
    }
}

pub proof fn lemma_production_cache_find_step(entries: Seq<ProductionCacheEntryV>, origin: Seq<char>, i: int)
    requires
        0 <= i <= entries.len(),
        forall|j: int| 0 <= j < i ==> entries[j].origin != origin,
    ensures
        spec_production_cache_find(entries, origin) == match spec_production_cache_find(entries.skip(i), origin) {
            Some(k) => Some(k + i),
            None => None::<int>,
        },
    decreases i,
{
    if i == 0 {
        assert(entries.skip(0) =~= entries);
    } else {
        lemma_production_cache_find_step(entries, origin, i - 1);
        assert(entries.skip(i - 1).drop_first() =~= entries.skip(i));
        assert(entries.skip(i - 1)[0] == entries[i - 1]);
    }
}


pub proof fn lemma_production_step_is_decide(node: NodeV, flight: FlightV, doc: DocumentBodyV, limit: nat)
    requires
        !(flight.job is External),
    ensures
        ({
            let (next, reply, born, notify) = spec_production_step(production_job_of(flight.job), doc, flight.now, node.retry_timeout, limit);
            let (after, sent) = spec_decide(node, flight, doc);
            match after.flight {
                Some(open) => {
                    &&& open.writing
                    &&& open.decided == Some(spec_encode_body(next))
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
                Some(chars) => crate::property_proof::lemma_string_realised(chars),
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

pub proof fn lemma_production_sequence(s: ASequence, n: ANode, tag: Seq<char>)
    requires
        s.step is Start,
    ensures
        ({
            let (acts, last, after) = spec_production_run(s, n, tag, 6);
            &&& acts == spec_production_calls(s, n)
            &&& last.step is Over
            &&& after == spec_production_node_after(s, n, tag)
        }),
{
    let (acts, last, after) = spec_production_run(s, n, tag, 6);
    lemma_production_sequence_cases(s, n, tag);
}


#[verifier::rlimit(20)]
proof fn lemma_production_sequence_cases(s: ASequence, n: ANode, tag: Seq<char>)
    requires
        s.step is Start,
    ensures
        spec_production_run(s, n, tag, 6).0 == spec_production_calls(s, n),
        spec_production_run(s, n, tag, 6).1.step is Over,
        spec_production_run(s, n, tag, 6).2 == spec_production_node_after(s, n, tag),
{
    reveal_with_fuel(spec_production_run, 7);
    let e = Seq::<AAct>::empty();
    if s.changed {
        let (s1, n1, o1) = spec_production_advance(s, n, AAnswer::Fresh);
        match spec_production_arms(s) {
            Some(key) => {
                assert(o1 == AOutcome::Act(AAct::PutKey(key)));
                let (s2, n2, o2) = spec_production_advance(s1, n1, AAnswer::Done);
                assert(s2.plan == spec_production_armed(s.plan, key));
                lemma_production_written(s2, n2, tag);
                let (acts, last, after) = spec_production_run(s2, n2, tag, 4);
                assert(spec_production_run(s, n, tag, 6).0 =~= seq![AAct::PutKey(key)] + (seq![AAct::Write { cond: s.etag, idle: false }] + acts));
                assert(spec_production_calls(s, n) =~= seq![AAct::PutKey(key)] + (seq![AAct::Write { cond: s.etag, idle: false }] + acts));
            },
            None => {
                assert(o1 == AOutcome::Act(AAct::Write { cond: s.etag, idle: false }));
                lemma_production_written(s1, n1, tag);
                let (acts, last, after) = spec_production_run(s1, n1, tag, 5);
                assert(spec_production_run(s, n, tag, 6).0 =~= seq![AAct::Write { cond: s.etag, idle: false }] + acts);
                assert(spec_production_calls(s, n) =~= seq![AAct::Write { cond: s.etag, idle: false }] + acts);
            },
        }
    } else if s.fired is Some {
        let f = s.fired->Some_0;
        let (s1, n1, o1) = spec_production_advance(s, n, AAnswer::Fresh);
        assert(o1 == AOutcome::Act(AAct::Write { cond: s.etag, idle: true }));
        let (s2, n2, o2) = spec_production_advance(s1, n1, AAnswer::Written(tag));
        assert(o2 == AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }));
        assert(n2 == spec_production_collected(n, s.origin, f.key));
        let (s3, n3, o3) = spec_production_advance(s2, n2, AAnswer::Done);
        assert(o3 == AOutcome::Act(AAct::Done { deleted: true }));
        assert(spec_production_run(s, n, tag, 6).0 =~= seq![AAct::Write { cond: s.etag, idle: true }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
        assert(spec_production_calls(s, n) =~= seq![AAct::Write { cond: s.etag, idle: true }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
    } else {
        let (s1, n1, o1) = spec_production_advance(s, n, AAnswer::Fresh);
        assert(o1 == AOutcome::Act(AAct::Done { deleted: false }));
        assert(spec_production_run(s, n, tag, 6).0 =~= seq![AAct::Done { deleted: false }]);
        assert(spec_production_calls(s, n) =~= seq![AAct::Done { deleted: false }]);
    }
}

/// From `Writing { idle: false }` on, with `plan` the plan the write runs
/// under: the key replaced is removed, the kept key remembered, the fired
/// key collected.

proof fn lemma_production_written(s: ASequence, n: ANode, tag: Seq<char>)
    requires
        s.step == (AStep::Writing { idle: false }),
        s.changed,
    ensures
        ({
            let disarm = match spec_production_to_disarm(s.plan) {
                Some(previous) => seq![AAct::DeleteKey { key: previous, by: n.id }],
                None => Seq::<AAct>::empty(),
            };
            let collect = match s.fired {
                Some(f) => seq![AAct::DeleteKey { key: f.key, by: f.by }],
                None => Seq::<AAct>::empty(),
            };
            let after = match s.fired {
                Some(f) => spec_production_collected(spec_production_finish(n, s.plan, tag), s.origin, f.key),
                None => spec_production_finish(n, s.plan, tag),
            };
            &&& spec_production_run(s, n, tag, 4).0 == disarm + collect + seq![AAct::Done { deleted: s.fired is Some }]
            &&& spec_production_run(s, n, tag, 5).0 == spec_production_run(s, n, tag, 4).0
            &&& spec_production_run(s, n, tag, 4).1.step is Over
            &&& spec_production_run(s, n, tag, 5).1.step is Over
            &&& spec_production_run(s, n, tag, 4).2 == after
            &&& spec_production_run(s, n, tag, 5).2 == after
        }),
{
    reveal_with_fuel(spec_production_run, 6);
    let (s1, n1, o1) = spec_production_advance(s, n, AAnswer::Written(tag));
    assert(s1.etag == Some(tag));
    match spec_production_to_disarm(s.plan) {
        Some(previous) => {
            assert(o1 == AOutcome::Act(AAct::DeleteKey { key: previous, by: n.id }));
            let (s2, n2, o2) = spec_production_advance(s1, n1, AAnswer::Done);
            assert(n2 == spec_production_finish(n, s.plan, tag) || s.fired is Some);
            match s.fired {
                Some(f) => {
                    assert(o2 == AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }));
                    let (s3, n3, o3) = spec_production_advance(s2, n2, AAnswer::Done);
                    assert(o3 == AOutcome::Act(AAct::Done { deleted: true }));
                    assert(spec_production_run(s, n, tag, 4).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(spec_production_run(s, n, tag, 5).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(seq![AAct::DeleteKey { key: previous, by: n.id }] + seq![AAct::DeleteKey { key: f.key, by: f.by }] + seq![AAct::Done { deleted: true }] =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                },
                None => {
                    assert(o2 == AOutcome::Act(AAct::Done { deleted: false }));
                    assert(spec_production_run(s, n, tag, 4).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::Done { deleted: false }]);
                    assert(spec_production_run(s, n, tag, 5).0 =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::Done { deleted: false }]);
                    assert(seq![AAct::DeleteKey { key: previous, by: n.id }] + Seq::<AAct>::empty() + seq![AAct::Done { deleted: false }] =~= seq![AAct::DeleteKey { key: previous, by: n.id }, AAct::Done { deleted: false }]);
                },
            }
        },
        None => {
            match s.fired {
                Some(f) => {
                    assert(o1 == AOutcome::Act(AAct::DeleteKey { key: f.key, by: f.by }));
                    assert(n1 == spec_production_collected(spec_production_finish(n, s.plan, tag), s.origin, f.key));
                    let (s2, n2, o2) = spec_production_advance(s1, n1, AAnswer::Done);
                    assert(o2 == AOutcome::Act(AAct::Done { deleted: true }));
                    assert(spec_production_run(s, n, tag, 4).0 =~= seq![AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(spec_production_run(s, n, tag, 5).0 =~= seq![AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                    assert(Seq::<AAct>::empty() + seq![AAct::DeleteKey { key: f.key, by: f.by }] + seq![AAct::Done { deleted: true }] =~= seq![AAct::DeleteKey { key: f.key, by: f.by }, AAct::Done { deleted: true }]);
                },
                None => {
                    assert(o1 == AOutcome::Act(AAct::Done { deleted: false }));
                    assert(n1 == spec_production_finish(n, s.plan, tag));
                    assert(spec_production_run(s, n, tag, 4).0 =~= seq![AAct::Done { deleted: false }]);
                    assert(spec_production_run(s, n, tag, 5).0 =~= seq![AAct::Done { deleted: false }]);
                    assert(Seq::<AAct>::empty() + Seq::<AAct>::empty() + seq![AAct::Done { deleted: false }] =~= seq![AAct::Done { deleted: false }]);
                },
            }
        },
    }
}


pub proof fn lemma_bulk_notifications_are_unique(
    map: Map<Seq<char>, crate::state::ObjV>,
    now: Time,
    retry_timeout: u64,
)
    requires
        forall|id: Seq<char>| map.contains_key(id) ==> (#[trigger] map[id].promise.listeners).no_duplicates(),
    ensures
        crate::handler::note_effect_keys(crate::handler::spec_bulk_workflow(map, now, retry_timeout).1).no_duplicates(),
{
    lemma_document_object_order(DocumentBodyV::Workflow(map));
    let keys = crate::handler::spec_sorted_present(map);
    assert(keys.no_duplicates());
    assert forall|i: int| 0 <= i < keys.len() implies
        map.contains_key(#[trigger] keys[i]) by {
        assert(keys.contains(keys[i]));
    };
    lemma_projected_offers_are_unique(map, keys, keys.len(), now, retry_timeout);
    lemma_projection_preserves_listeners(map, keys, keys.len(), now, retry_timeout);
    let projected = crate::handler::spec_project_workflow(map, now, retry_timeout);
    let offers = crate::handler::spec_project_offers(map, keys, keys.len(), now);
    assert(projected.dom() == map.dom());
    assert(crate::handler::spec_sorted_present(projected) == keys);
    lemma_callback_keys_preserve_collected_offers(projected, offers, keys, keys.len(), now, retry_timeout);
    let (resumed, callbacks) = crate::handler::spec_drain_callback_keys(projected, keys, keys.len(), now, retry_timeout);
    assert forall|id: Seq<char>| resumed.contains_key(id) implies
        (#[trigger] resumed[id].promise.listeners).no_duplicates() by {
        assert(resumed[id].promise.listeners == projected[id].promise.listeners);
        assert(projected[id].promise.listeners == map[id].promise.listeners);
    };
    lemma_listener_pass_is_unique(resumed, keys, keys.len());
    let (_, listeners) = crate::handler::spec_drain_listener_keys(resumed, keys, keys.len());
    let left = offers + callbacks;
    let all = left + listeners;
    let left_keys = crate::handler::note_effect_keys(left);
    let right_keys = crate::handler::note_effect_keys(listeners);
    let all_keys = crate::handler::note_effect_keys(all);
    assert(all_keys =~= left_keys + right_keys);
    assert forall|i: int, j: int| 0 <= i < j < all_keys.len() implies
        #[trigger] all_keys[i] != #[trigger] all_keys[j] by {
        if j < left.len() {
            assert(left_keys[i] != left_keys[j]);
        } else if i >= left.len() {
            assert(right_keys[i - left.len()] != right_keys[j - left.len()]);
        } else {
            assert(left[i] is Execute);
            assert(listeners[j - left.len()] is Unblock);
        }
    };
    assert(crate::handler::spec_bulk_workflow(map, now, retry_timeout).1 =~= all);
}

pub proof fn lemma_projection_preserves_listeners(
    map: Map<Seq<char>, crate::state::ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires count <= keys.len(),
    ensures
        ({
            let next = crate::handler::spec_project_keys(map, keys, count, now, retry_timeout);
            &&& next.dom() == map.dom()
            &&& forall|id: Seq<char>| map.contains_key(id) ==>
                #[trigger] next[id].promise.listeners == map[id].promise.listeners
        }),
    decreases count,
{
    if count > 0 {
        lemma_projection_preserves_listeners(map, keys, (count - 1) as nat, now, retry_timeout);
        let prior = crate::handler::spec_project_keys(map, keys, (count - 1) as nat, now, retry_timeout);
        let next = crate::handler::spec_project_keys(map, keys, count, now, retry_timeout);
        let key = keys[count as int - 1];
        assert forall|id: Seq<char>| map.contains_key(id) implies
            #[trigger] next[id].promise.listeners == map[id].promise.listeners by {
            assert(prior[id].promise.listeners == map[id].promise.listeners);
            if id != key { assert(next[id] == prior[id]); }
        };
    }
}

pub proof fn lemma_listener_pass_is_unique(
    map: Map<Seq<char>, crate::state::ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
)
    requires
        count <= keys.len(),
        keys.no_duplicates(),
        forall|id: Seq<char>| map.contains_key(id) ==> (#[trigger] map[id].promise.listeners).no_duplicates(),
    ensures
        ({
            let (next, notes) = crate::handler::spec_drain_listener_keys(map, keys, count);
            &&& next.dom() == map.dom()
            &&& crate::handler::note_effect_keys(notes).no_duplicates()
            &&& forall|id: Seq<char>| map.contains_key(id) && !keys.take(count as int).contains(id) ==>
                #[trigger] next[id] == map[id]
            &&& forall|i: int| 0 <= i < notes.len() ==> match #[trigger] notes[i] {
                NoteV::Unblock { promise, .. } => keys.take(count as int).contains(promise.id@),
                _ => false,
            }
        }),
    decreases count,
{
    if count > 0 {
        lemma_listener_pass_is_unique(map, keys, (count - 1) as nat);
        let (prior, collected) = crate::handler::spec_drain_listener_keys(map, keys, (count - 1) as nat);
        let id = keys[count as int - 1];
        assert(!keys.take(count as int - 1).contains(id));
        if map.contains_key(id) { assert(prior[id] == map[id]); }
        lemma_listener_collection_is_unique(prior, id);
        let (next, more) = crate::handler::spec_drain_listeners(prior, id);
        let all = collected + more;
        let left = crate::handler::note_effect_keys(collected);
        let right = crate::handler::note_effect_keys(more);
        let all_keys = crate::handler::note_effect_keys(all);
        assert(all_keys =~= left + right);
        assert forall|i: int, j: int| 0 <= i < j < all_keys.len() implies
            #[trigger] all_keys[i] != #[trigger] all_keys[j] by {
            if j < collected.len() {
                assert(left[i] != left[j]);
            } else if i >= collected.len() {
                assert(right[i - collected.len()] != right[j - collected.len()]);
            } else {
                match collected[i] {
                    NoteV::Unblock { promise, .. } => {
                        assert(keys.take(count as int - 1).contains(promise.id@));
                        assert(promise.id@ != id);
                    },
                    _ => {},
                }
            }
        };
        assert(keys.take(count as int)[count as int - 1] == id);
        assert(keys.take(count as int).contains(id));
        assert forall|other: Seq<char>| map.contains_key(other) && !keys.take(count as int).contains(other) implies
            #[trigger] next[other] == map[other] by {
            if keys.take(count as int - 1).contains(other) {
                let k = choose|k: int| 0 <= k < count as int - 1
                    && #[trigger] keys.take(count as int - 1)[k] == other;
                assert(keys.take(count as int)[k] == other);
                assert(keys.take(count as int).contains(other));
            }
            assert(prior[other] == map[other]);
        };
        assert forall|i: int| 0 <= i < all.len() implies match #[trigger] all[i] {
            NoteV::Unblock { promise, .. } => keys.take(count as int).contains(promise.id@),
            _ => false,
        } by {
            if i < collected.len() {
                match collected[i] {
                    NoteV::Unblock { promise, .. } => {
                        let k = choose|k: int| 0 <= k < count as int - 1
                            && #[trigger] keys.take(count as int - 1)[k] == promise.id@;
                        assert(keys.take(count as int)[k] == promise.id@);
                        assert(keys.take(count as int).contains(promise.id@));
                    },
                    _ => {},
                }
            }
        };
    } else {
        assert(crate::handler::note_effect_keys(Seq::<NoteV>::empty()) =~= Seq::empty());
    }
}

pub proof fn lemma_listener_collection_is_unique(
    map: Map<Seq<char>, crate::state::ObjV>,
    id: Seq<char>,
)
    requires
        map.contains_key(id) ==> map[id].promise.listeners.no_duplicates(),
    ensures
        ({
            let (next, notes) = crate::handler::spec_drain_listeners(map, id);
            &&& next.dom() == map.dom()
            &&& crate::handler::note_effect_keys(notes).no_duplicates()
            &&& forall|i: int| 0 <= i < notes.len() ==> match #[trigger] notes[i] {
                NoteV::Unblock { address, promise } =>
                    promise.id@ == id && map.contains_key(id)
                    && map[id].promise.listeners.contains(address),
                _ => false,
            }
            &&& forall|other: Seq<char>| map.contains_key(other) && other != id ==>
                #[trigger] next[other] == map[other]
        }),
{
    let (next, notes) = crate::handler::spec_drain_listeners(map, id);
    if map.contains_key(id) && map[id].promise.state != PromiseState::Pending {
        lemma_string_realised(id);
        let listeners = map[id].promise.listeners;
        assert(notes.len() == listeners.len());
        assert forall|i: int| 0 <= i < notes.len() implies match #[trigger] notes[i] {
            NoteV::Unblock { address, promise } =>
                promise.id@ == id && map.contains_key(id)
                && map[id].promise.listeners.contains(address),
            _ => false,
        } by {
            assert(listeners.contains(listeners[i]));
        };
        let keys = crate::handler::note_effect_keys(notes);
        assert forall|i: int, j: int| 0 <= i < j < keys.len() implies
            #[trigger] keys[i] != #[trigger] keys[j] by {
            assert(listeners[i] != listeners[j]);
        };
    } else {
        assert(crate::handler::note_effect_keys(notes) =~= Seq::empty());
    }
}

pub proof fn lemma_projected_offers_are_unique(
    map: Map<Seq<char>, crate::state::ObjV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
        keys.no_duplicates(),
        forall|i: int| 0 <= i < keys.len() ==> map.contains_key(#[trigger] keys[i]),
    ensures
        ({
            let next = crate::handler::spec_project_keys(map, keys, count, now, retry_timeout);
            let notes = crate::handler::spec_project_offers(map, keys, count, now);
            &&& next.dom() == map.dom()
            &&& forall|id: Seq<char>| map.contains_key(id) && !keys.take(count as int).contains(id) ==>
                #[trigger] next[id] == map[id]
            &&& crate::property_claim::collected_offers_valid(next, notes)
            &&& forall|i: int| 0 <= i < notes.len() ==> match #[trigger] notes[i] {
                NoteV::Execute { id, .. } => keys.take(count as int).contains(id),
                _ => false,
            }
        }),
    decreases count,
{
    if count == 0 {
        assert(keys.take(0) =~= Seq::<Seq<char>>::empty());
        assert(crate::handler::note_effect_keys(Seq::<NoteV>::empty()) =~= Seq::empty());
    } else {
        lemma_projected_offers_are_unique(map, keys, (count - 1) as nat, now, retry_timeout);
        let prior = crate::handler::spec_project_keys(map, keys, (count - 1) as nat, now, retry_timeout);
        let notes = crate::handler::spec_project_offers(map, keys, (count - 1) as nat, now);
        let id = keys[count as int - 1];
        assert(!keys.take(count as int - 1).contains(id));
        assert(prior[id] == map[id]);
        let projected = crate::handler::spec_project_due_object(prior[id], now, retry_timeout);
        let next = prior.insert(id, projected);
        assert(prior.contains_key(id));
        assert(next == crate::handler::spec_project_keys(map, keys, count, now, retry_timeout));
        assert(next.dom() == map.dom());
        assert(keys.take(count as int) =~= keys.take(count as int - 1).push(id));
        assert(keys.take(count as int).len() == count);
        assert(keys.take(count as int)[count as int - 1] == id);
        assert(keys.take(count as int).contains(id));
        assert forall|other: Seq<char>| map.contains_key(other) && !keys.take(count as int).contains(other) implies
            #[trigger] next[other] == map[other] by {
                assert(other != id);
                if keys.take(count as int - 1).contains(other) {
                    let k = choose|k: int| 0 <= k < count as int - 1
                        && #[trigger] keys.take(count as int - 1)[k] == other;
                    assert(keys.take(count as int)[k] == other);
                    assert(keys.take(count as int).contains(other));
                }
                assert(prior[other] == map[other]);
            };
        assert forall|i: int| 0 <= i < notes.len() implies match #[trigger] notes[i] {
            NoteV::Execute { id: offered, version } =>
                next.contains_key(offered) && next[offered].task is Some
                && next[offered].task.unwrap().state == TaskState::Pending
                && next[offered].task.unwrap().version == version,
            _ => false,
        } by {
            match notes[i] {
                NoteV::Execute { id: offered, .. } => {
                    assert(keys.take(count as int - 1).contains(offered));
                    assert(offered != id);
                },
                _ => {},
            }
        };
        if crate::handler::spec_due_offer(map[id], now) {
            let note = NoteV::Execute { id, version: map[id].task.unwrap().version };
            assert forall|i: int| 0 <= i < notes.len() implies
                crate::handler::protocol_effect_key(crate::handler::note_effect(#[trigger] notes[i]))
                    != crate::handler::protocol_effect_key(crate::handler::note_effect(note)) by {
                match notes[i] {
                    NoteV::Execute { id: offered, .. } => {
                        assert(keys.take(count as int - 1).contains(offered));
                        let k = choose|k: int| 0 <= k < count as int - 1
                            && #[trigger] keys.take(count as int - 1)[k] == offered;
                        assert(keys.take(count as int)[k] == offered);
                        assert(keys.take(count as int).contains(offered));
                        assert(offered != id);
                    },
                    _ => {},
                }
            };
            assert(crate::handler::note_effect_keys(notes.push(note))
                =~= crate::handler::note_effect_keys(notes).push(
                    crate::handler::protocol_effect_key(crate::handler::note_effect(note))));
            assert(crate::handler::note_effect_keys(notes.push(note)).no_duplicates());
            assert(crate::property_claim::collected_offers_valid(next, notes.push(note)));
        } else {
            assert(crate::property_claim::collected_offers_valid(next, notes));
        }
        let all = crate::handler::spec_project_offers(map, keys, count, now);
        assert forall|i: int| 0 <= i < all.len() implies match #[trigger] all[i] {
            NoteV::Execute { id: offered, .. } => keys.take(count as int).contains(offered),
            _ => false,
        } by {
            if i < notes.len() {
                assert(all[i] == notes[i]);
                match notes[i] {
                    NoteV::Execute { id: offered, .. } => {
                        assert(keys.take(count as int - 1).contains(offered));
                    },
                    _ => {},
                }
            } else {
                assert(all[i] == NoteV::Execute { id, version: map[id].task.unwrap().version });
            }
        };
    }
}

pub proof fn lemma_callback_keys_preserve_collected_offers(
    map: Map<Seq<char>, crate::state::ObjV>,
    notes: Seq<NoteV>,
    keys: Seq<Seq<char>>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        count <= keys.len(),
        crate::property_claim::collected_offers_valid(map, notes),
    ensures
        ({
            let (next, more) = crate::handler::spec_drain_callback_keys(map, keys, count, now, retry_timeout);
            &&& next.dom() == map.dom()
            &&& crate::property_claim::collected_offers_valid(next, notes + more)
            &&& forall|id: Seq<char>| map.contains_key(id) ==>
                #[trigger] next[id].promise.listeners == map[id].promise.listeners
        }),
    decreases count,
{
    if count > 0 {
        lemma_callback_keys_preserve_collected_offers(map, notes, keys, (count - 1) as nat, now, retry_timeout);
        let (prior, collected) = crate::handler::spec_drain_callback_keys(map, keys, (count - 1) as nat, now, retry_timeout);
        let id = keys[count as int - 1];
        if prior.contains_key(id) && prior[id].promise.state != PromiseState::Pending {
            lemma_callback_pass_preserves_collected_offers(
                prior, notes + collected, id, prior[id].promise.callbacks.len(), now, retry_timeout);
        }
        let (_, more) = crate::handler::spec_drain_settled_callbacks(prior, id, now, retry_timeout);
        let (next, _) = crate::handler::spec_drain_callback_keys(map, keys, count, now, retry_timeout);
        assert forall|key: Seq<char>| map.contains_key(key) implies
            #[trigger] next[key].promise.listeners == map[key].promise.listeners by {
            assert(prior.contains_key(key));
            assert(prior[key].promise.listeners == map[key].promise.listeners);
            if prior.contains_key(id) && prior[id].promise.state != PromiseState::Pending {
                let (drained, _) = crate::handler::spec_drain_callbacks(
                    prior, id, prior[id].promise.callbacks.len(), now, retry_timeout);
                assert(next == drained);
                assert(drained[key].promise.listeners == prior[key].promise.listeners);
            } else {
                assert(next == prior);
            }
        };
        assert(notes + (collected + more) =~= (notes + collected) + more);
    } else {
        assert(notes + Seq::<NoteV>::empty() =~= notes);
    }
}

pub proof fn lemma_callback_pass_preserves_collected_offers(
    map: Map<Seq<char>, crate::state::ObjV>,
    notes: Seq<NoteV>,
    id: Seq<char>,
    count: nat,
    now: Time,
    retry_timeout: u64,
)
    requires
        map.contains_key(id),
        map[id].promise.state != PromiseState::Pending,
        count <= map[id].promise.callbacks.len(),
        crate::property_claim::collected_offers_valid(map, notes),
    ensures
        ({
            let (next, more) = crate::handler::spec_drain_callbacks(map, id, count, now, retry_timeout);
            &&& next.dom() == map.dom()
            &&& next[id].promise.callbacks == map[id].promise.callbacks.skip(count as int)
            &&& next[id].promise.state == map[id].promise.state
            &&& crate::property_claim::collected_offers_valid(next, notes + more)
            &&& forall|key: Seq<char>| map.contains_key(key) ==>
                #[trigger] next[key].promise.listeners == map[key].promise.listeners
        }),
    decreases count,
{
    if count > 0 {
        lemma_callback_pass_preserves_collected_offers(map, notes, id, (count - 1) as nat, now, retry_timeout);
        let (prior, collected) = crate::handler::spec_drain_callbacks(map, id, (count - 1) as nat, now, retry_timeout);
        let obj = prior[id];
        let awaiter = obj.promise.callbacks[0];
        let since = match obj.promise.settled_at { Some(t) => t, None => 0 };
        let consumed = prior.insert(id, crate::state::ObjV {
            promise: crate::state::PromV { callbacks: obj.promise.callbacks.skip(1), ..obj.promise },
            ..obj
        });
        assert forall|key: Seq<char>| prior.contains_key(key) implies
            #[trigger] consumed[key].task == prior[key].task by {};
        assert(crate::property_claim::collected_offers_valid(consumed, notes + collected));
        lemma_resume_preserves_collected_offers(consumed, notes + collected, awaiter, id, since, now, retry_timeout);
        lemma_resume_offer_frame(consumed, awaiter, id, since, now, retry_timeout);
        let (_, more) = crate::handler::spec_resume_offer(consumed, awaiter, id, since, now, retry_timeout);
        let (next, _) = crate::handler::spec_drain_callbacks(map, id, count, now, retry_timeout);
        assert forall|key: Seq<char>| map.contains_key(key) implies
            #[trigger] next[key].promise.listeners == map[key].promise.listeners by {
            assert(prior[key].promise.listeners == map[key].promise.listeners);
            assert(consumed[key].promise.listeners == prior[key].promise.listeners);
            assert(next[key].promise == consumed[key].promise);
        };
        assert(notes + (collected + more) =~= (notes + collected) + more);
        assert(map[id].promise.callbacks.skip(count as int)
            =~= map[id].promise.callbacks.skip(count as int - 1).skip(1));
    } else {
        assert(notes + Seq::<NoteV>::empty() =~= notes);
        assert(map[id].promise.callbacks.skip(0) =~= map[id].promise.callbacks);
    }
}

pub proof fn lemma_resume_preserves_collected_offers(
    map: Map<Seq<char>, crate::state::ObjV>,
    notes: Seq<NoteV>,
    awaiter: Seq<char>,
    awaited: Seq<char>,
    since: Time,
    now: Time,
    retry_timeout: u64,
)
    requires
        crate::property_claim::collected_offers_valid(map, notes),
    ensures
        ({
            let (next, more) = crate::handler::spec_resume_offer(map, awaiter, awaited, since, now, retry_timeout);
            crate::property_claim::collected_offers_valid(next, notes + more)
        }),
{
    lemma_resume_offer_frame(map, awaiter, awaited, since, now, retry_timeout);
    let (next, more) = crate::handler::spec_resume_offer(map, awaiter, awaited, since, now, retry_timeout);
    assert forall|i: int| 0 <= i < notes.len() implies match #[trigger] notes[i] {
        NoteV::Execute { id, version } =>
            next.contains_key(id) && next[id].task is Some
            && next[id].task.unwrap().state == TaskState::Pending
            && next[id].task.unwrap().version == version,
        _ => false,
    } by {
        assert(crate::property_claim::collected_offers_valid(map, notes));
    };
    if more.len() == 0 {
        assert(notes + more =~= notes);
    } else {
        assert(more =~= seq![more[0]]);
        assert(notes + more =~= notes.push(more[0]));
        assert forall|i: int| 0 <= i < notes.len() implies
            crate::handler::protocol_effect_key(crate::handler::note_effect(#[trigger] notes[i]))
                != crate::handler::protocol_effect_key(crate::handler::note_effect(more[0])) by {
            match notes[i] {
                NoteV::Execute { id, .. } => {
                    assert(map[id].task.unwrap().state == TaskState::Pending);
                    assert(id != awaiter);
                },
                _ => {},
            }
        };
        assert(crate::handler::note_effect_keys(notes.push(more[0]))
            =~= crate::handler::note_effect_keys(notes).push(
                crate::handler::protocol_effect_key(crate::handler::note_effect(more[0]))));
    }
}

pub proof fn lemma_resume_offer_frame(
    map: Map<Seq<char>, crate::state::ObjV>,
    awaiter: Seq<char>,
    awaited: Seq<char>,
    since: Time,
    now: Time,
    retry_timeout: u64,
)
    ensures
        ({
            let (next, notes) = crate::handler::spec_resume_offer(map, awaiter, awaited, since, now, retry_timeout);
            &&& next.dom() == map.dom()
            &&& forall|id: Seq<char>| map.contains_key(id) ==>
                #[trigger] next[id].promise == map[id].promise
            &&& forall|id: Seq<char>| map.contains_key(id)
                && map[id].task is Some
                && map[id].task.unwrap().state == TaskState::Pending ==>
                    (#[trigger] next[id].task) is Some
                    && next[id].task.unwrap().state == TaskState::Pending
                    && next[id].task.unwrap().version == map[id].task.unwrap().version
            &&& notes.len() <= 1
            &&& notes.len() == 1 ==> {
                &&& map.contains_key(awaiter)
                &&& map[awaiter].task is Some
                &&& map[awaiter].task.unwrap().state == TaskState::Suspended
                &&& next[awaiter].task is Some
                &&& next[awaiter].task.unwrap().state == TaskState::Pending
                &&& notes[0] == NoteV::Execute { id: awaiter, version: next[awaiter].task.unwrap().version }
            }
        }),
{
    let (next, notes) = crate::handler::spec_resume_offer(map, awaiter, awaited, since, now, retry_timeout);
    assert forall|id: Seq<char>| map.contains_key(id) implies
        #[trigger] next[id].promise == map[id].promise by {
        if id != awaiter {
            assert(next[id] == map[id]);
        }
    };
    assert forall|id: Seq<char>| map.contains_key(id)
        && map[id].task is Some
        && map[id].task.unwrap().state == TaskState::Pending implies
            (#[trigger] next[id].task) is Some
            && next[id].task.unwrap().state == TaskState::Pending
            && next[id].task.unwrap().version == map[id].task.unwrap().version by {
        if id != awaiter {
            assert(next[id] == map[id]);
        }
    };
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_apply_changes_append<V>(
    entries: Map<Seq<char>, V>,
    first: Seq<ChangeV<V>>,
    second: Seq<ChangeV<V>>,
)
    ensures
        spec_apply_changes(entries, first + second)
            == spec_apply_changes(spec_apply_changes(entries, first), second),
    decreases second.len(),
{
    if second.len() == 0 {
        assert(first + second =~= first);
    } else {
        let prefix = second.drop_last();
        lemma_apply_changes_append(entries, first, prefix);
        assert((first + second).drop_last() =~= first + prefix);
        assert((first + second).last() == second.last());
    }
}

#[cfg(verus_keep_ghost)]
pub proof fn lemma_compose_preserves_apply<V>(
    document: FoldedV<V>,
    first: PartialV<V>,
    second: PartialV<V>,
)
    requires
        first.document == document.document,
        first.basever == document.version,
        second.document == document.document,
        second.basever == first.version,
        document.committed_at <= first.committed_at <= second.committed_at,
    ensures
        spec_apply_document(spec_apply_document(document, first), second)
            == spec_apply_document(document, spec_compose(first, second)),
{
    lemma_apply_changes_append(document.entries, first.changes, second.changes);
}

pub proof fn lemma_before_irreflexive(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_before_irreflexive(a.drop_first());
    }
}

pub proof fn lemma_before_transitive(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() > 0 && b.len() > 0 && c.len() > 0
        && a[0] == b[0] && b[0] == c[0]
    {
        lemma_before_transitive(
            a.drop_first(),
            b.drop_first(),
            c.drop_first(),
        );
    }
}

pub proof fn lemma_before_total(a: Seq<char>, b: Seq<char>)
    requires
        a != b,
    ensures
        spec_before(a, b) || spec_before(b, a),
    decreases a.len() + b.len(),
{
    if a.len() == 0 {
        if b.len() == 0 {
            assert(a =~= b);
            assert(a == b);
        }
    } else if b.len() == 0 {
    } else if a[0] < b[0] {
    } else if b[0] < a[0] {
    } else {
        assert(a[0] == b[0]);
        if a.drop_first() == b.drop_first() {
            assert(a.drop_first().len() == a.len() - 1);
            assert(b.drop_first().len() == b.len() - 1);
            assert(a.len() == b.len());
            assert forall|i: int| 0 <= i < a.len()
                implies #[trigger] a[i] == #[trigger] b[i] by {
                if i > 0 {
                    assert(a[i] == a.drop_first()[i - 1]);
                    assert(b[i] == b.drop_first()[i - 1]);
                }
            };
            assert(a =~= b);
            assert(a == b);
        } else {
            lemma_before_total(a.drop_first(), b.drop_first());
        }
    }
}

spec fn least(keys: Set<Seq<char>>, key: Seq<char>) -> bool {
    keys.contains(key)
        && forall|other: Seq<char>| keys.contains(other)
            ==> !spec_before(other, key)
}

proof fn lemma_least_exists(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        exists|key: Seq<char>| least(keys, key),
    decreases keys.len(),
{
    let x = keys.choose();
    assert(keys.contains(x));
    let rest = keys.remove(x);
    assert(rest.len() == keys.len() - 1);
    if rest.len() == 0 {
        assert forall|other: Seq<char>| keys.contains(other)
            implies !spec_before(other, x) by {
            if other == x {
                lemma_before_irreflexive(x);
            } else {
                assert(rest.contains(other));
            }
        };
        assert(least(keys, x));
    } else {
        lemma_least_exists(rest);
        let m = choose|key: Seq<char>| least(rest, key);
        if spec_before(x, m) {
            assert forall|other: Seq<char>| keys.contains(other)
                implies !spec_before(other, x) by {
                if other == x {
                    lemma_before_irreflexive(x);
                } else {
                    assert(rest.contains(other));
                    if spec_before(other, x) {
                        lemma_before_transitive(other, x, m);
                    }
                }
            };
            assert(least(keys, x));
        } else {
            assert forall|other: Seq<char>| keys.contains(other)
                implies !spec_before(other, m) by {
                if other != x {
                    assert(rest.contains(other));
                }
            };
            assert(least(keys, m));
        }
    }
}

proof fn lemma_min_key_least(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        least(keys, spec_min_key(keys)),
{
    reveal(spec_min_key);
    lemma_least_exists(keys);
}

proof fn lemma_sorted_properties(keys: Set<Seq<char>>)
    requires
        keys.finite(),
    ensures
        ({
            let ordered = spec_sorted(keys);
            &&& keys_strictly_sorted(ordered)
            &&& ordered.no_duplicates()
            &&& forall|key: Seq<char>| #[trigger] ordered.contains(key)
                <==> keys.contains(key)
        }),
    decreases keys.len(),
{
    if keys.len() == 0 {
        assert(spec_sorted(keys) =~= Seq::<Seq<char>>::empty());
    } else {
        lemma_min_key_least(keys);
        let first = spec_min_key(keys);
        let rest = keys.remove(first);
        lemma_sorted_properties(rest);
        let tail = spec_sorted(rest);
        let ordered = seq![first] + tail;
        assert(spec_sorted(keys) == ordered);

        assert forall|key: Seq<char>| #[trigger] ordered.contains(key)
            <==> keys.contains(key) by {
            if ordered.contains(key) {
                let i = choose|i: int| 0 <= i < ordered.len()
                    && #[trigger] ordered[i] == key;
                if i == 0 {
                    assert(key == first);
                } else {
                    assert(ordered[i] == tail[i - 1]);
                    assert(tail.contains(key));
                    assert(rest.contains(key));
                }
            } else if keys.contains(key) {
                if key == first {
                    assert(ordered[0] == first);
                    assert(ordered.contains(key));
                } else {
                    assert(rest.contains(key));
                    assert(tail.contains(key));
                    let i = choose|i: int| 0 <= i < tail.len()
                        && #[trigger] tail[i] == key;
                    assert(ordered[i + 1] == tail[i]);
                    assert(ordered.contains(key));
                }
            }
        };

        assert forall|i: int, j: int| 0 <= i < j < ordered.len()
            implies spec_before(#[trigger] ordered[i], #[trigger] ordered[j]) by {
            if i == 0 {
                let other = ordered[j];
                assert(tail.contains(other));
                assert(rest.contains(other));
                assert(other != first);
                lemma_before_total(first, other);
                if spec_before(other, first) {
                    assert(!spec_before(other, first));
                }
            } else {
                assert(ordered[i] == tail[i - 1]);
                assert(ordered[j] == tail[j - 1]);
            }
        };

        assert forall|i: int, j: int|
            0 <= i < ordered.len() && 0 <= j < ordered.len() && i != j
            implies ordered[i] != ordered[j] by {
            if i < j {
                lemma_before_irreflexive(ordered[i]);
            } else {
                lemma_before_irreflexive(ordered[j]);
            }
        };
    }
}

proof fn lemma_document_object_order(doc: DocumentBodyV)
    ensures
        document_object_order(doc),
{
    match doc {
        DocumentBodyV::Workflow(map) => {
            lemma_sorted_properties(map.dom());
        },
        DocumentBodyV::Schedule(_) => {},
    }
}

proof fn lemma_nodes_layout(config: Config, id: u64)
    requires
        id <= config.nodes,
    ensures
        ({
            let nodes = spec_nodes(config, id);
            &&& nodes.len() == (config.nodes - id) as nat
            &&& forall|k: int| 0 <= k < nodes.len()
                ==> #[trigger] nodes[k].0 == Pid::Node((id + k) as u64)
            &&& forall|i: int, j: int| 0 <= i < j < nodes.len()
                ==> #[trigger] nodes[i].0 != #[trigger] nodes[j].0
        }),
    decreases config.nodes - id,
{
    if id < config.nodes {
        lemma_nodes_layout(config, (id + 1) as u64);
    }
}

proof fn lemma_process_layout(config: Config)
    ensures
        process_layout(config),
{
    lemma_nodes_layout(config, 0);
    let nodes = spec_nodes(config, 0);
    let world = spec_world(config);
    assert(world == nodes + seq![(Pid::Store, crate::state::Proc::Store(
        crate::state::StoreV {
            entries: Seq::empty(),
            appendable: config.appendable,
            seen: Seq::empty(),
        },
    ))]);
    assert forall|i: int, j: int| 0 <= i < j < world.len()
        implies #[trigger] world[i].0 != #[trigger] world[j].0 by {
        if j < nodes.len() {
        } else {
            assert(j == nodes.len());
            assert(world[j].0 == Pid::Store);
            assert(i < nodes.len());
            assert(world[i].0 == nodes[i].0);
        }
    };
}

proof fn lemma_remember_integrity(
    node: NodeV,
    key: Seq<char>,
    body: Seq<u8>,
    etag: Option<Seq<char>>,
    i: int,
)
    requires
        document_keys_unique(node),
        document_key_ownership(node),
        spec_owns(node, key),
        0 <= i <= node.documents.len(),
        forall|k: int| 0 <= k < i
            ==> #[trigger] node.documents[k].key != key,
    ensures
        ({
            let next = NodeV {
                documents: spec_remember(node.documents, key, body, etag, i),
                ..node
            };
            document_keys_unique(next) && document_key_ownership(next)
        }),
    decreases node.documents.len() - i,
{
    let docs = node.documents;
    let next_docs = spec_remember(docs, key, body, etag, i);
    let next = NodeV { documents: next_docs, ..node };
    if i >= docs.len() {
        assert(next_docs == docs.push(CachedV { key, body, etag }));
        assert forall|j: int, k: int| 0 <= j < k < next_docs.len()
            implies #[trigger] next_docs[j].key != #[trigger] next_docs[k].key by {
            if k == docs.len() {
                assert(next_docs[j] == docs[j]);
            }
        };
        assert forall|k: int| 0 <= k < next_docs.len()
            implies spec_owns(next, #[trigger] next_docs[k].key) by {
            if k < docs.len() {
                assert(next_docs[k] == docs[k]);
                assert(spec_owns(node, docs[k].key));
            }
        };
    } else if docs[i].key == key {
        assert(next_docs == docs.update(i, CachedV { key, body, etag }));
        assert forall|j: int, k: int| 0 <= j < k < next_docs.len()
            implies #[trigger] next_docs[j].key != #[trigger] next_docs[k].key by {
            if j != i {
                assert(next_docs[j].key == docs[j].key);
            }
            if k != i {
                assert(next_docs[k].key == docs[k].key);
            }
        };
        assert forall|k: int| 0 <= k < next_docs.len()
            implies spec_owns(next, #[trigger] next_docs[k].key) by {
            if k != i {
                assert(next_docs[k] == docs[k]);
                assert(spec_owns(node, docs[k].key));
            }
        };
    } else {
        lemma_remember_integrity(node, key, body, etag, i + 1);
    }
}

proof fn lemma_forget_integrity(node: NodeV, key: Seq<char>, i: int)
    requires
        document_keys_unique(node),
        document_key_ownership(node),
        0 <= i <= node.documents.len(),
    ensures
        ({
            let next = NodeV {
                documents: spec_forget(node.documents, key, i),
                ..node
            };
            document_keys_unique(next) && document_key_ownership(next)
        }),
    decreases node.documents.len() - i,
{
    let docs = node.documents;
    let next_docs = spec_forget(docs, key, i);
    let next = NodeV { documents: next_docs, ..node };
    if i >= docs.len() {
    } else if docs[i].key == key {
        assert(next_docs == docs.take(i) + docs.skip(i + 1));
        assert forall|k: int| 0 <= k < next_docs.len()
            implies #[trigger] next_docs[k]
                == if k < i { docs[k] } else { docs[k + 1] } by {
            if k < i {
                assert(next_docs[k] == docs.take(i)[k]);
            } else {
                assert(next_docs[k] == docs.skip(i + 1)[k - i]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_docs.len()
            implies #[trigger] next_docs[j].key != #[trigger] next_docs[k].key by {};
        assert forall|k: int| 0 <= k < next_docs.len()
            implies spec_owns(next, #[trigger] next_docs[k].key) by {};
    } else {
        lemma_forget_integrity(node, key, i + 1);
    }
}

proof fn lemma_keep_integrity(
    node: NodeV,
    key: Seq<char>,
    doc: DocumentBodyV,
    etag: Option<Seq<char>>,
)
    requires
        document_keys_unique(node),
        document_key_ownership(node),
        spec_owns(node, key),
    ensures
        ({
            let next = NodeV {
                documents: spec_keep(node.documents, key, doc, etag),
                ..node
            };
            document_keys_unique(next) && document_key_ownership(next)
        }),
{
    if spec_body_is_empty(doc) && etag is None {
        lemma_forget_integrity(node, key, 0);
    } else {
        lemma_remember_integrity(node, key, crate::handler::spec_encode_body(doc), etag, 0);
    }
}

proof fn lemma_earliest_from_cached(
    node: NodeV,
    docs: Seq<CachedV>,
    i: int,
    now: Time,
    best: Option<(u64, Seq<char>)>,
)
    requires
        0 <= i <= docs.len(),
        match best {
            Some((_, key)) => exists|k: int| 0 <= k < docs.len()
                && #[trigger] docs[k].key == key,
            None => true,
        },
    ensures
        match spec_earliest_from(node, docs, i, now, best) {
            Some(key) => exists|k: int| 0 <= k < docs.len()
                && #[trigger] docs[k].key == key,
            None => true,
        },
    decreases docs.len() - i,
{
    if i < docs.len() {
        match crate::handler::spec_earliest_in(
            crate::handler::spec_read(docs[i].key, docs[i].body),
            now,
        ) {
            Some(at) if spec_owns(node, docs[i].key) => {
                let better = match best { None => true, Some((b, _)) => at < b };
                let next_best = if better { Some((at, docs[i].key)) } else { best };
                assert(match next_best {
                    Some((_, key)) => exists|k: int| 0 <= k < docs.len()
                        && #[trigger] docs[k].key == key,
                    None => true,
                }) by {
                    if better {
                        assert(docs[i].key == docs[i].key);
                    }
                };
                lemma_earliest_from_cached(node, docs, i + 1, now, next_best);
            },
            _ => {
                lemma_earliest_from_cached(node, docs, i + 1, now, best);
            },
        }
    }
}

proof fn lemma_earliest_owned(node: NodeV, now: Time)
    requires
        document_key_ownership(node),
    ensures
        match spec_earliest_key(node, now) {
            Some(key) => spec_owns(node, key),
            None => true,
        },
{
    lemma_earliest_from_cached(node, node.documents, 0, now, None);
    match spec_earliest_key(node, now) {
        Some(key) => {
            let i = choose|i: int| 0 <= i < node.documents.len()
                && #[trigger] node.documents[i].key == key;
            assert(spec_owns(node, node.documents[i].key));
        },
        None => {},
    }
}

proof fn lemma_commit_integrity(node: NodeV, flight: FlightV, tag: crate::state::Etag)
    requires
        state_properties(Proc::Node(node)),
        spec_owns(node, flight.key),
    ensures
        ({
            let next = spec_commit(node, flight, tag).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match flight.decided {
        Some(body) => {
            lemma_remember_integrity(node, flight.key, body, Some(tag.0@), 0);
        },
        None => {},
    }
}

proof fn lemma_decide_integrity(node: NodeV, flight: FlightV, doc: DocumentBodyV)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        spec_owns(node, flight.key),
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_decide(node, flight, doc).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    let (next_doc, reply, born, notify) = match flight.job {
        crate::state::JobV::External(request) => {
            let (next, response) = crate::handler::spec_handle(doc, request, flight.now);
            (next, Some(response), Seq::empty(), Seq::empty())
        },
        crate::state::JobV::Due => crate::handler::spec_run_due(doc, flight.now, node.retry_timeout),
        crate::state::JobV::Occurrence(pending) => (
            crate::handler::spec_occurrence(doc, pending, flight.now),
            None,
            Seq::empty(),
            Seq::empty(),
        ),
    };
    let previous = match spec_cached(node, flight.key) {
        Some(cached) => crate::handler::spec_read(flight.key, cached.body),
        None => crate::handler::spec_empty_body(flight.key),
    };
    if next_doc == previous && born.len() == 0 {
        lemma_keep_integrity(node, flight.key, next_doc, flight.etag);
    } else {
        assert(node.next_op < (node.next_op + 1) as u64);
    }
}

proof fn lemma_begin_integrity(
    node: NodeV,
    key: Seq<char>,
    job: crate::state::JobV,
    now: Time,
    caller: Option<(Seq<char>, u64)>,
)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        spec_owns(node, key),
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_begin(node, key, job, now, caller).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match spec_cached(node, key) {
        Some(cached) => {
            lemma_decide_integrity(
                node,
                crate::handler::spec_flight(0, key, cached.etag, now, caller, job),
                crate::handler::spec_read(key, cached.body),
            );
        },
        None => {
            assert(node.next_op < (node.next_op + 1) as u64);
        },
    }
}

proof fn lemma_request_integrity(node: NodeV, now: Time, request: Call)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_request(node, now, request).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match crate::handler::spec_key(request.request) {
        Some(key) if spec_owns(node, key) => {
            lemma_begin_integrity(
                node,
                key,
                crate::state::JobV::External(request.request),
                now,
                Some((request.client@, request.id)),
            );
        },
        _ => {},
    }
}

proof fn lemma_timeout_integrity(node: NodeV, now: Time)
    requires
        state_properties(Proc::Node(node)),
        node.flight is None,
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_timeout(node, now).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    if node.pending.len() > 0 {
        let pending = node.pending[0];
        let without = NodeV { pending: node.pending.skip(1), ..node };
        let key = crate::handler::spec_origin_key(echod_types::origin(pending.promise));
        if spec_owns(without, key) {
            lemma_begin_integrity(
                without,
                key,
                crate::state::JobV::Occurrence(pending),
                now,
                None,
            );
        }
    } else {
        lemma_earliest_owned(node, now);
        match spec_earliest_key(node, now) {
            Some(key) => {
                lemma_begin_integrity(node, key, crate::state::JobV::Due, now, None);
            },
            None => {},
        }
    }
}

proof fn lemma_store_reply_integrity(
    node: NodeV,
    op: u64,
    response: StoreRes,
)
    requires
        state_properties(Proc::Node(node)),
        node.next_op < u64::MAX,
    ensures
        ({
            let next = spec_store_reply(node, op, response).0;
            &&& state_properties(Proc::Node(next))
            &&& node.next_op <= next.next_op
        }),
{
    match node.flight {
        Some(flight) if flight.op == op => {
            if !flight.writing {
                match response {
                    StoreRes::Get { result: Ok(got) } => {
                        let (doc, etag) = match got {
                            Some((body, tag)) => (
                                crate::handler::spec_read(flight.key, body@),
                                Some(tag.0@),
                            ),
                            None => (crate::handler::spec_empty_body(flight.key), None),
                        };
                        lemma_decide_integrity(
                            NodeV { flight: None, ..node },
                            FlightV { etag, ..flight },
                            doc,
                        );
                    },
                    _ => {},
                }
            } else {
                match response {
                    StoreRes::PutIfNoneMatch { result: Ok(tag) } | StoreRes::PutIfMatch { result: Ok(tag) } => {
                        lemma_commit_integrity(node, flight, tag);
                    },
                    _ => {},
                }
            }
        },
        _ => {},
    }
}

proof fn lemma_node_step_integrity(
    config: Config,
    node: NodeV,
    now: Time,
    event: ProcessEvent<Pid, Message>,
)
    requires
        state_properties(Proc::Node(node)),
    ensures
        forall|i: int| 0 <= i < spec_node(node, now, event).len() ==> {
            let next = #[trigger] spec_node(node, now, event)[i].state;
            &&& state_properties(next)
            &&& transition_properties(Proc::Node(node), next)
        },
{
    match event {
        ProcessEvent::Timeout => {
            match node.wake {
                Some(at) if at <= now as nat && node.flight is None
                    && node.next_op < u64::MAX => {
                    lemma_timeout_integrity(node, now);
                },
                _ => {},
            }
        },
        ProcessEvent::Receive {
            sender: Pid::Outside,
            message: Message::Request(request),
        } => {
            if node.flight is None && node.next_op != u64::MAX {
                lemma_request_integrity(node, now, request);
            }
        },
        ProcessEvent::Receive {
            sender: Pid::Store,
            message: Message::StoreRes { op, response },
        } => {
            if node.flight is Some && node.next_op != u64::MAX {
                lemma_store_reply_integrity(node, op, response);
            }
        },
        _ => {},
    }
}

proof fn lemma_find_from(entries: Seq<EntryV>, key: Seq<char>, i: int)
    requires
        0 <= i <= entries.len(),
    ensures
        match spec_find(entries, key, i) {
            Some(j) => i <= j < entries.len()
                && entries[j].key == key
                && forall|k: int| i <= k < j
                    ==> #[trigger] entries[k].key != key,
            None => forall|k: int| i <= k < entries.len()
                ==> #[trigger] entries[k].key != key,
        },
    decreases entries.len() - i,
{
    if i < entries.len() && entries[i].key != key {
        lemma_find_from(entries, key, i + 1);
    }
}

proof fn lemma_find_at(store: StoreV, i: int)
    requires
        store_entries_unique(store),
        0 <= i < store.entries.len(),
    ensures
        spec_find(store.entries, store.entries[i].key, 0) == Some(i),
{
    lemma_find_from(store.entries, store.entries[i].key, 0);
    match spec_find(store.entries, store.entries[i].key, 0) {
        Some(j) => {
            if j < i {
                assert(store.entries[j].key != store.entries[i].key);
            } else if j > i {
                assert(store.entries[i].key != store.entries[i].key);
            }
        },
        None => {
            assert(store.entries[i].key != store.entries[i].key);
        },
    }
}

proof fn lemma_find_absent(entries: Seq<EntryV>, key: Seq<char>)
    requires
        forall|i: int| 0 <= i < entries.len()
            ==> #[trigger] entries[i].key != key,
    ensures
        spec_find(entries, key, 0) is None,
{
    lemma_find_from(entries, key, 0);
}

proof fn lemma_insert_integrity(
    store: StoreV,
    entry: EntryV,
    i: int,
)
    requires
        store_entries_ordered(store),
        store_entries_unique(store),
        store_versions_positive(store),
        entry.version > 0,
        0 <= i <= store.entries.len(),
        forall|k: int| 0 <= k < store.entries.len()
            ==> #[trigger] store.entries[k].key != entry.key,
        forall|k: int| 0 <= k < i
            ==> spec_before(#[trigger] store.entries[k].key, entry.key),
    ensures
        ({
            let next = StoreV {
                entries: spec_insert_at(store.entries, entry, i),
                ..store
            };
            &&& store_entries_ordered(next)
            &&& store_entries_unique(next)
            &&& store_versions_positive(next)
            &&& forall|k: int| 0 <= k < store.entries.len() ==> {
                let old = #[trigger] store.entries[k];
                match spec_find(next.entries, old.key, 0) {
                    Some(j) => next.entries[j].version == old.version,
                    None => false,
                }
            }
        }),
    decreases store.entries.len() - i,
{
    let entries = store.entries;
    let next_entries = spec_insert_at(entries, entry, i);
    let next = StoreV { entries: next_entries, ..store };
    if i >= entries.len() {
        assert(next_entries == entries.push(entry));
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies spec_before(
                #[trigger] next_entries[j].key,
                #[trigger] next_entries[k].key,
            ) by {
            if k == entries.len() {
                assert(next_entries[j] == entries[j]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies #[trigger] next_entries[j].key
                != #[trigger] next_entries[k].key by {
            if k == entries.len() {
                assert(next_entries[j] == entries[j]);
            }
        };
        assert forall|k: int| 0 <= k < next_entries.len()
            implies #[trigger] next_entries[k].version > 0 by {};
        assert forall|k: int| 0 <= k < entries.len() implies {
            let old = #[trigger] entries[k];
            match spec_find(next_entries, old.key, 0) {
                Some(j) => next_entries[j].version == old.version,
                None => false,
            }
        } by {
            let bare = StoreV { entries: next_entries, ..store };
            lemma_find_at(bare, k);
            assert(next_entries[k] == entries[k]);
        };
    } else if spec_before(entry.key, entries[i].key) {
        assert(next_entries == entries.take(i).push(entry) + entries.skip(i));
        assert forall|k: int| 0 <= k < next_entries.len()
            implies #[trigger] next_entries[k] == if k < i {
                entries[k]
            } else if k == i {
                entry
            } else {
                entries[k - 1]
            } by {
            if k < i {
                assert(next_entries[k] == entries.take(i).push(entry)[k]);
            } else if k == i {
                assert(next_entries[k] == entries.take(i).push(entry)[k]);
            } else {
                assert(next_entries[k] == entries.skip(i)[k - i - 1]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies spec_before(
                #[trigger] next_entries[j].key,
                #[trigger] next_entries[k].key,
            ) by {
            if j < i && k == i {
            } else if j == i {
                if k > i + 1 {
                    lemma_before_transitive(
                        entry.key,
                        entries[i].key,
                        entries[k - 1].key,
                    );
                }
            } else if j < i && k > i {
                assert(next_entries[j] == entries[j]);
                assert(next_entries[k] == entries[k - 1]);
            } else if j > i {
                assert(next_entries[j] == entries[j - 1]);
                assert(next_entries[k] == entries[k - 1]);
            }
        };
        assert forall|j: int, k: int| 0 <= j < k < next_entries.len()
            implies #[trigger] next_entries[j].key
                != #[trigger] next_entries[k].key by {
            lemma_before_irreflexive(next_entries[j].key);
        };
        assert forall|k: int| 0 <= k < next_entries.len()
            implies #[trigger] next_entries[k].version > 0 by {};
        assert forall|k: int| 0 <= k < entries.len() implies {
            let old = #[trigger] entries[k];
            match spec_find(next_entries, old.key, 0) {
                Some(j) => next_entries[j].version == old.version,
                None => false,
            }
        } by {
            let bare = StoreV { entries: next_entries, ..store };
            if k < i {
                lemma_find_at(bare, k);
            } else {
                lemma_find_at(bare, k + 1);
            }
        };
    } else {
        lemma_before_total(entry.key, entries[i].key);
        assert(spec_before(entries[i].key, entry.key));
        lemma_insert_integrity(store, entry, i + 1);
    }
}

proof fn lemma_put_integrity(store: StoreV, entry: EntryV)
    requires
        store_entries_ordered(store),
        store_entries_unique(store),
        store_versions_positive(store),
        entry.version > 0,
        match spec_find(store.entries, entry.key, 0) {
            Some(i) => store.entries[i].version <= entry.version,
            None => true,
        },
    ensures
        ({
            let next = StoreV { entries: spec_put(store.entries, entry), ..store };
            &&& store_entries_ordered(next)
            &&& store_entries_unique(next)
            &&& store_versions_positive(next)
            &&& forall|k: int| 0 <= k < store.entries.len() ==> {
                let old = #[trigger] store.entries[k];
                match spec_find(next.entries, old.key, 0) {
                    Some(j) => old.version <= next.entries[j].version,
                    None => false,
                }
            }
        }),
{
    lemma_find_from(store.entries, entry.key, 0);
    match spec_find(store.entries, entry.key, 0) {
        Some(i) => {
            let next_entries = store.entries.update(i, entry);
            let next = StoreV { entries: next_entries, ..store };
            assert forall|k: int| 0 <= k < next_entries.len()
                implies #[trigger] next_entries[k].key == store.entries[k].key by {};
            assert(store_entries_ordered(next));
            assert(store_entries_unique(next));
            assert(store_versions_positive(next));
            assert forall|k: int| 0 <= k < store.entries.len() implies {
                let old = #[trigger] store.entries[k];
                match spec_find(next_entries, old.key, 0) {
                    Some(j) => old.version <= next_entries[j].version,
                    None => false,
                }
            } by {
                lemma_find_at(next, k);
            };
        },
        None => {
            assert forall|k: int| 0 <= k < store.entries.len()
                implies #[trigger] store.entries[k].key != entry.key by {};
            lemma_insert_integrity(store, entry, 0);
        },
    }
}

proof fn lemma_remove_integrity(store: StoreV, i: int)
    requires
        state_properties(Proc::Store(store)),
        0 <= i < store.entries.len(),
    ensures
        ({
            let next = StoreV { entries: spec_remove_at(store.entries, i), ..store };
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    let entries = store.entries;
    let next_entries = spec_remove_at(entries, i);
    let next = StoreV { entries: next_entries, ..store };
    assert forall|k: int| 0 <= k < next_entries.len()
        implies #[trigger] next_entries[k] == if k < i {
            entries[k]
        } else {
            entries[k + 1]
        } by {
        if k < i {
            assert(next_entries[k] == entries.take(i)[k]);
        } else {
            assert(next_entries[k] == entries.skip(i + 1)[k - i]);
        }
    };
    assert(store_entries_ordered(next));
    assert(store_entries_unique(next));
    assert(store_versions_positive(next));
    assert forall|k: int| 0 <= k < entries.len() implies {
        let old = #[trigger] entries[k];
        match spec_find(next_entries, old.key, 0) {
            Some(j) => old.version <= next_entries[j].version,
            None => true,
        }
    } by {
        if k < i {
            assert(next_entries[k] == entries[k]);
            lemma_find_at(next, k);
            assert(spec_find(next_entries, entries[k].key, 0) == Some(k));
        } else if k > i {
            assert(next_entries[k - 1] == entries[k]);
            lemma_find_at(next, k - 1);
            assert(spec_find(next_entries, entries[k].key, 0) == Some(k - 1));
        } else {
            assert forall|j: int| 0 <= j < next_entries.len()
                implies #[trigger] next_entries[j].key != entries[k].key by {
                if j < i {
                    assert(next_entries[j] == entries[j]);
                    assert(entries[j].key != entries[i].key);
                } else {
                    assert(next_entries[j] == entries[j + 1]);
                    assert(entries[i].key != entries[j + 1].key);
                }
            };
            lemma_find_absent(next_entries, entries[k].key);
        }
    };
}

proof fn lemma_store_stutter(store: StoreV)
    requires
        state_properties(Proc::Store(store)),
    ensures
        transition_properties(Proc::Store(store), Proc::Store(store)),
{
    assert forall|i: int| 0 <= i < store.entries.len() implies {
        let old = #[trigger] store.entries[i];
        match spec_find(store.entries, old.key, 0) {
            Some(j) => old.version <= store.entries[j].version,
            None => true,
        }
    } by {
        lemma_find_at(store, i);
    };
}

proof fn lemma_apply_put_none(store: StoreV, key: String, body: Vec<u8>)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::PutIfNoneMatch { key, body };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    match spec_find(store.entries, key@, 0) {
        Some(_) => {},
        None => {
            lemma_put_integrity(
                store,
                EntryV { key: key@, body: body@, version: 1 },
            );
        },
    }
}

#[verifier::rlimit(20)]
proof fn lemma_apply_put_match(
    store: StoreV,
    key: String,
    body: Vec<u8>,
    etag: crate::state::Etag,
)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::PutIfMatch { key, body, etag };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    let request = StoreReq::PutIfMatch { key, body, etag };
    let next = spec_apply(store, request).0;
    match spec_find(store.entries, key@, 0) {
        Some(i) if crate::handler::spec_etag(store.entries[i].body) == etag => {
            assert(spec_bump(store.entries[i].version) >= store.entries[i].version);
            assert(spec_bump(store.entries[i].version) > 0);
            let entry = EntryV {
                key: key@,
                body: body@,
                version: spec_bump(store.entries[i].version),
            };
            lemma_put_integrity(
                store,
                entry,
            );
            assert(next == StoreV { entries: spec_put(store.entries, entry), ..store });
        },
        _ => {
            assert(next == store);
        },
    }
}

#[verifier::rlimit(40)]
proof fn lemma_apply_append(
    store: StoreV,
    key: String,
    offset: u64,
    body: Vec<u8>,
    etag: crate::state::Etag,
)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::AppIfMatch { key, offset, body, etag };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    let request = StoreReq::AppIfMatch { key, offset, body, etag };
    let next = spec_apply(store, request).0;
    if store.appendable {
        match spec_find(store.entries, key@, 0) {
            Some(i) if crate::handler::spec_etag(store.entries[i].body) == etag
                && store.entries[i].body.len() == offset => {
                assert(spec_bump(store.entries[i].version) >= store.entries[i].version);
                assert(spec_bump(store.entries[i].version) > 0);
                let entry = EntryV {
                    key: key@,
                    body: store.entries[i].body + body@,
                    version: spec_bump(store.entries[i].version),
                };
                lemma_put_integrity(store, entry);
                assert(next == StoreV { entries: spec_put(store.entries, entry), ..store });
            },
            _ => {
                assert(next == store);
            },
        }
    } else {
        assert(next == store);
    }
}

proof fn lemma_apply_put(store: StoreV, key: String, body: Vec<u8>)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::Put { key, body };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    let version = match spec_find(store.entries, key@, 0) {
        Some(i) => spec_bump(store.entries[i].version),
        None => 1,
    };
    assert(version > 0);
    match spec_find(store.entries, key@, 0) {
        Some(i) => assert(version >= store.entries[i].version),
        None => {},
    }
    lemma_put_integrity(store, EntryV { key: key@, body: body@, version });
}

proof fn lemma_apply_delete(store: StoreV, key: String)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let request = StoreReq::Del { key };
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    lemma_store_stutter(store);
    match spec_find(store.entries, key@, 0) {
        Some(i) => {
            lemma_find_from(store.entries, key@, 0);
            lemma_remove_integrity(store, i);
        },
        None => {},
    }
}

proof fn lemma_apply_integrity(store: StoreV, request: StoreReq)
    requires
        state_properties(Proc::Store(store)),
    ensures
        ({
            let next = spec_apply(store, request).0;
            &&& state_properties(Proc::Store(next))
            &&& transition_properties(Proc::Store(store), Proc::Store(next))
        }),
{
    match request {
        StoreReq::PutIfNoneMatch { key, body } =>
            lemma_apply_put_none(store, key, body),
        StoreReq::PutIfMatch { key, body, etag } =>
            lemma_apply_put_match(store, key, body, etag),
        StoreReq::AppIfMatch { key, offset, body, etag } =>
            lemma_apply_append(store, key, offset, body, etag),
        StoreReq::Put { key, body } => lemma_apply_put(store, key, body),
        StoreReq::Del { key } => lemma_apply_delete(store, key),
        _ => lemma_store_stutter(store),
    }
}

proof fn lemma_store_step_integrity(
    store: StoreV,
    event: ProcessEvent<Pid, Message>,
)
    requires
        state_properties(Proc::Store(store)),
    ensures
        forall|i: int| 0 <= i < spec_store(store, event).len() ==> {
            let next = #[trigger] spec_store(store, event)[i].state;
            &&& state_properties(next)
            &&& transition_properties(Proc::Store(store), next)
        },
{
    match event {
        ProcessEvent::Receive {
            sender,
            message: Message::StoreReq { op, request },
        } => {
            if store.seen.contains((sender, op)) {
                lemma_store_stutter(store);
            } else {
                lemma_apply_integrity(store, request);
                let applied = spec_apply(store, request).0;
                let next = StoreV {
                    seen: store.seen.push((sender, op)),
                    ..applied
                };
                assert(next.seen.no_duplicates()) by {
                    assert forall|i: int, j: int|
                        0 <= i < next.seen.len()
                            && 0 <= j < next.seen.len()
                            && i != j
                        implies #[trigger] next.seen[i]
                            != #[trigger] next.seen[j] by {
                        if i < store.seen.len() && j < store.seen.len() {
                        } else if i < store.seen.len() {
                            assert(next.seen[j] == (sender, op));
                        } else {
                            assert(next.seen[i] == (sender, op));
                        }
                    };
                };
                assert(store_entries_ordered(next));
                assert(store_entries_unique(next));
                assert(store_versions_positive(next));
                assert forall|i: int| 0 <= i < store.entries.len() implies {
                    let old = #[trigger] store.entries[i];
                    match spec_find(next.entries, old.key, 0) {
                        Some(j) => old.version <= next.entries[j].version,
                        None => true,
                    }
                } by {};
                assert forall|seen: (Pid, u64)| store.seen.contains(seen)
                    implies next.seen.contains(seen) by {
                    let i = choose|i: int| 0 <= i < store.seen.len()
                        && #[trigger] store.seen[i] == seen;
                    assert(next.seen[i] == store.seen[i]);
                };
                assert(state_properties(Proc::Store(next)));
                assert(transition_properties(
                    Proc::Store(store),
                    Proc::Store(next),
                ));
            }
        },
        _ => {},
    }
}

proof fn lemma_initial_node(config: Config, id: u64)
    ensures
        state_properties(Proc::Node(crate::rover::spec_initial_node(config, id))),
{
}

proof fn lemma_initial_nodes(config: Config, id: u64)
    requires
        id <= config.nodes,
    ensures
        forall|i: int| 0 <= i < spec_nodes(config, id).len()
            ==> state_properties(#[trigger] spec_nodes(config, id)[i].1),
    decreases config.nodes - id,
{
    if id < config.nodes {
        lemma_initial_node(config, id);
        lemma_initial_nodes(config, (id + 1) as u64);
        let nodes = spec_nodes(config, id);
        let tail = spec_nodes(config, (id + 1) as u64);
        assert(nodes == seq![(
            Pid::Node(id),
            Proc::Node(crate::rover::spec_initial_node(config, id)),
        )] + tail);
        assert forall|i: int| 0 <= i < nodes.len()
            implies state_properties(#[trigger] nodes[i].1) by {
            if i == 0 {
                assert(nodes[0].1
                    == Proc::Node(crate::rover::spec_initial_node(config, id)));
            } else {
                assert(nodes[i] == tail[i - 1]);
            }
        };
    }
}

proof fn lemma_initial_world(config: Config)
    ensures
        forall|i: int| 0 <= i < spec_world(config).len()
            ==> state_properties(#[trigger] spec_world(config)[i].1),
{
    lemma_initial_nodes(config, 0);
}

pub proof fn property_proof(config: Config)
    ensures
        property_claim(config),
{
    lemma_process_layout(config);
    assert forall|doc: DocumentBodyV| document_object_order(doc) by {
        lemma_document_object_order(doc);
    };
    lemma_initial_world(config);
    assert forall|before: Proc, now: Time, event: ProcessEvent<Pid, Message>, i: int|
        #![trigger before.on_event(config, now, event)[i]]
        state_properties(before)
        && 0 <= i
        && i < before.on_event(config, now, event).len()
        implies step_properties(
            before,
            before.on_event(config, now, event)[i],
        ) by {
        match before {
            Proc::Node(node) => {
                lemma_node_step_integrity(config, node, now, event);
            },
            Proc::Store(store) => {
                lemma_store_step_integrity(store, event);
            },
        }
    };
}

pub proof fn lemma_string_realised(chars: Seq<char>)
    ensures
        spec_string(chars)@ == chars,
{
    reveal(spec_string);
    axiom_string_realised(chars);
}

pub proof fn lemma_string_of(s: String)
    ensures
        spec_string(s@) == s,
{
    lemma_string_realised(s@);
    axiom_string_ext(spec_string(s@), s);
}

pub proof fn lemma_bytes_realised(bytes: Seq<u8>)
    ensures
        spec_bytes(bytes)@ == bytes,
{
    reveal(spec_bytes);
    axiom_bytes_realised(bytes);
}

pub proof fn lemma_keyed_notes_from_input(
    doc: DocumentBodyV,
    notes: Seq<NoteV>,
    count: nat,
    k: int,
)
    requires
        count <= notes.len(),
        0 <= k < spec_keyed_notes(doc, notes, count).len(),
    ensures
        exists|j: int| 0 <= j < count
            && spec_keyed_notes(doc, notes, count)[k] == notes[j],
    decreases count,
{
    if count > 0 {
        let prior = spec_keyed_notes(doc, notes, (count - 1) as nat);
        let note = notes[count as int - 1];
        if !spec_note_relevant(doc, note) || exists|i: int| 0 <= i < prior.len()
            && spec_note_key(prior[i]) == spec_note_key(note)
        {
            lemma_keyed_notes_from_input(doc, notes, (count - 1) as nat, k);
        } else if k < prior.len() {
            lemma_keyed_notes_from_input(doc, notes, (count - 1) as nat, k);
        } else {
            assert(k == prior.len());
        }
    }
}

proof fn lemma_before_irrefl(a: Seq<char>)
    ensures
        !spec_before(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_before_irrefl(a.drop_first());
    }
}

proof fn lemma_before_trans(a: Seq<char>, b: Seq<char>, c: Seq<char>)
    requires
        spec_before(a, b),
        spec_before(b, c),
    ensures
        spec_before(a, c),
    decreases a.len() + b.len() + c.len(),
{
    if a.len() == 0 {
    } else if b.len() == 0 {
    } else if c.len() == 0 {
    } else if a[0] != b[0] {
    } else if b[0] != c[0] {
    } else {
        lemma_before_trans(a.drop_first(), b.drop_first(), c.drop_first());
    }
}

proof fn lemma_least_key_exists(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        exists|k: Seq<char>| least_key(keys, k),
    decreases keys.len(),
{
    let x = keys.choose();
    assert(keys.contains(x));
    let rest = keys.remove(x);
    assert(rest.len() == keys.len() - 1);
    if rest.len() == 0 {
        assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
            if o != x {
                assert(rest.contains(o));
            } else {
                lemma_before_irrefl(x);
            }
        };
        assert(least_key(keys, x));
    } else {
        lemma_least_key_exists(rest);
        let m = choose|m: Seq<char>| least_key(rest, m);
        assert(keys.contains(m));
        if spec_before(x, m) {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, x) by {
                if o == x {
                    lemma_before_irrefl(x);
                } else {
                    assert(rest.contains(o));
                    if spec_before(o, x) {
                        lemma_before_trans(o, x, m);
                    }
                }
            };
            assert(least_key(keys, x));
        } else {
            assert forall|o: Seq<char>| keys.contains(o) implies !spec_before(o, m) by {
                if o != x {
                    assert(rest.contains(o));
                }
            };
            assert(least_key(keys, m));
        }
    }
}

pub proof fn lemma_min_key_present(keys: Set<Seq<char>>)
    requires
        keys.finite(),
        keys.len() > 0,
    ensures
        keys.contains(spec_min_key(keys)),
{
    reveal(spec_min_key);
    lemma_least_key_exists(keys);
    let k = choose|k: Seq<char>| least_key(keys, k);
    assert(keys.contains(k) && forall|o: Seq<char>| keys.contains(o) ==> !spec_before(o, k));
}



pub proof fn lemma_prefix_bounds(bytes: Seq<u8>, width: nat, pos: nat)
    requires
        pos <= bytes.len(),
        pos <= width,
    ensures
        pos <= spec_prefix(bytes, width, pos) <= bytes.len(),
    decreases width - pos,
{
    if pos >= width {
    } else if pos >= bytes.len() || !spec_utf8_ok(bytes[0], pos, bytes[pos as int]) {
    } else {
        lemma_prefix_bounds(bytes, width, pos + 1);
    }
}


}
