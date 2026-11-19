use vstd::prelude::*;
use echod_concrete_spec::state::*;
use echod_concrete_spec::handler::*;
use echod_types::ProductionOwner;

verus! {

pub enum Delivery {
    Pending,
    Delivered,
    Cancelled,
}

pub struct Invocation {
    pub incarnation: nat,
    pub op: u64,
    pub request: StoreReqSpec,
    pub outcome: Option<StoreRes>,
    pub delivery: Delivery,
}

pub open spec fn issue(
    history: Seq<Invocation>, incarnation: nat, op: u64, request: StoreReqSpec,
) -> Seq<Invocation> {
    history.push(Invocation {
        incarnation, op, request, outcome: None, delivery: Delivery::Pending,
    })
}

pub open spec fn record_outcome(
    history: Seq<Invocation>, iid: int, response: StoreRes,
) -> Option<Seq<Invocation>> {
    if 0 <= iid < history.len() && history[iid].outcome.is_none() {
        Some(history.update(iid, Invocation { outcome: Some(response), ..history[iid] }))
    } else {
        None
    }
}

pub open spec fn deliver(history: Seq<Invocation>, iid: int)
    -> Option<(Seq<Invocation>, nat, u64, StoreRes)>
{
    if 0 <= iid < history.len() && history[iid].delivery is Pending
        && history[iid].outcome.is_some()
    {
        Some((history.update(iid, Invocation { delivery: Delivery::Delivered, ..history[iid] }),
            history[iid].incarnation, history[iid].op, history[iid].outcome.unwrap()))
    } else {
        None
    }
}

pub open spec fn cancel(history: Seq<Invocation>, iid: int) -> Option<Seq<Invocation>> {
    if 0 <= iid < history.len() && history[iid].delivery is Pending {
        Some(history.update(iid, Invocation { delivery: Delivery::Cancelled, ..history[iid] }))
    } else {
        None
    }
}

pub open spec fn callback(history: Seq<Invocation>, iid: int, clock: u64)
    -> Option<(nat, ProductionEventV)>
{
    match deliver(history, iid) {
        Some((_, incarnation, op, response)) =>
            Some((incarnation, ProductionEventV::Store { op, response, clock })),
        None => None,
    }
}

pub proof fn callback_projects_to_the_actual_event(history: Seq<Invocation>, iid: int, clock: u64)
    requires deliver(history, iid).is_some(),
    ensures callback(history, iid, clock)
        == Some((history[iid].incarnation,
            ProductionEventV::Store { op: history[iid].op, response: history[iid].outcome.unwrap(), clock })),
{
}

pub proof fn same_wire_callback_is_indistinguishable_to_handler(
    history: Seq<Invocation>, first: int, second: int, clock: u64, state: ProductionStateV,
)
    requires
        deliver(history, first).is_some(),
        deliver(history, second).is_some(),
        history[first].incarnation == history[second].incarnation,
        history[first].op == history[second].op,
        history[first].outcome == history[second].outcome,
    ensures
        callback(history, first, clock) == callback(history, second, clock),
        production_handler_spec_on_event(state, callback(history, first, clock).unwrap().1)
            == production_handler_spec_on_event(state, callback(history, second, clock).unwrap().1),
{
}

pub open spec fn well_formed(history: Seq<Invocation>) -> bool {
    forall|i: int| 0 <= i < history.len() && history[i].delivery is Delivered
        ==> history[i].outcome.is_some()
}

pub enum Action {
    Issue { incarnation: nat, op: u64, request: StoreReqSpec },
    Record { iid: int, response: StoreRes },
    Deliver { iid: int },
    Cancel { iid: int },
}

pub open spec fn advance(history: Seq<Invocation>, action: Action) -> Option<Seq<Invocation>> {
    match action {
        Action::Issue { incarnation, op, request } => Some(issue(history, incarnation, op, request)),
        Action::Record { iid, response } => record_outcome(history, iid, response),
        Action::Deliver { iid } => match deliver(history, iid) {
            Some((next, _, _, _)) => Some(next),
            None => None,
        },
        Action::Cancel { iid } => cancel(history, iid),
    }
}

pub proof fn lifecycle_step_preserves_receipt_history(history: Seq<Invocation>, action: Action)
    requires well_formed(history), advance(history, action).is_some(),
    ensures ({
        let next = advance(history, action).unwrap();
        &&& well_formed(next)
        &&& next.len() >= history.len()
        &&& forall|i: int| 0 <= i < history.len() ==> {
            &&& next[i].incarnation == history[i].incarnation
            &&& next[i].op == history[i].op
            &&& next[i].request == history[i].request
            &&& (history[i].outcome.is_some() ==> next[i].outcome == history[i].outcome)
            &&& (!(history[i].delivery is Pending) ==> next[i].delivery == history[i].delivery)
        }
    }),
{
    match action {
        Action::Issue { .. } => {},
        Action::Record { .. } => {},
        Action::Deliver { .. } => {},
        Action::Cancel { .. } => {},
    }
}

pub open spec fn run(history: Seq<Invocation>, actions: Seq<Action>) -> Option<Seq<Invocation>>
    decreases actions.len(),
{
    if actions.len() == 0 {
        Some(history)
    } else {
        match run(history, actions.drop_last()) {
            Some(prefix) => advance(prefix, actions.last()),
            None => None,
        }
    }
}

pub proof fn lifecycle_prefix_preserves_receipts(
    history: Seq<Invocation>, actions: Seq<Action>,
)
    requires well_formed(history), run(history, actions).is_some(),
    ensures ({
        let next = run(history, actions).unwrap();
        &&& well_formed(next)
        &&& next.len() >= history.len()
        &&& forall|i: int| 0 <= i < history.len() ==> {
            &&& next[i].incarnation == history[i].incarnation
            &&& next[i].op == history[i].op
            &&& next[i].request == history[i].request
            &&& (history[i].outcome.is_some() ==> next[i].outcome == history[i].outcome)
            &&& (!(history[i].delivery is Pending) ==> next[i].delivery == history[i].delivery)
        }
    }),
    decreases actions.len(),
{
    if actions.len() > 0 {
        lifecycle_prefix_preserves_receipts(history, actions.drop_last());
        lifecycle_step_preserves_receipt_history(
            run(history, actions.drop_last()).unwrap(), actions.last());
    }
}

pub proof fn emitted_effect_has_distinct_ghost_invocation(
    history: Seq<Invocation>, incarnation: nat, effect: ProductionEffectV,
)
    requires effect is Store,
    ensures match effect {
        ProductionEffectV::Store { op, request } => {
        let next = issue(history, incarnation, op, request);
        &&& next.len() == history.len() + 1
        &&& next.take(history.len() as int) == history
        &&& next.last().incarnation == incarnation
        &&& next.last().op == op
        &&& next.last().request == request
        &&& next.last().outcome.is_none()
        },
        _ => false,
    },
{
}

pub proof fn outcome_is_recorded_once(history: Seq<Invocation>, iid: int, response: StoreRes)
    requires record_outcome(history, iid, response).is_some(),
    ensures
        forall|other: StoreRes|
            record_outcome(record_outcome(history, iid, response).unwrap(), iid, other).is_none(),
        record_outcome(history, iid, response).unwrap()[iid].request == history[iid].request,
        record_outcome(history, iid, response).unwrap()[iid].op == history[iid].op,
{
}

pub proof fn delivery_is_once_and_erases_ghost_identity(history: Seq<Invocation>, iid: int)
    requires deliver(history, iid).is_some(),
    ensures ({
        let (next, incarnation, op, response) = deliver(history, iid).unwrap();
        &&& deliver(next, iid).is_none()
        &&& incarnation == history[iid].incarnation
        &&& op == history[iid].op
        &&& response == history[iid].outcome.unwrap()
        &&& next[iid].request == history[iid].request
    }),
{
}

pub proof fn cancellation_does_not_erase_a_store_outcome(history: Seq<Invocation>, iid: int)
    requires cancel(history, iid).is_some(),
    ensures
        cancel(history, iid).unwrap()[iid].outcome == history[iid].outcome,
        deliver(cancel(history, iid).unwrap(), iid).is_none(),
{
}

pub proof fn cancellation_allows_later_outcome_recording(
    history: Seq<Invocation>, iid: int, response: StoreRes,
)
    requires
        0 <= iid < history.len(),
        history[iid].delivery is Pending,
        history[iid].outcome.is_none(),
    ensures ({
        let cancelled = cancel(history, iid).unwrap();
        let completed = record_outcome(cancelled, iid, response);
        &&& completed.is_some()
        &&& completed.unwrap()[iid].outcome == Some(response)
        &&& deliver(completed.unwrap(), iid).is_none()
    }),
{
}

pub proof fn reused_wire_id_does_not_suppress_an_older_completion(
    history: Seq<Invocation>, incarnation: nat, op: u64,
    old_request: StoreReqSpec, new_request: StoreReqSpec, response: StoreRes,
)
    ensures ({
        let first = issue(history, incarnation, op, old_request);
        let completed = record_outcome(first, history.len() as int, response).unwrap();
        let second = issue(completed, incarnation, op, new_request);
        let callback = deliver(second, history.len() as int);
        &&& callback.is_some()
        &&& callback.unwrap().2 == op
        &&& callback.unwrap().3 == response
        &&& second.last().op == op
        &&& second.last().request == new_request
        &&& second.last().delivery is Pending
    }),
{
}

pub proof fn matched_read_receipt_binds_working_snapshot(
    history: Seq<Invocation>, iid: int, store: StoreV, state: ProductionStateV,
    origin: Seq<char>, key: String, bytes: Vec<u8>, etag: Etag, loaded: LoadedDocumentV,
)
    requires
        0 <= iid < history.len(),
        history[iid].request == (StoreReqSpec::Get { key: key@ }),
        history[iid].outcome.is_none(),
        key@ == production_keys_spec_doc_key(state.keys.prefix, origin),
        spec_apply(store, StoreReq::Get { key }).1
            == (StoreRes::Get { result: Ok(Some((bytes, etag))) }),
        production_document_spec_decode_workflow(bytes@) == Ok(loaded),
    ensures ({
        let response = StoreRes::Get { result: Ok(Some((bytes, etag))) };
        let next = record_outcome(history, iid, response);
        &&& next.is_some()
        &&& next.unwrap()[iid].request == history[iid].request
        &&& next.unwrap()[iid].outcome == Some(response)
        &&& store.entries[spec_find(store.entries, key@, 0).unwrap()].body == bytes@
        &&& etag == spec_etag(bytes@)
        &&& production_handler_docs_spec_loaded_origin(state, origin, None, response).1
            == Ok(ProductionWorkingV {
                target: origin, key: key@, loaded, etag: Some(etag.deep_view()),
            })
    }),
{
    super::provenance::successful_read_binds_working_snapshot(
        store, state, origin, key, bytes, etag, loaded);
}

pub proof fn issued_write_is_recorded_without_wire_id_freshness(
    history: Seq<Invocation>, incarnation: nat, state: ProductionStateV,
    fid: u64, commit: ProductionCommittingV, cond: Option<Seq<char>>, idle: bool,
)
    ensures ({
        let (issued, next_commit) =
            production_handler_docs_spec_issue_write(state, fid, commit, cond, idle);
        &&& next_commit.w == commit.w
        &&& match issued.out.last() {
            ProductionEffectV::Store { op, request } => {
                let next = issue(history, incarnation, op, request);
                &&& next.take(history.len() as int) == history
                &&& next.last().op == state.next_op
                &&& next.last().request == request
                &&& issued.ops[op] == ProductionOwner::Flight(fid)
            },
            _ => false,
        }
    }),
{
    super::provenance::write_issue_preserves_working_snapshot(state, fid, commit, cond, idle);
}

pub proof fn issued_write_body_is_the_actual_codec_observation(
    state: ProductionStateV, fid: u64, commit: ProductionCommittingV,
    cond: Option<Seq<char>>, idle: bool,
)
    ensures match production_handler_docs_spec_issue_write(state, fid, commit, cond, idle).0.out.last() {
        ProductionEffectV::Store { request, .. } => match request {
            StoreReqSpec::PutIfNoneMatch { body, .. }
            | StoreReqSpec::PutIfMatch { body, .. } =>
                body == production_document_spec_encode_body(commit.after),
            StoreReqSpec::AppIfMatch { body, offset, .. } =>
                body == production_document_spec_encode_delta(commit.w.loaded.document, commit.after).0
                    && offset == commit.w.loaded.bytes,
            _ => false,
        },
        _ => false,
    },
{
    reveal(production_handler_docs_spec_issue_write);
}

pub proof fn completion_and_delivery_frame_other_receipts(
    history: Seq<Invocation>, iid: int, response: StoreRes,
)
    requires record_outcome(history, iid, response).is_some(),
    ensures ({
        let next = record_outcome(history, iid, response).unwrap();
        &&& next.len() == history.len()
        &&& forall|j: int| 0 <= j < history.len() && j != iid ==> next[j] == history[j]
        &&& match deliver(next, iid) {
            Some((delivered, _, _, _)) =>
                forall|j: int| 0 <= j < history.len() && j != iid ==> delivered[j] == history[j],
            None => true,
        }
    }),
{
}

}
