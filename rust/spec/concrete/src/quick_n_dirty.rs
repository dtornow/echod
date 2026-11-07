//! The local preservation theorem for a complete document request.
//!
//! A request is not a raw handler call.  The committed transition closes
//! work already due, runs the raw handler, and closes work made immediately
//! due by that handler.  Exhausting either finite closure budget is an atomic
//! 503: the stored document and all effects are left untouched.

use vstd::prelude::*;

use echod_types::Request;

#[cfg(verus_keep_ghost)]
use crate::document::well_formed;
use crate::document::StoredDocumentV;
#[cfg(verus_keep_ghost)]
use crate::node::{
    spec_advance_stored, spec_key, spec_request_commits, spec_request_document,
    spec_request_transition, spec_stored_body, spec_stored_committed_at, spec_stored_name,
};
#[cfg(verus_keep_ghost)]
use crate::interpret::{lemma_origin_key, lemma_schedule_key};

verus! {

/// Apply one complete request transition.  A closure failure is not a
/// commit, so even the document metadata remains unchanged.
pub open spec fn on_request(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
) -> StoredDocumentV {
    let (body, _, _, _) = spec_request_transition(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        limit,
    );
    if spec_request_commits(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        limit,
    ) {
        spec_advance_stored(document, body, now)
    } else {
        document
    }
}

/// The request is routed to this stored document.
pub open spec fn routed(document: StoredDocumentV, request: Request) -> bool {
    match (document, spec_key(request)) {
        (StoredDocumentV::Workflow(workflow), Some(key)) =>
            key == seq!['o', '/'] + workflow.document,
        (StoredDocumentV::Schedule(schedule), Some(key)) =>
            key == seq!['s', '/'] + schedule.document,
        (_, None) => false,
    }
}

proof fn lemma_key_names_document(request: Request)
    ensures
        match (spec_key(request), spec_request_document(request)) {
            (Some(key), Some(document)) => key.skip(2) == document,
            (None, None) => true,
            _ => false,
        },
{
    match request {
        Request::PromiseGet(_)
        | Request::PromiseCreate(_)
        | Request::PromiseSettle(_)
        | Request::PromiseRegisterCallback(_)
        | Request::PromiseRegisterListener(_)
        | Request::TaskGet(_)
        | Request::TaskCreate(_)
        | Request::TaskAcquire(_)
        | Request::TaskFulfill(_)
        | Request::TaskRelease(_)
        | Request::TaskHalt(_)
        | Request::TaskContinue(_)
        | Request::TaskFence(_)
        | Request::TaskFenceCheck(_)
        | Request::TaskSuspend(_) => {
            lemma_origin_key(spec_request_document(request)->0);
        },
        Request::TaskHeartbeat(q) => {
            if q.tasks@.len() > 0 {
                lemma_origin_key(spec_request_document(request)->0);
            }
        },
        Request::ScheduleGet(_)
        | Request::ScheduleCreate(_)
        | Request::ScheduleDelete(_) => {
            lemma_schedule_key(spec_request_document(request)->0);
        },
    }
}

proof fn lemma_routed_document(document: StoredDocumentV, request: Request)
    requires
        routed(document, request),
    ensures
        spec_request_document(request) == Some(spec_stored_name(document)),
{
    lemma_key_names_document(request);
    match document {
        StoredDocumentV::Workflow(workflow) => {
            lemma_origin_key(workflow.document);
        },
        StoredDocumentV::Schedule(schedule) => {
            lemma_schedule_key(schedule.document);
        },
    }
}

/// Full preservation: all promise, task, callback, suspended-rung, schedule,
/// metadata, and exact-next-wake clauses in `document::well_formed` survive
/// the complete request transition.
pub proof fn lemma_request_preserves_well_formed(
    document: StoredDocumentV,
    request: Request,
    now: u64,
    retry_timeout: u64,
    limit: nat,
)
    requires
        well_formed(document),
        routed(document, request),
        spec_stored_committed_at(document) <= now,
    ensures
        well_formed(on_request(document, request, now, retry_timeout, limit)),
{
    if spec_request_commits(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        limit,
    ) {
        lemma_routed_document(document, request);
        let (body, _, _, _) = spec_request_transition(
            spec_stored_body(document),
            request,
            now,
            retry_timeout,
            limit,
        );
        assert(crate::document::body_well_formed(
            spec_stored_name(document),
            body,
            now,
        ));
        match (document, body) {
            (StoredDocumentV::Workflow(_), crate::node::DocumentBodyV::Workflow(_)) => {},
            (StoredDocumentV::Schedule(_), crate::node::DocumentBodyV::Schedule(_)) => {},
            _ => {},
        }
    }
}

} // verus!
