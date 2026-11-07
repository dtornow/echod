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
    spec_advance_stored, spec_key, spec_request_transition, spec_stored_body,
    spec_stored_committed_at, spec_unavailable,
};

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
    let (body, response, _, _) = spec_request_transition(
        spec_stored_body(document),
        request,
        now,
        retry_timeout,
        limit,
    );
    if response == spec_unavailable(request) {
        document
    } else {
        spec_advance_stored(document, body, now)
    }
}

/// The request is routed to this stored document.
pub open spec fn routed(document: StoredDocumentV, request: Request) -> bool {
    match (document, spec_key(request)) {
        (StoredDocumentV::Workflow(workflow), Some(key)) =>
            key == seq!['d', '/'] + workflow.document,
        (StoredDocumentV::Schedule(schedule), Some(key)) =>
            key == seq!['s', '/'] + schedule.document,
        (_, None) => false,
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
}

} // verus!
