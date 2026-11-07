//! Small, local document theorems.
//!
//! This module deliberately does not mention Rover, worlds, nodes, the
//! network, or the object store.  It treats the concrete document machine as
//! a pure transition system: apply one document event, then install the
//! resulting body in the same stored document.

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use echod_types::origin;
use echod_types::Request;

use crate::document::{DocumentBodyV, StoredDocumentV};
use crate::node::PendingV;
#[cfg(verus_keep_ghost)]
use crate::node::{
    spec_advance_stored, spec_body_deadline, spec_handle, spec_occurrence, spec_run_due,
    spec_stored_body, spec_stored_committed_at, spec_stored_name, spec_stored_version, spec_sweep,
};

verus! {

/// The document-level events whose updates can be checked without a Rover
/// world.  `at` is the logical instant assigned to the resulting commit.
pub ghost enum Event {
    Request { request: Request, at: u64 },
    Sweep { at: u64, retry_timeout: u64, limit: nat },
    Due { at: u64, retry_timeout: u64 },
    Occurrence { pending: PendingV, at: u64 },
}

pub open spec fn event_time(event: Event) -> u64 {
    match event {
        Event::Request { at, .. }
        | Event::Sweep { at, .. }
        | Event::Due { at, .. }
        | Event::Occurrence { at, .. } => at,
    }
}

/// The metadata's cached wake is exactly the body's least deadline.
pub open spec fn expected_wake(body: DocumentBodyV) -> Option<u64> {
    match spec_body_deadline(body) {
        Some(at) => Some(at as u64),
        None => None,
    }
}

/// The first local invariant: redundant wake metadata agrees with the body.
/// More document-local clauses can be conjoined here without involving the
/// Rover model.
pub open spec fn well_formed(document: StoredDocumentV) -> bool {
    match document {
        StoredDocumentV::Workflow(workflow) =>
            workflow.next_wake_at
                == expected_wake(DocumentBodyV::Workflow(workflow.objects)),
        StoredDocumentV::Schedule(schedule) =>
            schedule.next_wake_at
                == expected_wake(DocumentBodyV::Schedule(schedule.schedule)),
    }
}

/// The update produced by one event, independently of process/store
/// orchestration.
pub open spec fn update(body: DocumentBodyV, event: Event) -> DocumentBodyV {
    match event {
        Event::Request { request, at } => spec_handle(body, request, at).0,
        Event::Sweep { at, retry_timeout, limit } =>
            spec_sweep(body, at, retry_timeout, limit).0,
        Event::Due { at, retry_timeout } =>
            spec_run_due(body, at, retry_timeout).0,
        Event::Occurrence { pending, at } =>
            spec_occurrence(body, pending, at),
    }
}

/// An event is routed to the document whose identity it can mutate.
pub open spec fn applicable(document: StoredDocumentV, event: Event) -> bool {
    match (document, event) {
        (StoredDocumentV::Workflow(workflow), Event::Occurrence { pending, .. }) =>
            origin(pending.promise) == workflow.document,
        (StoredDocumentV::Workflow(_), Event::Sweep { .. })
        | (StoredDocumentV::Workflow(_), Event::Due { .. }) => true,
        (StoredDocumentV::Schedule(_), Event::Due { .. }) => true,
        (StoredDocumentV::Schedule(_), Event::Sweep { .. }) => true,
        (_, Event::Request { request, .. }) => {
            // The real process performs the same routing check before opening
            // a document.  The theorem needs only the resulting body shape:
            // workflow requests preserve workflow bodies and schedule
            // requests preserve schedule bodies.
            match (document, request) {
                (StoredDocumentV::Workflow(_), Request::ScheduleGet(_)
                    | Request::ScheduleCreate(_) | Request::ScheduleDelete(_)) => false,
                (StoredDocumentV::Schedule(_), Request::ScheduleGet(_)
                    | Request::ScheduleCreate(_) | Request::ScheduleDelete(_)) => true,
                (StoredDocumentV::Workflow(_), _) => true,
                (StoredDocumentV::Schedule(_), _) => false,
            }
        },
        _ => false,
    }
}

/// A top-level document step: compute its update, then install that update as
/// a new committed version of the same document.
pub open spec fn on_event(document: StoredDocumentV, event: Event) -> StoredDocumentV {
    spec_advance_stored(
        document,
        update(spec_stored_body(document), event),
        event_time(event),
    )
}

/// Request handlers preserve the document family.  This is intentionally
/// local and can be strengthened as more clauses are added to `well_formed`.
pub proof fn lemma_request_shape(
    body: DocumentBodyV,
    request: Request,
    now: u64,
)
    requires
        match (body, request) {
            (DocumentBodyV::Workflow(_), Request::ScheduleGet(_)
                | Request::ScheduleCreate(_) | Request::ScheduleDelete(_)) => false,
            (DocumentBodyV::Schedule(_), Request::ScheduleGet(_)
                | Request::ScheduleCreate(_) | Request::ScheduleDelete(_)) => true,
            (DocumentBodyV::Workflow(_), _) => true,
            (DocumentBodyV::Schedule(_), _) => false,
        },
    ensures
        body is Workflow ==> spec_handle(body, request, now).0 is Workflow,
        body is Schedule ==> spec_handle(body, request, now).0 is Schedule,
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
        | Request::TaskHeartbeat(_)
        | Request::TaskSuspend(_) => {},
        Request::ScheduleGet(_)
        | Request::ScheduleCreate(_)
        | Request::ScheduleDelete(_) => {},
    }
}

/// Installing an update preserves identity, advances the logical version,
/// and records the event's commit instant.
pub proof fn lemma_on_event_metadata(
    document: StoredDocumentV,
    event: Event,
)
    ensures
        spec_stored_name(on_event(document, event)) == spec_stored_name(document),
        spec_stored_version(on_event(document, event))
            == spec_stored_version(document).saturating_add(1),
        spec_stored_committed_at(on_event(document, event)) == event_time(event),
{
}

/// The single local invariant: every applicable event takes a well-formed
/// document to another well-formed document.
pub proof fn lemma_on_event_preserves_well_formed(
    document: StoredDocumentV,
    event: Event,
)
    requires
        well_formed(document),
        applicable(document, event),
    ensures
        well_formed(on_event(document, event)),
{
    let body = spec_stored_body(document);
    let next = update(body, event);
    match event {
        Event::Request { request, at } => {
            lemma_request_shape(body, request, at);
        },
        Event::Sweep { .. } | Event::Due { .. } | Event::Occurrence { .. } => {},
    }
}

} // verus!
