//! One deliberately small document theorem, independent of Rover.

use vstd::prelude::*;

use echod_types::Request;

#[cfg(verus_keep_ghost)]
use crate::document::well_formed;
use crate::document::StoredDocumentV;
#[cfg(verus_keep_ghost)]
use crate::node::{spec_advance_stored, spec_handle, spec_stored_body};

verus! {

/// Apply an existing request handler's update to the stored document.
pub open spec fn on_request(
    document: StoredDocumentV,
    request: Request,
    now: u64,
) -> StoredDocumentV {
    spec_advance_stored(
        document,
        spec_handle(spec_stored_body(document), request, now).0,
        now,
    )
}

/// Every request takes a well-formed document to a well-formed document.
pub proof fn lemma_request_preserves_well_formed(
    document: StoredDocumentV,
    request: Request,
    now: u64,
)
    requires
        well_formed(document),
    ensures
        well_formed(on_request(document, request, now)),
{
}

} // verus!
