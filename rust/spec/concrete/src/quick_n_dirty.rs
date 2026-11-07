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

/// The preservation statement to discharge handler by handler. It is kept as
/// a proposition, not asserted as a theorem: with the full document
/// invariant, current handlers do not yet establish it.
pub open spec fn request_preserves_well_formed(
    document: StoredDocumentV,
    request: Request,
    now: u64,
) -> bool {
    well_formed(document) ==> well_formed(on_request(document, request, now))
}

} // verus!
