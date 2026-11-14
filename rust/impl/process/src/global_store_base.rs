//! ETag/base compatibility and successful-write provenance for invariant 1.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code))]

use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::global_store_invariants::{
    certificate_belongs_to_commit, commit_issued_phase_provenance,
    commit_static_provenance, invariant1_certificate_matches_request,
};
#[cfg(verus_keep_ghost)]
use crate::state::S;

#[cfg(verus_keep_ghost)]
verus! {

/// A write can only be issued from the certified loaded base carried by the
/// commit. Append and rewrite requests both retain that exact base/ETag
/// relationship in their operation certificate.
pub proof fn lemma_certified_base_issues_compatible_write(
    core: S,
    fid: u64,
    commit: crate::handler_docs::CommittingSpec,
    condition: Option<Seq<char>>,
    idle: bool,
)
    requires
        commit_static_provenance(core, commit),
        commit_issued_phase_provenance(commit),
    ensures
        ({
            let issued = crate::handler_docs::spec_issue_write(
                core,
                fid,
                commit,
                condition,
                idle,
            );
            issued.2 ==> {
                let op = issued.1.expects().unwrap();
                &&& issued.0.store_requests.contains_key(op)
                &&& issued.0.store_certificates.contains_key(op)
                &&& invariant1_certificate_matches_request(
                    issued.0.keys.prefix,
                    issued.0.keys.bucket_ms,
                    issued.0.store_requests[op],
                    issued.0.store_certificates[op],
                )
                &&& certificate_belongs_to_commit(
                    issued.0.store_certificates[op],
                    issued.1,
                )
            }
        }),
{
    crate::global_store_invariants::
        lemma_issue_write_from_provenance_is_invariant1_safe(
            core,
            fid,
            commit,
            condition,
            idle,
        );
}

} // verus!
