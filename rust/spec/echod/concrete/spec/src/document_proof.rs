//! Proofs of the partial composition algebra.

use vstd::prelude::*;
use echod_types::{PromiseState, Schedule, Tags, TaskState, Value, MAX_TIME, MAX_VERSION};
#[cfg(verus_keep_ghost)]
use echod_types::origin;
use crate::document::*;

verus! {


/// Applying concatenated edits is the same as applying each sequence.
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


/// Compacting adjacent partials preserves their logical effect.
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
        spec_apply(spec_apply(document, first), second)
            == spec_apply(document, spec_compose(first, second)),
{
    lemma_apply_changes_append(document.entries, first.changes, second.changes);
}

} // verus!
