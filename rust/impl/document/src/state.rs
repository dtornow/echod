//! The document as the specification sees it: three maps, the fold of the rows.

use vstd::prelude::*;

use crate::types::*;

verus! {

/// Replay rows: each row replaces the entry at its key.
pub open spec fn fold_by<T, K, V>(s: Seq<T>, key: spec_fn(T) -> K, val: spec_fn(T) -> V) -> Map<K, V>
    decreases s.len(),
{
    if s.len() == 0 {
        Map::empty()
    } else {
        fold_by(s.drop_last(), key, val).insert(key(s.last()), val(s.last()))
    }
}

/// Some row carries key `k`.
pub open spec fn mentions<T, K>(s: Seq<T>, key: spec_fn(T) -> K, k: K) -> bool {
    exists|i: int| 0 <= i < s.len() && #[trigger] key(s[i]) == k
}

/// No two rows share a key.
pub open spec fn distinct_by<T, K>(s: Seq<T>, key: spec_fn(T) -> K) -> bool {
    forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && #[trigger] key(s[i]) == #[trigger] key(s[j]) ==> i == j
}

// ---------------------------------------------------------------------------
// The state
// ---------------------------------------------------------------------------

/// The state as the specification sees it. The executable rows are the
/// kernel's `State`; this is what `State::view` returns.
#[cfg(verus_keep_ghost)]
pub struct AState {
    pub objects: Map<Seq<char>, APromise>,
    pub schedules: Map<Seq<char>, ASchedule>,
    pub outbox: Map<OutboxKey, AOutboxEntry>,
}

pub open spec fn obj_key() -> spec_fn(Promise) -> Seq<char> {
    |p: Promise| p.id@
}

pub open spec fn obj_val() -> spec_fn(Promise) -> APromise {
    |p: Promise| p@
}

pub open spec fn sched_key() -> spec_fn(Schedule) -> Seq<char> {
    |c: Schedule| c.id@
}

pub open spec fn sched_val() -> spec_fn(Schedule) -> ASchedule {
    |c: Schedule| c@
}

pub open spec fn out_key() -> spec_fn(OutboxEntry) -> OutboxKey {
    |e: OutboxEntry| e@.key()
}

pub open spec fn out_val() -> spec_fn(OutboxEntry) -> AOutboxEntry {
    |e: OutboxEntry| e@
}

} // verus!
