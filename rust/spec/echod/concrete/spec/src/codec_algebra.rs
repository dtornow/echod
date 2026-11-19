use vstd::prelude::*;

use crate::handler::{spec_apply_change, spec_apply_changes, spec_apply_document};
use crate::property_proof::lemma_apply_changes_append;
use crate::state::{ChangeV, FoldedV, PartialV};

verus! {

pub open spec fn enumerates<V>(rows: Map<Seq<char>, V>, keys: Seq<Seq<char>>) -> bool {
    keys.no_duplicates() && keys.to_set() == rows.dom()
}

pub open spec fn snapshot_changes<V>(
    rows: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
) -> Seq<ChangeV<V>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        snapshot_changes(rows, keys.drop_last()).push(
            ChangeV::Upsert { id: keys.last(), value: rows[keys.last()] },
        )
    }
}

pub open spec fn changed_upserts<V>(
    before: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
) -> Seq<ChangeV<V>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let prefix = changed_upserts(before, after, keys.drop_last());
        let id = keys.last();
        if !before.contains_key(id) || before[id] != after[id] {
            prefix.push(ChangeV::Upsert { id, value: after[id] })
        } else {
            prefix
        }
    }
}

pub open spec fn removed_changes<V>(
    after: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
) -> Seq<ChangeV<V>>
    decreases keys.len(),
{
    if keys.len() == 0 {
        Seq::empty()
    } else {
        let prefix = removed_changes(after, keys.drop_last());
        let id = keys.last();
        if after.contains_key(id) {
            prefix
        } else {
            prefix.push(ChangeV::Remove { id })
        }
    }
}

pub open spec fn delta_changes<V>(
    before: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    old_keys: Seq<Seq<char>>,
    new_keys: Seq<Seq<char>>,
) -> Seq<ChangeV<V>> {
    changed_upserts(before, after, new_keys) + removed_changes(after, old_keys)
}

pub open spec fn changed_count<V>(
    before: Map<Seq<char>, V>, after: Map<Seq<char>, V>, keys: Seq<Seq<char>>,
) -> nat
    decreases keys.len(),
{
    if keys.len() == 0 {
        0
    } else {
        changed_count(before, after, keys.drop_last())
            + if !before.contains_key(keys.last()) || before[keys.last()] != after[keys.last()] {
                1nat
            } else { 0nat }
    }
}

pub open spec fn removed_count<V>(after: Map<Seq<char>, V>, keys: Seq<Seq<char>>) -> nat
    decreases keys.len(),
{
    if keys.len() == 0 {
        0
    } else {
        removed_count(after, keys.drop_last())
            + if after.contains_key(keys.last()) { 0nat } else { 1nat }
    }
}

proof fn lemma_changed_count<V>(
    before: Map<Seq<char>, V>, after: Map<Seq<char>, V>, keys: Seq<Seq<char>>,
)
    ensures
        changed_upserts(before, after, keys).len() == changed_count(before, after, keys),
        changed_count(before, after, keys) <= keys.len(),
    decreases keys.len(),
{
    if keys.len() > 0 {
        lemma_changed_count(before, after, keys.drop_last());
    }
}

proof fn lemma_removed_count<V>(after: Map<Seq<char>, V>, keys: Seq<Seq<char>>)
    ensures
        removed_changes(after, keys).len() == removed_count(after, keys),
        removed_count(after, keys) <= keys.len(),
    decreases keys.len(),
{
    if keys.len() > 0 {
        lemma_removed_count(after, keys.drop_last());
    }
}

pub proof fn lemma_delta_count<V>(
    before: Map<Seq<char>, V>, after: Map<Seq<char>, V>,
    old_keys: Seq<Seq<char>>, new_keys: Seq<Seq<char>>,
)
    ensures
        delta_changes(before, after, old_keys, new_keys).len()
            == changed_count(before, after, new_keys) + removed_count(after, old_keys),
        delta_changes(before, after, old_keys, new_keys).len() <= old_keys.len() + new_keys.len(),
{
    lemma_changed_count(before, after, new_keys);
    lemma_removed_count(after, old_keys);
}

pub open spec fn overlay<V>(
    before: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
) -> Map<Seq<char>, V> {
    Map::new(
        before.dom().union(keys.to_set()),
        |id: Seq<char>| if keys.contains(id) { after[id] } else { before[id] },
    )
}

pub open spec fn prune<V>(
    rows: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
) -> Map<Seq<char>, V> {
    rows.remove_keys(keys.to_set().difference(after.dom()))
}

proof fn lemma_keys_last(keys: Seq<Seq<char>>)
    requires keys.len() > 0,
    ensures
        keys == keys.drop_last().push(keys.last()),
        forall|id: Seq<char>| keys.contains(id)
            <==> keys.drop_last().contains(id) || id == keys.last(),
{
    assert(keys == keys.drop_last().push(keys.last()));
}

proof fn lemma_apply_push<V>(rows: Map<Seq<char>, V>, changes: Seq<ChangeV<V>>, c: ChangeV<V>)
    ensures spec_apply_changes(rows, changes.push(c))
        == spec_apply_change(spec_apply_changes(rows, changes), c),
{
    assert(changes.push(c).drop_last() == changes);
    assert(changes.push(c).last() == c);
    reveal_with_fuel(spec_apply_changes, 2);
}

proof fn lemma_snapshot_overlay<V>(
    base: Map<Seq<char>, V>,
    rows: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
)
    requires keys.to_set().subset_of(rows.dom()),
    ensures
        spec_apply_changes(base, snapshot_changes(rows, keys)) == overlay(base, rows, keys),
        snapshot_changes(rows, keys).len() == keys.len(),
    decreases keys.len(),
{
    reveal_with_fuel(spec_apply_changes, 2);
    reveal_with_fuel(snapshot_changes, 2);
    if keys.len() == 0 {
        assert(overlay(base, rows, keys) =~= base);
    } else {
        lemma_keys_last(keys);
        assert(keys.drop_last().to_set().subset_of(rows.dom()));
        lemma_snapshot_overlay(base, rows, keys.drop_last());
        lemma_apply_push(base, snapshot_changes(rows, keys.drop_last()),
            ChangeV::Upsert { id: keys.last(), value: rows[keys.last()] });
        assert(overlay(base, rows, keys)
            =~= overlay(base, rows, keys.drop_last()).insert(keys.last(), rows[keys.last()]));
    }
}

pub proof fn lemma_snapshot_changes<V>(
    rows: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
)
    requires enumerates(rows, keys),
    ensures
        spec_apply_changes(Map::empty(), snapshot_changes(rows, keys)) == rows,
        snapshot_changes(rows, keys).len() == keys.len(),
{
    lemma_snapshot_overlay(Map::empty(), rows, keys);
    assert(overlay(Map::empty(), rows, keys) =~= rows);
}

proof fn lemma_changed_overlay<V>(
    before: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
)
    requires keys.to_set().subset_of(after.dom()),
    ensures
        spec_apply_changes(before, changed_upserts(before, after, keys))
            == overlay(before, after, keys),
    decreases keys.len(),
{
    reveal_with_fuel(spec_apply_changes, 2);
    reveal_with_fuel(changed_upserts, 2);
    if keys.len() == 0 {
        assert(overlay(before, after, keys) =~= before);
    } else {
        lemma_keys_last(keys);
        assert(keys.drop_last().to_set().subset_of(after.dom()));
        lemma_changed_overlay(before, after, keys.drop_last());
        let id = keys.last();
        if !before.contains_key(id) || before[id] != after[id] {
            lemma_apply_push(before, changed_upserts(before, after, keys.drop_last()),
                ChangeV::Upsert { id, value: after[id] });
            assert(overlay(before, after, keys)
                =~= overlay(before, after, keys.drop_last()).insert(id, after[id]));
        } else {
            assert(overlay(before, after, keys) =~= overlay(before, after, keys.drop_last()));
        }
    }
}

proof fn lemma_removed_prune<V>(
    rows: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    keys: Seq<Seq<char>>,
)
    ensures spec_apply_changes(rows, removed_changes(after, keys)) == prune(rows, after, keys),
    decreases keys.len(),
{
    reveal_with_fuel(spec_apply_changes, 2);
    reveal_with_fuel(removed_changes, 2);
    if keys.len() == 0 {
        assert(prune(rows, after, keys) =~= rows);
    } else {
        lemma_keys_last(keys);
        lemma_removed_prune(rows, after, keys.drop_last());
        let id = keys.last();
        if after.contains_key(id) {
            assert(prune(rows, after, keys) =~= prune(rows, after, keys.drop_last()));
        } else {
            lemma_apply_push(rows, removed_changes(after, keys.drop_last()), ChangeV::Remove { id });
            assert(prune(rows, after, keys) =~= prune(rows, after, keys.drop_last()).remove(id));
        }
    }
}

pub proof fn lemma_delta_changes<V>(
    before: Map<Seq<char>, V>,
    after: Map<Seq<char>, V>,
    old_keys: Seq<Seq<char>>,
    new_keys: Seq<Seq<char>>,
)
    requires enumerates(before, old_keys), enumerates(after, new_keys),
    ensures spec_apply_changes(before, delta_changes(before, after, old_keys, new_keys)) == after,
{
    lemma_changed_overlay(before, after, new_keys);
    lemma_removed_prune(overlay(before, after, new_keys), after, old_keys);
    lemma_apply_changes_append(
        before, changed_upserts(before, after, new_keys), removed_changes(after, old_keys),
    );
    assert(prune(overlay(before, after, new_keys), after, old_keys) =~= after);
}

pub open spec fn partial_valid<V>(f: FoldedV<V>, p: PartialV<V>) -> bool {
    &&& p.document == f.document
    &&& p.basever == f.version
    &&& p.basever < p.version <= u64::MAX
    &&& f.committed_at <= p.committed_at <= u64::MAX
    &&& match p.next_wake_at { Some(at) => at <= u64::MAX, None => true }
}

pub open spec fn checked_apply<V>(f: FoldedV<V>, p: PartialV<V>) -> Option<FoldedV<V>> {
    if partial_valid(f, p) { Some(spec_apply_document(f, p)) } else { None }
}

pub open spec fn fold_from<V>(f: FoldedV<V>, ps: Seq<PartialV<V>>) -> Option<FoldedV<V>>
    decreases ps.len(),
{
    if ps.len() == 0 {
        Some(f)
    } else {
        match fold_from(f, ps.drop_last()) {
            Some(before) => checked_apply(before, ps.last()),
            None => None,
        }
    }
}

pub open spec fn changes_count<V>(ps: Seq<PartialV<V>>) -> nat
    decreases ps.len(),
{
    if ps.len() == 0 { 0 } else { changes_count(ps.drop_last()) + ps.last().changes.len() }
}

pub proof fn lemma_checked_fold_append<V>(
    f: FoldedV<V>, ps: Seq<PartialV<V>>, p: PartialV<V>,
)
    ensures
        fold_from(f, ps.push(p)) == match fold_from(f, ps) {
            Some(before) => checked_apply(before, p),
            None => None,
        },
{
    assert(ps.push(p).drop_last() == ps);
    assert(ps.push(p).last() == p);
    reveal_with_fuel(fold_from, 2);
}

pub open spec fn empty_fold<V>(document: Seq<char>) -> FoldedV<V> {
    FoldedV { document, version: 0, committed_at: 0, next_wake_at: None, entries: Map::empty() }
}

pub open spec fn snapshot<V>(after: FoldedV<V>, keys: Seq<Seq<char>>) -> PartialV<V> {
    PartialV {
        document: after.document, basever: 0, version: after.version,
        committed_at: after.committed_at, next_wake_at: after.next_wake_at,
        changes: snapshot_changes(after.entries, keys),
    }
}

pub open spec fn delta<V>(
    before: FoldedV<V>, after: FoldedV<V>,
    old_keys: Seq<Seq<char>>, new_keys: Seq<Seq<char>>,
) -> PartialV<V> {
    PartialV {
        document: after.document, basever: before.version, version: after.version,
        committed_at: after.committed_at, next_wake_at: after.next_wake_at,
        changes: delta_changes(before.entries, after.entries, old_keys, new_keys),
    }
}

pub proof fn lemma_snapshot_valid<V>(after: FoldedV<V>, keys: Seq<Seq<char>>)
    requires
        enumerates(after.entries, keys),
        partial_valid(empty_fold::<V>(after.document), snapshot(after, keys)),
    ensures
        checked_apply(empty_fold::<V>(after.document), snapshot(after, keys)) == Some(after),
        snapshot(after, keys).changes.len() == keys.len(),
{
    lemma_snapshot_changes(after.entries, keys);
}

pub proof fn lemma_delta_valid<V>(
    before: FoldedV<V>, after: FoldedV<V>,
    old_keys: Seq<Seq<char>>, new_keys: Seq<Seq<char>>,
)
    requires
        enumerates(before.entries, old_keys),
        enumerates(after.entries, new_keys),
        partial_valid(before, delta(before, after, old_keys, new_keys)),
    ensures
        checked_apply(before, delta(before, after, old_keys, new_keys)) == Some(after),
{
    lemma_delta_changes(before.entries, after.entries, old_keys, new_keys);
}

pub proof fn lemma_count_append<V>(ps: Seq<PartialV<V>>, tail: Seq<PartialV<V>>)
    ensures changes_count(ps + tail) == changes_count(ps) + changes_count(tail),
    decreases tail.len(),
{
    if tail.len() == 0 {
        assert(ps + tail == ps);
    } else {
        lemma_count_append(ps, tail.drop_last());
        assert((ps + tail).drop_last() == ps + tail.drop_last());
        assert((ps + tail).last() == tail.last());
    }
}

pub proof fn lemma_retired_schedule_snapshot(row: echod_types::Schedule, version: nat, time: nat)
    requires
        row.next_run_at is None,
        0 < version <= u64::MAX,
        time <= u64::MAX,
    ensures ({
        let after = FoldedV {
            document: row.id@, version, committed_at: time, next_wake_at: None,
            entries: Map::empty().insert(row.id@, row),
        };
        let p = snapshot(after, seq![row.id@]);
        &&& checked_apply(empty_fold::<echod_types::Schedule>(row.id@), p) == Some(after)
        &&& p.changes.len() == 1
        &&& p.next_wake_at is None
    }),
{
    let rows = Map::empty().insert(row.id@, row);
    let keys = seq![row.id@];
    assert(keys.to_set() =~= rows.dom());
    let after = FoldedV {
        document: row.id@, version, committed_at: time, next_wake_at: None, entries: rows,
    };
    lemma_snapshot_valid(after, keys);
}

pub proof fn lemma_empty_schedule_snapshot(document: Seq<char>, version: nat, time: nat)
    requires 0 < version <= u64::MAX, time <= u64::MAX,
    ensures ({
        let after = FoldedV::<echod_types::Schedule> {
            document, version, committed_at: time, next_wake_at: None, entries: Map::empty(),
        };
        let p = snapshot(after, Seq::empty());
        &&& checked_apply(empty_fold::<echod_types::Schedule>(document), p) == Some(after)
        &&& p.changes.len() == 0
    }),
{
    let after = FoldedV::<echod_types::Schedule> {
        document, version, committed_at: time, next_wake_at: None, entries: Map::empty(),
    };
    assert(Seq::<Seq<char>>::empty().to_set() =~= after.entries.dom());
    lemma_snapshot_valid(after, Seq::empty());
}

}
