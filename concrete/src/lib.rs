//! The deterministic Concrete document model.
//!
//! A document is its persisted promise rows, in order. The kernel's maps are
//! derived views used at the specification boundary; Concrete never
//! reconstructs row order from a map. Updating an existing promise preserves
//! its row position and a birth appends one row.

#![cfg_attr(not(verus_keep_ghost), allow(unused_imports, dead_code, unused_variables))]

use vstd::prelude::*;

use echod_kernel::steps::executable_single_pass;
use echod_kernel::store::{object_order, AState};
use echod_kernel::types::{APromise, Promise};

verus! {

/// One persisted origin document.
pub struct Store {
    pub rows: Vec<Promise>,
}

/// The mathematical Concrete state. Order is intrinsic to `rows`.
#[cfg(verus_keep_ghost)]
pub struct AStore {
    pub rows: Seq<APromise>,
}

#[cfg(verus_keep_ghost)]
impl View for Store {
    type V = AStore;

    open spec fn view(&self) -> AStore {
        AStore { rows: self.rows.deep_view() }
    }
}

/// Replay persisted rows, last row winning.
pub open spec fn object_map(rows: Seq<APromise>) -> Map<Seq<char>, APromise>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Map::empty()
    } else {
        let p = rows.last();
        object_map(rows.drop_last()).insert(p.id, p)
    }
}

/// Promise ids in persisted row order.
pub open spec fn row_ids(rows: Seq<APromise>) -> Seq<Seq<char>> {
    rows.map_values(|p: APromise| p.id)
}

pub open spec fn rows_wf(rows: Seq<APromise>) -> bool {
    row_ids(rows).no_duplicates()
}

/// The kernel map view derived from Concrete rows.
pub open spec fn kernel_view(store: AStore) -> AState {
    AState {
        objects: object_map(store.rows),
        schedules: Map::empty(),
        outbox: Map::empty(),
    }
}

impl Store {
    pub fn new() -> (store: Store)
        ensures
            store@.rows == Seq::<APromise>::empty(),
            rows_wf(store@.rows),
    {
        Store { rows: Vec::new() }
    }
}

/// Refresh existing rows from a kernel result without changing order.
pub open spec fn refresh_rows(
    rows: Seq<APromise>,
    objects: Map<Seq<char>, APromise>,
) -> Seq<APromise>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        let p = rows.last();
        refresh_rows(rows.drop_last(), objects).push(
            if objects.contains_key(p.id) { objects[p.id] } else { p },
        )
    }
}

/// Append one newly born promise; updates use `refresh_rows` instead.
pub open spec fn append_birth(
    rows: Seq<APromise>,
    before: Map<Seq<char>, APromise>,
    after: Map<Seq<char>, APromise>,
    id: Seq<char>,
) -> Seq<APromise> {
    let updated = refresh_rows(rows, after);
    if !before.contains_key(id) && after.contains_key(id) {
        updated.push(after[id])
    } else {
        updated
    }
}

/// Concrete's exact one-pass normalization in persisted row order.
pub open spec fn normalize(
    store: AStore,
    now: nat,
    retry_timeout: nat,
) -> AStore {
    let before = kernel_view(store);
    let after = executable_single_pass(
        before,
        row_ids(store.rows),
        now,
        retry_timeout,
    );
    AStore { rows: refresh_rows(store.rows, after.objects) }
}

pub proof fn lemma_row_ids_refresh(
    rows: Seq<APromise>,
    objects: Map<Seq<char>, APromise>,
)
    requires
        forall|i: int| 0 <= i < rows.len()
            ==> objects.contains_key(#[trigger] rows[i].id)
                && objects[rows[i].id].id == rows[i].id,
    ensures
        row_ids(refresh_rows(rows, objects)) == row_ids(rows),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_row_ids_refresh(rows.drop_last(), objects);
        let p = rows.last();
        assert(objects.contains_key(p.id));
        assert(objects[p.id].id == p.id);
        assert(refresh_rows(rows, objects)
            == refresh_rows(rows.drop_last(), objects).push(objects[p.id]));
        assert(row_ids(rows) == row_ids(rows.drop_last()).push(p.id));
    }
}

pub proof fn lemma_object_map_contains(rows: Seq<APromise>, id: Seq<char>)
    ensures
        object_map(rows).contains_key(id) <==> row_ids(rows).contains(id),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_object_map_contains(rows.drop_last(), id);
        let p = rows.last();
        assert(row_ids(rows) == row_ids(rows.drop_last()).push(p.id));
        assert(object_map(rows) == object_map(rows.drop_last()).insert(p.id, p));
        assert(row_ids(rows).contains(id)
            <==> (row_ids(rows.drop_last()).contains(id) || p.id == id)) by {
            if row_ids(rows).contains(id) {
                let i = choose|i: int| 0 <= i < row_ids(rows).len()
                    && row_ids(rows)[i] == id;
                if i < row_ids(rows).len() - 1 {
                    assert(row_ids(rows.drop_last())[i] == id);
                }
            }
            if row_ids(rows.drop_last()).contains(id) {
                let i = choose|i: int| 0 <= i < row_ids(rows.drop_last()).len()
                    && row_ids(rows.drop_last())[i] == id;
                assert(row_ids(rows)[i] == id);
            }
            if p.id == id {
                assert(row_ids(rows)[rows.len() - 1] == id);
            }
        }
    }
}

/// A well-formed Concrete row sequence is its derived map's order witness.
pub proof fn lemma_rows_are_object_order(store: AStore)
    requires
        rows_wf(store.rows),
    ensures
        object_order(kernel_view(store), row_ids(store.rows)),
{
    assert(row_ids(store.rows).no_duplicates());
    assert forall|i: int| 0 <= i < row_ids(store.rows).len()
        implies kernel_view(store).objects.contains_key(
            #[trigger] row_ids(store.rows)[i],
        ) by {
        lemma_object_map_contains(store.rows, row_ids(store.rows)[i]);
        assert(row_ids(store.rows).contains(row_ids(store.rows)[i]));
    }
    assert forall|id: Seq<char>|
        #[trigger] kernel_view(store).objects.contains_key(id)
        implies row_ids(store.rows).contains(id) by {
        lemma_object_map_contains(store.rows, id);
    }
}

} // verus!
