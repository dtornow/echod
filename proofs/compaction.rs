//! Compaction replays to the same document.
//!
//! The object at `wf/<origin>` is a log of rows; the document is the fold of
//! the rows, each row replacing the entry for its id. Compaction rewrites the
//! object as one row per id. This proves that any such rewrite, in any row
//! order, folds to the document the log folded to.
//!
//! Check with `verus proofs/compaction.rs` (Verus 0.2026.10.13, z3 4.16.0).

use vstd::prelude::*;

verus! {

/// A row: the id and the promise it carries. The promise is opaque here.
pub struct Row {
    pub id: int,
    pub body: int,
}

pub type Doc = Map<int, int>;

/// Replay a log: each row replaces the entry for its id.
pub open spec fn fold(log: Seq<Row>) -> Doc
    decreases log.len(),
{
    if log.len() == 0 {
        Map::empty()
    } else {
        fold(log.drop_last()).insert(log.last().id, log.last().body)
    }
}

/// `x` is an id some row of the log carries.
pub open spec fn mentions(log: Seq<Row>, x: int) -> bool {
    exists|i: int| 0 <= i < log.len() && #[trigger] log[i].id == x
}

/// No two rows share an id.
pub open spec fn distinct(log: Seq<Row>) -> bool {
    forall|i: int, j: int|
        0 <= i < log.len() && 0 <= j < log.len() && #[trigger] log[i].id == #[trigger] log[j].id
            ==> i == j
}

/// `c` is a compaction of `log`: one row per id of `fold(log)`, each carrying
/// the body `fold(log)` holds for that id. Row order is unconstrained.
pub open spec fn is_compaction(c: Seq<Row>, log: Seq<Row>) -> bool {
    &&& distinct(c)
    &&& forall|i: int| 0 <= i < c.len()
            ==> fold(log).contains_key(#[trigger] c[i].id) && c[i].body == fold(log)[c[i].id]
    &&& forall|x: int| fold(log).contains_key(x)
            ==> exists|i: int| 0 <= i < c.len() && #[trigger] c[i].id == x
}

/// The fold's domain is exactly the ids the log mentions.
proof fn lemma_fold_dom(log: Seq<Row>)
    ensures
        forall|x: int| #[trigger] fold(log).contains_key(x) <==> mentions(log, x),
    decreases log.len(),
{
    if log.len() == 0 {
        assert forall|x: int| !mentions(log, x) by {
            if mentions(log, x) {
                let i = choose|i: int| 0 <= i < log.len() && #[trigger] log[i].id == x;
            }
        }
    } else {
        let init = log.drop_last();
        lemma_fold_dom(init);
        assert forall|x: int| #[trigger] fold(log).contains_key(x) implies mentions(log, x) by {
            if x == log.last().id {
                assert(log[log.len() - 1].id == x);
            } else {
                assert(fold(init).contains_key(x));
                assert(mentions(init, x));
                let i = choose|i: int| 0 <= i < init.len() && #[trigger] init[i].id == x;
                assert(log[i] == init[i]);
                assert(log[i].id == x);
            }
        }
        assert forall|x: int| mentions(log, x) implies #[trigger] fold(log).contains_key(x) by {
            let i = choose|i: int| 0 <= i < log.len() && #[trigger] log[i].id == x;
            if i == log.len() - 1 {
            } else {
                assert(init[i] == log[i]);
                assert(init[i].id == x);
                assert(mentions(init, x));
                assert(fold(init).contains_key(x));
            }
        }
    }
}

/// With distinct ids, the fold holds every row's body under its id.
proof fn lemma_fold_distinct(c: Seq<Row>)
    requires
        distinct(c),
    ensures
        forall|i: int| 0 <= i < c.len()
            ==> fold(c).contains_key(#[trigger] c[i].id) && fold(c)[c[i].id] == c[i].body,
    decreases c.len(),
{
    if c.len() == 0 {
    } else {
        let init = c.drop_last();
        let last = c.last();
        assert(distinct(init));
        lemma_fold_distinct(init);
        assert forall|i: int| 0 <= i < c.len()
            implies fold(c).contains_key(#[trigger] c[i].id) && fold(c)[c[i].id] == c[i].body by {
            if i == c.len() - 1 {
            } else {
                assert(c[i].id != last.id);
                assert(init[i] == c[i]);
            }
        }
    }
}

/// The compaction statement: a compaction folds to the log's document.
pub proof fn compaction_replays_to_the_same_document(c: Seq<Row>, log: Seq<Row>)
    requires
        is_compaction(c, log),
    ensures
        fold(c) =~= fold(log),
{
    lemma_fold_dom(c);
    lemma_fold_distinct(c);
    assert forall|x: int| #[trigger] fold(c).contains_key(x) implies fold(log).contains_key(x) by {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] c[i].id == x;
    }
    assert forall|x: int| #[trigger] fold(log).contains_key(x) implies fold(c).contains_key(x) by {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] c[i].id == x;
    }
    assert forall|x: int| #[trigger] fold(c).contains_key(x) implies fold(c)[x] == fold(log)[x] by {
        let i = choose|i: int| 0 <= i < c.len() && #[trigger] c[i].id == x;
    }
}

} // verus!

fn main() {}
