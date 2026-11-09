//! `MARKS` lists exactly the marks the spec can put on an outcome: every
//! `mk("...")` in the abstract model's `machine` module, and nothing else.

use std::collections::BTreeSet;
use echod_abstract;

#[test]
fn the_list_of_marks_matches_the_spec() {
    let spec = concat!(
        include_str!("../../abstract/src/machine/mod.rs"),
        include_str!("../../abstract/src/machine/external.rs"),
        include_str!("../../abstract/src/machine/internal.rs"),
        include_str!("../../abstract/src/model.rs"),
    );
    let in_spec: BTreeSet<&str> = spec.split("mk(\"").skip(1).filter_map(|rest| rest.split('"').next()).collect();
    let listed: BTreeSet<&str> = echod_abstract::MARKS.iter().copied().collect();
    assert_eq!(listed, in_spec, "update MARKS in rust/spec/abstract/src/history/mod.rs");
    assert_eq!(listed.len(), echod_abstract::MARKS.len(), "a mark is listed twice");
}
