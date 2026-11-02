//! `MARKS` lists exactly the marks the spec can put on an outcome: every
//! `mk("...")` in the abstract model's `exec` module, and nothing else.

use std::collections::BTreeSet;
use echod_abstract;

#[test]
fn the_list_of_marks_matches_the_spec() {
    let spec = concat!(
        include_str!("../../abstract/src/exec/mod.rs"),
        include_str!("../../abstract/src/exec/external.rs"),
        include_str!("../../abstract/src/exec/internal.rs"),
        include_str!("../../abstract/src/exec/system.rs"),
    );
    let in_spec: BTreeSet<&str> = spec.split("mk(\"").skip(1).filter_map(|rest| rest.split('"').next()).collect();
    let listed: BTreeSet<&str> = echod_abstract::MARKS.iter().copied().collect();
    assert_eq!(listed, in_spec, "update MARKS in rust/spec/abstract/src/explore.rs");
    assert_eq!(listed.len(), echod_abstract::MARKS.len(), "a mark is listed twice");
}
