//! `MARKS` lists exactly the marks the spec can put on an outcome: every
//! `mk("...")` in the executable abstract model, and nothing else.

use std::collections::BTreeSet;
use echod_abstract_exec;

#[test]
fn the_list_of_marks_matches_the_spec() {
    let spec = concat!(
        include_str!("../src/state.rs"),
        include_str!("../src/requests.rs"),
        include_str!("../src/work.rs"),
        include_str!("../src/rover.rs"),
    );
    let in_spec: BTreeSet<&str> = spec.split("mk(\"").skip(1).filter_map(|rest| rest.split('"').next()).collect();
    let listed: BTreeSet<&str> = echod_abstract_exec::coverage::MARKS.iter().copied().collect();
    assert_eq!(listed, in_spec, "update MARKS in rust/spec/echod/abstract/exec/src/coverage.rs");
    assert_eq!(listed.len(), echod_abstract_exec::coverage::MARKS.len(), "a mark is listed twice");
}
