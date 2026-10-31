//! `MARKS` lists exactly the marks the spec can put on an outcome: every
//! `mk("...")` in `src/exec.rs`, and nothing else.

use std::collections::BTreeSet;
use accordant::rover::resonate;

#[test]
fn the_list_of_marks_matches_the_spec() {
    let spec = include_str!("../src/rover/resonate/exec.rs");
    let in_spec: BTreeSet<&str> = spec.split("mk(\"").skip(1).filter_map(|rest| rest.split('"').next()).collect();
    let listed: BTreeSet<&str> = resonate::MARKS.iter().copied().collect();
    assert_eq!(listed, in_spec, "update MARKS in src/explore.rs");
    assert_eq!(listed.len(), resonate::MARKS.len(), "a mark is listed twice");
}
