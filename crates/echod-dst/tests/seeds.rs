use echod_dst::sim::{run, Options};

#[test]
fn a_handful_of_seeds_pass() {
    for seed in 1..=4 {
        let r = run(Options { seed, operations: 120, ..Options::default() });
        assert!(r.ok, "seed {seed}: {:?}", r.failures);
        assert!(r.overlapping_pairs > 0, "seed {seed} never overlapped");
    }
}

#[test]
fn the_same_seed_replays_the_same_run() {
    let a = run(Options { seed: 7, operations: 80, ..Options::default() });
    let b = run(Options { seed: 7, operations: 80, ..Options::default() });
    assert_eq!(serde_json::to_string(&a).unwrap(), serde_json::to_string(&b).unwrap());
}
