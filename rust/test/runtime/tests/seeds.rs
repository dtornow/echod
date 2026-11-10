use echod_sim::sim::{run, Options};

#[test]
fn a_handful_of_seeds_pass() {
    for seed in 1..=4 {
        let r = run(Options {
            seed,
            operations: 120,
            ..Options::default()
        });
        assert!(r.ok, "seed {seed}: {:?}", r.failures);
        assert!(r.overlapping_pairs > 0, "seed {seed} never overlapped");
    }
}

#[test]
fn the_same_seed_replays_the_same_run() {
    let a = run(Options {
        seed: 7,
        operations: 80,
        ..Options::default()
    });
    let b = run(Options {
        seed: 7,
        operations: 80,
        ..Options::default()
    });
    assert_eq!(
        serde_json::to_string(&a).unwrap(),
        serde_json::to_string(&b).unwrap()
    );
}

#[test]
fn schedules_run_in_the_synchronous_system() {
    let report = run(Options {
        seed: 11,
        operations: 60,
        schedules: true,
        ..Options::default()
    });
    assert!(report.ok, "{:?}", report.failures);
}

#[test]
fn lifecycle_and_fault_events_are_scheduled_synchronously() {
    let report = run(Options {
        seed: 19,
        operations: 30,
        chaos_every_ms: 10,
        crash_percent: 100,
        stop_percent: 100,
        join_percent: 100,
        outage_percent: 100,
        jump_percent: 100,
        disruption_ms: 25,
        jump_ms: 10,
        ..Options::default()
    });
    assert!(report.ok, "{:?}", report.failures);
    assert!(report.crashes > 0);
    assert!(report.stops > 0);
    assert!(report.joins > 0);
    assert!(report.outages > 0);
    assert!(report.jumps > 0);
}
