//! Every origin that owes a deadline has its key in the timeout bucket.

use echod_concrete::timeouts::{bucket_of, TimeoutStore, HOUR_MS};

#[test]
fn an_origin_timeout_is_filed_in_the_bucket_it_falls_in() {
    let mut store = TimeoutStore::new(HOUR_MS);
    assert!(store.reflected());
    assert!(store.in_bucket(0).is_empty());

    store.commit_origin("alpha", Some(1_500_000), 1, "node-a");
    store.commit_origin("beta", Some(HOUR_MS), 2, "node-a");
    store.commit_origin("gamma", Some(2 * HOUR_MS + 1), 3, "node-b");
    store.commit_origin("quiet", None, 4, "node-a");

    assert!(store.reflected());
    assert_eq!(bucket_of(1_500_000, HOUR_MS), 0);
    assert_eq!(bucket_of(HOUR_MS, HOUR_MS), HOUR_MS);
    assert_eq!(bucket_of(2 * HOUR_MS + 1, HOUR_MS), 2 * HOUR_MS);

    let alpha = &store.in_bucket(0)[0];
    assert_eq!(alpha.origin, "alpha");
    assert_eq!(alpha.deadline, 1_500_000);
    assert_eq!(alpha.token, 1);
    assert_eq!(alpha.by, "node-a");

    assert_eq!(store.in_bucket(HOUR_MS).len(), 1);
    assert_eq!(store.in_bucket(HOUR_MS)[0].origin, "beta");
    assert_eq!(store.in_bucket(2 * HOUR_MS)[0].origin, "gamma");
    assert!(store.buckets.values().flatten().all(|k| k.origin != "quiet"));
}

#[test]
fn a_second_commit_keeps_every_origin_reflected() {
    let mut store = TimeoutStore::new(HOUR_MS);
    store.commit_origin("alpha", Some(1_500_000), 1, "node-a");
    store.commit_origin("beta", Some(HOUR_MS), 2, "node-a");

    store.commit_origin("alpha", Some(1_500_000), 9, "node-a");
    assert_eq!(store.in_bucket(0).len(), 1);

    store.commit_origin("alpha", Some(HOUR_MS + 10), 10, "node-b");
    assert!(store.reflected());
    assert_eq!(store.nearest["alpha"], Some(HOUR_MS + 10));
    assert!(store.in_bucket(HOUR_MS).iter().any(|k| k.origin == "alpha" && k.deadline == HOUR_MS + 10));
    assert!(store.in_bucket(HOUR_MS).iter().any(|k| k.origin == "beta" && k.deadline == HOUR_MS));
}
