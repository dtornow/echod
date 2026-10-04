//! The JobQueue sample: background work that eventually completes, and a timer
//! that times a job out if it has not.

use accordant::{Checker, Config, Fairness, Footprint, HashedMap, Keyed, Model, Outcome, StepResult, Succ, Time, Touches};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Status {
    Pending,
    Completed,
    Failed,
    TimedOut,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
struct Queue {
    jobs: HashedMap<u32, Status>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Request {
    /// Submit a job that times out at an absolute time.
    Submit(u32, Time),
    Get(u32),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Response {
    Accepted,
    Duplicate,
    NotFound,
    Is(Status),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Internal {
    Run(u32),
    Timeout(u32),
}

/// `run_within`: how long after submission a job may run before it must be done.
struct JobModel {
    run_within: Option<Time>,
}

const NEVER: Time = Time::MAX / 2;

impl Model for JobModel {
    type State = Queue;
    type External = Request;
    type Response = Response;
    type Internal = Internal;

    fn external(&self, op: &Request, s: &Queue, _now: Time) -> Vec<Outcome<Self>> {
        vec![match *op {
            Request::Submit(j, _) if s.jobs.contains_key(&j) => Outcome::same(Response::Duplicate, s),
            Request::Submit(j, timeout_at) => {
                let mut n = s.clone();
                n.jobs.insert(j, Status::Pending);
                Outcome::new(Response::Accepted, n).spawn(Internal::Run(j)).timer(timeout_at, Internal::Timeout(j))
            }
            Request::Get(j) => match s.jobs.get(&j) {
                None => Outcome::same(Response::NotFound, s),
                Some(st) => Outcome::same(Response::Is(*st), s),
            },
        }]
    }

    fn internal(&self, step: &Internal, s: &Queue, _now: Time) -> StepResult<Self> {
        let (Internal::Run(j) | Internal::Timeout(j)) = *step;
        if s.jobs.get(&j) != Some(&Status::Pending) {
            return StepResult::Discharged;
        }
        let to = |st| {
            let mut n = s.clone();
            n.jobs.insert(j, st);
            Succ::new(n)
        };
        match step {
            Internal::Run(_) => StepResult::Next(vec![to(Status::Completed), to(Status::Failed)]),
            Internal::Timeout(_) => StepResult::Next(vec![to(Status::TimedOut)]),
        }
    }

    fn fairness(&self, step: &Internal) -> Fairness {
        match step {
            Internal::Run(_) => Fairness::Eventually { within: self.run_within },
            Internal::Timeout(_) => Fairness::Eventually { within: Some(0) }, // exact timer
        }
    }

}

impl Footprint for JobModel {
    type Object = u32;

    fn external_touches(&self, op: &Request) -> Touches<u32> {
        match *op {
            Request::Submit(j, _) | Request::Get(j) => Touches::one(j),
        }
    }

    fn internal_touches(&self, step: &Internal) -> Touches<u32> {
        let (Internal::Run(j) | Internal::Timeout(j)) = *step;
        Touches::one(j)
    }
}

fn checker(run_within: Option<Time>) -> Checker<Keyed<JobModel>> {
    Checker::with_footprints(JobModel { run_within }, Queue::default(), Config::default())
}

#[test]
fn completion_is_observed_and_the_profile_collapses() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, NEVER), Response::Accepted).unwrap();
    c.call(2, Request::Get(7), Response::Is(Status::Pending)).unwrap();
    assert_eq!(c.profile().len(), 1, "the run is deferred, not expanded");
    c.call(3, Request::Get(7), Response::Is(Status::Failed)).unwrap();
    assert!(c.all(|s| s.jobs[&7] == Status::Failed));
    assert!(c.call(4, Request::Get(7), Response::Is(Status::Completed)).is_err());
}

#[test]
fn run_deadline_rejects_a_stuck_job() {
    let mut c = checker(Some(1_000));
    c.call(1, Request::Submit(7, NEVER), Response::Accepted).unwrap();
    c.tick(999).unwrap();
    c.call(2, Request::Get(7), Response::Is(Status::Pending)).unwrap(); // before the deadline: allowed
    c.tick(1_000).unwrap(); // at the deadline the run has happened
    let v = c.call(3, Request::Get(7), Response::Is(Status::Pending)).unwrap_err();
    println!("{v}");
}

#[test]
fn timer_times_out_a_job_at_its_deadline() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.tick(499).unwrap();
    c.call(2, Request::Get(7), Response::Is(Status::Pending)).unwrap();
    c.tick(2_000).unwrap(); // passes 500 on the way: the timer fires unless the run beat it
    assert!(c.call(3, Request::Get(7), Response::Is(Status::Pending)).is_err());
    c.call(4, Request::Get(7), Response::Is(Status::TimedOut)).unwrap();
}

#[test]
fn timer_does_not_fire_early() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.tick(499).unwrap();
    assert!(c.call(2, Request::Get(7), Response::Is(Status::TimedOut)).is_err());
}

#[test]
fn a_get_in_flight_across_the_timeout_may_see_pending() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.tick(100).unwrap();
    c.invoke(2, Request::Get(7)).unwrap();
    c.tick(2_000).unwrap();
    c.ret(2, Response::Is(Status::Pending)).unwrap(); // it linearized before 500
    c.call(3, Request::Get(7), Response::Is(Status::TimedOut)).unwrap();
}

#[test]
fn a_get_invoked_after_the_timeout_cannot_see_pending() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.tick(500).unwrap();
    assert!(c.call(2, Request::Get(7), Response::Is(Status::Pending)).is_err());
}

#[test]
fn a_run_may_beat_the_timer_unobserved() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.tick(2_000).unwrap();
    c.call(2, Request::Get(7), Response::Is(Status::Completed)).unwrap();
}

#[test]
fn a_run_that_beats_the_timer_wins() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.tick(300).unwrap();
    c.call(2, Request::Get(7), Response::Is(Status::Completed)).unwrap();
    c.tick(2_000).unwrap();
    c.call(3, Request::Get(7), Response::Is(Status::Completed)).unwrap();
    assert!(c.profile().iter().all(|n| n.pending.is_empty()), "the timer discharged");
}

#[test]
fn quiesce_discharges_unbounded_eventually() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, NEVER), Response::Accepted).unwrap();
    c.call(2, Request::Get(7), Response::Is(Status::Pending)).unwrap();
    c.quiesce().unwrap();
    assert!(c.all(|s| s.jobs[&7] != Status::Pending));
    assert!(c.call(3, Request::Get(7), Response::Is(Status::Pending)).is_err());
}

#[test]
fn quiesce_does_not_fire_future_timers() {
    let mut c = checker(Some(10_000));
    c.call(1, Request::Submit(7, 500), Response::Accepted).unwrap();
    c.quiesce().unwrap(); // the run must be done; the timeout is not due yet
    assert!(c.all(|s| matches!(s.jobs[&7], Status::Completed | Status::Failed)));
}

#[test]
fn a_get_in_flight_across_completion_may_see_either() {
    let mut c = checker(None);
    c.call(1, Request::Submit(7, NEVER), Response::Accepted).unwrap();
    c.invoke(2, Request::Get(7)).unwrap();
    c.call(3, Request::Get(7), Response::Is(Status::Completed)).unwrap();
    // Call 2 was in flight while the job completed: Pending is still a valid answer.
    c.ret(2, Response::Is(Status::Pending)).unwrap();
}

#[test]
fn independent_jobs_stay_deferred() {
    let mut c = checker(None);
    for j in 0..12 {
        c.call(j as u64, Request::Submit(j, NEVER), Response::Accepted).unwrap();
    }
    c.call(100, Request::Get(3), Response::Is(Status::Completed)).unwrap();
    // Twelve runs, each with two outcomes, but only job 3 was ever expanded.
    assert_eq!(c.stats.max_width, 1, "{:?}", c.stats);
}

#[test]
fn time_cannot_go_backwards() {
    let mut c = checker(None);
    c.tick(10).unwrap();
    assert!(c.tick(5).is_err());
}
