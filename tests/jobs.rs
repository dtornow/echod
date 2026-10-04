//! The JobQueue sample: background work that eventually completes, and a timer
//! that times a job out if it has not.

use accordant::{Checker, Config, Fairness, HashedMap, Keys, Outcome, Spec, StepResult, Succ, Time};

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
enum Op {
    /// Submit a job that times out at an absolute time.
    Submit(u32, Time),
    Get(u32),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Resp {
    Accepted,
    Duplicate,
    NotFound,
    Is(Status),
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Step {
    Run(u32),
    Timeout(u32),
}

/// `run_within`: how long after submission a job may run before it must be done.
struct JobSpec {
    run_within: Option<Time>,
}

const NEVER: Time = Time::MAX / 2;

impl Spec for JobSpec {
    type State = Queue;
    type Op = Op;
    type Resp = Resp;
    type Step = Step;
    type Key = u32;

    fn apply(&self, op: &Op, s: &Queue, _now: Time) -> Vec<Outcome<Self>> {
        vec![match *op {
            Op::Submit(j, _) if s.jobs.contains_key(&j) => Outcome::same(Resp::Duplicate, s),
            Op::Submit(j, timeout_at) => {
                let mut n = s.clone();
                n.jobs.insert(j, Status::Pending);
                Outcome::new(Resp::Accepted, n).spawn(Step::Run(j)).timer(timeout_at, Step::Timeout(j))
            }
            Op::Get(j) => match s.jobs.get(&j) {
                None => Outcome::same(Resp::NotFound, s),
                Some(st) => Outcome::same(Resp::Is(*st), s),
            },
        }]
    }

    fn step(&self, step: &Step, s: &Queue, _now: Time) -> StepResult<Self> {
        let (Step::Run(j) | Step::Timeout(j)) = *step;
        if s.jobs.get(&j) != Some(&Status::Pending) {
            return StepResult::Discharged;
        }
        let to = |st| {
            let mut n = s.clone();
            n.jobs.insert(j, st);
            Succ::new(n)
        };
        match step {
            Step::Run(_) => StepResult::Next(vec![to(Status::Completed), to(Status::Failed)]),
            Step::Timeout(_) => StepResult::Next(vec![to(Status::TimedOut)]),
        }
    }

    fn fairness(&self, step: &Step) -> Fairness {
        match step {
            Step::Run(_) => Fairness::Eventually { within: self.run_within },
            Step::Timeout(_) => Fairness::Eventually { within: Some(0) }, // exact timer
        }
    }

    fn op_keys(&self, op: &Op) -> Keys<u32> {
        match *op {
            Op::Submit(j, _) | Op::Get(j) => Keys::one(j),
        }
    }

    fn step_keys(&self, step: &Step) -> Keys<u32> {
        let (Step::Run(j) | Step::Timeout(j)) = *step;
        Keys::one(j)
    }
}

fn checker(run_within: Option<Time>) -> Checker<JobSpec> {
    Checker::new(JobSpec { run_within }, Queue::default(), Config::default())
}

#[test]
fn completion_is_observed_and_the_profile_collapses() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, NEVER), Resp::Accepted).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    assert_eq!(c.profile().len(), 1, "the run is deferred, not expanded");
    c.call(3, Op::Get(7), Resp::Is(Status::Failed)).unwrap();
    assert!(c.all(|s| s.jobs[&7] == Status::Failed));
    assert!(c.call(4, Op::Get(7), Resp::Is(Status::Completed)).is_err());
}

#[test]
fn run_deadline_rejects_a_stuck_job() {
    let mut c = checker(Some(1_000));
    c.call(1, Op::Submit(7, NEVER), Resp::Accepted).unwrap();
    c.tick(999).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap(); // before the deadline: allowed
    c.tick(1_000).unwrap(); // at the deadline the run has happened
    let v = c.call(3, Op::Get(7), Resp::Is(Status::Pending)).unwrap_err();
    println!("{v}");
}

#[test]
fn timer_times_out_a_job_at_its_deadline() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.tick(499).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    c.tick(2_000).unwrap(); // passes 500 on the way: the timer fires unless the run beat it
    assert!(c.call(3, Op::Get(7), Resp::Is(Status::Pending)).is_err());
    c.call(4, Op::Get(7), Resp::Is(Status::TimedOut)).unwrap();
}

#[test]
fn timer_does_not_fire_early() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.tick(499).unwrap();
    assert!(c.call(2, Op::Get(7), Resp::Is(Status::TimedOut)).is_err());
}

#[test]
fn a_get_in_flight_across_the_timeout_may_see_pending() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.tick(100).unwrap();
    c.invoke(2, Op::Get(7)).unwrap();
    c.tick(2_000).unwrap();
    c.ret(2, Resp::Is(Status::Pending)).unwrap(); // it linearized before 500
    c.call(3, Op::Get(7), Resp::Is(Status::TimedOut)).unwrap();
}

#[test]
fn a_get_invoked_after_the_timeout_cannot_see_pending() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.tick(500).unwrap();
    assert!(c.call(2, Op::Get(7), Resp::Is(Status::Pending)).is_err());
}

#[test]
fn a_run_may_beat_the_timer_unobserved() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.tick(2_000).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Completed)).unwrap();
}

#[test]
fn a_run_that_beats_the_timer_wins() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.tick(300).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Completed)).unwrap();
    c.tick(2_000).unwrap();
    c.call(3, Op::Get(7), Resp::Is(Status::Completed)).unwrap();
    assert!(c.profile().iter().all(|n| n.pending.is_empty()), "the timer discharged");
}

#[test]
fn quiesce_discharges_unbounded_eventually() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, NEVER), Resp::Accepted).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    c.quiesce().unwrap();
    assert!(c.all(|s| s.jobs[&7] != Status::Pending));
    assert!(c.call(3, Op::Get(7), Resp::Is(Status::Pending)).is_err());
}

#[test]
fn quiesce_does_not_fire_future_timers() {
    let mut c = checker(Some(10_000));
    c.call(1, Op::Submit(7, 500), Resp::Accepted).unwrap();
    c.quiesce().unwrap(); // the run must be done; the timeout is not due yet
    assert!(c.all(|s| matches!(s.jobs[&7], Status::Completed | Status::Failed)));
}

#[test]
fn a_get_in_flight_across_completion_may_see_either() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7, NEVER), Resp::Accepted).unwrap();
    c.invoke(2, Op::Get(7)).unwrap();
    c.call(3, Op::Get(7), Resp::Is(Status::Completed)).unwrap();
    // Call 2 was in flight while the job completed: Pending is still a valid answer.
    c.ret(2, Resp::Is(Status::Pending)).unwrap();
}

#[test]
fn independent_jobs_stay_deferred() {
    let mut c = checker(None);
    for j in 0..12 {
        c.call(j as u64, Op::Submit(j, NEVER), Resp::Accepted).unwrap();
    }
    c.call(100, Op::Get(3), Resp::Is(Status::Completed)).unwrap();
    // Twelve runs, each with two outcomes, but only job 3 was ever expanded.
    assert_eq!(c.stats.max_width, 1, "{:?}", c.stats);
}

#[test]
fn time_cannot_go_backwards() {
    let mut c = checker(None);
    c.tick(10).unwrap();
    assert!(c.tick(5).is_err());
}
