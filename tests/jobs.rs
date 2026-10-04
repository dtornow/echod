//! The JobQueue sample: background work that eventually completes.

use std::collections::BTreeMap;

use accordant::{Checker, Config, Fairness, Keys, Outcome, Spec, StepResult};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Status {
    Pending,
    Completed,
    Failed,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
struct Queue {
    jobs: BTreeMap<u32, Status>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
enum Op {
    Submit(u32),
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
}

/// `within` is how many later responses may still show a job Pending.
struct JobSpec {
    within: Option<u32>,
}

impl Spec for JobSpec {
    type State = Queue;
    type Op = Op;
    type Resp = Resp;
    type Step = Step;
    type Key = u32;

    fn apply(&self, op: &Op, s: &Queue) -> Vec<Outcome<Self>> {
        vec![match *op {
            Op::Submit(j) if s.jobs.contains_key(&j) => Outcome::same(Resp::Duplicate, s),
            Op::Submit(j) => {
                let mut n = s.clone();
                n.jobs.insert(j, Status::Pending);
                Outcome::new(Resp::Accepted, n).spawn(Step::Run(j))
            }
            Op::Get(j) => match s.jobs.get(&j) {
                None => Outcome::same(Resp::NotFound, s),
                Some(st) => Outcome::same(Resp::Is(*st), s),
            },
        }]
    }

    fn step(&self, step: &Step, s: &Queue) -> StepResult<Self> {
        let Step::Run(j) = *step;
        if s.jobs.get(&j) != Some(&Status::Pending) {
            return StepResult::Discharged;
        }
        let done = |st| {
            let mut n = s.clone();
            n.jobs.insert(j, st);
            (n, vec![])
        };
        StepResult::Next(vec![done(Status::Completed), done(Status::Failed)])
    }

    fn fairness(&self, _: &Step) -> Fairness {
        Fairness::Eventually { within: self.within }
    }

    fn op_keys(&self, op: &Op) -> Keys<u32> {
        match *op {
            Op::Submit(j) | Op::Get(j) => Keys::one(j),
        }
    }

    fn step_keys(&self, Step::Run(j): &Step) -> Keys<u32> {
        Keys::one(*j)
    }
}

fn checker(within: Option<u32>) -> Checker<JobSpec> {
    Checker::new(JobSpec { within }, Queue::default(), Config::default())
}

#[test]
fn completion_is_observed_and_the_profile_collapses() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7), Resp::Accepted).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    assert_eq!(c.profile().len(), 1, "the run is deferred, not expanded");
    c.call(3, Op::Get(7), Resp::Is(Status::Failed)).unwrap();
    assert!(c.all(|s| s.jobs[&7] == Status::Failed));
    assert!(c.call(4, Op::Get(7), Resp::Is(Status::Completed)).is_err());
}

#[test]
fn bounded_eventually_rejects_a_stuck_job() {
    let mut c = checker(Some(2));
    c.call(1, Op::Submit(7), Resp::Accepted).unwrap();
    // `within: 2`: two later reads may still show it Pending, the third may not.
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    c.call(3, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    let v = c.call(4, Op::Get(7), Resp::Is(Status::Pending)).unwrap_err();
    println!("{v}");
}

#[test]
fn quiesce_discharges_unbounded_eventually() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7), Resp::Accepted).unwrap();
    c.call(2, Op::Get(7), Resp::Is(Status::Pending)).unwrap();
    c.quiesce().unwrap();
    assert_eq!(c.profile().len(), 2, "Completed or Failed, nothing pending");
    assert!(c.all(|s| s.jobs[&7] != Status::Pending));
    assert!(c.call(3, Op::Get(7), Resp::Is(Status::Pending)).is_err());
}

#[test]
fn a_get_in_flight_across_completion_may_see_either() {
    let mut c = checker(None);
    c.call(1, Op::Submit(7), Resp::Accepted).unwrap();
    c.invoke(2, Op::Get(7)).unwrap();
    c.call(3, Op::Get(7), Resp::Is(Status::Completed)).unwrap();
    // Call 2 was in flight while the job completed: Pending is still a valid answer.
    c.ret(2, Resp::Is(Status::Pending)).unwrap();
}

#[test]
fn independent_jobs_stay_deferred() {
    let mut c = checker(None);
    for j in 0..12 {
        c.call(j as u64, Op::Submit(j), Resp::Accepted).unwrap();
    }
    c.call(100, Op::Get(3), Resp::Is(Status::Completed)).unwrap();
    // Twelve runs, each with two outcomes, but only job 3 was ever expanded.
    assert_eq!(c.stats.max_width, 1, "{:?}", c.stats);
}
