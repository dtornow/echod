//! state definitions for the abstract model.
#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::contrib::make_spec_type;
use echod_types::*;
#[cfg(verus_keep_ghost)]
use echod_types::common::*;
use rover_spec::rover::comm::{Sched, ProcessEvent};
use rover_spec::rover::RoverSpec;
use RoverSpec::{Label, Proc as _, Spec as _, StepResultV};
#[cfg(verus_keep_ghost)]
use crate::axioms::*;

verus! {
pub type Time = u64;

pub type Chars = Seq<char>;

pub struct PromiseV {
    pub state: PromiseState,
    pub value: Value,
    pub param: Value,
    pub timeout_at: Time,
    pub created_at: Time,
    pub settled_at: Option<Time>,
    pub tags: Tags,
    pub callbacks: Set<Chars>,
    pub listeners: Set<Chars>,
}

pub struct TaskV {
    pub state: TaskState,
    pub version: u64,
    pub pid: Option<Chars>,
    pub ttl: Option<Time>,
    pub acquired_at: Time,
    pub retry_timeout_at: Option<Time>,
    pub resumes: Seq<Chars>,
}

pub struct ScheduleV {
    pub id: Chars,
    pub cron: Chars,
    pub promise_id: Chars,
    pub promise_timeout: Time,
    pub promise_param: Value,
    pub promise_tags: Tags,
    pub created_at: Time,
    pub next_run_at: Time,
    pub last_run_at: Option<Time>,
}

pub struct StoreV {
    pub promises: Map<Chars, PromiseV>,
    pub tasks: Map<Chars, TaskV>,
    pub schedules: Map<Chars, ScheduleV>,
}

pub enum InternalV {
    PromiseTimeout(Chars),
    Callback { awaited: Chars, awaiter: Chars },
    Listener { awaited: Chars, address: Chars },
    TaskLeaseTimeout(Chars),
    TaskRetryTimeout(Chars),
    ScheduleTimeout { id: Chars, promise: Chars },
    Occurrence { promise: Chars, at: Time, timeout: Time, param: Value, tags: Tags },
}

pub struct OutV {
    pub resp: Response,
    pub next: StoreV,
    pub work: Seq<Sched<InternalV>>,
    pub send: Seq<DispatchV>,
}

pub struct InOutV {
    pub next: StoreV,
    pub work: Seq<Sched<InternalV>>,
    pub send: Seq<DispatchV>,
    pub not_due: bool,
}

pub const MAX_VERSION: u32 = u32::MAX;

pub type Id = String;

#[allow(dead_code)]
pub enum SpecHeld {
    Ok(TaskV),
    Missing,
    Stale,
}

pub struct Proc {
    pub store: StoreV,
    pub pending: Seq<Sched<InternalV>>,
}
}
