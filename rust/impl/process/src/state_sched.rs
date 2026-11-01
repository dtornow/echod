//! One schedule's rows: the half a schedule handler decides on.
//!
//! The proved step takes them as `verified::State` with an empty promise half.
//! A run that is due is decided across both halves, in `handler_sched`.

use crate::verified::{Schedule, State as Proved};

/// The rows of one schedule.
pub struct Sched {
    pub rows: Vec<Schedule>,
}

impl Sched {
    /// The proved document, promises empty.
    pub fn proved(rows: Vec<Schedule>) -> Proved {
        Proved { objects: Vec::new(), schedules: rows, outbox: Vec::new() }
    }

    pub fn rows_of(s: &Proved) -> Vec<Schedule> {
        s.schedules.clone()
    }
}
