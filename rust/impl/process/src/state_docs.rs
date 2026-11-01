//! The promise rows of one origin: the half a document handler decides on.
//!
//! A task is a field of its promise, so this is the promises and the tasks
//! inside them. The proved step takes the rows as `verified::State` with an
//! empty schedule half.

use crate::verified::{Promise, State as Proved};

/// The promise rows of one origin.
pub struct Docs {
    pub rows: Vec<Promise>,
}

impl Docs {
    /// The proved document, schedules empty.
    pub fn proved(rows: Vec<Promise>) -> Proved {
        Proved { objects: rows, schedules: Vec::new(), outbox: Vec::new() }
    }

    pub fn rows_of(s: &Proved) -> Vec<Promise> {
        s.objects.clone()
    }
}
