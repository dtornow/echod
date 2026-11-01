//! What the node takes from outside the store: the clock, and whoever
//! wants to hear what the core notes. Both are ports so a simulation can
//! own them.

use echod_logic::Note;

/// Wall time in ms, or whatever stands in for it.
pub trait Clock: Send + Sync {
    fn now(&self) -> u64;
}

/// The system clock.
pub struct SystemClock;

impl Clock for SystemClock {
    fn now(&self) -> u64 {
        resonate_core::util::system_time_ms().max(0) as u64
    }
}

/// What a simulation watches: every note the core makes, the internal
/// steps a node runs on its own among them, which no client sees but
/// which a model must account for.
pub trait Notes: Send + Sync {
    fn note(&self, node: &str, note: &Note) {
        let _ = (node, note);
    }
}

/// Hears nothing.
pub struct NoNotes;

impl Notes for NoNotes {}
