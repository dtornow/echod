//! Virtual time. Under tokio's paused clock, `Instant` advances only when
//! every task is idle, and then straight to the next timer; this reads it
//! through the server's `Clock` port.

use echod_server::env::Clock;

pub struct SimClock {
    base_ms: u64,
    start: tokio::time::Instant,
}

impl SimClock {
    /// A clock reading `base_ms` now, in virtual time.
    pub fn new(base_ms: u64) -> Self {
        Self { base_ms, start: tokio::time::Instant::now() }
    }
}

impl Clock for SimClock {
    fn now(&self) -> u64 {
        self.base_ms + self.start.elapsed().as_millis() as u64
    }
}
