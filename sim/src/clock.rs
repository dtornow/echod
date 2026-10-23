//! Virtual time. Under tokio's paused clock, `Instant` advances only when
//! every task is idle, and then straight to the next timer. `SimClock` reads
//! it through the node's `Clock` port: the reference every client stamps
//! its requests with. `NodeClock` is what a node sees: the reference plus a
//! fixed skew, a drift that grows with time, and the jumps the run inflicts,
//! backwards included. Nothing a node does with its clock may make the state
//! wrong; the membership rules and the per-origin clamp are what it tests.

use echod::env::Clock;

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

pub struct NodeClock {
    reference: std::sync::Arc<SimClock>,
    skew_ms: i64,
    drift_ppm: i64,
    /// Jumps move the clock within this band, either way, so what a run
    /// inflicts stays inside the skew the server is told to expect.
    band_ms: i64,
    offset: std::sync::Mutex<i64>,
}

impl NodeClock {
    pub fn new(reference: std::sync::Arc<SimClock>, skew_ms: i64, drift_ppm: i64, band_ms: i64) -> Self {
        Self { reference, skew_ms, drift_ppm, band_ms, offset: std::sync::Mutex::new(0) }
    }

    /// Step the clock by `delta_ms`, negative for a step back, within the band.
    pub fn jump(&self, delta_ms: i64) {
        let mut o = self.offset.lock().unwrap();
        *o = (*o + delta_ms).clamp(-self.band_ms, self.band_ms);
    }

    pub fn offset(&self) -> i64 {
        *self.offset.lock().unwrap()
    }
}

impl Clock for NodeClock {
    fn now(&self) -> u64 {
        let elapsed = self.reference.start.elapsed().as_millis() as i64;
        let drift = elapsed * self.drift_ppm / 1_000_000;
        let t = self.reference.now() as i64 + self.skew_ms + drift + self.offset();
        t.max(0) as u64
    }
}
