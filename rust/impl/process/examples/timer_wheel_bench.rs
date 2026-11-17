use echod_logic::state_timers::TimerWheel;
use std::time::Instant;

fn main() {
    for n in [10_000, 20_000, 40_000] {
        let mut wheel = TimerWheel::new();
        let start = Instant::now();
        for i in 0..n {
            wheel.arm(i, format!("timer-{i:08}"));
        }
        println!("entries={n} elapsed_ms={:.3}", start.elapsed().as_secs_f64() * 1_000.0);
        assert_eq!(wheel.len(), n as usize);
    }
}
