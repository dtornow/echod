//! Test support for tracing and driving the Echod abstract model.

pub mod trace;
pub mod workload;

pub use trace::{history_rank, history_responses, rover_trace, HistoryEvent};
pub use workload::{arbitrary, finish, next_cron, plain, suggest, Action, IDS, SCHEDULES};
