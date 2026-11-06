//! The next time a schedule is due.
//!
//! A 5-field expression is read as minutes first, with the seconds field
//! fixed at 0. The cron calendar stops around year 2100, so a later instant
//! is matched to the same month, day, weekday and time of day inside that
//! range, and the distance is added back.

use chrono::{Datelike, Timelike};
use cron::Schedule;
use std::str::FromStr;

fn normalize(expr: &str) -> String {
    if expr.split_whitespace().count() == 5 {
        format!("0 {}", expr.trim())
    } else {
        expr.trim().to_string()
    }
}

/// Whether the engine accepts the expression.
pub fn valid(expr: &str) -> bool {
    Schedule::from_str(&normalize(expr)).is_ok()
}

/// The next occurrence strictly after `after_ms`, in milliseconds.
/// An expression that does not parse is retried a minute later.
pub fn next_after(expr: &str, after_ms: i64) -> i64 {
    let full = normalize(expr);
    if let Ok(schedule) = Schedule::from_str(&full) {
        let after_secs = after_ms / 1000;
        let after_dt = chrono::DateTime::from_timestamp(after_secs, 0).unwrap_or_else(|| chrono::DateTime::from_timestamp(0, 0).unwrap());
        const MAX_CRON_YEAR: i32 = 2099;
        let (ref_dt, delta_secs) = if after_dt.year() <= MAX_CRON_YEAR {
            (after_dt, 0i64)
        } else {
            let naive = after_dt.naive_utc();
            let (month, day, hour, minute, second) = (naive.month(), naive.day(), naive.hour(), naive.minute(), naive.second());
            let target_weekday = naive.weekday();
            let is_leap_day = month == 2 && day == 29;
            let equiv_secs = (1970i32..=MAX_CRON_YEAR).rev().find_map(|y| {
                if is_leap_day && chrono::NaiveDate::from_ymd_opt(y, 2, 29).is_none() {
                    return None;
                }
                chrono::NaiveDate::from_ymd_opt(y, month, day)
                    .filter(|d| d.weekday() == target_weekday)
                    .and_then(|d| d.and_hms_opt(hour, minute, second))
                    .map(|dt| dt.and_utc().timestamp())
            });
            if let Some(ref_secs) = equiv_secs {
                let ref_dt = chrono::DateTime::from_timestamp(ref_secs, 0).unwrap();
                (ref_dt, after_secs - ref_secs)
            } else {
                (after_dt, 0i64)
            }
        };
        if let Some(next) = schedule.after(&ref_dt).next() {
            return (next.timestamp() + delta_secs) * 1000;
        }
    }
    after_ms + 60_000
}

/// `next_after`, as a `u64` instant strictly after `after_ms`.
pub fn next_run_at(expr: &str, after_ms: u64) -> u64 {
    let after = i64::try_from(after_ms).unwrap_or(i64::MAX);
    let next = next_after(expr, after).max(after.saturating_add(1));
    u64::try_from(next).unwrap_or_else(|_| after_ms.saturating_add(60_000).max(after_ms.saturating_add(1)))
}
