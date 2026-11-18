//! The next supported occurrence of a schedule, without synthetic deadlines.
//! Five-field expressions have an implicit zero seconds field. Calendar
//! support follows the cron engine (1970 through 2100, inclusive).

use chrono::{Datelike, TimeZone};
use cron::{Schedule, TimeUnitSpec};
use std::str::FromStr;

fn normalize(expr: &str) -> String {
    if expr.split_whitespace().count() == 5 {
        format!("0 {}", expr.trim())
    } else {
        expr.trim().to_string()
    }
}

pub fn valid(expr: &str) -> bool {
    Schedule::from_str(&normalize(expr)).is_ok()
}

/// None means no supported future occurrence, including invalid input.
pub fn next_after(expr: &str, after_ms: i64) -> Option<i64> {
    let schedule = Schedule::from_str(&normalize(expr)).ok()?;
    let after = chrono::DateTime::from_timestamp_millis(after_ms)?;
    let year = schedule.years().iter().find(|year| *year as i32 >= after.year())?;
    // cron 0.12 retains the original month/day lower bounds when skipping an
    // excluded year. Start just before the actual allowed year, not a remapped year.
    let cursor = if year as i32 > after.year() {
        chrono::Utc.with_ymd_and_hms(year as i32, 1, 1, 0, 0, 0).single()?
            .checked_sub_signed(chrono::Duration::milliseconds(1))?
    } else {
        after
    };
    schedule.after(&cursor).next().map(|next| next.timestamp_millis())
}

pub fn next_run_at(expr: &str, after_ms: u64) -> Option<u64> {
    let after = i64::try_from(after_ms).ok()?;
    u64::try_from(next_after(expr, after)?).ok().filter(|next| *next > after_ms)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn instant(value: &str) -> i64 {
        chrono::DateTime::parse_from_rfc3339(value).unwrap().timestamp_millis()
    }

    #[test]
    fn invalid_and_impossible_expressions_have_no_occurrence() {
        let now = instant("2026-01-01T00:00:00Z");
        assert_eq!(next_after("", now), None);
        assert_eq!(next_after("not a cron", now), None);
        assert!(valid("0 0 30 2 *"));
        assert_eq!(next_after("0 0 30 2 *", now), None);
    }

    #[test]
    fn finite_year_expires_at_its_final_occurrence() {
        let final_run = instant("2020-01-01T00:00:00Z");
        let cron = "0 0 0 1 1 * 2020";
        for offset in [1, 10_000, 86_400_000, 31 * 86_400_000, 366 * 86_400_000] {
            assert_eq!(next_after(cron, final_run - offset), Some(final_run));
        }
        assert_eq!(next_after(cron, final_run), None);
        assert_eq!(next_after(cron, final_run + 1), None);
        assert_eq!(next_after(cron, instant("2200-01-01T00:00:00Z")), None);
    }

    #[test]
    fn jumping_to_a_later_allowed_year_resets_calendar_bounds() {
        let at = instant("2026-01-01T00:00:00Z");
        assert_eq!(next_run_at("0 0 0 1 1 * 2026", (at - 10_000) as u64), Some(at as u64));
        assert_eq!(
            next_after("0 0 0 1 1 * 2026,2028", instant("2027-12-31T23:59:50Z")),
            Some(instant("2028-01-01T00:00:00Z")),
        );
        assert_eq!(
            next_after("0 0 0 1 1 * 2026,2028", at),
            Some(instant("2028-01-01T00:00:00Z")),
        );
    }

    #[test]
    fn year_2100_is_supported_without_remapping() {
        let at = instant("2100-01-01T00:00:00Z");
        assert_eq!(next_after("0 0 0 1 1 * 2100", at - 1), Some(at));
        assert_eq!(next_after("0 0 0 1 1 * 2100", at), None);
        assert_eq!(next_after("0 0 1 1 *", at - 1), Some(at));
        assert_eq!(next_after("0 0 1 1 *", at), None);
    }

    #[test]
    fn ordinary_schedules_are_strictly_future() {
        let at = instant("2026-01-01T00:00:00Z");
        assert_eq!(next_after("* * * * *", at), Some(at + 60_000));
        assert_eq!(next_after("* * * * * *", at + 999), Some(at + 1_000));
        assert_eq!(next_run_at("* * * * * *", at as u64), Some(at as u64 + 1_000));
    }

    #[test]
    fn leap_days_follow_the_calendar() {
        assert_eq!(
            next_after("0 0 29 2 *", instant("2026-01-01T00:00:00Z")),
            Some(instant("2028-02-29T00:00:00Z")),
        );
        assert_eq!(next_after("0 0 29 2 *", instant("2096-02-29T00:00:00Z")), None);
    }

    #[test]
    fn unrepresentable_instants_have_no_occurrence() {
        assert_eq!(next_after("* * * * * *", i64::MAX), None);
        assert_eq!(next_run_at("* * * * * *", u64::MAX), None);
    }
}
