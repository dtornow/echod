//! Schedules as objects, fired by the owner.
//!
//! A schedule is one row at `sched/<id>`, and one timer key for its next run.
//! Firing creates the occurrence's promise in its origin's document and
//! advances the schedule, both through the kernel, in one actor turn on the
//! promise's origin. A crash between the two refires the occurrence, and the
//! kernel's `createIfAbsent` makes that a no-op.

use std::sync::Arc;

use echod_kernel::{Occurrence, ScheduleTimeoutReq, State};
use resonate_core::{util, Unavailable};

use crate::applier::Applier;
use crate::keys::origin_of;

pub struct Schedules {
    applier: Arc<Applier>,
}

impl Schedules {
    pub fn new(applier: Arc<Applier>) -> Self {
        Self { applier }
    }

    /// The promise id an occurrence expands to.
    pub fn expand(template: &str, id: &str, at: u64) -> String {
        template.replace("{{.id}}", id).replace("{{.timestamp}}", &at.to_string())
    }

    /// Fire the occurrence at `deadline`, noticed at `now`.
    pub async fn fire(&self, id: &str, deadline: u64, now: u64) -> Result<(), Unavailable> {
        // The schedule row decides the promise id, so it is read first, alone.
        let Some(c) = self.applier.peek_schedule(id).await? else { return Ok(()) };
        if c.next_run_at != deadline {
            // Fired already, or moved on. The key is stale.
            return Ok(());
        }
        let promise_id = Self::expand(&c.promise_id, id, deadline);
        let origin = origin_of(&promise_id).to_string();
        let next = util::compute_next_cron(&c.cron, deadline as i64).max(deadline as i64 + 1) as u64;
        let cfg = self.applier.kernel_config();
        let req = ScheduleTimeoutReq { schedule: id.to_string(), occurrences: vec![Occurrence { at: deadline, promise_id }], next_run_at: next };
        self.applier
            .apply(Some(&origin), Some(id), now, None, |s: &mut State, now: u64| {
                let Some(i) = s.schedules.iter().position(|c| c.id == req.schedule) else { return ((), false) };
                if s.schedules[i].next_run_at != deadline {
                    return ((), false);
                }
                // The fired promise carries the schedule's stamp and its own
                // lineage; the schedule row keeps its template tags.
                let template = s.schedules[i].promise_tags.clone();
                s.schedules[i].promise_tags = stamped(&template, &req.schedule, &req.occurrences[0].promise_id);
                s.process_schedule(&req, now, &cfg);
                if let Some(c) = s.schedules.iter_mut().find(|c| c.id == req.schedule) {
                    c.promise_tags = template;
                }
                ((), false)
            })
            .await
            .map(|_| ())
    }
}

/// `resonate:schedule`, and the lineage tags, onto the promise the schedule
/// fires, over the schedule's template tags.
fn stamped(template: &[(String, String)], id: &str, promise_id: &str) -> Vec<(String, String)> {
    let mut tags: Vec<(String, String)> = template.iter().filter(|(k, _)| !k.starts_with("resonate:schedule") && !["resonate:origin", "resonate:branch", "resonate:parent", "resonate:prefix"].contains(&k.as_str())).cloned().collect();
    tags.push(("resonate:schedule".to_string(), id.to_string()));
    for key in ["resonate:origin", "resonate:branch", "resonate:parent", "resonate:prefix"] {
        tags.push((key.to_string(), promise_id.to_string()));
    }
    tags.sort();
    tags
}
