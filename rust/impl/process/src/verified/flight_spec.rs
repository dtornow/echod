//! Production document decisions and commit ordering, owned by the concrete specification.

pub use echod_concrete_spec::state::{AJob, AFired, AStep, ASequence, AAct, AAnswer, AOutcome};
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    spec_production_step as spec_step,
    production_job_of as job_of,
    production_answer_v as answer_v,
    spec_production_new as spec_new,
    spec_production_collect as spec_collect,
    spec_production_advance as spec_advance,
    spec_production_served as spec_served,
    spec_production_run as spec_run,
    spec_production_arms as spec_arms,
    spec_production_plan_after as spec_plan_after,
    spec_production_calls as spec_calls,
    spec_production_node_after as spec_node_after,
};
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::property_proof::{
    lemma_production_step_is_decide as lemma_step_is_decide,
    lemma_production_sequence as lemma_sequence,
};
