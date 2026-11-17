//! Commit ordering definitions are owned by the concrete specification.

pub use echod_concrete_spec::state::ACommit;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    spec_production_prepare as spec_prepare,
    spec_production_armed as spec_armed,
    spec_production_to_disarm as spec_to_disarm,
    spec_production_keep as spec_keep,
    spec_production_finish as spec_finish,
    production_opt_nat as opt_nat,
    production_opt_str as opt_str,
};
