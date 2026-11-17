//! Mathematical node ownership and timer memory, owned by the concrete specification.

use vstd::prelude::*;
pub use echod_concrete_spec::state::{AKey, AArmed, AEntry, ANode};
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::handler::{
    production_hash as hash,
    spec_production_owner as spec_owner,
    spec_production_fresh as spec_fresh,
    spec_production_acts as spec_acts,
    spec_production_read_config as spec_read_config,
    spec_production_filled as spec_filled,
    spec_production_forget as spec_forget,
    spec_production_set_armed as spec_set_armed,
    spec_production_collected as spec_collected,
};

verus! {
pub type Id = Seq<char>;
pub type Origin = Seq<char>;
}
