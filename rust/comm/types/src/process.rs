//! Shared executor loop tags and operational outcomes.

use vstd::prelude::*;

verus! {
#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural)]
pub enum ProductionOwner {
    Flight(u64),
    Members,
    Timers,
    Debug,
    /// Nobody: a best-effort call whose answer changes nothing.
    Ignored,
}
#[cfg(verus_keep_ghost)]
impl DeepView for ProductionOwner {
    type V = ProductionOwner;
    open spec fn deep_view(&self) -> ProductionOwner {
        *self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Structural, Hash, PartialOrd, Ord)]
pub enum ProductionArmed {
    /// The heartbeat interval.
    Heartbeat,
    /// The wheel: a deadline falling due, or a bucket listing.
    Wheel,
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionArmed {
    type V = ProductionArmed;
    open spec fn deep_view(&self) -> ProductionArmed {
        *self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Structural)]
pub enum ProductionFired {
    /// Deleted from the bucket.
    Deleted,
    /// Still in the bucket: the delete failed. It fires again.
    Kept,
}

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionFired {
    type V = ProductionFired;
    open spec fn deep_view(&self) -> ProductionFired {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionWriteMode { Create, Rewrite, Append }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionWriteMode {
    type V = ProductionWriteMode;
    open spec fn deep_view(&self) -> ProductionWriteMode {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionCommitOutcome { Committed, Raced, Failed, Exhausted }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionCommitOutcome {
    type V = ProductionCommitOutcome;
    open spec fn deep_view(&self) -> ProductionCommitOutcome {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionCacheResult { Revalidated, Refreshed, Absent, Miss }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionCacheResult {
    type V = ProductionCacheResult;
    open spec fn deep_view(&self) -> ProductionCacheResult {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionConfigWrite { Written, Conflict, Failed }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionConfigWrite {
    type V = ProductionConfigWrite;
    open spec fn deep_view(&self) -> ProductionConfigWrite {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionTimerKind { Origin, Schedule }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionTimerKind {
    type V = ProductionTimerKind;
    open spec fn deep_view(&self) -> ProductionTimerKind {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionFireOutcome { Deleted, Kept, Failed, Deferred }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionFireOutcome {
    type V = ProductionFireOutcome;
    open spec fn deep_view(&self) -> ProductionFireOutcome {
        *self
    }
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, Structural, PartialOrd, Ord)]
pub enum ProductionSweepOutcome { Fired, Idle, Failed }

#[cfg(verus_keep_ghost)]
impl DeepView for ProductionSweepOutcome {
    type V = ProductionSweepOutcome;
    open spec fn deep_view(&self) -> ProductionSweepOutcome {
        *self
    }
}

}

macro_rules! label {
    ($name:ident { $($variant:ident => $text:literal),+ $(,)? }) => {
        impl $name {
            pub fn as_str(self) -> &'static str {
                match self { $(Self::$variant => $text),+ }
            }
        }
    };
}

label! { ProductionWriteMode { Create => "create", Rewrite => "rewrite", Append => "append" } }
label! { ProductionCommitOutcome { Committed => "committed", Raced => "raced", Failed => "failed", Exhausted => "exhausted" } }
label! { ProductionCacheResult { Revalidated => "revalidated", Refreshed => "refreshed", Absent => "absent", Miss => "miss" } }
label! { ProductionConfigWrite { Written => "written", Conflict => "conflict", Failed => "failed" } }
label! { ProductionTimerKind { Origin => "origin", Schedule => "schedule" } }
label! { ProductionFireOutcome { Deleted => "deleted", Kept => "kept", Failed => "failed", Deferred => "deferred" } }
label! { ProductionSweepOutcome { Fired => "fired", Idle => "idle", Failed => "failed" } }
