//! The dials the core decides with. No flags, no environment: the
//! executor fills these in from wherever it takes its configuration.

use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
pub use echod_concrete_spec::state::ProductionConfigV as ConfigSpec;

verus! {
#[derive(Debug, Clone, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]

pub struct Config {
    /// This node's id, as the other nodes and the bucket know it.
    pub node_id: String,
    /// This node's URL as the workers reach it: stamped into every
    /// execute message and announced in the bucket.
    pub url: String,
    /// Prefix under which every key lives.
    pub prefix: String,
    /// Rewrite a document once it carries this many stale rows; 0 rewrites
    /// on every write.
    pub compact: u32,
    /// Whether the store appends, so a document can grow as a log.
    pub appendable: bool,
    /// How long a task is left unclaimed before it is re-offered, ms.
    pub retry_timeout: u64,
    /// The width of a timer bucket, ms.
    pub timer_bucket_ms: u64,
    pub timer_rediscovery_ms: u64,
    /// How often this node refreshes its announcement, ms.
    pub heartbeat_ms: u64,
    /// A node whose announcement is older than this is dead, ms.
    pub node_ttl_ms: u64,
    /// Documents held in the read cache, at most.
    pub cache_entries: usize,
    /// Bytes of documents held in the read cache, at most.
    pub cache_bytes: u64,
    /// Debug mode, as the runtime reads it: it admits debug operations,
    /// and a request may name the instant it is decided at.
    pub debug: bool,
}

#[cfg(verus_keep_ghost)]
impl DeepView for Config {
    type V = ConfigSpec;
    open spec fn deep_view(&self) -> ConfigSpec {
        ConfigSpec {
            node_id: self.node_id@,
            url: self.url@,
            prefix: self.prefix@,
            compact: self.compact,
            appendable: self.appendable,
            retry_timeout: self.retry_timeout,
            timer_bucket_ms: self.timer_bucket_ms,
            timer_rediscovery_ms: self.timer_rediscovery_ms,
            heartbeat_ms: self.heartbeat_ms,
            node_ttl_ms: self.node_ttl_ms,
            cache_entries: self.cache_entries,
            cache_bytes: self.cache_bytes,
            debug: self.debug,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for Config {
    type V = ConfigSpec;
    open spec fn view(&self) -> ConfigSpec {
        self.deep_view()
    }
}

} // verus!

impl Config {
    /// Validate dials whose arithmetic is used by the protocol core.
    pub fn validate(&self) -> Result<(), String> {
        if self.timer_rediscovery_ms == 0 || self.timer_rediscovery_ms > echod_types::MAX_TIME {
            return Err(format!("timer rediscovery interval must be between 1 and {}", echod_types::MAX_TIME));
        }
        if self.retry_timeout == 0 {
            return Err("retry timeout must be greater than zero".to_string());
        }
        if self.retry_timeout > echod_types::MAX_TIME {
            return Err(format!(
                "retry timeout must be at most {}",
                echod_types::MAX_TIME
            ));
        }
        Ok(())
    }

    /// A node on an in-memory store, for tests.
    pub fn memory(node_id: &str) -> Self {
        Self {
            node_id: node_id.to_string(),
            url: format!("memory://{node_id}/"),
            prefix: String::new(),
            compact: 0,
            appendable: false,
            retry_timeout: 60_000,
            timer_bucket_ms: 3_600_000,
            timer_rediscovery_ms: 300_000,
            heartbeat_ms: 500,
            node_ttl_ms: 2_000,
            cache_entries: 1_000,
            cache_bytes: 16 * 1024 * 1024,
            debug: false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Config;

    #[test]
    fn timer_rediscovery_interval_is_positive_and_bounded() {
        let mut cfg = Config::memory("node");
        assert_eq!(cfg.timer_rediscovery_ms, 300_000);
        for interval in [0, echod_types::MAX_TIME + 1] {
            cfg.timer_rediscovery_ms = interval;
            assert!(cfg.validate().is_err());
        }
        for interval in [1, 2_500, echod_types::MAX_TIME] {
            cfg.timer_rediscovery_ms = interval;
            assert!(cfg.validate().is_ok());
        }
    }

    #[test]
    fn retry_timeout_respects_protocol_bounds() {
        let mut cfg = Config::memory("node");
        cfg.retry_timeout = 0;
        assert!(cfg.validate().is_err());

        cfg.retry_timeout = echod_types::MAX_TIME + 1;
        assert!(cfg.validate().is_err());

        cfg.retry_timeout = echod_types::MAX_TIME;
        assert!(cfg.validate().is_ok());
    }
}
