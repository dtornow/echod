//! The dials the core decides with. No flags, no environment: the
//! executor fills these in from wherever it takes its configuration.

#[derive(Debug, Clone)]
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
    /// How often this node refreshes its announcement, ms.
    pub heartbeat_ms: u64,
    /// A node whose announcement is older than this is dead, ms.
    pub node_ttl_ms: u64,
    /// Documents held in the read cache, at most.
    pub cache_entries: usize,
    /// Bytes of documents held in the read cache, at most.
    pub cache_bytes: u64,
    /// The clock a request is decided at is the request's
    /// `resonate:debug_time` when it carries one.
    pub debug: bool,
}

impl Config {
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
            heartbeat_ms: 500,
            node_ttl_ms: 2_000,
            cache_entries: 1_000,
            cache_bytes: 16 * 1024 * 1024,
            debug: false,
        }
    }

    pub fn kernel(&self) -> echod_kernel::Config {
        echod_kernel::Config { retry_timeout: self.retry_timeout, compact: self.compact }
    }
}
