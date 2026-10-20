//! The dials. Flags, then environment, then defaults.

use clap::Parser;

#[derive(Debug, Clone, Parser)]
#[command(name = "echod-server", about = "A Resonate server over an S3 bucket", version)]
pub struct Config {
    /// The store, as a URL: `s3://bucket/prefix`, `gs://bucket`,
    /// `az://container`, `file:///dir`, `memory:///`. Without it and without a
    /// bucket the server runs on an in-memory store and nothing survives the
    /// process.
    #[arg(long, env = "ECHOD_STORE")]
    pub store: Option<String>,

    /// S3 bucket holding every object; the same as `--store s3://bucket`,
    /// except with `--express`, where writes append.
    #[arg(long, env = "ECHOD_BUCKET")]
    pub bucket: Option<String>,

    /// Region. Defaults to what the environment says.
    #[arg(long, env = "ECHOD_REGION")]
    pub region: Option<String>,

    /// Endpoint override, for an S3-compatible service.
    #[arg(long, env = "ECHOD_ENDPOINT")]
    pub endpoint: Option<String>,

    /// Prefix under which every key lives.
    #[arg(long, env = "ECHOD_PREFIX", default_value = "")]
    pub prefix: String,

    /// The bucket is an S3 Express One Zone directory bucket: writes append.
    #[arg(long, env = "ECHOD_EXPRESS", default_value_t = false)]
    pub express: bool,

    /// Rewrite an origin's object once it carries this many stale rows.
    /// 0 rewrites on every write, which is what general-purpose S3 does anyway.
    #[arg(long, env = "ECHOD_COMPACT", default_value_t = 64)]
    pub compact: u32,

    /// Where to listen.
    #[arg(long, env = "ECHOD_BIND", default_value = "0.0.0.0:8001")]
    pub bind: String,

    /// This node's URL as the other nodes and the workers reach it.
    /// Stamped into every execute message and announced in the bucket.
    #[arg(long, env = "ECHOD_URL")]
    pub url: Option<String>,

    /// This node's id. Random when unset.
    #[arg(long, env = "ECHOD_NODE_ID")]
    pub node_id: Option<String>,

    /// How long a task is left unclaimed before it is re-offered, in ms.
    #[arg(long, env = "ECHOD_RETRY_TIMEOUT", default_value_t = 60_000)]
    pub retry_timeout: u64,

    /// The width of a timer bucket, in ms. Deadlines are keyed by the bucket
    /// they fall in; a node lists one bucket at a time as the clock reaches it.
    #[arg(long, env = "ECHOD_TIMER_BUCKET", default_value_t = 3_600_000)]
    pub timer_bucket_ms: u64,

    /// How often this node refreshes its announcement, in ms.
    #[arg(long, env = "ECHOD_HEARTBEAT", default_value_t = 5_000)]
    pub heartbeat_ms: u64,

    /// A node whose announcement is older than this is dead, in ms.
    #[arg(long, env = "ECHOD_NODE_TTL", default_value_t = 15_000)]
    pub node_ttl_ms: u64,

    /// Documents held in the read cache, at most.
    #[arg(long, env = "ECHOD_CACHE_ENTRIES", default_value_t = 10_000)]
    pub cache_entries: usize,

    /// Bytes of documents held in the read cache, at most, by object size.
    #[arg(long, env = "ECHOD_CACHE_BYTES", default_value_t = 256 * 1024 * 1024)]
    pub cache_bytes: u64,

    /// Forward a request for an origin another node owns to that node.
    #[arg(long, env = "ECHOD_FORWARD", default_value_t = true, action = clap::ArgAction::Set)]
    pub forward: bool,

    /// Debug mode: the clock is the request's `resonate:debug_time`, and no
    /// loop runs on wall time.
    #[arg(long, env = "ECHOD_DEBUG", default_value_t = false)]
    pub debug: bool,
}

impl Config {
    /// A configuration for an in-memory, single-node server. Tests.
    pub fn memory(bind: &str) -> Self {
        Self {
            store: None,
            bucket: None,
            region: None,
            endpoint: None,
            prefix: String::new(),
            express: false,
            compact: 0,
            bind: bind.to_string(),
            url: None,
            node_id: None,
            retry_timeout: 60_000,
            timer_bucket_ms: 3_600_000,
            heartbeat_ms: 500,
            node_ttl_ms: 2_000,
            cache_entries: 1_000,
            cache_bytes: 16 * 1024 * 1024,
            forward: true,
            debug: false,
        }
    }

    pub fn kernel(&self) -> echod_kernel::Config {
        echod_kernel::Config { retry_timeout: self.retry_timeout, compact: self.compact }
    }
}
