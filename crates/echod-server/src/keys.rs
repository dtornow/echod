//! Where everything lives under the bucket.
//!
//! ```text
//! <prefix>wf/<origin>                                    an origin's document: rows
//! <prefix>sched/<id>                                     a schedule: one row
//! <prefix>t/<bucket>/<deadline>_<origin>@<token>         a deadline for an origin, empty
//! <prefix>t/<bucket>/<deadline>_sched:<id>@<token>       a schedule's next run, empty
//! <prefix>nodes/<node id>                                a node's announcement
//! <prefix>members                                        the configuration: members and epoch
//! ```
//!
//! A deadline key lives in the time bucket its deadline falls in, so what is
//! due is found by listing the buckets at or before now and nothing later. The
//! token names the arm that wrote the key, so a writer removes exactly the key
//! its predecessor wrote and never one that happens to share the deadline.

const DEADLINE_WIDTH: usize = 20;

#[derive(Debug, Clone)]
pub struct KeySpace {
    prefix: String,
    /// The width of a timer bucket, ms.
    bucket_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimerEntry {
    Origin { deadline: u64, origin: String, token: u64, by: String },
    Schedule { deadline: u64, id: String, token: u64, by: String },
}

impl TimerEntry {
    pub fn deadline(&self) -> u64 {
        match self {
            TimerEntry::Origin { deadline, .. } | TimerEntry::Schedule { deadline, .. } => *deadline,
        }
    }
    /// What ownership is decided on.
    pub fn target(&self) -> &str {
        match self {
            TimerEntry::Origin { origin, .. } => origin,
            TimerEntry::Schedule { id, .. } => id,
        }
    }
}

/// Percent-encode anything that is not safe and stable in a key.
pub fn encode_key(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for b in s.as_bytes() {
        match b {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'.' | b'-' => out.push(*b as char),
            other => out.push_str(&format!("%{other:02X}")),
        }
    }
    out
}

pub fn decode_key(s: &str) -> Option<String> {
    let bytes = s.as_bytes();
    let mut out: Vec<u8> = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'%' {
            if i + 2 >= bytes.len() {
                return None;
            }
            let hex = std::str::from_utf8(&bytes[i + 1..i + 3]).ok()?;
            out.push(u8::from_str_radix(hex, 16).ok()?);
            i += 3;
        } else {
            out.push(bytes[i]);
            i += 1;
        }
    }
    String::from_utf8(out).ok()
}

/// FNV-1a: one stable hash, the same on every node and every build.
pub fn fnv1a(s: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.as_bytes() {
        h ^= *b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

/// The origin of an id: everything before the first `:`.
pub fn origin_of(id: &str) -> &str {
    id.split_once(':').map(|(o, _)| o).unwrap_or(id)
}

impl KeySpace {
    pub fn new(prefix: &str, bucket_ms: u64) -> Self {
        let mut prefix = prefix.to_string();
        if !prefix.is_empty() && !prefix.ends_with('/') {
            prefix.push('/');
        }
        Self { prefix, bucket_ms: bucket_ms.max(1) }
    }

    pub fn bucket_ms(&self) -> u64 {
        self.bucket_ms
    }

    pub fn doc_key(&self, origin: &str) -> String {
        format!("{}wf/{}", self.prefix, encode_key(origin))
    }

    pub fn sched_key(&self, id: &str) -> String {
        format!("{}sched/{}", self.prefix, encode_key(id))
    }

    /// The configuration object: the members and their epoch.
    pub fn members_key(&self) -> String {
        format!("{}members", self.prefix)
    }

    pub fn node_prefix(&self) -> String {
        format!("{}nodes/", self.prefix)
    }

    pub fn node_key(&self, id: &str) -> String {
        format!("{}nodes/{}", self.prefix, encode_key(id))
    }

    pub fn node_of_key(&self, key: &str) -> Option<String> {
        decode_key(key.strip_prefix(&self.node_prefix())?)
    }

    /// The start of the bucket an instant falls in.
    pub fn bucket_of(&self, at: u64) -> u64 {
        at / self.bucket_ms * self.bucket_ms
    }

    /// Every timer key lives under this.
    pub fn timer_prefix(&self) -> String {
        format!("{}t/", self.prefix)
    }

    /// The keys of one bucket live under this. `bucket` is a bucket start.
    pub fn bucket_prefix(&self, bucket: u64) -> String {
        format!("{}t/{:0width$}/", self.prefix, bucket, width = DEADLINE_WIDTH)
    }

    /// The bucket start a bucket prefix names, as a listing returns it.
    pub fn parse_bucket_prefix(&self, prefix: &str) -> Option<u64> {
        let name = prefix.strip_prefix(&self.timer_prefix())?.trim_end_matches('/');
        if name.len() != DEADLINE_WIDTH {
            return None;
        }
        name.parse().ok()
    }

    /// A key names what is due, when, a token drawn per arm, and the node
    /// that armed it: only that node deletes it outright.
    fn timer_key_for(&self, encoded: &str, at: u64, token: u64, by: &str) -> String {
        format!("{}{:0width$}_{}@{:016x}~{}", self.bucket_prefix(self.bucket_of(at)), at, encoded, token, encode_key(by), width = DEADLINE_WIDTH)
    }

    pub fn timer_key(&self, origin: &str, at: u64, token: u64, by: &str) -> String {
        self.timer_key_for(&encode_key(origin), at, token, by)
    }

    pub fn sched_timer_key(&self, id: &str, at: u64, token: u64, by: &str) -> String {
        self.timer_key_for(&format!("sched:{}", encode_key(id)), at, token, by)
    }

    pub fn timer_key_of(&self, e: &TimerEntry) -> String {
        match e {
            TimerEntry::Origin { deadline, origin, token, by } => self.timer_key(origin, *deadline, *token, by),
            TimerEntry::Schedule { deadline, id, token, by } => self.sched_timer_key(id, *deadline, *token, by),
        }
    }

    pub fn parse_timer_key(&self, key: &str) -> Option<TimerEntry> {
        let name = key.rsplit('/').next()?;
        if name.len() < DEADLINE_WIDTH + 2 {
            return None;
        }
        let (deadline, rest) = name.split_at(DEADLINE_WIDTH);
        let deadline: u64 = deadline.parse().ok()?;
        let (target, rest) = rest.strip_prefix('_')?.rsplit_once('@')?;
        let (token, by) = rest.split_once('~')?;
        let token = u64::from_str_radix(token, 16).ok()?;
        let by = decode_key(by)?;
        match target.strip_prefix("sched:") {
            Some(id) => Some(TimerEntry::Schedule { deadline, id: decode_key(id)?, token, by }),
            None => Some(TimerEntry::Origin { deadline, origin: decode_key(target)?, token, by }),
        }
    }
}
