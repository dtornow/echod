//! Where everything lives under the bucket.
//!
//! ```text
//! <prefix>wf/<origin>                    an origin's document: rows
//! <prefix>sched/<id>                     a schedule: one row
//! <prefix>t/<shard>/<deadline>_<origin>  a deadline for an origin, empty
//! <prefix>t/<shard>/<deadline>_sched:<id>
//! <prefix>nodes/<node id>                a node's announcement
//! ```

const DEADLINE_WIDTH: usize = 20;

#[derive(Debug, Clone)]
pub struct KeySpace {
    prefix: String,
    timer_shards: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimerEntry {
    Origin { deadline: u64, origin: String },
    Schedule { deadline: u64, id: String },
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
    pub fn new(prefix: &str, timer_shards: u32) -> Self {
        let mut prefix = prefix.to_string();
        if !prefix.is_empty() && !prefix.ends_with('/') {
            prefix.push('/');
        }
        Self { prefix, timer_shards: timer_shards.max(1) }
    }

    pub fn timer_shards(&self) -> u32 {
        self.timer_shards
    }

    pub fn doc_key(&self, origin: &str) -> String {
        format!("{}wf/{}", self.prefix, encode_key(origin))
    }

    pub fn sched_key(&self, id: &str) -> String {
        format!("{}sched/{}", self.prefix, encode_key(id))
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

    pub fn timer_shard_prefix(&self, shard: u32) -> String {
        format!("{}t/{:02}/", self.prefix, shard % self.timer_shards)
    }

    fn shard_of(&self, target: &str) -> u32 {
        (fnv1a(target) % self.timer_shards as u64) as u32
    }

    fn timer_key_for(&self, target: &str, encoded: &str, at: u64) -> String {
        format!("{}{:0width$}_{}", self.timer_shard_prefix(self.shard_of(target)), at, encoded, width = DEADLINE_WIDTH)
    }

    pub fn timer_key(&self, origin: &str, at: u64) -> String {
        self.timer_key_for(origin, &encode_key(origin), at)
    }

    pub fn sched_timer_key(&self, id: &str, at: u64) -> String {
        self.timer_key_for(id, &format!("sched:{}", encode_key(id)), at)
    }

    pub fn timer_key_of(&self, e: &TimerEntry) -> String {
        match e {
            TimerEntry::Origin { deadline, origin } => self.timer_key(origin, *deadline),
            TimerEntry::Schedule { deadline, id } => self.sched_timer_key(id, *deadline),
        }
    }

    pub fn parse_timer_key(&self, key: &str) -> Option<TimerEntry> {
        let name = key.rsplit('/').next()?;
        if name.len() < DEADLINE_WIDTH + 2 {
            return None;
        }
        let (deadline, rest) = name.split_at(DEADLINE_WIDTH);
        let deadline: u64 = deadline.parse().ok()?;
        let target = rest.strip_prefix('_')?;
        match target.strip_prefix("sched:") {
            Some(id) => Some(TimerEntry::Schedule { deadline, id: decode_key(id)? }),
            None => Some(TimerEntry::Origin { deadline, origin: decode_key(target)? }),
        }
    }
}
