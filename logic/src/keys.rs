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

use echod_codec::store_key_text::{
    bucket_of_exec, class_of_text_key, decode_runtime_store_key, encode_runtime_store_key,
    KeyClass, StringStoreKey,
};

const DEADLINE_WIDTH: usize = 20;

#[derive(Debug, Clone)]
pub struct KeySpace {
    prefix: String,
    /// The width of a timer bucket, ms.
    bucket_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TimerEntry {
    Origin {
        deadline: u64,
        origin: String,
        token: u64,
        by: String,
    },
    Schedule {
        deadline: u64,
        id: String,
        token: u64,
        by: String,
    },
}

impl TimerEntry {
    pub fn deadline(&self) -> u64 {
        match self {
            TimerEntry::Origin { deadline, .. } | TimerEntry::Schedule { deadline, .. } => {
                *deadline
            }
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
    let key = encode_runtime_store_key(&String::new(), 1, &StringStoreKey::Document(s.to_string()))
        .expect("UTF-8 text has a canonical StoreKey encoding");
    key.strip_prefix("wf/")
        .expect("document StoreKey prefix")
        .to_string()
}

pub fn decode_key(s: &str) -> Option<String> {
    let key = format!("wf/{s}");
    match decode_runtime_store_key(&String::new(), 1, &key).ok()? {
        StringStoreKey::Document(value) => Some(value),
        _ => None,
    }
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
        Self {
            prefix,
            bucket_ms: bucket_ms.max(1),
        }
    }

    pub fn bucket_ms(&self) -> u64 {
        self.bucket_ms
    }

    fn encode(&self, key: StringStoreKey) -> String {
        encode_runtime_store_key(&self.prefix, self.bucket_ms, &key)
            .expect("runtime StoreKey is canonically encodable")
    }

    fn decode(&self, key: &str) -> Option<StringStoreKey> {
        decode_runtime_store_key(&self.prefix, self.bucket_ms, &key.to_string()).ok()
    }

    /// The class of object a key names: its first path segment under the
    /// prefix (`wf`, `sched`, `t`, `nodes`, `members`); `None` for a key
    /// outside the prefix.
    pub fn class_of<'a>(&self, key: &'a str) -> Option<&'a str> {
        match class_of_text_key(&self.prefix, &key.to_string())? {
            KeyClass::Document => Some("wf"),
            KeyClass::Schedule => Some("sched"),
            KeyClass::Timer => Some("t"),
            KeyClass::Node => Some("nodes"),
            KeyClass::Membership => Some("members"),
        }
    }

    pub fn doc_key(&self, origin: &str) -> String {
        self.encode(StringStoreKey::Document(origin.to_string()))
    }

    pub fn sched_key(&self, id: &str) -> String {
        self.encode(StringStoreKey::Schedule(id.to_string()))
    }

    /// The configuration object: the members and their epoch.
    pub fn members_key(&self) -> String {
        self.encode(StringStoreKey::Membership)
    }

    pub fn node_prefix(&self) -> String {
        self.node_key("")
    }

    pub fn node_key(&self, id: &str) -> String {
        self.encode(StringStoreKey::Node(id.to_string()))
    }

    pub fn node_of_key(&self, key: &str) -> Option<String> {
        match self.decode(key)? {
            StringStoreKey::Node(id) => Some(id),
            _ => None,
        }
    }

    /// The start of the bucket an instant falls in.
    pub fn bucket_of(&self, at: u64) -> u64 {
        bucket_of_exec(at, self.bucket_ms)
    }

    /// Every timer key lives under this.
    pub fn timer_prefix(&self) -> String {
        format!("{}t/", self.prefix)
    }

    /// The keys of one bucket live under this. `bucket` is a bucket start.
    pub fn bucket_prefix(&self, bucket: u64) -> String {
        format!(
            "{}t/{:0width$}/",
            self.prefix,
            bucket,
            width = DEADLINE_WIDTH
        )
    }

    /// The bucket start a bucket prefix names, as a listing returns it.
    pub fn parse_bucket_prefix(&self, prefix: &str) -> Option<u64> {
        let name = prefix
            .strip_prefix(&self.timer_prefix())?
            .trim_end_matches('/');
        if name.len() != DEADLINE_WIDTH {
            return None;
        }
        let candidate = format!("{prefix}{name}_x@0000000000000000~x");
        match decode_runtime_store_key(&self.prefix, 1, &candidate).ok()? {
            StringStoreKey::TimerOrigin { bucket, .. } => Some(bucket),
            _ => None,
        }
    }

    /// A key names what is due, when, a token drawn per arm, and the node
    /// that armed it: only that node deletes it outright.
    pub fn timer_key(&self, origin: &str, at: u64, token: u64, by: &str) -> String {
        self.encode(StringStoreKey::TimerOrigin {
            bucket: self.bucket_of(at),
            deadline: at,
            origin: origin.to_string(),
            token,
            by: by.to_string(),
        })
    }

    pub fn sched_timer_key(&self, id: &str, at: u64, token: u64, by: &str) -> String {
        self.encode(StringStoreKey::TimerSchedule {
            bucket: self.bucket_of(at),
            deadline: at,
            id: id.to_string(),
            token,
            by: by.to_string(),
        })
    }

    pub fn timer_key_of(&self, e: &TimerEntry) -> String {
        match e {
            TimerEntry::Origin {
                deadline,
                origin,
                token,
                by,
            } => self.timer_key(origin, *deadline, *token, by),
            TimerEntry::Schedule {
                deadline,
                id,
                token,
                by,
            } => self.sched_timer_key(id, *deadline, *token, by),
        }
    }

    pub fn parse_timer_key(&self, key: &str) -> Option<TimerEntry> {
        match self.decode(key)? {
            StringStoreKey::TimerOrigin {
                deadline,
                origin,
                token,
                by,
                ..
            } => Some(TimerEntry::Origin {
                deadline,
                origin,
                token,
                by,
            }),
            StringStoreKey::TimerSchedule {
                deadline,
                id,
                token,
                by,
                ..
            } => Some(TimerEntry::Schedule {
                deadline,
                id,
                token,
                by,
            }),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verified_keyspace_preserves_textual_layout() {
        let keys = KeySpace::new("pre", 1_000);
        assert_eq!(keys.doc_key("order"), "pre/wf/order");
        assert_eq!(keys.sched_key("计划/a"), "pre/sched/%E8%AE%A1%E5%88%92%2Fa");
        assert_eq!(keys.node_key("node_a"), "pre/nodes/node%5Fa");
        assert_eq!(keys.members_key(), "pre/members");
        assert_eq!(
            keys.timer_key("origin", 1_234, 0xab, "node"),
            "pre/t/00000000000000001000/00000000000000001234_origin@00000000000000ab~node"
        );
        assert_eq!(
            keys.parse_bucket_prefix("pre/t/00000000000000001000/"),
            Some(1_000)
        );
    }

    #[test]
    fn verified_key_parser_rejects_noncanonical_and_malformed_text() {
        let keys = KeySpace::new("pre", 1_000);
        for malformed in [
            "pre/wf/%6f", // lowercase and redundant escape
            "pre/wf/%",
            "pre/wf/%FF",
            "pre/t/00000000000000001001/00000000000000001234_o@0000000000000000~n",
            "pre/t/00000000000000001000/00000000000000001234_o@000000000000000A~n",
            "other/t/00000000000000001000/00000000000000001234_o@0000000000000000~n",
        ] {
            assert!(
                keys.decode(malformed).is_none(),
                "accepted malformed key: {malformed}"
            );
        }
        assert_eq!(decode_key("%6f"), None);
        assert_eq!(decode_key("%FF"), None);
    }
}
