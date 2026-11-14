//! Where everything lives under the bucket.
//!
//! ```text
//! <prefix>wf/<origin>                                    a workflow document: rows
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
//!
//! The text of a key is written and read by `text`, plain Rust; each of its
//! functions is stated once, as the characters it produces, and `KeySpace`
//! computes those statements. Which bucket an instant falls in is proved.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::verified::text::copy_string;

verus! {

pub const DEADLINE_WIDTH: usize = 20;

#[make_spec_type]
#[derive(Debug, Clone)]
#[verifier::allow(autoderive_clone_without_spec)]
pub struct KeySpace {
    pub prefix: String,
    /// The width of a timer bucket, ms. At least 1.
    pub bucket_ms: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[verifier::allow(autoderive_clone_without_spec)]
pub enum TimerEntry {
    Origin { deadline: u64, origin: String, token: u64, by: String },
    Schedule { deadline: u64, id: String, token: u64, by: String },
}

#[cfg(verus_keep_ghost)]
pub ghost enum TimerEntrySpec {
    Origin { deadline: u64, origin: Seq<char>, token: u64, by: Seq<char> },
    Schedule { deadline: u64, id: Seq<char>, token: u64, by: Seq<char> },
}

#[cfg(verus_keep_ghost)]
impl DeepView for TimerEntry {
    type V = TimerEntrySpec;
    open spec fn deep_view(&self) -> TimerEntrySpec {
        match self {
            TimerEntry::Origin { deadline, origin, token, by } => TimerEntrySpec::Origin { deadline: *deadline, origin: origin@, token: *token, by: by@ },
            TimerEntry::Schedule { deadline, id, token, by } => TimerEntrySpec::Schedule { deadline: *deadline, id: id@, token: *token, by: by@ },
        }
    }
}

#[cfg(verus_keep_ghost)]
impl TimerEntrySpec {
    pub open spec fn deadline(self) -> u64 {
        match self {
            TimerEntrySpec::Origin { deadline, .. } | TimerEntrySpec::Schedule { deadline, .. } => deadline,
        }
    }

    pub open spec fn target(self) -> Seq<char> {
        match self {
            TimerEntrySpec::Origin { origin, .. } => origin,
            TimerEntrySpec::Schedule { id, .. } => id,
        }
    }

    pub open spec fn token(self) -> u64 {
        match self {
            TimerEntrySpec::Origin { token, .. } | TimerEntrySpec::Schedule { token, .. } => token,
        }
    }

    pub open spec fn by(self) -> Seq<char> {
        match self {
            TimerEntrySpec::Origin { by, .. } | TimerEntrySpec::Schedule { by, .. } => by,
        }
    }
}

impl TimerEntry {
    pub fn deadline(&self) -> (r: u64)
        ensures
            r == self.deep_view().deadline(),
    {
        match self {
            TimerEntry::Origin { deadline, .. } | TimerEntry::Schedule { deadline, .. } => *deadline,
        }
    }

    /// What ownership is decided on.
    pub fn target(&self) -> (r: &String)
        ensures
            r@ == self.deep_view().target(),
    {
        match self {
            TimerEntry::Origin { origin, .. } => origin,
            TimerEntry::Schedule { id, .. } => id,
        }
    }

    pub fn token(&self) -> (r: u64)
        ensures
            r == self.deep_view().token(),
    {
        match self {
            TimerEntry::Origin { token, .. } | TimerEntry::Schedule { token, .. } => *token,
        }
    }

    pub fn by(&self) -> (r: &String)
        ensures
            r@ == self.deep_view().by(),
    {
        match self {
            TimerEntry::Origin { by, .. } | TimerEntry::Schedule { by, .. } => by,
        }
    }
}

// ---------------------------------------------------------------------------
// The text of a key, stated
// ---------------------------------------------------------------------------

pub uninterp spec fn spec_encode_key(s: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_decode_key(s: Seq<char>) -> Option<Seq<char>>;
pub uninterp spec fn spec_normalize_prefix(s: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_class_of(prefix: Seq<char>, key: Seq<char>) -> Option<Seq<char>>;
pub uninterp spec fn spec_doc_key(prefix: Seq<char>, origin: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_sched_key(prefix: Seq<char>, id: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_members_key(prefix: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_node_prefix(prefix: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_node_key(prefix: Seq<char>, id: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_node_of_key(prefix: Seq<char>, key: Seq<char>) -> Option<Seq<char>>;
pub uninterp spec fn spec_timer_prefix(prefix: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_bucket_prefix(prefix: Seq<char>, bucket: u64) -> Seq<char>;
pub uninterp spec fn spec_parse_bucket_prefix(prefix: Seq<char>, p: Seq<char>) -> Option<u64>;
pub uninterp spec fn spec_timer_key(prefix: Seq<char>, bucket_ms: u64, origin: Seq<char>, at: u64, token: u64, by: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_sched_timer_key(prefix: Seq<char>, bucket_ms: u64, id: Seq<char>, at: u64, token: u64, by: Seq<char>) -> Seq<char>;
pub uninterp spec fn spec_parse_timer_key(key: Seq<char>) -> Option<TimerEntrySpec>;
pub uninterp spec fn spec_last_segment(key: Seq<char>) -> Seq<char>;

pub assume_specification [text::encode_key](s: &str) -> (r: String)
    ensures
        r@ == spec_encode_key(s@);

pub assume_specification [text::decode_key](s: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_decode_key(s@);

pub assume_specification [text::normalize_prefix](s: &str) -> (r: String)
    ensures
        r@ == spec_normalize_prefix(s@);

pub assume_specification [text::class_of](prefix: &str, key: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_class_of(prefix@, key@);

pub assume_specification [text::doc_key](prefix: &str, origin: &str) -> (r: String)
    ensures
        r@ == spec_doc_key(prefix@, origin@);

pub assume_specification [text::sched_key](prefix: &str, id: &str) -> (r: String)
    ensures
        r@ == spec_sched_key(prefix@, id@);

pub assume_specification [text::members_key](prefix: &str) -> (r: String)
    ensures
        r@ == spec_members_key(prefix@);

pub assume_specification [text::node_prefix](prefix: &str) -> (r: String)
    ensures
        r@ == spec_node_prefix(prefix@);

pub assume_specification [text::node_key](prefix: &str, id: &str) -> (r: String)
    ensures
        r@ == spec_node_key(prefix@, id@);

pub assume_specification [text::node_of_key](prefix: &str, key: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_node_of_key(prefix@, key@);

pub assume_specification [text::timer_prefix](prefix: &str) -> (r: String)
    ensures
        r@ == spec_timer_prefix(prefix@);

pub assume_specification [text::bucket_prefix](prefix: &str, bucket: u64) -> (r: String)
    ensures
        r@ == spec_bucket_prefix(prefix@, bucket);

pub assume_specification [text::parse_bucket_prefix](prefix: &str, p: &str) -> (r: Option<u64>)
    ensures
        r == spec_parse_bucket_prefix(prefix@, p@);

pub assume_specification [text::timer_key](prefix: &str, bucket_ms: u64, origin: &str, at: u64, token: u64, by: &str) -> (r: String)
    ensures
        r@ == spec_timer_key(prefix@, bucket_ms, origin@, at, token, by@);

pub assume_specification [text::sched_timer_key](prefix: &str, bucket_ms: u64, id: &str, at: u64, token: u64, by: &str) -> (r: String)
    ensures
        r@ == spec_sched_timer_key(prefix@, bucket_ms, id@, at, token, by@);

pub assume_specification [text::parse_timer_key](key: &str) -> (r: Option<TimerEntry>)
    ensures
        r.deep_view() == spec_parse_timer_key(key@);

pub assume_specification [text::last_segment](key: &str) -> (r: String)
    ensures
        r@ == spec_last_segment(key@);

/// Percent-encode anything that is not safe and stable in a key.
pub fn encode_key(s: &str) -> (r: String)
    ensures
        r@ == spec_encode_key(s@),
{
    text::encode_key(s)
}

pub fn decode_key(s: &str) -> (r: Option<String>)
    ensures
        r.deep_view() == spec_decode_key(s@),
{
    text::decode_key(s)
}

/// The last `/`-separated segment of a key: its own name.
pub fn last_segment(key: &str) -> (r: String)
    ensures
        r@ == spec_last_segment(key@),
{
    text::last_segment(key)
}

/// FNV-1a: the hash `verified::node` proves against `hash`.
pub fn fnv1a(s: &str) -> (r: u64)
    ensures
        r as nat == crate::verified::node_spec::hash(s@),
{
    crate::verified::node::fnv1a(s)
}

/// The start of the bucket `at` falls in.
pub open spec fn spec_bucket_of(at: u64, bucket_ms: u64) -> u64 {
    let width = if bucket_ms < 1 { 1u64 } else { bucket_ms };
    ((at / width) * width) as u64
}

/// The start of the bucket `at` falls in. `bucket_ms` is at least 1, as
/// `KeySpace::new` stores it.
pub fn bucket_of(at: u64, bucket_ms: u64) -> (r: u64)
    ensures
        r == spec_bucket_of(at, bucket_ms),
{
    let width = if bucket_ms < 1 { 1 } else { bucket_ms };
    proof {
        let q = (at / width) as int;
        let w = width as int;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(at as int, w);
        vstd::arithmetic::div_mod::lemma_mod_bound(at as int, w);
        assert(q * w == w * q) by (nonlinear_arith);
        assert(q * w <= at);
    }
    at / width * width
}

/// The version a body quotes, as an S3 ETag: the same bytes are the same version.
pub fn content_etag(body: &[u8]) -> (r: crate::types::Etag)
    ensures
        r == echod_concrete_spec::state::spec_etag(body@),
{
    crate::concrete::content_etag(body)
}

/// The origin of an id: everything before the first `:`.
pub fn origin_of<'a>(id: &'a str) -> (r: &'a str)
    ensures
        r@ == echod_types::origin(id@),
{
    echod_types::origin_of(id)
}

impl KeySpace {
    pub fn new(prefix: &str, bucket_ms: u64) -> (r: KeySpace)
        ensures
            r.deep_view() == (KeySpaceSpec {
                prefix: spec_normalize_prefix(prefix@),
                bucket_ms: if bucket_ms < 1 { 1u64 } else { bucket_ms },
            }),
    {
        KeySpace { prefix: text::normalize_prefix(prefix), bucket_ms: if bucket_ms < 1 { 1 } else { bucket_ms } }
    }

    pub fn copy(&self) -> (r: KeySpace)
        ensures
            r == *self,
    {
        KeySpace { prefix: copy_string(&self.prefix), bucket_ms: self.bucket_ms }
    }

    pub fn bucket_ms(&self) -> (r: u64)
        ensures
            r == self.bucket_ms,
    {
        self.bucket_ms
    }

    /// The class of object a key names: its first path segment under the
    /// prefix (`wf`, `sched`, `t`, `nodes`, `members`); `None` for a key
    /// outside the prefix.
    pub fn class_of(&self, key: &str) -> (r: Option<String>)
        ensures
            r.deep_view() == spec_class_of(self.prefix@, key@),
    {
        text::class_of(self.prefix.as_str(), key)
    }

    pub fn doc_key(&self, origin: &str) -> (r: String)
        ensures
            r@ == spec_doc_key(self.prefix@, origin@),
    {
        text::doc_key(self.prefix.as_str(), origin)
    }

    pub fn sched_key(&self, id: &str) -> (r: String)
        ensures
            r@ == spec_sched_key(self.prefix@, id@),
    {
        text::sched_key(self.prefix.as_str(), id)
    }

    /// The configuration object: the members and their epoch.
    pub fn members_key(&self) -> (r: String)
        ensures
            r@ == spec_members_key(self.prefix@),
    {
        text::members_key(self.prefix.as_str())
    }

    pub fn node_prefix(&self) -> (r: String)
        ensures
            r@ == spec_node_prefix(self.prefix@),
    {
        text::node_prefix(self.prefix.as_str())
    }

    pub fn node_key(&self, id: &str) -> (r: String)
        ensures
            r@ == spec_node_key(self.prefix@, id@),
    {
        text::node_key(self.prefix.as_str(), id)
    }

    pub fn node_of_key(&self, key: &str) -> (r: Option<String>)
        ensures
            r.deep_view() == spec_node_of_key(self.prefix@, key@),
    {
        text::node_of_key(self.prefix.as_str(), key)
    }

    /// The start of the bucket an instant falls in.
    pub fn bucket_of(&self, at: u64) -> (r: u64)
        ensures
            r == spec_bucket_of(at, self.bucket_ms),
    {
        bucket_of(at, self.bucket_ms)
    }

    /// Every timer key lives under this.
    pub fn timer_prefix(&self) -> (r: String)
        ensures
            r@ == spec_timer_prefix(self.prefix@),
    {
        text::timer_prefix(self.prefix.as_str())
    }

    /// The keys of one bucket live under this. `bucket` is a bucket start.
    pub fn bucket_prefix(&self, bucket: u64) -> (r: String)
        ensures
            r@ == spec_bucket_prefix(self.prefix@, bucket),
    {
        text::bucket_prefix(self.prefix.as_str(), bucket)
    }

    /// The bucket start a bucket prefix names, as a listing returns it.
    pub fn parse_bucket_prefix(&self, prefix: &str) -> (r: Option<u64>)
        ensures
            r == spec_parse_bucket_prefix(self.prefix@, prefix@),
    {
        text::parse_bucket_prefix(self.prefix.as_str(), prefix)
    }

    pub fn timer_key(&self, origin: &str, at: u64, token: u64, by: &str) -> (r: String)
        ensures
            r@ == spec_timer_key(self.prefix@, self.bucket_ms, origin@, at, token, by@),
    {
        text::timer_key(self.prefix.as_str(), self.bucket_ms, origin, at, token, by)
    }

    pub fn sched_timer_key(&self, id: &str, at: u64, token: u64, by: &str) -> (r: String)
        ensures
            r@ == spec_sched_timer_key(self.prefix@, self.bucket_ms, id@, at, token, by@),
    {
        text::sched_timer_key(self.prefix.as_str(), self.bucket_ms, id, at, token, by)
    }

    pub fn parse_timer_key(&self, key: &str) -> (r: Option<TimerEntry>)
        ensures
            r.deep_view() == spec_parse_timer_key(key@),
    {
        text::parse_timer_key(key)
    }
}

} // verus!

/// The text of each key, and what a key's text says. Plain Rust: stated
/// above, as the characters each function writes or reads.
pub mod text {
    use super::{TimerEntry, DEADLINE_WIDTH};

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

    /// The prefix with its trailing `/`, when it has any text.
    pub fn normalize_prefix(prefix: &str) -> String {
        let mut prefix = prefix.to_string();
        if !prefix.is_empty() && !prefix.ends_with('/') {
            prefix.push('/');
        }
        prefix
    }

    pub fn class_of(prefix: &str, key: &str) -> Option<String> {
        let rest = key.strip_prefix(prefix)?;
        Some(rest.split('/').next().unwrap_or(rest).to_string())
    }

    pub fn last_segment(key: &str) -> String {
        key.rsplit('/').next().unwrap_or(key).to_string()
    }

    pub fn doc_key(prefix: &str, origin: &str) -> String {
        format!("{}wf/{}", prefix, encode_key(origin))
    }

    pub fn sched_key(prefix: &str, id: &str) -> String {
        format!("{}sched/{}", prefix, encode_key(id))
    }

    pub fn members_key(prefix: &str) -> String {
        format!("{}members", prefix)
    }

    pub fn node_prefix(prefix: &str) -> String {
        format!("{}nodes/", prefix)
    }

    pub fn node_key(prefix: &str, id: &str) -> String {
        format!("{}nodes/{}", prefix, encode_key(id))
    }

    pub fn node_of_key(prefix: &str, key: &str) -> Option<String> {
        decode_key(key.strip_prefix(&node_prefix(prefix))?)
    }

    pub fn timer_prefix(prefix: &str) -> String {
        format!("{}t/", prefix)
    }

    pub fn bucket_prefix(prefix: &str, bucket: u64) -> String {
        format!("{}t/{:0width$}/", prefix, bucket, width = DEADLINE_WIDTH)
    }

    pub fn parse_bucket_prefix(prefix: &str, p: &str) -> Option<u64> {
        let name = p.strip_prefix(&timer_prefix(prefix))?.trim_end_matches('/');
        if name.len() != DEADLINE_WIDTH {
            return None;
        }
        name.parse().ok()
    }

    fn bucket_of(at: u64, bucket_ms: u64) -> u64 {
        let width = bucket_ms.max(1);
        at / width * width
    }

    /// A key names what is due, when, a token drawn per arm, and the node
    /// that armed it: only that node deletes it outright.
    fn timer_key_for(prefix: &str, bucket_ms: u64, encoded: &str, at: u64, token: u64, by: &str) -> String {
        format!("{}{:0width$}_{}@{:016x}~{}", bucket_prefix(prefix, bucket_of(at, bucket_ms)), at, encoded, token, encode_key(by), width = DEADLINE_WIDTH)
    }

    pub fn timer_key(prefix: &str, bucket_ms: u64, origin: &str, at: u64, token: u64, by: &str) -> String {
        timer_key_for(prefix, bucket_ms, &encode_key(origin), at, token, by)
    }

    pub fn sched_timer_key(prefix: &str, bucket_ms: u64, id: &str, at: u64, token: u64, by: &str) -> String {
        timer_key_for(prefix, bucket_ms, &format!("sched:{}", encode_key(id)), at, token, by)
    }

    pub fn parse_timer_key(key: &str) -> Option<TimerEntry> {
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
