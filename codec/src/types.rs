//! Typed persistence models. Text fields are validated UTF-8 byte strings.

use vstd::contrib::make_spec_type;
use vstd::prelude::*;

use crate::text::Text;

verus! {

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Header {
    pub stamp: u64,
    pub nonce: u64,
}

#[cfg(verus_keep_ghost)]
pub type AHeader = HeaderSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Announcement {
    pub id: Text,
    pub url: Text,
    pub at: u64,
}

#[cfg(verus_keep_ghost)]
pub type AAnnouncement = AnnouncementSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Membership {
    pub epoch: u64,
    pub members: Vec<Text>,
}

#[cfg(verus_keep_ghost)]
pub type AMembership = MembershipSpec;

#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub enum StoreKey {
    Document(Text),
    Schedule(Text),
    TimerOrigin {
        bucket: u64,
        deadline: u64,
        origin: Text,
        token: u64,
        by: Text,
    },
    TimerSchedule {
        bucket: u64,
        deadline: u64,
        id: Text,
        token: u64,
        by: Text,
    },
    Node(Text),
    Membership,
}

#[cfg(verus_keep_ghost)]
pub enum AStoreKey {
    Document(Seq<u8>),
    Schedule(Seq<u8>),
    TimerOrigin {
        bucket: u64,
        deadline: u64,
        origin: Seq<u8>,
        token: u64,
        by: Seq<u8>,
    },
    TimerSchedule {
        bucket: u64,
        deadline: u64,
        id: Seq<u8>,
        token: u64,
        by: Seq<u8>,
    },
    Node(Seq<u8>),
    Membership,
}

#[cfg(verus_keep_ghost)]
impl DeepView for StoreKey {
    type V = AStoreKey;

    open spec fn deep_view(&self) -> AStoreKey {
        match self {
            StoreKey::Document(value) => AStoreKey::Document(value@),
            StoreKey::Schedule(value) => AStoreKey::Schedule(value@),
            StoreKey::TimerOrigin { bucket, deadline, origin, token, by } => {
                AStoreKey::TimerOrigin {
                    bucket: *bucket,
                    deadline: *deadline,
                    origin: origin@,
                    token: *token,
                    by: by@,
                }
            }
            StoreKey::TimerSchedule { bucket, deadline, id, token, by } => {
                AStoreKey::TimerSchedule {
                    bucket: *bucket,
                    deadline: *deadline,
                    id: id@,
                    token: *token,
                    by: by@,
                }
            }
            StoreKey::Node(value) => AStoreKey::Node(value@),
            StoreKey::Membership => AStoreKey::Membership,
        }
    }
}

#[cfg(verus_keep_ghost)]
impl View for StoreKey {
    type V = AStoreKey;

    open spec fn view(&self) -> AStoreKey {
        self.deep_view()
    }
}

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Value {
    pub headers: Vec<(Text, Text)>,
    pub data: Option<Text>,
}

#[cfg(verus_keep_ghost)]
pub type AValue = ValueSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Task {
    pub state: echod_kernel::TaskState,
    pub version: u64,
    pub ttl: Option<u64>,
    pub pid: Option<Text>,
    pub lease_timeout_at: Option<u64>,
    pub retry_timeout_at: Option<u64>,
    pub resumes: Vec<Text>,
}

#[cfg(verus_keep_ghost)]
pub type ATask = TaskSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Promise {
    pub id: Text,
    pub state: echod_kernel::PromiseState,
    pub tags: Vec<(Text, Text)>,
    pub param: Value,
    pub value: Value,
    pub timeout_at: u64,
    pub created_at: u64,
    pub settled_at: Option<u64>,
    pub callbacks: Vec<Text>,
    pub listeners: Vec<Text>,
    pub task: Option<Task>,
}

#[cfg(verus_keep_ghost)]
pub type APromise = PromiseSpec;

#[make_spec_type]
#[cfg_attr(not(verus_keep_ghost), derive(Clone, Debug, PartialEq, Eq))]
pub struct Schedule {
    pub id: Text,
    pub cron: Text,
    pub promise_id: Text,
    pub promise_timeout: u64,
    pub promise_param: Value,
    pub promise_tags: Vec<(Text, Text)>,
    pub next_run_at: u64,
    pub last_run_at: Option<u64>,
    pub created_at: u64,
}

#[cfg(verus_keep_ghost)]
pub type ASchedule = ScheduleSpec;

} // verus!
