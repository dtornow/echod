//! TigerBeetle's state machine, its data model: what the cluster stores, what a
//! client sends, what it gets back, and the work the cluster does on its own.
//! Ported from tigerbeetle/tigerbeetle (`src/tigerbeetle.zig` for the types,
//! `src/state_machine.zig` for what is stored and how it changes).
//!
//! Lean, so differences from TigerBeetle, all deliberate:
//! - A request is one batch of one operation. TigerBeetle packs several batches
//!   of the same operation into one message (multi-batch); they run one after
//!   the other, as separate requests would.
//! - Only accounts and transfers: `create_*` and `lookup_*`. Not modeled yet:
//!   `get_account_transfers`, `get_account_balances` (and with it the `history`
//!   flag and the account-events groove), `query_*`, `get_change_events`.
//! - No `user_data_*`, `reserved`, padding, or `imported` (events with a
//!   client-chosen past timestamp). Their status codes go with them.
//! - What a client creates is its own type (`NewAccount`, `NewTransfer`), not
//!   the stored record with must-be-zero fields, so the `*_must_be_zero` codes
//!   for balances and `timestamp` cannot occur.
//! - A pending transfer's status is keyed by the transfer's id, not by its
//!   timestamp as in TigerBeetle's `transfers_pending` groove.
//! - Time is `Server::now`, moved only by `AdvanceClock`. TigerBeetle's clock is
//!   the cluster's wall clock; there is no debug clock to drive.
//!
//! Plain Rust for now; it moves into `verus!` with the steps, as `resonate`.

use accordant::{HashedMap, HashedSet};

pub type Id = u128;

/// Nanoseconds on the cluster's clock. Every event that changes the state gets
/// a timestamp of its own, unique and increasing across the whole cluster.
pub type Time = u64;

pub type Amount = u128;

pub const ID_MAX: Id = u128::MAX;

pub const NS_PER_S: Time = 1_000_000_000;

// ------------------------------------------------------------------ accounts

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct AccountFlags {
    /// Links this event to the next one in the batch: the chain succeeds or
    /// fails as a unit. Stored with the account like any other flag.
    pub linked: bool,
    pub debits_must_not_exceed_credits: bool,
    pub credits_must_not_exceed_debits: bool,
    /// No transfer may move money in or out. Set at creation or by a pending
    /// closing transfer; cleared when that transfer is voided or expires.
    pub closed: bool,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Account {
    pub ledger: u32,
    pub code: u16,
    pub flags: AccountFlags,
    pub debits_pending: Amount,
    pub debits_posted: Amount,
    pub credits_pending: Amount,
    pub credits_posted: Amount,
    /// When it was created.
    pub timestamp: Time,
}

// ----------------------------------------------------------------- transfers

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub struct TransferFlags {
    pub linked: bool,
    /// The first phase of a two-phase transfer: reserves `amount` as pending.
    pub pending: bool,
    /// The second phase: posts (part of) the pending transfer `pending_id`.
    pub post_pending_transfer: bool,
    /// The second phase: voids the pending transfer `pending_id`.
    pub void_pending_transfer: bool,
    /// Move at most the debit account's available balance.
    pub balancing_debit: bool,
    /// Move at most the credit account's available balance.
    pub balancing_credit: bool,
    /// Pending only: closes the debit account until voided or expired.
    pub closing_debit: bool,
    /// Pending only: closes the credit account until voided or expired.
    pub closing_credit: bool,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Transfer {
    pub debit_account_id: Id,
    pub credit_account_id: Id,
    /// What moved: for a balancing transfer, at most what was asked; for a post,
    /// at most the pending amount.
    pub amount: Amount,
    /// For a post or a void, the pending transfer it completes. Otherwise 0.
    pub pending_id: Id,
    /// Seconds after `timestamp` a pending transfer expires. 0: never.
    pub timeout: u32,
    pub ledger: u32,
    pub code: u16,
    pub flags: TransferFlags,
    /// When it was created.
    pub timestamp: Time,
}

impl Transfer {
    /// When a pending transfer with a timeout expires.
    pub fn expires_at(&self) -> Option<Time> {
        if self.timeout == 0 {
            None
        } else {
            Some(self.timestamp.saturating_add(self.timeout as Time * NS_PER_S))
        }
    }
}

/// Where a pending transfer is. Kept only for pending transfers; the transfer
/// itself never changes once stored.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum PendingStatus {
    Pending,
    Posted,
    Voided,
    Expired,
}

// -------------------------------------------------------------------- server

#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Server {
    /// The cluster's clock.
    pub now: Time,
    /// The last timestamp given to an event (`commit_timestamp`). The next
    /// batch's events get `max(commit, now) + 1, + 2, ...`, so timestamps never
    /// repeat, even when the clock stands still.
    pub commit: Time,
    pub accounts: HashedMap<Id, Account>,
    pub transfers: HashedMap<Id, Transfer>,
    /// The status of every pending transfer, by its id.
    pub pending: HashedMap<Id, PendingStatus>,
    /// Ids of transfers that failed for a reason that might not hold on a retry
    /// (an account not found yet, insufficient funds, ...). Such an id is spent:
    /// it can never be created (TigerBeetle's orphaned primary keys).
    pub failed: HashedSet<Id>,
}

// ------------------------------------------------------------------ requests

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct NewAccount {
    pub id: Id,
    pub ledger: u32,
    pub code: u16,
    pub flags: AccountFlags,
}

/// For a post or a void, zero in `debit_account_id`, `credit_account_id`,
/// `ledger` and `code` means "as the pending transfer"; so does an `amount` of
/// 0 for a void and of `u128::MAX` for a post.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct NewTransfer {
    pub id: Id,
    pub debit_account_id: Id,
    pub credit_account_id: Id,
    pub amount: Amount,
    pub pending_id: Id,
    pub timeout: u32,
    pub ledger: u32,
    pub code: u16,
    pub flags: TransferFlags,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Request {
    /// The driver moves the cluster's clock. Expiries now due may run any time
    /// after, not necessarily before the next request.
    AdvanceClock(Time),
    /// One result per account, in order. Linked chains are all-or-nothing.
    CreateAccounts(Vec<NewAccount>),
    /// One result per transfer, in order. Linked chains are all-or-nothing.
    CreateTransfers(Vec<NewTransfer>),
    LookupAccounts(Vec<Id>),
    LookupTransfers(Vec<Id>),
}

// ----------------------------------------------------------------- responses

/// Why an account was or was not created. Ordered as TigerBeetle checks them:
/// the first that applies is the result.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum CreateAccountStatus {
    Created,
    LinkedEventFailed,
    LinkedEventChainOpen,
    IdMustNotBeZero,
    IdMustNotBeIntMax,
    ExistsWithDifferentFlags,
    ExistsWithDifferentLedger,
    ExistsWithDifferentCode,
    /// The same account exists: the timestamp is the existing one's.
    Exists,
    FlagsAreMutuallyExclusive,
    LedgerMustNotBeZero,
    CodeMustNotBeZero,
}

/// Why a transfer was or was not created. Ordered as TigerBeetle checks them:
/// the first that applies is the result.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum CreateTransferStatus {
    Created,
    LinkedEventFailed,
    LinkedEventChainOpen,
    IdMustNotBeZero,
    IdMustNotBeIntMax,
    ExistsWithDifferentFlags,
    ExistsWithDifferentPendingId,
    ExistsWithDifferentTimeout,
    ExistsWithDifferentDebitAccountId,
    ExistsWithDifferentCreditAccountId,
    ExistsWithDifferentAmount,
    ExistsWithDifferentLedger,
    ExistsWithDifferentCode,
    /// The same transfer exists: the timestamp is the existing one's.
    Exists,
    IdAlreadyFailed,
    FlagsAreMutuallyExclusive,
    DebitAccountIdMustNotBeZero,
    DebitAccountIdMustNotBeIntMax,
    CreditAccountIdMustNotBeZero,
    CreditAccountIdMustNotBeIntMax,
    AccountsMustBeDifferent,
    PendingIdMustBeZero,
    PendingIdMustNotBeZero,
    PendingIdMustNotBeIntMax,
    PendingIdMustBeDifferent,
    TimeoutReservedForPendingTransfer,
    ClosingTransferMustBePending,
    LedgerMustNotBeZero,
    CodeMustNotBeZero,
    DebitAccountNotFound,
    CreditAccountNotFound,
    AccountsMustHaveTheSameLedger,
    TransferMustHaveTheSameLedgerAsAccounts,
    PendingTransferNotFound,
    PendingTransferNotPending,
    PendingTransferHasDifferentDebitAccountId,
    PendingTransferHasDifferentCreditAccountId,
    PendingTransferHasDifferentLedger,
    PendingTransferHasDifferentCode,
    ExceedsPendingTransferAmount,
    PendingTransferHasDifferentAmount,
    PendingTransferAlreadyPosted,
    PendingTransferAlreadyVoided,
    PendingTransferExpired,
    DebitAccountAlreadyClosed,
    CreditAccountAlreadyClosed,
    OverflowsDebitsPending,
    OverflowsCreditsPending,
    OverflowsDebitsPosted,
    OverflowsCreditsPosted,
    OverflowsDebits,
    OverflowsCredits,
    OverflowsTimeout,
    ExceedsCredits,
    ExceedsDebits,
}

impl CreateTransferStatus {
    /// Whether a retry with the same transfer could succeed: the failure depends
    /// on the state, not on the transfer. Such a failure spends the id.
    pub fn transient(self) -> bool {
        use CreateTransferStatus::*;
        matches!(
            self,
            DebitAccountNotFound
                | CreditAccountNotFound
                | PendingTransferNotFound
                | ExceedsCredits
                | ExceedsDebits
                | DebitAccountAlreadyClosed
                | CreditAccountAlreadyClosed
        )
    }
}

/// Every result carries a timestamp: the new or existing object's, or, on any
/// other failure, the one the event was given.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Result<S> {
    pub timestamp: Time,
    pub status: S,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Response {
    /// `AdvanceClock`.
    Ok,
    AccountsCreated(Vec<Result<CreateAccountStatus>>),
    TransfersCreated(Vec<Result<CreateTransferStatus>>),
    /// The accounts found, in the order asked; ids not found are left out.
    Accounts(Vec<(Id, Account)>),
    /// The transfers found, in the order asked; ids not found are left out.
    Transfers(Vec<(Id, Transfer)>),
}

// ------------------------------------------------------------ internal work

/// What the cluster does on its own: expire a pending transfer whose timeout
/// has passed (TigerBeetle's `pulse`). Started when the transfer is created, to
/// run after its `expires_at`; at its run, it does nothing unless the transfer
/// is still pending. Expiring gives back the pending amounts, reopens accounts
/// a closing transfer closed, and takes a timestamp like any other event.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Internal {
    Expire(Id),
}

/// TigerBeetle sends nothing on its own: a client sees only responses.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum Dispatch {}
