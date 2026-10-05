import Accordant

/-!
# TigerBeetle's state machine, as an accordant model

Accounts, transfers, two-phase transfers and their expiry, and the queries over
them, read from tigerbeetle/tigerbeetle (`src/tigerbeetle.zig` for the types,
`src/state_machine.zig` for what is stored and how each operation changes it).
Names are TigerBeetle's, so the two read side by side.

The parts of an accordant `Model` (see `Accordant.lean`):

* `State`    = `Server`: the clock, accounts, transfers, pending statuses, spent
  ids, and the account events (one per transfer or expiry).
* `External` = `Request`: create, look up and query accounts and transfers; read
  change events; move the clock.
* `Response` = `Response`: one result per created item; the items found.
* `Internal` = `Internal`: the `pulse` that expires pending transfers.
* `Dispatch` = `Empty`: TigerBeetle sends nothing on its own.

`model lim` puts them together. The `#guard`s at the bottom run it.

Differences from TigerBeetle, all deliberate:
- A request is one batch of one operation. TigerBeetle packs several batches of
  one operation into a message; they run one after the other, as separate
  requests would. The deprecated operation encodings are not modeled.
- No `imported` events (created with a past timestamp the client chooses), no
  `reserved` fields or padding; their status codes go with them.
- What a client creates is its own type (`NewAccount`, `NewTransfer`), so the
  `*_must_be_zero` codes for balances and `timestamp` cannot occur.
- Amounts, ids and times are `Nat`, bounded by `u128_max` and `timestamp_max`
  where TigerBeetle checks them.
- Objects are kept in lists in timestamp order (TigerBeetle's object trees), a
  pending transfer's status is keyed by its id rather than its timestamp, and an
  account event holds the accounts after the event rather than their balances,
  so a change event is read off it without looking the accounts up again.
- Time is `Server.now`, moved by `advance_clock`; TigerBeetle uses the cluster's
  wall clock. A pulse that finds nothing to expire changes nothing here; in
  TigerBeetle it still moves `prepare_timestamp` on, as if the clock had been later.

Checked with Lean 4.31.0, core only: `cd lean && lake build`.
-/

namespace TigerBeetle

open Accordant (ExternalOutcome InternalOutcome Sched)

abbrev Id := Nat
/-- Nanoseconds on the cluster's clock. Every event that changes the state gets a
    timestamp of its own, unique and increasing across the cluster. -/
abbrev Time := Nat
abbrev Amount := Nat

def u128_max : Nat := 2 ^ 128 - 1
/-- The largest timestamp: the top bit of a `u64` is the LSM's tombstone. -/
def timestamp_max : Nat := 2 ^ 63 - 1
def ns_per_s : Nat := 1_000_000_000

/-- TigerBeetle's size limits, set by its message size. With the default 1 MiB
    message, `batch_max` is 8189. -/
structure Limits where
  /-- Most events in a batch (`batch_max.create_transfers`). A pulse expires at
      most this many, and moves `prepare_timestamp` on by as many. -/
  batch_max         : Nat
  /-- Most results a query returns, whatever its `limit`. -/
  result_max        : Nat
  /-- Most results `get_change_events` returns, whatever its `limit`. -/
  change_events_max : Nat

/-! ## Accounts -/

structure AccountFlags where
  /-- Links this event to the next in the batch: the chain succeeds or fails as a unit. -/
  linked                         : Bool := false
  debits_must_not_exceed_credits : Bool := false
  credits_must_not_exceed_debits : Bool := false
  /-- Keep the account's balance after every transfer, for `get_account_balances`. -/
  history                        : Bool := false
  /-- No transfer may move money in or out. Set at creation or by a pending closing
      transfer; cleared when that transfer is voided or expires. -/
  closed                         : Bool := false
  deriving DecidableEq, Repr

structure Account where
  user_data_128   : Nat
  user_data_64    : Nat
  user_data_32    : Nat
  ledger          : Nat
  code            : Nat
  flags           : AccountFlags
  debits_pending  : Amount
  debits_posted   : Amount
  credits_pending : Amount
  credits_posted  : Amount
  /-- When it was created. -/
  timestamp       : Time
  deriving DecidableEq, Repr

/-- An account's balances at one point: a row of `get_account_balances`. -/
structure AccountBalance where
  debits_pending  : Amount
  debits_posted   : Amount
  credits_pending : Amount
  credits_posted  : Amount
  /-- The transfer that left the account with these balances. -/
  timestamp       : Time
  deriving DecidableEq, Repr

/-! ## Transfers -/

structure TransferFlags where
  linked                : Bool := false
  /-- First phase of a two-phase transfer: reserves `amount` as pending. -/
  pending               : Bool := false
  /-- Second phase: posts (part of) the pending transfer `pending_id`. -/
  post_pending_transfer : Bool := false
  /-- Second phase: voids the pending transfer `pending_id`. -/
  void_pending_transfer : Bool := false
  /-- Move at most what the debit account has available. -/
  balancing_debit       : Bool := false
  /-- Move at most what the credit account has available. -/
  balancing_credit      : Bool := false
  /-- Pending only: closes the debit account until voided or expired. -/
  closing_debit         : Bool := false
  /-- Pending only: closes the credit account until voided or expired. -/
  closing_credit        : Bool := false
  deriving DecidableEq, Repr

structure Transfer where
  debit_account_id  : Id
  credit_account_id : Id
  /-- What moved: for a balancing transfer at most what was asked, for a post at
      most the pending amount. -/
  amount            : Amount
  /-- For a post or a void, the pending transfer it completes; otherwise 0. -/
  pending_id        : Id
  user_data_128     : Nat
  user_data_64      : Nat
  user_data_32      : Nat
  /-- Seconds after `timestamp` a pending transfer expires; 0: never. -/
  timeout           : Nat
  ledger            : Nat
  code              : Nat
  flags             : TransferFlags
  /-- When it was created. -/
  timestamp         : Time
  deriving DecidableEq, Repr

/-- When a pending transfer with a timeout expires. -/
def Transfer.expires_at (t : Transfer) : Option Time :=
  if t.timeout = 0 then none else some (t.timestamp + t.timeout * ns_per_s)

/-- Where a pending transfer is. `none` marks an event that is not about a
    pending transfer: a single-phase transfer. -/
inductive TransferPendingStatus where
  | none | pending | posted | voided | expired
  deriving DecidableEq, Repr

/-- What happened at one timestamp to two accounts: a transfer was created, or a
    pending transfer expired. Kept for every transfer, whatever the accounts'
    `history` flags: `get_change_events` reads them all. -/
structure AccountEvent where
  timestamp               : Time
  /-- The transfer created at `timestamp`; for an expiry, the pending transfer. -/
  transfer_id             : Id
  /-- `none` or `pending` for a transfer created, `posted` or `voided` for the
      second phase, `expired` for an expiry. -/
  transfer_pending_status : TransferPendingStatus
  dr_account_id           : Id
  /-- The debit account just after the event. -/
  dr_account              : Account
  cr_account_id           : Id
  /-- The credit account just after the event. -/
  cr_account              : Account
  deriving DecidableEq, Repr

/-! ## The server -/

structure Server where
  /-- The cluster's clock. -/
  now               : Time := 0
  /-- The last timestamp handed out. A batch of `n` events gets the timestamps
      `max prepare_timestamp now + 1, ..., + n`, so timestamps never repeat, even
      while the clock stands still. -/
  prepare_timestamp : Time := 0
  /-- In timestamp order, as created. -/
  accounts          : List (Id × Account) := []
  /-- In timestamp order, as created. A stored transfer never changes. -/
  transfers         : List (Id × Transfer) := []
  /-- The status of every pending transfer, by its id. -/
  transfers_pending : List (Id × TransferPendingStatus) := []
  /-- Ids of transfers that failed for a reason that may not hold on a retry. Such
      an id is spent: it can never be created (TigerBeetle's orphaned keys). -/
  orphaned          : List Id := []
  /-- In timestamp order. -/
  account_events    : List AccountEvent := []
  deriving Repr

def get {α : Type} (l : List (Id × α)) (id : Id) : Option α :=
  (l.find? (·.1 == id)).map (·.2)

/-- Replaces what `id` maps to, if anything. -/
def put {α : Type} (l : List (Id × α)) (id : Id) (a : α) : List (Id × α) :=
  l.map fun p => if p.1 == id then (id, a) else p

/-! ## Requests -/

structure NewAccount where
  id            : Id
  user_data_128 : Nat := 0
  user_data_64  : Nat := 0
  user_data_32  : Nat := 0
  ledger        : Nat
  code          : Nat
  flags         : AccountFlags := {}
  deriving DecidableEq, Repr

/-- For a post or a void, 0 in `debit_account_id`, `credit_account_id`, `ledger`,
    `code` and `user_data_*` means "as the pending transfer"; so does an `amount`
    of 0 for a void and of `u128_max` for a post. -/
structure NewTransfer where
  id                : Id
  debit_account_id  : Id := 0
  credit_account_id : Id := 0
  amount            : Amount := 0
  pending_id        : Id := 0
  user_data_128     : Nat := 0
  user_data_64      : Nat := 0
  user_data_32      : Nat := 0
  timeout           : Nat := 0
  ledger            : Nat := 0
  code              : Nat := 0
  flags             : TransferFlags := {}
  deriving DecidableEq, Repr

structure AccountFilterFlags where
  /-- Include transfers that debit the account. -/
  debits   : Bool := true
  /-- Include transfers that credit the account. -/
  credits  : Bool := true
  /-- Newest first. -/
  reversed : Bool := false
  deriving DecidableEq, Repr

/-- The transfers of one account, for `get_account_transfers` and
    `get_account_balances`. A 0 filters nothing. -/
structure AccountFilter where
  account_id    : Id
  user_data_128 : Nat := 0
  user_data_64  : Nat := 0
  user_data_32  : Nat := 0
  code          : Nat := 0
  /-- Inclusive. -/
  timestamp_min : Time := 0
  /-- Inclusive. -/
  timestamp_max : Time := 0
  limit         : Nat
  flags         : AccountFilterFlags := {}
  deriving DecidableEq, Repr

/-- Accounts or transfers by their fields, for `query_accounts` and
    `query_transfers`. A 0 filters nothing. -/
structure QueryFilter where
  user_data_128 : Nat := 0
  user_data_64  : Nat := 0
  user_data_32  : Nat := 0
  ledger        : Nat := 0
  code          : Nat := 0
  timestamp_min : Time := 0
  timestamp_max : Time := 0
  limit         : Nat
  /-- Newest first. -/
  reversed      : Bool := false
  deriving DecidableEq, Repr

/-- Account events, oldest first, for `get_change_events`. A 0 filters nothing. -/
structure ChangeEventsFilter where
  timestamp_min : Time := 0
  timestamp_max : Time := 0
  limit         : Nat
  deriving DecidableEq, Repr

inductive Request where
  /-- The driver moves the cluster's clock. -/
  | advance_clock (to : Time)
  /-- One result per account, in order. Linked chains are all-or-nothing. -/
  | create_accounts (events : List NewAccount)
  /-- One result per transfer, in order. Linked chains are all-or-nothing. -/
  | create_transfers (events : List NewTransfer)
  | lookup_accounts (ids : List Id)
  | lookup_transfers (ids : List Id)
  | get_account_transfers (filter : AccountFilter)
  | get_account_balances (filter : AccountFilter)
  | query_accounts (filter : QueryFilter)
  | query_transfers (filter : QueryFilter)
  | get_change_events (filter : ChangeEventsFilter)
  deriving DecidableEq, Repr

/-! ## Responses -/

/-- Why an account was or was not created, in the order TigerBeetle checks: the
    first that applies is the result. -/
inductive CreateAccountStatus where
  | created
  | linked_event_failed
  | linked_event_chain_open
  | id_must_not_be_zero
  | id_must_not_be_int_max
  | exists_with_different_flags
  | exists_with_different_user_data_128
  | exists_with_different_user_data_64
  | exists_with_different_user_data_32
  | exists_with_different_ledger
  | exists_with_different_code
  /-- The same account exists; the result's timestamp is the existing one's. -/
  | «exists»
  | flags_are_mutually_exclusive
  | ledger_must_not_be_zero
  | code_must_not_be_zero
  deriving DecidableEq, Repr

/-- Why a transfer was or was not created, in the order TigerBeetle checks: the
    first that applies is the result. -/
inductive CreateTransferStatus where
  | created
  | linked_event_failed
  | linked_event_chain_open
  | id_must_not_be_zero
  | id_must_not_be_int_max
  | exists_with_different_flags
  | exists_with_different_pending_id
  | exists_with_different_timeout
  | exists_with_different_debit_account_id
  | exists_with_different_credit_account_id
  | exists_with_different_amount
  | exists_with_different_user_data_128
  | exists_with_different_user_data_64
  | exists_with_different_user_data_32
  | exists_with_different_ledger
  | exists_with_different_code
  /-- The same transfer exists; the result's timestamp is the existing one's. -/
  | «exists»
  | id_already_failed
  | flags_are_mutually_exclusive
  | debit_account_id_must_not_be_zero
  | debit_account_id_must_not_be_int_max
  | credit_account_id_must_not_be_zero
  | credit_account_id_must_not_be_int_max
  | accounts_must_be_different
  | pending_id_must_be_zero
  | pending_id_must_not_be_zero
  | pending_id_must_not_be_int_max
  | pending_id_must_be_different
  | timeout_reserved_for_pending_transfer
  | closing_transfer_must_be_pending
  | ledger_must_not_be_zero
  | code_must_not_be_zero
  | debit_account_not_found
  | credit_account_not_found
  | accounts_must_have_the_same_ledger
  | transfer_must_have_the_same_ledger_as_accounts
  | pending_transfer_not_found
  | pending_transfer_not_pending
  | pending_transfer_has_different_debit_account_id
  | pending_transfer_has_different_credit_account_id
  | pending_transfer_has_different_ledger
  | pending_transfer_has_different_code
  | exceeds_pending_transfer_amount
  | pending_transfer_has_different_amount
  | pending_transfer_already_posted
  | pending_transfer_already_voided
  | pending_transfer_expired
  | debit_account_already_closed
  | credit_account_already_closed
  | overflows_debits_pending
  | overflows_credits_pending
  | overflows_debits_posted
  | overflows_credits_posted
  | overflows_debits
  | overflows_credits
  | overflows_timeout
  | exceeds_credits
  | exceeds_debits
  deriving DecidableEq, Repr

/-- Whether a retry of the same transfer could succeed: the failure depends on the
    state, not the transfer. Such a failure spends the id. -/
def CreateTransferStatus.transient : CreateTransferStatus → Bool
  | .debit_account_not_found | .credit_account_not_found | .pending_transfer_not_found
  | .exceeds_credits | .exceeds_debits
  | .debit_account_already_closed | .credit_account_already_closed => true
  | _ => false

/-- Every result carries a timestamp: the new or existing object's, or, on any
    other failure, the one the event was given. -/
structure CreateResult (S : Type) where
  timestamp : Time
  status    : S
  deriving DecidableEq, Repr

inductive ChangeEventType where
  | single_phase | two_phase_pending | two_phase_posted | two_phase_voided | two_phase_expired
  deriving DecidableEq, Repr

/-- An account event as `get_change_events` returns it: the transfer, and both
    accounts as they were just after the event. -/
structure ChangeEvent where
  type              : ChangeEventType
  timestamp         : Time
  transfer_id       : Id
  transfer          : Transfer
  debit_account_id  : Id
  debit_account     : Account
  credit_account_id : Id
  credit_account    : Account
  deriving DecidableEq, Repr

inductive Response where
  /-- `advance_clock`. -/
  | ok
  | create_accounts (results : List (CreateResult CreateAccountStatus))
  | create_transfers (results : List (CreateResult CreateTransferStatus))
  /-- The accounts found, in the order asked; ids not found are left out. -/
  | lookup_accounts (found : List (Id × Account))
  /-- The transfers found, in the order asked; ids not found are left out. -/
  | lookup_transfers (found : List (Id × Transfer))
  | get_account_transfers (found : List (Id × Transfer))
  | get_account_balances (found : List AccountBalance)
  | query_accounts (found : List (Id × Account))
  | query_transfers (found : List (Id × Transfer))
  | get_change_events (found : List ChangeEvent)
  deriving DecidableEq, Repr

/-! ## Internal work -/

/-- TigerBeetle's `pulse`: expire every pending transfer whose timeout has passed.
    Each pending transfer with a timeout starts one, to run after it expires;
    a pulse with nothing to expire does nothing. -/
inductive Internal where
  | pulse
  deriving DecidableEq, Repr

/-! ## The account rules

TigerBeetle names a rule by its flag, and checks it with `debits_exceed_credits`
and `credits_exceed_debits` (`src/tigerbeetle.zig`): would moving `amount` more
break it? Pending debits count, pending credits do not. -/

def Account.debits_exceed_credits (a : Account) (amount : Amount) : Bool :=
  a.flags.debits_must_not_exceed_credits &&
    decide (a.debits_pending + a.debits_posted + amount > a.credits_posted)

def Account.credits_exceed_debits (a : Account) (amount : Amount) : Bool :=
  a.flags.credits_must_not_exceed_debits &&
    decide (a.credits_pending + a.credits_posted + amount > a.debits_posted)

/-- The rule `debits_must_not_exceed_credits` holds for the account. -/
def Account.debits_must_not_exceed_credits (a : Account) : Prop :=
  a.flags.debits_must_not_exceed_credits = true →
    a.debits_pending + a.debits_posted ≤ a.credits_posted

/-- The rule `credits_must_not_exceed_debits` holds for the account. -/
def Account.credits_must_not_exceed_debits (a : Account) : Prop :=
  a.flags.credits_must_not_exceed_debits = true →
    a.credits_pending + a.credits_posted ≤ a.debits_posted

/-- The rule holds exactly when TigerBeetle's check, with nothing added, passes:
    the rule we prove and the check the steps run are one. -/
theorem debits_must_not_exceed_credits_iff (a : Account) :
    a.debits_must_not_exceed_credits ↔ a.debits_exceed_credits 0 = false := by
  unfold Account.debits_must_not_exceed_credits Account.debits_exceed_credits
  cases h : a.flags.debits_must_not_exceed_credits <;> simp

theorem credits_must_not_exceed_debits_iff (a : Account) :
    a.credits_must_not_exceed_debits ↔ a.credits_exceed_debits 0 = false := by
  unfold Account.credits_must_not_exceed_debits Account.credits_exceed_debits
  cases h : a.flags.credits_must_not_exceed_debits <;> simp

/-! ## Creating accounts (`create_account`) -/

def create_account_exists (a : NewAccount) (e : Account) : CreateAccountStatus := Id.run do
  if a.flags ≠ e.flags then return .exists_with_different_flags
  if a.user_data_128 ≠ e.user_data_128 then return .exists_with_different_user_data_128
  if a.user_data_64 ≠ e.user_data_64 then return .exists_with_different_user_data_64
  if a.user_data_32 ≠ e.user_data_32 then return .exists_with_different_user_data_32
  if a.ledger ≠ e.ledger then return .exists_with_different_ledger
  if a.code ≠ e.code then return .exists_with_different_code
  return .exists

def Server.create_account (s : Server) (ts : Time) (a : NewAccount) :
    Server × CreateResult CreateAccountStatus := Id.run do
  let fail : CreateAccountStatus → Server × CreateResult CreateAccountStatus :=
    fun st => (s, ⟨ts, st⟩)
  if a.id = 0 then return fail .id_must_not_be_zero
  if a.id = u128_max then return fail .id_must_not_be_int_max
  if let some e := get s.accounts a.id then
    let st := create_account_exists a e
    return (s, ⟨if st = .exists then e.timestamp else ts, st⟩)
  if a.flags.debits_must_not_exceed_credits && a.flags.credits_must_not_exceed_debits then
    return fail .flags_are_mutually_exclusive
  if a.ledger = 0 then return fail .ledger_must_not_be_zero
  if a.code = 0 then return fail .code_must_not_be_zero
  let account : Account :=
    { user_data_128 := a.user_data_128, user_data_64 := a.user_data_64,
      user_data_32 := a.user_data_32, ledger := a.ledger, code := a.code, flags := a.flags,
      debits_pending := 0, debits_posted := 0, credits_pending := 0, credits_posted := 0,
      timestamp := ts }
  return ({ s with accounts := s.accounts ++ [(a.id, account)] }, ⟨ts, .created⟩)

/-! ## Creating transfers (`create_transfer`) -/

def Server.create_transfer_exists (s : Server) (t : NewTransfer) (e : Transfer) :
    CreateTransferStatus := Id.run do
  if t.flags ≠ e.flags then return .exists_with_different_flags
  if t.pending_id ≠ e.pending_id then return .exists_with_different_pending_id
  if t.timeout ≠ e.timeout then return .exists_with_different_timeout
  if t.flags.post_pending_transfer || t.flags.void_pending_transfer then
    -- A post or a void may leave fields 0 to mean "as the pending transfer".
    let some p := get s.transfers t.pending_id | return .exists
    if t.debit_account_id ≠ 0 && t.debit_account_id ≠ e.debit_account_id then
      return .exists_with_different_debit_account_id
    if t.credit_account_id ≠ 0 && t.credit_account_id ≠ e.credit_account_id then
      return .exists_with_different_credit_account_id
    let amount :=
      if t.flags.void_pending_transfer then (if t.amount = 0 then p.amount else t.amount)
      else (if t.amount = u128_max then p.amount else t.amount)
    if amount ≠ e.amount then return .exists_with_different_amount
    let ud (x px : Nat) := if x = 0 then px else x
    if ud t.user_data_128 p.user_data_128 ≠ e.user_data_128 then
      return .exists_with_different_user_data_128
    if ud t.user_data_64 p.user_data_64 ≠ e.user_data_64 then
      return .exists_with_different_user_data_64
    if ud t.user_data_32 p.user_data_32 ≠ e.user_data_32 then
      return .exists_with_different_user_data_32
    if t.ledger ≠ 0 && t.ledger ≠ e.ledger then return .exists_with_different_ledger
    if t.code ≠ 0 && t.code ≠ e.code then return .exists_with_different_code
    return .exists
  if t.debit_account_id ≠ e.debit_account_id then return .exists_with_different_debit_account_id
  if t.credit_account_id ≠ e.credit_account_id then
    return .exists_with_different_credit_account_id
  -- A balancing transfer may have moved less than asked.
  if t.flags.balancing_debit || t.flags.balancing_credit then
    if t.amount < e.amount then return .exists_with_different_amount
  else if t.amount ≠ e.amount then return .exists_with_different_amount
  if t.user_data_128 ≠ e.user_data_128 then return .exists_with_different_user_data_128
  if t.user_data_64 ≠ e.user_data_64 then return .exists_with_different_user_data_64
  if t.user_data_32 ≠ e.user_data_32 then return .exists_with_different_user_data_32
  if t.ledger ≠ e.ledger then return .exists_with_different_ledger
  if t.code ≠ e.code then return .exists_with_different_code
  return .exists

/-- The second phase of a two-phase transfer (`post_or_void_pending_transfer`). -/
def Server.post_or_void_pending_transfer (s : Server) (ts : Time) (t : NewTransfer) :
    Server × CreateResult CreateTransferStatus := Id.run do
  let fail : CreateTransferStatus → Server × CreateResult CreateTransferStatus :=
    fun st => (s, ⟨ts, st⟩)
  let post := t.flags.post_pending_transfer
  let void := t.flags.void_pending_transfer
  if post && void then return fail .flags_are_mutually_exclusive
  if t.flags.pending || t.flags.balancing_debit || t.flags.balancing_credit ||
      t.flags.closing_debit || t.flags.closing_credit then
    return fail .flags_are_mutually_exclusive
  if t.pending_id = 0 then return fail .pending_id_must_not_be_zero
  if t.pending_id = u128_max then return fail .pending_id_must_not_be_int_max
  if t.pending_id = t.id then return fail .pending_id_must_be_different
  if t.timeout ≠ 0 then return fail .timeout_reserved_for_pending_transfer
  let some p := get s.transfers t.pending_id | return fail .pending_transfer_not_found
  if !p.flags.pending then return fail .pending_transfer_not_pending
  -- A pending transfer's accounts exist: accounts are never deleted.
  let some dr := get s.accounts p.debit_account_id | return fail .debit_account_not_found
  let some cr := get s.accounts p.credit_account_id | return fail .credit_account_not_found
  if t.debit_account_id ≠ 0 && t.debit_account_id ≠ p.debit_account_id then
    return fail .pending_transfer_has_different_debit_account_id
  if t.credit_account_id ≠ 0 && t.credit_account_id ≠ p.credit_account_id then
    return fail .pending_transfer_has_different_credit_account_id
  if t.ledger ≠ 0 && t.ledger ≠ p.ledger then return fail .pending_transfer_has_different_ledger
  if t.code ≠ 0 && t.code ≠ p.code then return fail .pending_transfer_has_different_code
  let amount :=
    if void then (if t.amount = 0 then p.amount else t.amount)
    else (if t.amount = u128_max then p.amount else t.amount)
  if amount > p.amount then return fail .exceeds_pending_transfer_amount
  if void && amount < p.amount then return fail .pending_transfer_has_different_amount
  match get s.transfers_pending t.pending_id with
  | some .posted  => return fail .pending_transfer_already_posted
  | some .voided  => return fail .pending_transfer_already_voided
  | some .expired => return fail .pending_transfer_expired
  | _ => pure ()
  -- Past its timeout, a pending transfer is expired, whether or not a pulse has
  -- expired it yet.
  if let some x := p.expires_at then
    if x ≤ ts then return fail .pending_transfer_expired
  if dr.flags.closed && !void then return fail .debit_account_already_closed
  if cr.flags.closed && !void then return fail .credit_account_already_closed
  let ud (x px : Nat) := if x = 0 then px else x
  let transfer : Transfer :=
    { debit_account_id := p.debit_account_id, credit_account_id := p.credit_account_id,
      amount, pending_id := t.pending_id,
      user_data_128 := ud t.user_data_128 p.user_data_128,
      user_data_64 := ud t.user_data_64 p.user_data_64,
      user_data_32 := ud t.user_data_32 p.user_data_32,
      timeout := 0, ledger := p.ledger, code := p.code, flags := t.flags, timestamp := ts }
  let dr' : Account :=
    { dr with
      debits_pending := dr.debits_pending - p.amount,
      debits_posted := if post then dr.debits_posted + amount else dr.debits_posted,
      flags := if void && p.flags.closing_debit then { dr.flags with closed := false } else dr.flags }
  let cr' : Account :=
    { cr with
      credits_pending := cr.credits_pending - p.amount,
      credits_posted := if post then cr.credits_posted + amount else cr.credits_posted,
      flags := if void && p.flags.closing_credit then { cr.flags with closed := false } else cr.flags }
  let status : TransferPendingStatus := if post then .posted else .voided
  return ({ s with
      transfers := s.transfers ++ [(t.id, transfer)],
      transfers_pending := put s.transfers_pending t.pending_id status,
      accounts := put (put s.accounts p.debit_account_id dr') p.credit_account_id cr',
      account_events := s.account_events ++
        [{ timestamp := ts, transfer_id := t.id, transfer_pending_status := status,
           dr_account_id := p.debit_account_id, dr_account := dr',
           cr_account_id := p.credit_account_id, cr_account := cr' }] },
    ⟨ts, .created⟩)

def Server.create_transfer (s : Server) (ts : Time) (t : NewTransfer) :
    Server × CreateResult CreateTransferStatus := Id.run do
  let fail : CreateTransferStatus → Server × CreateResult CreateTransferStatus :=
    fun st => (s, ⟨ts, st⟩)
  if t.id = 0 then return fail .id_must_not_be_zero
  if t.id = u128_max then return fail .id_must_not_be_int_max
  if let some e := get s.transfers t.id then
    let st := s.create_transfer_exists t e
    return (s, ⟨if st = .exists then e.timestamp else ts, st⟩)
  if s.orphaned.contains t.id then return fail .id_already_failed
  if t.flags.post_pending_transfer || t.flags.void_pending_transfer then
    return s.post_or_void_pending_transfer ts t
  if t.debit_account_id = 0 then return fail .debit_account_id_must_not_be_zero
  if t.debit_account_id = u128_max then return fail .debit_account_id_must_not_be_int_max
  if t.credit_account_id = 0 then return fail .credit_account_id_must_not_be_zero
  if t.credit_account_id = u128_max then return fail .credit_account_id_must_not_be_int_max
  if t.credit_account_id = t.debit_account_id then return fail .accounts_must_be_different
  if t.pending_id ≠ 0 then return fail .pending_id_must_be_zero
  if !t.flags.pending then
    if t.timeout ≠ 0 then return fail .timeout_reserved_for_pending_transfer
    if t.flags.closing_debit || t.flags.closing_credit then
      return fail .closing_transfer_must_be_pending
  if t.ledger = 0 then return fail .ledger_must_not_be_zero
  if t.code = 0 then return fail .code_must_not_be_zero
  let some dr := get s.accounts t.debit_account_id | return fail .debit_account_not_found
  let some cr := get s.accounts t.credit_account_id | return fail .credit_account_not_found
  if dr.ledger ≠ cr.ledger then return fail .accounts_must_have_the_same_ledger
  if t.ledger ≠ dr.ledger then return fail .transfer_must_have_the_same_ledger_as_accounts
  if dr.flags.closed then return fail .debit_account_already_closed
  if cr.flags.closed then return fail .credit_account_already_closed
  -- A balancing transfer moves at most what the account has available (`-` on
  -- `Nat` saturates at 0, as Zig's `-|`).
  let mut amount := t.amount
  if t.flags.balancing_debit then
    amount := min amount (dr.credits_posted - (dr.debits_posted + dr.debits_pending))
  if t.flags.balancing_credit then
    amount := min amount (cr.debits_posted - (cr.credits_posted + cr.credits_pending))
  if t.flags.pending then
    if amount + dr.debits_pending > u128_max then return fail .overflows_debits_pending
    if amount + cr.credits_pending > u128_max then return fail .overflows_credits_pending
  if amount + dr.debits_posted > u128_max then return fail .overflows_debits_posted
  if amount + cr.credits_posted > u128_max then return fail .overflows_credits_posted
  if amount + dr.debits_pending + dr.debits_posted > u128_max then return fail .overflows_debits
  if amount + cr.credits_pending + cr.credits_posted > u128_max then
    return fail .overflows_credits
  if ts + t.timeout * ns_per_s > timestamp_max then return fail .overflows_timeout
  if dr.debits_exceed_credits amount then return fail .exceeds_credits
  if cr.credits_exceed_debits amount then return fail .exceeds_debits
  let transfer : Transfer :=
    { debit_account_id := t.debit_account_id, credit_account_id := t.credit_account_id,
      amount, pending_id := 0, user_data_128 := t.user_data_128,
      user_data_64 := t.user_data_64, user_data_32 := t.user_data_32, timeout := t.timeout,
      ledger := t.ledger, code := t.code, flags := t.flags, timestamp := ts }
  let pending := t.flags.pending
  let dr' : Account :=
    { dr with
      debits_pending := if pending then dr.debits_pending + amount else dr.debits_pending,
      debits_posted := if pending then dr.debits_posted else dr.debits_posted + amount,
      flags := if t.flags.closing_debit then { dr.flags with closed := true } else dr.flags }
  let cr' : Account :=
    { cr with
      credits_pending := if pending then cr.credits_pending + amount else cr.credits_pending,
      credits_posted := if pending then cr.credits_posted else cr.credits_posted + amount,
      flags := if t.flags.closing_credit then { cr.flags with closed := true } else cr.flags }
  return ({ s with
      transfers := s.transfers ++ [(t.id, transfer)],
      transfers_pending :=
        if pending then s.transfers_pending ++ [(t.id, .pending)] else s.transfers_pending,
      accounts := put (put s.accounts t.debit_account_id dr') t.credit_account_id cr',
      account_events := s.account_events ++
        [{ timestamp := ts, transfer_id := t.id,
           transfer_pending_status := if pending then .pending else .none,
           dr_account_id := t.debit_account_id, dr_account := dr',
           cr_account_id := t.credit_account_id, cr_account := cr' }] },
    ⟨ts, .created⟩)

/-! ## Batches and linked chains (`execute_create`)

Events run in order, the `i`-th (from 0) at timestamp `base + i + 1`. A linked
chain runs from its first `linked` event to the next event without the flag. If
any event in it fails, the state goes back to where it was before the chain, the
events before the failure turn into `linked_event_failed`, and so do the ones
after it. A chain still open at the end of the batch fails with
`linked_event_chain_open` on its last event. -/

/-- A linked chain in progress: where it started, and the state before it. -/
structure Chain where
  start  : Nat
  saved  : Server
  broken : Bool

def run_batch {E S : Type} [DecidableEq S]
    (step : Server → Time → E → Server × CreateResult S) (linked : E → Bool)
    (created failed chain_open : S) (on_fail : Server → E → S → Server) (base n : Nat) :
    Nat → List E → Server → Option Chain → Array (CreateResult S) →
      Server × Array (CreateResult S)
  | _, [], s, _, rs => (s, rs)
  | i, e :: rest, s, chain, rs =>
    let ts := base + i + 1
    let chain := if linked e && chain.isNone then some ⟨i, s, false⟩ else chain
    let (s, r) :=
      if linked e && i + 1 = n then (s, ⟨ts, chain_open⟩)
      else if chain.any (·.broken) then (s, ⟨ts, failed⟩)
      else step s ts e
    let (s, rs, chain) :=
      if r.status = created then (s, rs, chain)
      else match chain with
        | some c =>
          if c.broken then (on_fail s e r.status, rs, chain)
          else
            -- The chain breaks here: roll back, and fail the events before.
            (on_fail c.saved e r.status,
             rs.mapIdx (fun j x => if j ≥ c.start then { x with status := failed } else x),
             some { c with broken := true })
        | none => (on_fail s e r.status, rs, none)
    let rs := rs.push r
    let chain := if !linked e || r.status = chain_open then none else chain
    run_batch step linked created failed chain_open on_fail base n (i + 1) rest s chain rs

def Server.create_accounts (s : Server) (events : List NewAccount) :
    Server × List (CreateResult CreateAccountStatus) :=
  let base := max s.prepare_timestamp s.now
  let n := events.length
  let (s', rs) := run_batch (fun s ts a => s.create_account ts a) (·.flags.linked)
    .created .linked_event_failed .linked_event_chain_open (fun s _ _ => s) base n 0 events s
    none #[]
  ({ s' with prepare_timestamp := base + n }, rs.toList)

/-- A transient failure spends the transfer's id. -/
def spend (s : Server) (t : NewTransfer) (st : CreateTransferStatus) : Server :=
  if st.transient then { s with orphaned := s.orphaned ++ [t.id] } else s

/-- Creates the transfers, and starts a pulse for each new pending transfer with a
    timeout, to run after it expires. -/
def Server.create_transfers (s : Server) (events : List NewTransfer) :
    Server × List (CreateResult CreateTransferStatus) × List (Sched Internal) :=
  let base := max s.prepare_timestamp s.now
  let n := events.length
  let (s', rs) := run_batch (fun s ts t => s.create_transfer ts t) (·.flags.linked)
    .created .linked_event_failed .linked_event_chain_open spend base n 0 events s none #[]
  let created := s'.transfers.drop s.transfers.length
  let pulses := created.filterMap fun (_, t) =>
    if t.flags.pending then t.expires_at.map (Sched.after · .pulse) else none
  ({ s' with prepare_timestamp := base + n }, rs.toList, pulses)

/-! ## Expiry (`execute_expire_pending_transfers`) -/

/-- Expires one pending transfer: gives back its pending amounts, and reopens the
    accounts it closed. -/
def Server.expire (s : Server) (ts : Time) (id : Id) (p : Transfer) : Server :=
  match get s.accounts p.debit_account_id, get s.accounts p.credit_account_id with
  | some dr, some cr =>
    let dr' : Account :=
      { dr with
        debits_pending := dr.debits_pending - p.amount,
        flags := if p.flags.closing_debit then { dr.flags with closed := false } else dr.flags }
    let cr' : Account :=
      { cr with
        credits_pending := cr.credits_pending - p.amount,
        flags := if p.flags.closing_credit then { cr.flags with closed := false } else cr.flags }
    { s with
      transfers_pending := put s.transfers_pending id .expired,
      accounts := put (put s.accounts p.debit_account_id dr') p.credit_account_id cr',
      account_events := s.account_events ++
        [{ timestamp := ts, transfer_id := id, transfer_pending_status := .expired,
           dr_account_id := p.debit_account_id, dr_account := dr',
           cr_account_id := p.credit_account_id, cr_account := cr' }] }
  | _, _ => s

def Server.expire_all : Server → Time → List (Id × Transfer) → Server
  | s, _, [] => s
  | s, ts, (id, p) :: rest => (s.expire ts id p).expire_all (ts + 1) rest

/-- The pulse runs at `T = max prepare_timestamp now + batch_max` and expires the
    pending transfers with `expires_at ≤ T`, earliest first, at most `batch_max`,
    the `k` of them at timestamps `T - k + 1, ..., T`. If more are due, another
    pulse follows. -/
def Server.pulse (lim : Limits) (s : Server) : Server × List (Sched Internal) :=
  let T := max s.prepare_timestamp s.now + lim.batch_max
  let due := s.transfers.filter fun (id, t) =>
    get s.transfers_pending id == some .pending && t.expires_at.any (· ≤ T)
  let due := due.mergeSort fun (_, a) (_, b) =>
    let x := a.expires_at.getD 0
    let y := b.expires_at.getD 0
    decide (x < y) || (x == y && decide (a.timestamp ≤ b.timestamp))
  if due.isEmpty then (s, [])
  else
    let now := due.take lim.batch_max
    let s' := s.expire_all (T - now.length + 1) now
    ({ s' with prepare_timestamp := T },
     if due.length > lim.batch_max then [.later .pulse] else [])

/-! ## Queries

A query with an invalid filter returns nothing. Results come in timestamp order
(newest first if `reversed`), at most `limit` of them. -/

def timestamp_valid (t : Time) : Bool := decide (1 ≤ t) && decide (t ≤ timestamp_max)

def range_valid (min max : Time) : Bool :=
  (min == 0 || timestamp_valid min) && (max == 0 || timestamp_valid max) &&
    (max == 0 || decide (min ≤ max))

def in_range (min max t : Time) : Bool :=
  (min == 0 || decide (min ≤ t)) && (max == 0 || decide (t ≤ max))

/-- A filter field: 0 matches anything. -/
def filter_matches (filter x : Nat) : Bool := filter == 0 || filter == x

def ordered {α : Type} (reversed : Bool) (l : List α) : List α :=
  if reversed then l.reverse else l

def AccountFilter.valid (f : AccountFilter) : Bool :=
  f.account_id != 0 && f.account_id != u128_max && range_valid f.timestamp_min f.timestamp_max &&
    f.limit != 0 && (f.flags.debits || f.flags.credits)

/-- The account's transfers that the filter selects, before `limit`. -/
def Server.account_transfers (s : Server) (f : AccountFilter) : List (Id × Transfer) :=
  ordered f.flags.reversed <| s.transfers.filter fun (_, t) =>
    ((f.flags.debits && t.debit_account_id == f.account_id) ||
      (f.flags.credits && t.credit_account_id == f.account_id)) &&
    filter_matches f.user_data_128 t.user_data_128 && filter_matches f.user_data_64 t.user_data_64 &&
    filter_matches f.user_data_32 t.user_data_32 && filter_matches f.code t.code &&
    in_range f.timestamp_min f.timestamp_max t.timestamp

def Server.get_account_transfers (lim : Limits) (s : Server) (f : AccountFilter) :
    List (Id × Transfer) :=
  if f.valid then (s.account_transfers f).take (min f.limit lim.result_max) else []

/-- The account's balances after each transfer the filter selects. Only for an
    account with the `history` flag. -/
def Server.get_account_balances (lim : Limits) (s : Server) (f : AccountFilter) :
    List AccountBalance :=
  match get s.accounts f.account_id with
  | some a =>
    if a.flags.history && f.valid then
      ((s.account_transfers f).take (min f.limit lim.result_max)).filterMap fun (_, t) =>
        (s.account_events.find? (·.timestamp == t.timestamp)).map fun ev =>
          let b := if ev.dr_account_id == f.account_id then ev.dr_account else ev.cr_account
          { debits_pending := b.debits_pending, debits_posted := b.debits_posted,
            credits_pending := b.credits_pending, credits_posted := b.credits_posted,
            timestamp := ev.timestamp }
    else []
  | none => []

def QueryFilter.valid (f : QueryFilter) : Bool :=
  range_valid f.timestamp_min f.timestamp_max && f.limit != 0

def QueryFilter.selects (f : QueryFilter) (ud128 ud64 ud32 ledger code ts : Nat) : Bool :=
  filter_matches f.user_data_128 ud128 && filter_matches f.user_data_64 ud64 && filter_matches f.user_data_32 ud32 &&
    filter_matches f.ledger ledger && filter_matches f.code code && in_range f.timestamp_min f.timestamp_max ts

def Server.query_accounts (lim : Limits) (s : Server) (f : QueryFilter) : List (Id × Account) :=
  if f.valid then
    (ordered f.reversed <| s.accounts.filter fun (_, a) =>
      f.selects a.user_data_128 a.user_data_64 a.user_data_32 a.ledger a.code a.timestamp
    ).take (min f.limit lim.result_max)
  else []

def Server.query_transfers (lim : Limits) (s : Server) (f : QueryFilter) : List (Id × Transfer) :=
  if f.valid then
    (ordered f.reversed <| s.transfers.filter fun (_, t) =>
      f.selects t.user_data_128 t.user_data_64 t.user_data_32 t.ledger t.code t.timestamp
    ).take (min f.limit lim.result_max)
  else []

def AccountEvent.type (ev : AccountEvent) : ChangeEventType :=
  match ev.transfer_pending_status with
  | .none => .single_phase
  | .pending => .two_phase_pending
  | .posted => .two_phase_posted
  | .voided => .two_phase_voided
  | .expired => .two_phase_expired

/-- Account events, always oldest first. -/
def Server.get_change_events (lim : Limits) (s : Server) (f : ChangeEventsFilter) :
    List ChangeEvent :=
  if range_valid f.timestamp_min f.timestamp_max && f.limit != 0 then
    ((s.account_events.filter (in_range f.timestamp_min f.timestamp_max ·.timestamp)).take
      (min f.limit lim.change_events_max)).filterMap fun ev =>
      (get s.transfers ev.transfer_id).map fun t =>
        { type := ev.type, timestamp := ev.timestamp, transfer_id := ev.transfer_id,
          transfer := t, debit_account_id := ev.dr_account_id, debit_account := ev.dr_account,
          credit_account_id := ev.cr_account_id, credit_account := ev.cr_account }
  else []

/-! ## The model -/

def Server.external (lim : Limits) (s : Server) :
    Request → ExternalOutcome Server Response Internal Empty
  | .advance_clock to => ⟨{ s with now := max s.now to }, .ok, [], []⟩
  | .create_accounts events =>
    let (s', rs) := s.create_accounts events
    ⟨s', .create_accounts rs, [], []⟩
  | .create_transfers events =>
    let (s', rs, pulses) := s.create_transfers events
    ⟨s', .create_transfers rs, pulses, []⟩
  | .lookup_accounts ids =>
    ⟨s, .lookup_accounts (ids.filterMap fun id => (get s.accounts id).map (id, ·)), [], []⟩
  | .lookup_transfers ids =>
    ⟨s, .lookup_transfers (ids.filterMap fun id => (get s.transfers id).map (id, ·)), [], []⟩
  | .get_account_transfers f => ⟨s, .get_account_transfers (s.get_account_transfers lim f), [], []⟩
  | .get_account_balances f => ⟨s, .get_account_balances (s.get_account_balances lim f), [], []⟩
  | .query_accounts f => ⟨s, .query_accounts (s.query_accounts lim f), [], []⟩
  | .query_transfers f => ⟨s, .query_transfers (s.query_transfers lim f), [], []⟩
  | .get_change_events f => ⟨s, .get_change_events (s.get_change_events lim f), [], []⟩

def Server.internal (lim : Limits) (s : Server) : Internal → InternalOutcome Server Internal Empty
  | .pulse => let (s', more) := s.pulse lim; ⟨s', more, []⟩

/-- TigerBeetle as an accordant model. Every request and every pulse has exactly
    one outcome: the state machine is deterministic. -/
def model (lim : Limits) : Accordant.Model where
  State    := Server
  External := Request
  Response := Response
  Internal := Internal
  Dispatch := Empty
  external := fun req s => [s.external lim req]
  internal := fun w s => [s.internal lim w]
  admits   := fun expected observed => decide (expected = observed)
  now      := (·.now)

/-! ## Scenarios, run -/

section Scenarios

def lim : Limits := ⟨8189, 8189, 2730⟩

def statuses {S : Type} (rs : List (CreateResult S)) : List S := rs.map (·.status)

def balances (s : Server) (id : Id) : Option (Nat × Nat × Nat × Nat) :=
  (get s.accounts id).map fun a => (a.debits_pending, a.debits_posted, a.credits_pending, a.credits_posted)

/-- Two accounts on ledger 1: 1 may not go negative, 2 is unrestricted. -/
def opened : Server :=
  (Server.create_accounts {}
    [{ id := 1, ledger := 1, code := 1, flags := { debits_must_not_exceed_credits := true, history := true } },
     { id := 2, ledger := 1, code := 1 }]).1

def tr (id dr cr amount : Nat) (flags : TransferFlags := {}) (timeout := 0) : NewTransfer :=
  { id, debit_account_id := dr, credit_account_id := cr, amount, ledger := 1, code := 1, flags, timeout }

-- Funding 1 from 2, then 1 may spend what it has, not more.
def funded : Server := (opened.create_transfers [tr 10 2 1 100]).1
#guard statuses (funded.create_transfers [tr 11 1 2 150]).2.1 == [.exceeds_credits]
#guard statuses (funded.create_transfers [tr 11 1 2 100]).2.1 == [.created]

-- A transient failure spends the id; the same transfer later is refused.
#guard statuses (((funded.create_transfers [tr 11 1 2 150]).1.create_transfers
  [tr 11 1 2 50]).2.1) == [.id_already_failed]

-- The same transfer again: `exists`, with the original timestamp.
#guard (funded.create_transfers [tr 10 2 1 100]).2.1 == [⟨3, .exists⟩]

-- A linked chain is all-or-nothing.
def chained := funded.create_transfers [tr 20 1 2 60 { linked := true }, tr 21 1 2 60]
#guard statuses chained.2.1 == [.linked_event_failed, .exceeds_credits]
#guard balances chained.1 1 == balances funded 1

-- A chain open at the end of the batch.
#guard statuses (funded.create_transfers [tr 22 1 2 1 { linked := true }]).2.1 ==
  [.linked_event_chain_open]

-- A balancing transfer moves what is available.
#guard (get (funded.create_transfers [tr 23 1 2 500 { balancing_debit := true }]).1.transfers 23).map
  (·.amount) == some 100

-- Two-phase: pending reserves, post moves part, the rest goes back.
def held := funded.create_transfers [tr 30 1 2 70 { pending := true } (timeout := 1)]
#guard balances held.1 1 == some (70, 0, 0, 100)
#guard held.2.2.length == 1
#guard statuses (held.1.create_transfers [tr 31 1 2 40]).2.1 == [.exceeds_credits]
def posted := held.1.create_transfers
  [{ id := 32, pending_id := 30, amount := 50, flags := { post_pending_transfer := true } }]
#guard statuses posted.2.1 == [.created]
#guard balances posted.1 1 == some (0, 50, 0, 100)
#guard statuses (posted.1.create_transfers
  [{ id := 33, pending_id := 30, flags := { void_pending_transfer := true } }]).2.1 ==
  [.pending_transfer_already_posted]

-- Expiry: past its timeout the transfer can't be posted, even before the pulse;
-- the pulse gives the amount back.
def late : Server := (held.1.external lim (.advance_clock (ns_per_s + 10))).next
#guard statuses (late.create_transfers
  [{ id := 34, pending_id := 30, flags := { post_pending_transfer := true }, amount := u128_max }]).2.1 ==
  [.pending_transfer_expired]
def expired := (late.pulse lim).1
#guard balances expired 1 == some (0, 0, 0, 100)
#guard get expired.transfers_pending 30 == some .expired

-- Queries.
#guard ((expired.get_account_transfers lim { account_id := 1, limit := 10 }).map (·.1)) == [10, 30]
#guard ((expired.get_account_transfers lim
  { account_id := 1, limit := 1, flags := { reversed := true } }).map (·.1)) == [30]
#guard (expired.get_account_balances lim { account_id := 1, limit := 10 }).map
  (fun b => (b.debits_pending, b.credits_posted)) == [(0, 100), (70, 100)]
#guard (expired.get_account_balances lim { account_id := 2, limit := 10 }) == []
#guard ((expired.query_accounts lim { ledger := 1, limit := 10 }).map (·.1)) == [1, 2]
#guard ((expired.get_change_events lim { limit := 10 }).map (·.type)) ==
  [.single_phase, .two_phase_pending, .two_phase_expired]

end Scenarios

end TigerBeetle
