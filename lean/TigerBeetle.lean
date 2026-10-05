/-!
# TigerBeetle's state machine, as an accordant model: the data model

Accounts and transfers, read from tigerbeetle/tigerbeetle (`src/tigerbeetle.zig`
for the types, `src/state_machine.zig` for what is stored and how it changes).
Names are TigerBeetle's, so the two read side by side.

The parts of an accordant `Model` (see `Accordant.lean`):

* `State`    = `Server`: the clock, accounts, transfers, pending statuses, spent ids.
* `External` = `Request`: create or look up accounts and transfers; move the clock.
* `Response` = `Response`: one result per created item; the items found.
* `Internal` = `Internal`: expire a pending transfer whose timeout has passed.
* `Dispatch` = `Dispatch`: none; TigerBeetle sends nothing on its own.

The steps come next.

Lean, so differences from TigerBeetle, all deliberate:
- A request is one batch of one operation (TigerBeetle packs several batches of
  one operation into a message; they run one after the other).
- Only `create_*` and `lookup_*`. Not yet: `get_account_transfers`,
  `get_account_balances` (and the `history` flag), `query_*`, `get_change_events`.
- No `user_data_*`, `reserved`, padding, or `imported`; their status codes go too.
- What a client creates is its own type (`NewAccount`, `NewTransfer`), so the
  `*_must_be_zero` codes for balances and `timestamp` cannot occur.
- Amounts and ids are `Nat`, bounded by `u128_max` where TigerBeetle checks it.
- A pending transfer's status is keyed by its id, not by its timestamp.
- Time is `Server.now`, moved by `advance_clock`.

Meant for Lean 4.31.0, core only: `lean lean/TigerBeetle.lean`. Not yet checked.
-/

namespace TigerBeetle

abbrev Id := Nat
/-- Nanoseconds on the cluster's clock. Every event that changes the state gets a
    timestamp of its own, unique and increasing across the cluster. -/
abbrev Time := Nat
abbrev Amount := Nat

def u128_max : Nat := 2 ^ 128 - 1
def ns_per_s : Nat := 1_000_000_000

/-! ## Accounts -/

structure AccountFlags where
  /-- Links this event to the next in the batch: the chain succeeds or fails as a unit. -/
  linked                         : Bool := false
  debits_must_not_exceed_credits : Bool := false
  credits_must_not_exceed_debits : Bool := false
  /-- No transfer may move money in or out. Set at creation or by a pending closing
      transfer; cleared when that transfer is voided or expires. -/
  closed                         : Bool := false
  deriving DecidableEq, Repr

structure Account where
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

/-- Where a pending transfer is. Kept for pending transfers only; a stored
    transfer itself never changes. -/
inductive TransferPendingStatus where
  | pending | posted | voided | expired
  deriving DecidableEq, Repr

/-! ## The server -/

structure Server where
  /-- The cluster's clock. -/
  now               : Time
  /-- The last timestamp given to an event (`commit_timestamp`). A batch's events
      get `max commit now + 1, + 2, ...`, so timestamps never repeat. -/
  commit            : Time
  accounts          : Id → Option Account
  transfers         : Id → Option Transfer
  /-- The status of every pending transfer, by its id. -/
  transfers_pending : Id → Option TransferPendingStatus
  /-- Ids of transfers that failed for a reason that may not hold on a retry. Such
      an id is spent: it can never be created (TigerBeetle's orphaned keys). -/
  orphaned          : Id → Bool

def Server.empty : Server :=
  ⟨0, 0, fun _ => none, fun _ => none, fun _ => none, fun _ => false⟩

/-! ## Requests -/

structure NewAccount where
  id     : Id
  ledger : Nat
  code   : Nat
  flags  : AccountFlags
  deriving DecidableEq, Repr

/-- For a post or a void, 0 in `debit_account_id`, `credit_account_id`, `ledger`
    and `code` means "as the pending transfer"; so does an `amount` of 0 for a
    void and of `u128_max` for a post. -/
structure NewTransfer where
  id                : Id
  debit_account_id  : Id
  credit_account_id : Id
  amount            : Amount
  pending_id        : Id
  timeout           : Nat
  ledger            : Nat
  code              : Nat
  flags             : TransferFlags
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

inductive Response where
  /-- `advance_clock`. -/
  | ok
  | create_accounts (results : List (CreateResult CreateAccountStatus))
  | create_transfers (results : List (CreateResult CreateTransferStatus))
  /-- The accounts found, in the order asked; ids not found are left out. -/
  | lookup_accounts (found : List (Id × Account))
  /-- The transfers found, in the order asked; ids not found are left out. -/
  | lookup_transfers (found : List (Id × Transfer))

/-! ## Internal work, dispatches -/

/-- Expire a pending transfer (TigerBeetle's `pulse`). Started when the transfer is
    created, to run after its `expires_at`; does nothing unless it is still
    pending. Gives back the pending amounts, reopens accounts it closed, and takes
    a timestamp like any other event. -/
inductive Internal where
  | expire (id : Id)

/-- TigerBeetle sends nothing on its own: a client sees only responses. -/
abbrev Dispatch := Empty

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

end TigerBeetle
