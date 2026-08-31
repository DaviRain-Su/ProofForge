import ProofForge.Attr
import ProofForge.Core.Value

namespace ProofForge.Wasm.Near.Runtime

/-! NEAR compatibility name for the shared, allocation-free u128 value. -/

/-- YoctoNEAR amount, least-significant `UInt64` word first. -/
abbrev NearToken := ProofForge.Core.Value.UInt128

/--
Lossless host-returned NEAR account id: byte length plus eight little-endian
`UInt64` words (64-byte protocol maximum). Bytes above `length` are zero.

This is a source value, not a pointer or a Rust `String`. Context host calls
already guarantee a valid NEAR AccountId; the compiler-owned bounded JSON input
plan validates syntax before constructing it, and any future decoder must do likewise.
-/
@[pf_boundary] structure AccountId where
  length : UInt64
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Compiler-owned optional bounded memo decoded from a specialized JSON input policy.
`present = 0` means `None`; `present = 1` preserves `Some ""` separately. Active UTF-8 bytes are
packed little-endian into `w0,w1`, and bytes at/above `length` are zero. -/
@[pf_boundary] structure OptionalMemo16 where
  present : UInt64
  length : UInt64
  w0 : UInt64
  w1 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Required bounded `msg` JSON string for the future transfer-call path. Decoded UTF-8 bytes are
packed little-endian; bytes at/above `length` are zero. -/
@[pf_boundary] structure BoundedMessage64 where
  length : UInt64
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  w4 : UInt64
  w5 : UInt64
  w6 : UInt64
  w7 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Compiler-owned exact frame for the bounded canonical `ft_transfer`-shaped JSON parser.
This is an input carrier only: it does not implement or claim the public NEP-141 method. -/
@[pf_boundary] structure FtTransferArgs where
  receiverId : AccountId
  amount : ProofForge.Core.Value.UInt128
  memo : OptionalMemo16
  deriving Repr, DecidableEq, Inhabited, BEq

/--
Current block height. Extractor matches this name and the NEAR emitter
imports `env.block_index` (u64, view-safe). Not Solana `Clock.slot`, not
EVM `NUMBER`.

Host stub is irreducible: theorems treat it as an unspecified `UInt64`.
-/
@[irreducible] def blockIndex : UInt64 := 0

/--
Parent block timestamp in **seconds**. Extractor matches this name; emitter
calls `env.block_timestamp` (nanoseconds) and divides by 10^9. View-safe.
Not `Clock.unix_timestamp`, not EVM `TIMESTAMP`.
-/
@[irreducible] def blockTimestamp : UInt64 := 0

/-- Current trie storage usage in bytes, including writes already performed in this invocation.
Raw host ABI: view-safe `env.storage_usage() -> u64`. -/
@[irreducible] def storageUsage : UInt64 := 0

/--
`predecessor_account_id` as the first 8 bytes of the UTF-8 account id,
little-endian. Init/entry only: NEAR forbids this host call in view context,
and the emitter fail-closes views that mention it. This legacy w0 projection is
not an identity; `predecessorAccountId` owns the complete 9-leaf value.
-/
@[irreducible] def predecessor : UInt64 := 0

@[irreducible] def predecessorLen : UInt64 := 0
@[irreducible] def predecessorW1 : UInt64 := 0
@[irreducible] def predecessorW2 : UInt64 := 0
@[irreducible] def predecessorW3 : UInt64 := 0
@[irreducible] def predecessorW4 : UInt64 := 0
@[irreducible] def predecessorW5 : UInt64 := 0
@[irreducible] def predecessorW6 : UInt64 := 0
@[irreducible] def predecessorW7 : UInt64 := 0

/-- Complete immediate-caller account id. `predecessor` remains the legacy w0 leaf. -/
def predecessorAccountId : AccountId :=
  { length := predecessorLen
    w0 := predecessor
    w1 := predecessorW1
    w2 := predecessorW2
    w3 := predecessorW3
    w4 := predecessorW4
    w5 := predecessorW5
    w6 := predecessorW6
    w7 := predecessorW7 }

/-- Legacy UInt64 `attached_deposit`. The emitter traps when the host u128 high
word is nonzero. Use `attachedDeposit128` for the lossless amount. -/
@[irreducible] def attachedDeposit : UInt64 := 0

/-- Dedicated lossless `attached_deposit` leaves. They are distinct from the
legacy leaf because projecting `w0` from a valid u128 must not impose the old
UInt64 overflow trap. Init/entry only. -/
@[irreducible] def attachedDepositW0 : UInt64 := 0
@[irreducible] def attachedDepositW1 : UInt64 := 0

/-- Complete attached deposit as the host's little-endian u128. -/
def attachedDeposit128 : NearToken :=
  { w0 := attachedDepositW0, w1 := attachedDepositW1 }

/-- Legacy UInt64 `account_balance`, trapping when its high word is nonzero.
Use `accountBalance128` for the lossless, view-safe amount. -/
@[irreducible] def accountBalance : UInt64 := 0

@[irreducible] def accountBalanceW0 : UInt64 := 0
@[irreducible] def accountBalanceW1 : UInt64 := 0

/-- Complete current-account balance as the host's little-endian u128. -/
def accountBalance128 : NearToken :=
  { w0 := accountBalanceW0, w1 := accountBalanceW1 }

/-!
Pure full-width token arithmetic leaves. Wasm i64 arithmetic wraps, so result limbs are modular;
callers must enforce the matching `Ok` predicate before using them as checked arithmetic. Keeping
carry and borrow target-owned avoids invoking checked UInt64 operations before the second limb can
observe the wrap.
-/

@[irreducible] def nearTokenAddOk
    (_leftLo _leftHi _rightLo _rightHi : UInt64) : UInt64 := 0
@[irreducible] def nearTokenAddW0
    (_leftLo _leftHi _rightLo _rightHi : UInt64) : UInt64 := 0
@[irreducible] def nearTokenAddW1
    (_leftLo _leftHi _rightLo _rightHi : UInt64) : UInt64 := 0
@[irreducible] def nearTokenSubOk
    (_leftLo _leftHi _rightLo _rightHi : UInt64) : UInt64 := 0
@[irreducible] def nearTokenSubW0
    (_leftLo _leftHi _rightLo _rightHi : UInt64) : UInt64 := 0
@[irreducible] def nearTokenSubW1
    (_leftLo _leftHi _rightLo _rightHi : UInt64) : UInt64 := 0
@[irreducible] def nearTokenMulU64Ok
    (_valueLo _valueHi _factor : UInt64) : UInt64 := 0
@[irreducible] def nearTokenMulU64W0
    (_valueLo _valueHi _factor : UInt64) : UInt64 := 0
@[irreducible] def nearTokenMulU64W1
    (_valueLo _valueHi _factor : UInt64) : UInt64 := 0

/--
Emit one statically known UTF-8 message through `env.log_utf8`. The source return is always zero
and exists only so ordinary Lean `let` sequencing can retain the Runtime effect. The extractor
rejects dynamic strings and messages above the target-owned bound.
-/
@[irreducible] def logUtf8 (message : String) : UInt64 :=
  let _ := message
  0

/--
Emit the active UTF-8 bytes of one bounded source string through `env.log_utf8`. The capacity is
compile-time and the logical carrier remains pointer-free; extraction stages exactly `length`
bytes through the invocation-local guest arena. Callers constructing the value internally must
preserve `BoundedString.wellFormed`; canonical NEAR String input already enforces it.
-/
@[irreducible] def logUtf8Bounded (capacity : Nat)
    (message : ProofForge.Core.Value.BoundedString capacity) : UInt64 :=
  let _ := capacity
  let _ := message
  0

/-- Emit one exact NEP-297 envelope whose `data` member is a bounded dynamic JSON string.
Metadata remains compile-time; the target owns all JSON escaping and the final host log. -/
@[irreducible] def nep297StringData (capacity : Nat) (standard version event : String)
    (data : ProofForge.Core.Value.BoundedString capacity) : UInt64 :=
  let _ := capacity
  let _ := standard
  let _ := version
  let _ := event
  let _ := data
  0

/-- Emit the exact no-memo NEP-141 v1.0.0 `ft_mint` event for one owner/amount record. -/
@[irreducible] def nep141FtMint (owner : AccountId) (amount : NearToken) : UInt64 :=
  let _ := owner
  let _ := amount
  0

/-- Emit the exact no-memo NEP-141 v1.0.0 `ft_transfer` event for one ownership change. -/
@[irreducible] def nep141FtTransfer
    (oldOwner newOwner : AccountId) (amount : NearToken) : UInt64 :=
  let _ := oldOwner
  let _ := newOwner
  let _ := amount
  0

/-- Emit the exact no-memo NEP-141 v1.0.0 `ft_burn` event for one owner/amount record. -/
@[irreducible] def nep141FtBurn (owner : AccountId) (amount : NearToken) : UInt64 :=
  let _ := owner
  let _ := amount
  0

/-- Emit one exact NEP-141 `ft_mint` event with a bounded UTF-8 memo. -/
@[irreducible] def nep141FtMintMemo (memoCapacity : Nat) (owner : AccountId)
    (amount : NearToken) (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  let _ := owner
  let _ := amount
  let _ := memo
  0

/-- Emit one exact NEP-141 `ft_transfer` event with a bounded UTF-8 memo. -/
@[irreducible] def nep141FtTransferMemo (memoCapacity : Nat) (oldOwner newOwner : AccountId)
    (amount : NearToken) (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  let _ := oldOwner
  let _ := newOwner
  let _ := amount
  let _ := memo
  0

/-- Emit one exact NEP-141 `ft_burn` event with a bounded UTF-8 memo. -/
@[irreducible] def nep141FtBurnMemo (memoCapacity : Nat) (owner : AccountId)
    (amount : NearToken) (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  let _ := owner
  let _ := amount
  let _ := memo
  0

/-!
Detached cross-contract call foundation. Receiver and method are compile-time literals; arguments
remain a bounded source frame, deposit is passed losslessly as two u64 limbs, and gas is an inline
u64. The emitter uses the same batch-create plus function-call action sequence as near-sdk-rs.
This schedules work but does not call `promise_return`; callbacks and result observation are
separate target effects.
-/

@[irreducible] def promiseFunctionCallDetached (argsCapacity : Nat)
    (receiver method : String)
    (arguments : ProofForge.Core.Value.BoundedBytes argsCapacity)
    (depositLo depositHi gas : UInt64) : UInt64 :=
  let _ := argsCapacity
  let _ := receiver
  let _ := method
  let _ := arguments
  let _ := depositLo
  let _ := depositHi
  let _ := gas
  0

/-- Schedule a static cross-contract call and forward its eventual result as the current method's
result. The Promise remains asynchronous; nearcore links the returned receipt to the transaction
outcome. -/
@[irreducible] def promiseFunctionCallReturned (argsCapacity : Nat)
    (receiver method : String)
    (arguments : ProofForge.Core.Value.BoundedBytes argsCapacity)
    (depositLo depositHi gas : UInt64) : UInt64 :=
  let _ := argsCapacity
  let _ := receiver
  let _ := method
  let _ := arguments
  let _ := depositLo
  let _ := depositHi
  let _ := gas
  0

/-- Schedule one native NEAR transfer without linking its receipt to the current method result. -/
@[irreducible] def promiseTransferDetached
    (receiver : String) (amountLo amountHi : UInt64) : UInt64 :=
  let _ := receiver
  let _ := amountLo
  let _ := amountHi
  0

/-- Schedule one native NEAR transfer and forward the transfer receipt's eventual result. -/
@[irreducible] def promiseTransferReturned
    (receiver : String) (amountLo amountHi : UInt64) : UInt64 :=
  let _ := receiver
  let _ := amountLo
  let _ := amountHi
  0

/-- Schedule one native NEAR transfer to a complete dynamic AccountId without linking its receipt
to the current method result. The target stages only the active `length` bytes. -/
@[irreducible] def promiseTransferAccountDetached
    (receiver : AccountId) (amountLo amountHi : UInt64) : UInt64 :=
  let _ := receiver
  let _ := amountLo
  let _ := amountHi
  0

/-- Schedule one native NEAR transfer to a complete dynamic AccountId and forward that receipt's
eventual result. -/
@[irreducible] def promiseTransferAccountReturned
    (receiver : AccountId) (amountLo amountHi : UInt64) : UInt64 :=
  let _ := receiver
  let _ := amountLo
  let _ := amountHi
  0

/-- Schedule the specialized weighted `ft_on_transfer` child call used by the future
`ft_transfer_call` path. The receiver and sender are complete dynamic AccountIds; the target owns
the exact JSON payload, fixed zero deposit, method name, and weighted host action. -/
@[irreducible] def promiseFtOnTransferReturned
    (receiver sender : AccountId) (amount : NearToken) (msg : BoundedMessage64) : UInt64 :=
  let _ := receiver
  let _ := sender
  let _ := amount
  let _ := msg
  0

/-- Schedule one static child call followed by one static callback on the current contract, then
forward the callback's eventual result. The child result is available to the callback only through
`promiseResultsCount` / `promiseResultRead`; callback arguments remain an independent input frame. -/
@[irreducible] def promiseFunctionCallThenReturned
    (childArgsCapacity callbackArgsCapacity : Nat)
    (receiver childMethod callbackMethod : String)
    (childArguments : ProofForge.Core.Value.BoundedBytes childArgsCapacity)
    (callbackArguments : ProofForge.Core.Value.BoundedBytes callbackArgsCapacity)
    (childDepositLo childDepositHi childGas : UInt64)
    (callbackDepositLo callbackDepositHi callbackGas : UInt64) : UInt64 :=
  let _ := childArgsCapacity
  let _ := callbackArgsCapacity
  let _ := receiver
  let _ := childMethod
  let _ := callbackMethod
  let _ := childArguments
  let _ := callbackArguments
  let _ := childDepositLo
  let _ := childDepositHi
  let _ := childGas
  let _ := callbackDepositLo
  let _ := callbackDepositHi
  let _ := callbackGas
  0

/-- Schedule two ordered static child calls, join them, then schedule one static callback on the
current contract and forward only the callback's eventual result. The joint Promise is internal:
actions are appended to the callback receipt, never to the join itself. -/
@[irreducible] def promiseFunctionCallAndThenReturned
    (leftArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat)
    (leftReceiver leftMethod rightReceiver rightMethod callbackMethod : String)
    (leftArguments : ProofForge.Core.Value.BoundedBytes leftArgsCapacity)
    (rightArguments : ProofForge.Core.Value.BoundedBytes rightArgsCapacity)
    (callbackArguments : ProofForge.Core.Value.BoundedBytes callbackArgsCapacity)
    (leftDepositLo leftDepositHi leftGas : UInt64)
    (rightDepositLo rightDepositHi rightGas : UInt64)
    (callbackDepositLo callbackDepositHi callbackGas : UInt64) : UInt64 :=
  let _ := leftArgsCapacity
  let _ := rightArgsCapacity
  let _ := callbackArgsCapacity
  let _ := leftReceiver
  let _ := leftMethod
  let _ := rightReceiver
  let _ := rightMethod
  let _ := callbackMethod
  let _ := leftArguments
  let _ := rightArguments
  let _ := callbackArguments
  let _ := leftDepositLo
  let _ := leftDepositHi
  let _ := leftGas
  let _ := rightDepositLo
  let _ := rightDepositHi
  let _ := rightGas
  let _ := callbackDepositLo
  let _ := callbackDepositHi
  let _ := callbackGas
  0

/-!
Callback-result foundation. `promiseResultsCount` is immutable invocation context. Every
`promiseResultRead` replaces one invocation-local bounded descriptor. Status is the exact nearcore
ABI: 0 not ready, 1 successful, 2 failed. Only status 1 writes the host register, so the target
must not inspect it for the other statuses. An out-of-range result index aborts in nearcore.
-/

@[irreducible] def promiseResultsCount : UInt64 := 0

@[irreducible] def promiseResultRead (capacity : Nat) (index : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  0

/-- Exact nearcore 0/1/2 status for the latest Promise-result read. -/
@[irreducible] def promiseResultStatus (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-- Successful result length, including an oversized length; zero for status 0/2. -/
@[irreducible] def promiseResultLength (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-- One unless a successful result exceeded the declared capacity. Meaningful with status 1. -/
@[irreducible] def promiseResultFits (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-- Byte from the latest bounded successful copy. Unavailable or uncopied lanes read as zero. -/
@[irreducible] def promiseResultByte (capacity : Nat) (index : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  0

/-- Strict decoder over the active callback-result descriptor. The target requires status 1,
`fits`, and exact length 8 before reading little-endian bytes; otherwise it returns `fallback`. -/
@[irreducible] def promiseResultBorshUInt64D
    (capacity : Nat) (fallback : UInt64) : UInt64 :=
  let _ := capacity
  let _ := fallback
  0

/-!
Invocation-local guest-Wasm arena leaves. Capacity is compile-time fixed by the SDK descriptor;
the extractor rejects malformed geometry. The physical pointer remains target-owned and cannot
enter source state or persistent storage.
-/

@[irreducible] def transientBuffer64Begin (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

@[irreducible] def transientBuffer64Set
    (capacity : Nat) (index value : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  let _ := value
  0

@[irreducible] def transientBuffer64Get (capacity : Nat) (index : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  0

@[irreducible] def transientBuffer64Finish (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-!
Raw NEAR key-value storage leaves. Keys and values remain fixed `BoundedBytes` source frames;
the target stages only their active binary prefixes in guest memory. Every operation replaces one
invocation-local result descriptor. Read/write/remove copy a present/evicted/removed host register
only when it fits the declared result capacity. No guest pointer enters source code.
-/

@[irreducible] def storageRead (resultCapacity keyCapacity : Nat)
    (key : ProofForge.Core.Value.BoundedBytes keyCapacity) : UInt64 :=
  let _ := resultCapacity
  let _ := key
  0

@[irreducible] def storageWrite (resultCapacity keyCapacity valueCapacity : Nat)
    (key : ProofForge.Core.Value.BoundedBytes keyCapacity)
    (value : ProofForge.Core.Value.BoundedBytes valueCapacity) : UInt64 :=
  let _ := resultCapacity
  let _ := key
  let _ := value
  0

@[irreducible] def storageRemove (resultCapacity keyCapacity : Nat)
    (key : ProofForge.Core.Value.BoundedBytes keyCapacity) : UInt64 :=
  let _ := resultCapacity
  let _ := key
  0

@[irreducible] def storageHasKey (resultCapacity keyCapacity : Nat)
    (key : ProofForge.Core.Value.BoundedBytes keyCapacity) : UInt64 :=
  let _ := resultCapacity
  let _ := key
  0

/-!
Closed Identity AccountId-to-NearToken storage leaves. The extractor stages the exact
`prefix4 || u32_le(account.length) || active account bytes` key and exact 16-byte Borsh value,
then lowers to the same raw-storage operations above. Keeping the dynamic key geometry target-owned
avoids treating inactive AccountId carrier lanes as identity bytes.
-/

@[irreducible] def accountNearTokenRead (tag : UInt64) (account : AccountId) : UInt64 :=
  let _ := tag
  let _ := account
  0

@[irreducible] def accountNearTokenHasKey (tag : UInt64) (account : AccountId) : UInt64 :=
  let _ := tag
  let _ := account
  0

@[irreducible] def accountNearTokenWrite
    (tag : UInt64) (account : AccountId) (value : NearToken) : UInt64 :=
  let _ := tag
  let _ := account
  let _ := value
  0

@[irreducible] def accountNearTokenRemove (tag : UInt64) (account : AccountId) : UInt64 :=
  let _ := tag
  let _ := account
  0

/-- Fixture-only malformed-value seed for exact-decoder runtime tests. Not an SDK operation. -/
@[irreducible] def accountNearTokenFixtureWriteMalformed
    (tag : UInt64) (account : AccountId) (length : UInt64) : UInt64 :=
  let _ := tag
  let _ := account
  let _ := length
  0

/-- Raw nearcore 0/1 status for the latest operation. -/
@[irreducible] def storageResultStatus (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-- Actual copied-register length for status 1, including an oversized length; otherwise zero. -/
@[irreducible] def storageResultLength (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-- One unless a status-1 register exceeded the declared result capacity. -/
@[irreducible] def storageResultFits (capacity : Nat) : UInt64 :=
  let _ := capacity
  0

/-- Byte from the latest bounded copy. Inactive or uncopied lanes read as zero. -/
@[irreducible] def storageResultByte (capacity : Nat) (index : UInt64) : UInt64 :=
  let _ := capacity
  let _ := index
  0

/-- Strict typed-map view decode of the active 16-byte storage result. Missing returns zero;
present malformed/oversized values trap in the target instead of exposing partial/stale data. -/
@[irreducible] def storageResultNearTokenW0Strict : UInt64 := 0
@[irreducible] def storageResultNearTokenW1Strict : UInt64 := 0

/--
`current_account_id` as the first 8 bytes of the UTF-8 account id,
little-endian. View-safe — unlike `predecessor`. Not a 20-byte address,
not a complete identity; `selfAccountId` owns the complete 9-leaf value.
-/
@[irreducible] def currentAccountId : UInt64 := 0

@[irreducible] def currentAccountIdLen : UInt64 := 0
@[irreducible] def currentAccountIdW1 : UInt64 := 0
@[irreducible] def currentAccountIdW2 : UInt64 := 0
@[irreducible] def currentAccountIdW3 : UInt64 := 0
@[irreducible] def currentAccountIdW4 : UInt64 := 0
@[irreducible] def currentAccountIdW5 : UInt64 := 0
@[irreducible] def currentAccountIdW6 : UInt64 := 0
@[irreducible] def currentAccountIdW7 : UInt64 := 0

/-- Complete current contract account id. `currentAccountId` remains the legacy w0 leaf. -/
def selfAccountId : AccountId :=
  { length := currentAccountIdLen
    w0 := currentAccountId
    w1 := currentAccountIdW1
    w2 := currentAccountIdW2
    w3 := currentAccountIdW3
    w4 := currentAccountIdW4
    w5 := currentAccountIdW5
    w6 := currentAccountIdW6
    w7 := currentAccountIdW7 }

end ProofForge.Wasm.Near.Runtime
