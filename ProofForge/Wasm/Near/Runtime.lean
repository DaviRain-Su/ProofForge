import ProofForge.Core.Value

namespace ProofForge.Wasm.Near.Runtime

/-! NEAR compatibility name for the shared, allocation-free u128 value. -/

/-- YoctoNEAR amount, least-significant `UInt64` word first. -/
abbrev NearToken := ProofForge.Core.Value.UInt128

/--
Lossless host-returned NEAR account id: byte length plus eight little-endian
`UInt64` words (64-byte protocol maximum). Bytes above `length` are zero.

This is a source value, not a pointer or a Rust `String`. Context host calls
already guarantee a valid NEAR AccountId; future user-input decoding must
validate syntax before constructing this type.
-/
structure AccountId where
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

/--
Emit one statically known UTF-8 message through `env.log_utf8`. The source return is always zero
and exists only so ordinary Lean `let` sequencing can retain the Runtime effect. The extractor
rejects dynamic strings and messages above the target-owned bound.
-/
@[irreducible] def logUtf8 (message : String) : UInt64 :=
  let _ := message
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
