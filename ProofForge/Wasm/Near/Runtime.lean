namespace ProofForge.Wasm.Near.Runtime

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

/--
`attached_deposit` as a UInt64. The host writes a little-endian u128; if the
high limb is nonzero the contract traps (`overflow`). Init/entry only — view
context cannot call `attached_deposit`.
-/
@[irreducible] def attachedDeposit : UInt64 := 0

/--
`account_balance` of the current account, same u128-truncation rule as
`attachedDeposit`. View-safe.
-/
@[irreducible] def accountBalance : UInt64 := 0

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
