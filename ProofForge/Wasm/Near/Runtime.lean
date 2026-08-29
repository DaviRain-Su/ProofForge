namespace ProofForge.Wasm.Near.Runtime

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
and the emitter fail-closes views that mention it. Not a 20-byte address,
not `signerKey0`, not a 9-leaf Principal.
-/
@[irreducible] def predecessor : UInt64 := 0

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
not a 9-leaf Principal.
-/
@[irreducible] def currentAccountId : UInt64 := 0

end ProofForge.Wasm.Near.Runtime
