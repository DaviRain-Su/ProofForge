/-!
# XRPL Bedrock runtime stubs

普通 Lean 名，抽出后变成 `host_lib` 调用。不是 EVM `Addr20` / `CALLER`，
也不是 SVM `clockSlot`。宿主返回 0，不要 unfold。
-/

namespace ProofForge.Wasm.Xrpl.Runtime

/--
20 字节 XRPL AccountID，三个 `UInt64` 叶：w0/w1 各 8 字节，w2 只低 4 字节。
小端装账户字节 0..19。不是 `Evm.Runtime.Addr20`。
-/
structure AccountId where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

@[irreducible] def xrplCallerW0 : UInt64 := 0
@[irreducible] def xrplCallerW1 : UInt64 := 0
@[irreducible] def xrplCallerW2 : UInt64 := 0
@[irreducible] def xrplSelfW0 : UInt64 := 0
@[irreducible] def xrplSelfW1 : UInt64 := 0
@[irreducible] def xrplSelfW2 : UInt64 := 0

/-- 当前 `ContractCall` 的 `sfAccount`（20 字节）。抽出认三叶。 -/
def xrplCaller20 : AccountId :=
  { w0 := xrplCallerW0, w1 := xrplCallerW1, w2 := xrplCallerW2 }

/-- 当前合约 `sfContractAccount`。抽出认三叶。 -/
def xrplSelf20 : AccountId :=
  { w0 := xrplSelfW0, w1 := xrplSelfW1, w2 := xrplSelfW2 }

/-- `host_lib.get_ledger_sqn`，i32 零扩展到 UInt64。不是 `clockSlot`。 -/
@[irreducible] def xrplLedgerSqn : UInt64 := 0

/-- `host_lib.get_parent_ledger_time`，i32 零扩展到 UInt64。不是 `evmTimestamp`。 -/
@[irreducible] def xrplParentTime : UInt64 := 0

/--
`host_lib.get_parent_ledger_hash` 写出 32 字节，本叶只取第一个小端 UInt64。
不是 EVM `blockhash`，完整 32B 仍 fail closed。
-/
@[irreducible] def xrplParentHashW0 : UInt64 := 0

/-- `host_lib.get_base_fee`，i32 零扩展到 UInt64。不是 EVM `baseFee` UInt256。 -/
@[irreducible] def xrplBaseFee : UInt64 := 0

/--
编译期 ASCII 字面量的 SHA-512Half。抽出器认这个名字，发射
`host_lib.compute_sha512_half`。返回 32 字节 digest 的第一个小端 `u64`。
宿主 stub 返回 0。完整 32B / 动态输入 / keccak 本剖面 fail closed。
不是 SVM `sha256Lit`，也不是 EVM `keccak256`。
-/
@[irreducible] def xrplSha512HalfLit (seed : String) : UInt64 :=
  let _ := seed
  0

/-- Caller's XRP Balance in drops. Host: accountroot_id + cache_le + le_field.
Not EVM `selfBalance`. IOU/MPT fail closed (mantissa only). -/
@[irreducible] def xrplCallerBalanceDrops : UInt64 := 0

/-- AccountRoot.Sequence (UInt32 LE → UInt64). Same cache as Balance. -/
@[irreducible] def xrplCallerSequence : UInt64 := 0

/-- AccountRoot.Flags (UInt32 LE → UInt64). -/
@[irreducible] def xrplCallerFlags : UInt64 := 0

/-- AccountRoot.OwnerCount (UInt32 LE → UInt64). Snapshot at cache_le. -/
@[irreducible] def xrplCallerOwnerCount : UInt64 := 0

/-- Current `ContractCall` Sequence. Host: `tx_field(sfSequence=131076)`. -/
@[irreducible] def xrplTxSequence : UInt64 := 0

/-- Current `ContractCall` Fee in drops. Host: `tx_field(sfFee=393224)`. -/
@[irreducible] def xrplTxFeeDrops : UInt64 := 0

/-- Compile-time 20-byte AccountID as three little-endian limbs.
`hex` is 40 lowercase hex chars. Host stub 0; extractor keeps the literal. -/
@[irreducible] def xrplAccountLitW0 (hex : String) : UInt64 :=
  let _ := hex
  0

@[irreducible] def xrplAccountLitW1 (hex : String) : UInt64 :=
  let _ := hex
  0

@[irreducible] def xrplAccountLitW2 (hex : String) : UInt64 :=
  let _ := hex
  0

/-- Three-limb compile-time AccountID. Extractor unfolds ofLimbs after these leaves. -/
def xrplAccountLit (hex : String) : AccountId :=
  { w0 := xrplAccountLitW0 hex, w1 := xrplAccountLitW1 hex, w2 := xrplAccountLitW2 hex }

/-- Current `ContractCall` Flags. Host: `tx_field(sfFlags=131074)`. -/
@[irreducible] def xrplTxFlags : UInt64 := 0

/-- Compile-time AccountID's XRP Balance in drops. Same host path as
`xrplCallerBalanceDrops`, keylet from `hex`. Persist owner stays the caller. -/
@[irreducible] def xrplLitBalanceDrops (hex : String) : UInt64 :=
  let _ := hex
  0

/-- Rewrite persist Owner to these three little-endian limbs, then return `w2`.
Host stub returns `w2`. Extractor keeps the three operands. Not a Map. -/
@[irreducible] def xrplStoreOwner (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  w2

/-- Persist `v` onto the current Owner card, then return `v`. Host stub returns `v`. -/
@[irreducible] def xrplFlushBal (v : UInt64) : UInt64 :=
  v

/-- Rewrite persist Owner to `(w0,w1,w2)`, load that card's `bal` (missing → 0).
Host stub returns 0. Not a Map, not a Payment. -/
@[irreducible] def xrplPeekOwner (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Persist `v` onto the current Owner card under JSON key `halt`. -/
@[irreducible] def xrplFlushHalt (v : UInt64) : UInt64 :=
  v

/-- Load `halt` from the card owned by `(w0,w1,w2)` (missing → 0). Rewrites
persist Owner. Not a Map. -/
@[irreducible] def xrplPeekHalt (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Persist `v` onto the current Owner card under JSON key `supp`. -/
@[irreducible] def xrplFlushSupp (v : UInt64) : UInt64 :=
  v

/-- Load `supp` from the card owned by `(w0,w1,w2)` (missing → 0). -/
@[irreducible] def xrplPeekSupp (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Persist `v` onto the current Owner card under JSON key `cap`. -/
@[irreducible] def xrplFlushCap (v : UInt64) : UInt64 :=
  v

/-- Load `cap` from the card owned by `(w0,w1,w2)` (missing → 0 = unlimited). -/
@[irreducible] def xrplPeekCap (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Persist `v` onto the current Owner card under JSON key `allw`. -/
@[irreducible] def xrplFlushAllw (v : UInt64) : UInt64 :=
  v

/-- Load `allw` from the card owned by `(w0,w1,w2)` (missing → 0). -/
@[irreducible] def xrplPeekAllw (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Persist `v` onto the current Owner card under JSON key `lock`. -/
@[irreducible] def xrplFlushLock (v : UInt64) : UInt64 :=
  v

/-- Load `lock` from the card owned by `(w0,w1,w2)` (missing → 0). Rewrites
persist Owner. Per-user freeze, not global `halt`. Not a Map. -/
@[irreducible] def xrplPeekLock (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Persist `v` onto the current Owner card under JSON key `esc`. -/
@[irreducible] def xrplFlushEsc (v : UInt64) : UInt64 :=
  v

/-- Load `esc` from the card owned by `(w0,w1,w2)` (missing → 0). Rewrites
persist Owner. Escrow on the contract card, not a Map. -/
@[irreducible] def xrplPeekEsc (w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0
  let _ := w1
  let _ := w2
  0

/-- Local 2.6.1 `build_txn` / `add_txn_field` / `emit_built_txn` Payment of 192
drops to the caller. Host stub 0. Public AlphaNet is tefBAD_AUTH -196.
Not `Sdk.Payments`, not a Map. -/
@[irreducible] def xrplEmitPay : UInt64 := 0

/-- Same host path as `xrplEmitPay`, Amount = `0x40…` OR `drops`. Host stub 0. -/
@[irreducible] def xrplEmitPayDrops (drops : UInt64) : UInt64 :=
  let _ := drops
  0

/-- Local 2.6.1 Payment of 192 drops to a compile-time 20-byte AccountID.
`hex` is 40 lowercase chars. Host stub 0. Public -196. Not `Sdk.Payments`. -/
@[irreducible] def xrplEmitPayToLit (hex : String) : UInt64 :=
  let _ := hex
  0

end ProofForge.Wasm.Xrpl.Runtime
