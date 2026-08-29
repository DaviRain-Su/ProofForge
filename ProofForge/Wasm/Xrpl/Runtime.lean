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
编译期 ASCII 字面量的 SHA-512Half。抽出器认这个名字，发射
`host_lib.compute_sha512_half`。返回 32 字节 digest 的第一个小端 `u64`。
宿主 stub 返回 0。完整 32B / 动态输入 / keccak 本剖面 fail closed。
不是 SVM `sha256Lit`，也不是 EVM `keccak256`。
-/
@[irreducible] def xrplSha512HalfLit (seed : String) : UInt64 :=
  let _ := seed
  0

end ProofForge.Wasm.Xrpl.Runtime
