/-!
# WASM 家族宿主合同

每条 WASM 链与其它链的差别收敛为三点（共享 WAT 发射器的注入点）：

1. **host function / runtime**：wasm import 表。模块名、函数名都是链的。
   XRPL 是 `host_lib`（XLS-0102）；不是通用 `pf` import，也不是 wasmtime。
2. **存储布局**：UInt64 槽如何落到 linear memory，以及经哪条 host 调用读写。
   XRPL v0：`ContractData` JSON 对象字段（`get/set_data_object_field`），
   每个槽一个 key；UINT64 写 `STI_UINT64` + 大端 8 字节。本 Bedrock
   镜像的 `update_data` 不落账本。
3. **入口 ABI**：export 名字与返回约定（mutating `i32` 状态码，view `i64`）
   仍在共享发射器里分支。XRPL 不把 `UINT64` 当 wasm `i64` 参数传入；
   值经 `host_lib.function_param` 拷进 linear memory。链用
   `functionParam` 注入这条 import；空字符串表示参数走 wasm `(param i64)`。
-/

namespace ProofForge.Wasm.Host

/-- One chain's host contract for the shared WAT emitter. -/
structure Contract where
  /-- Short chain name used in rejection and error prefixes (e.g. "xrpl"). -/
  name : String
  /-- Canonical digest domain; unique per chain (e.g. "xrpl-bedrock|"). -/
  digestDomain : String
  /-- Artifact identity header tag (e.g. "PROOF-FORGE-XRPL-BEDROCK v0"). -/
  headerTag : String
  /-- Artifact-header note lines. -/
  headerNotes : Array String
  /-- WASM import module (e.g. "host_lib"). -/
  importModule : String
  /-- Host function that reads a field of the home ledger object. -/
  homeLeField : String
  /-- Host function that replaces the home object's Data blob.
  Unused when `getDataObject` is set. -/
  setData : String
  /-- Numeric sfield id of the Data blob (XRPL: 458779). -/
  sfieldData : Nat
  /-- Host function that copies a ContractCall parameter into linear memory.
  Empty means the chain passes UInt64 args as wasm `(param i64)`. XRPL:
  `function_param(index, STI_UINT64, ptr, len) -> i32`. -/
  functionParam : String := ""
  /-- Serialized-type code for UINT64 (XRPL STI_UINT64 = 3). -/
  stiUint64 : Nat := 3
  /-- Host errors that mean storage is not present yet. Mutating entries
  treat these as zeros instead of returning them. Empty means any negative
  load is fatal. -/
  missingFields : Array Int := #[]
  /-- Host function `get_data_object_field(acc, acc_len, key, key_len, out, out_len)`.
  Non-empty selects ContractData object-field storage instead of the Data blob. -/
  getDataObject : String := ""
  /-- Host function `set_data_object_field(acc, acc_len, key, key_len, data, data_len)`. -/
  setDataObject : String := ""
  /-- sfield of the data-owner AccountID (XRPL `sfOwner` = 524290). -/
  sfieldAccount : Nat := 0
  /-- Host `get_tx_field(field, ptr, len) -> i32`. Empty means no tx-field env leaves. -/
  getTxField : String := ""
  /-- sfield of the transaction Account (XRPL `sfAccount` = 524289). -/
  sfieldTxAccount : Nat := 0
  /-- sfield of the contract AccountID on the Contract SLE (XRPL `sfContractAccount` = 524315). -/
  sfieldContractAccount : Nat := 0
  /-- Host `get_ledger_sqn() -> i32`. Empty skips the ledger-sqn leaf. -/
  getLedgerSqn : String := ""
  /-- Host `get_parent_ledger_time() -> i32`. Empty skips the parent-time leaf. -/
  getParentTime : String := ""
  /-- Host `compute_sha512_half(data, data_len, out, out_len) -> i32`. Empty skips hash lits. -/
  computeSha512Half : String := ""
  deriving Inhabited

/-- Object-field storage (XRPL ContractData) rather than a packed Data blob. -/
def Contract.objectStore (c : Contract) : Bool :=
  !c.getDataObject.isEmpty

end ProofForge.Wasm.Host
