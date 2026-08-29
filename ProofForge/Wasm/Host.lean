/-!
# WASM 家族宿主合同

每条 WASM 链与其它链的差别收敛为三点（共享 WAT 发射器的注入点）：

1. **host function / runtime**：wasm import 表。模块名、函数名都是链的。
   XRPL 是 `host_lib`（XLS-0102）；不是通用 `pf` import，也不是 wasmtime。
2. **存储布局**：UInt64 槽如何落到 linear memory，以及经哪条 host 调用读写。
   XRPL v0：home 对象 `Data` 字段（sfield 458779），读 `home_le_field`、写
   `set_data`；槽按声明顺序每 8 字节小端打包。
3. **入口 ABI**：export 的名字、参数、返回约定（XRPL：mutating `i32` 状态码，
   view `i64`）。入口包装在共享发射器里，按 view/mutating 分支，不经本结构。
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
  /-- Host function that replaces the home object's Data blob. -/
  setData : String
  /-- Numeric sfield id of the Data blob (XRPL: 458779). -/
  sfieldData : Nat
  deriving Inhabited

end ProofForge.Wasm.Host
