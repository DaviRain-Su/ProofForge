/-!
# WASM 家族宿主合同

每条 WASM 链与其它链的差别收敛为三点（这也是家族共享发射器的注入点）：

1. **存储**：状态槽如何持久化（XRPL：合约 pseudo-account 的
   `get_data`/`set_data`；CosmWasm 会是自己的 storage API）；
2. **host function / runtime**：宿主能力叶子（ledger time、caller、hash——v0 全部
   缺席，各链方言未来在自己的 `Ops` 里钉）；
3. **SDK / 入口 ABI**：导出函数的签名与约定（XRPL：`#[unsafe(no_mangle)]
   pub extern "C" fn … -> i32` 状态码 + 取反 epilogue + `@xrpl-function` 注释）。

其余一切——checked 算术到 Rust 的发射、控制流、状态 threading、退出语义、
canonical digest 拼写——由家族共享的 `Wasm.IR` / `Wasm.Emit` 拥有，对所有
「经 Rust 编译到 wasm」的链一致。digest 域字符串本身仍由链拥有，经本结构注入。
-/

namespace ProofForge.Wasm.Host

/-- One chain's host contract for the shared WASM Rust emitter. -/
structure Contract where
  /-- Short chain name used in rejection and error prefixes (e.g. "xrpl"). -/
  name : String
  /-- Canonical digest domain; unique per chain (e.g. "xrpl-bedrock|"). -/
  digestDomain : String
  /-- Artifact identity header tag (e.g. "PROOF-FORGE-XRPL-BEDROCK v0"). -/
  headerTag : String
  /-- Artifact-header note lines: chain identity, compile surface, honesty pins. -/
  headerNotes : Array String
  /-- Crate-level prelude: attrs, cfg gates, host imports. -/
  prelude : Array String
  /-- Storage helper definitions; the shared emitter calls `readSlot`/`writeSlot`. -/
  storageHelpers : Array String
  /-- Host read helper name for one UInt64 state slot. -/
  readSlot : String
  /-- Host write helper name for one UInt64 state slot. -/
  writeSlot : String
  /-- State key constant expression for one slot name. -/
  slotKey : String → String
  /-- Wrap one mutating entry: fn name, params, echo-dropped flag, slot loads, region
  body. Owns the doc lines, attributes, signature, and status convention. -/
  wrapMutating : String → String → Bool → Array String → Array String → Array String
  /-- Wrap one view: fn name, params, slot loads, region body. -/
  wrapView : String → String → Array String → Array String → Array String
  deriving Inhabited

end ProofForge.Wasm.Host
