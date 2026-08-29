import ProofForge.Wasm.Emit
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Host

/-!
# XRPL target emitter（薄封装）

发射核心在家族共享的 `ProofForge.Wasm.Emit`；XRPL 的存储、host import 与入口
ABI 全部来自 `Xrpl.Host.contract`。本文件不持有任何发射逻辑。
-/

namespace ProofForge.Wasm.Xrpl.Emit

/-- Render one XRPL program as a complete Bedrock-dialect Rust source. The digest line
pins the canonical IR identity of the artifact. -/
def emit (p : IR.Program) : Except String String :=
  Wasm.Emit.emit Host.contract IR.extValCanon IR.extOpCanon p

end ProofForge.Wasm.Xrpl.Emit
