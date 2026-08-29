import ProofForge.Wasm.Emit
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Host

/-!
# XRPL target emitter（薄封装）

发射核心在家族共享的 `ProofForge.Wasm.Emit`（Core → WAT）。XRPL 的 host
import 表与存储布局全部来自 `Xrpl.Host.contract`。
-/

namespace ProofForge.Wasm.Xrpl.Emit

/-- Render one XRPL program as WAT. The digest line pins the canonical IR identity. -/
def emit (p : IR.Program) : Except String String :=
  Wasm.Emit.emit Host.contract IR.extValCanon IR.extOpCanon p

end ProofForge.Wasm.Xrpl.Emit
