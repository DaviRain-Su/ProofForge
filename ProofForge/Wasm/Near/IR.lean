import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Wasm.IR
import ProofForge.Wasm.Near.Ops
import ProofForge.Wasm.Near.Host

/-!
# NEAR target IR（薄封装）

NEAR Protocol 的 registration 实例化与家族 IR 的窄门面：程序形状、v0 子集检查
和 canonical 拼写都在家族共享的 `ProofForge.Wasm.IR` 里；本文件只钉 NEAR 的
方言类型（`Near.Ops`）、digest 域（`near-raw-u64|`）和 ext canonical 标签。
外来 svm/evm 叶子经家族约定拒绝（错误前缀 `near`）。
-/

namespace ProofForge.Wasm.Near.IR

abbrev CFG := Core.CFG.Graph Ops.ValKind Ops.OpExt
abbrev Method := Wasm.IR.Method Ops.ValKind Ops.OpExt
abbrev Program := Wasm.IR.Program Ops.ValKind Ops.OpExt

/-- Static registration of the extractor-to-NEAR projection. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt :=
  Wasm.IR.mkRegistration Host.chainName Ops.ValKind.arity Ops.cfgDialect Ops.Op.wellFormed

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

/-- v0 has no NEAR dialect extension leaves; the tag keeps the canonical spelling total. -/
def extValCanon : Ops.ValKind → String := fun _ => "wext"

def extOpCanon : Ops.OpExt (Wasm.IR.Val Ops.ValKind) → String := fun _ => "wext"

def slotNames (p : Program) : Array String :=
  Wasm.IR.slotNames p

def fromExtracted (src : Extract.IR.Program) : Except String Program :=
  Wasm.IR.fromExtracted extractRegistration src

/-- Digest domain is chain-owned (`near-raw-u64|`), deliberately different from the
SVM / EVM / XRPL domains. -/
def digestHex (p : Program) : String :=
  Wasm.IR.digestHex Host.digestDomain extValCanon extOpCanon p

end ProofForge.Wasm.Near.IR
