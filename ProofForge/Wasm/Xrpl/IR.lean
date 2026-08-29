import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Wasm.IR
import ProofForge.Wasm.Xrpl.Ops
import ProofForge.Wasm.Xrpl.Host

/-!
# XRPL target IR（薄封装）

XRPL Bedrock（XLS-0101）的 registration 实例化与家族 IR 的窄门面：程序形状、
v0 子集检查和 canonical 拼写都在家族共享的 `ProofForge.Wasm.IR` 里；本文件只
钉 XRPL 的方言类型（`Xrpl.Ops`）、digest 域（经 `Xrpl.Host.contract`）和 ext
canonical 标签。外来 svm/evm 叶子经家族约定拒绝（错误前缀 `xrpl`）。
-/

namespace ProofForge.Wasm.Xrpl.IR

abbrev CFG := Core.CFG.Graph Ops.ValKind Ops.OpExt
abbrev Method := Wasm.IR.Method Ops.ValKind Ops.OpExt
abbrev Program := Wasm.IR.Program Ops.ValKind Ops.OpExt

/-- Static registration of the extractor-to-XRPL projection. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt :=
  Wasm.IR.mkRegistration Host.contract.name Ops.ValKind.arity Ops.cfgDialect Ops.Op.wellFormed

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

/-- v0 has no XRPL dialect extension leaves; the tag keeps the canonical spelling total. -/
def extValCanon : Ops.ValKind → String := fun _ => "wext"

def extOpCanon : Ops.OpExt (Wasm.IR.Val Ops.ValKind) → String := fun _ => "wext"

def slotNames (p : Program) : Array String :=
  Wasm.IR.slotNames p

def fromExtracted (src : Extract.IR.Program) : Except String Program :=
  Wasm.IR.fromExtracted extractRegistration src

/-- Digest domain is chain-owned (`xrpl-bedrock|`), deliberately different from the
SVM / EVM domains and from any future wasm-family chain. -/
def digestHex (p : Program) : String :=
  Wasm.IR.digestHex Host.contract.digestDomain extValCanon extOpCanon p

end ProofForge.Wasm.Xrpl.IR
