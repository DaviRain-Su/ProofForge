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

private def projectValExt : Extract.IR.ValKind → Except String Ops.ValKind
  | .xrpl kind =>
      match kind with
      | .reserved => throw "extract/unsupported: xrpl rejects reserved value"
      | k => pure k
  | .svm _ => throw "extract/unsupported: xrpl rejects svm value"
  | .evm _ => throw "extract/unsupported: xrpl rejects evm value"

private def projectOpExt
    (_projectVal : Extract.IR.Val → Except String Ops.Val) :
    Extract.IR.OpExt Extract.IR.Val → Except String (Ops.OpExt Ops.Val)
  | .xrpl .reserved => throw "extract/unsupported: xrpl rejects reserved effect"
  | .svm _ => throw "extract/unsupported: xrpl rejects svm effect"
  | .evm _ => throw "extract/unsupported: xrpl rejects evm effect"

/-- Static registration of the extractor-to-XRPL projection. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt :=
  Wasm.IR.mkRegistration Host.contract.name Ops.ValKind.arity Ops.cfgDialect Ops.Op.wellFormed
    projectValExt projectOpExt

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

def extValCanon : Ops.ValKind → String
  | .reserved => "wext"
  | .callerW0 => "xc0" | .callerW1 => "xc1" | .callerW2 => "xc2"
  | .selfW0 => "xs0" | .selfW1 => "xs1" | .selfW2 => "xs2"
  | .ledgerSqn => "xsqn"
  | .parentTime => "xtime"
  | .parentHashW0 => "xhash0"
  | .baseFee => "xfee"
  | .sha512HalfLit seed => s!"xsha.{seed}"
  | .callerBalanceDrops => "xbal"
  | .callerSequence => "xseq"
  | .callerFlags => "xflags"
  | .callerOwnerCount => "xownc"
  | .txSequence => "xtseq"
  | .txFeeDrops => "xtfee"
  | .accountLitW0 hex => s!"xacc0.{hex}"
  | .accountLitW1 hex => s!"xacc1.{hex}"
  | .accountLitW2 hex => s!"xacc2.{hex}"
  | .txFlags => "xtflags"
  | .litBalanceDrops hex => s!"xlitbal.{hex}"

def extOpCanon : Ops.OpExt (Wasm.IR.Val Ops.ValKind) → String
  | .reserved => "wext"

def slotNames (p : Program) : Array String :=
  Wasm.IR.slotNames p

def fromExtracted (src : Extract.IR.Program) : Except String Program :=
  Wasm.IR.fromExtracted extractRegistration src

/-- Digest domain is chain-owned (`xrpl-bedrock|`), deliberately different from the
SVM / EVM domains and from any future wasm-family chain. -/
def digestHex (p : Program) : String :=
  Wasm.IR.digestHex Host.contract.digestDomain extValCanon extOpCanon p

end ProofForge.Wasm.Xrpl.IR
