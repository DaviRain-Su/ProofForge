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

private def projectValExt : Extract.IR.ValKind → Except String Ops.ValKind
  | .near kind =>
      match kind with
      | .reserved => throw "extract/unsupported: near rejects reserved value"
      | k => pure k
  | .svm _ => throw "extract/unsupported: near rejects svm value"
  | .evm _ => throw "extract/unsupported: near rejects evm value"
  | .xrpl _ => throw "extract/unsupported: near rejects xrpl value"

private def projectOpExt
    (_projectVal : Extract.IR.Val → Except String Ops.Val) :
    Extract.IR.OpExt Extract.IR.Val → Except String (Ops.OpExt Ops.Val)
  | .near payload =>
      match payload with
      | .logUtf8 message => pure (.logUtf8 message)
      | .reserved => throw "extract/unsupported: near rejects reserved effect"
  | .svm _ => throw "extract/unsupported: near rejects svm effect"
  | .evm _ => throw "extract/unsupported: near rejects evm effect"
  | .xrpl _ => throw "extract/unsupported: near rejects xrpl effect"

/-- Static registration of the extractor-to-NEAR projection. Foreign svm/evm leaves
fail closed. NEAR host reads project through. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt where
  name := "NEAR"
  projectValExt := projectValExt
  projectOpExt := projectOpExt
  projectionError := fun method reason =>
    if reason.startsWith "extract/unsupported: near rejects" then
      s!"{reason} in {method}"
    else reason
  valArity := Ops.ValKind.arity
  opWellFormed := Ops.Op.wellFormed
  cfgDialect := Ops.cfgDialect

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

def extValCanon : Ops.ValKind → String
  | .blockIndex => "nblk"
  | .blockTimestamp => "nts"
  | .predecessor => "npred"
  | .predecessorLen => "nplen"
  | .predecessorW1 => "np1" | .predecessorW2 => "np2"
  | .predecessorW3 => "np3" | .predecessorW4 => "np4"
  | .predecessorW5 => "np5" | .predecessorW6 => "np6" | .predecessorW7 => "np7"
  | .attachedDeposit => "ndep"
  | .attachedDepositW0 => "ndep0" | .attachedDepositW1 => "ndep1"
  | .accountBalance => "nbal"
  | .accountBalanceW0 => "nbal0" | .accountBalanceW1 => "nbal1"
  | .currentAccountId => "nself"
  | .currentAccountIdLen => "nslen"
  | .currentAccountIdW1 => "ns1" | .currentAccountIdW2 => "ns2"
  | .currentAccountIdW3 => "ns3" | .currentAccountIdW4 => "ns4"
  | .currentAccountIdW5 => "ns5" | .currentAccountIdW6 => "ns6"
  | .currentAccountIdW7 => "ns7"
  | .reserved => "wext"

def extOpCanon : Ops.OpExt (Wasm.IR.Val Ops.ValKind) → String
  | .logUtf8 message => s!"nlog:{message.toUTF8.size}:{message}"
  | .reserved => "wext"

def slotNames (p : Program) : Array String :=
  Wasm.IR.slotNames p

def fromExtracted (src : Extract.IR.Program) : Except String Program :=
  Wasm.IR.fromExtracted extractRegistration src

/-- Digest domain is chain-owned (`near-raw-u64|`), deliberately different from the
SVM / EVM / XRPL domains. -/
def digestHex (p : Program) : String :=
  Wasm.IR.digestHex Host.digestDomain extValCanon extOpCanon p

end ProofForge.Wasm.Near.IR
