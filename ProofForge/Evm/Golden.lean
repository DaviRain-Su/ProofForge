import ProofForge.Extract.LegacyGolden
import ProofForge.Evm.IRCompat
import ProofForge.Evm.Ops
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.Golden

open ProofForge.Evm
open ProofForge.Crypto

/-- 竖切夹具：无 SVM 叶子。窄槽 / Option 双叶已开。 -/
def sources : Array Extract.Legacy.Program := #[
  ProofForge.Golden.extractedCounter,
  ProofForge.Golden.extractedPair,
  ProofForge.Golden.extractedWindow,
  ProofForge.Golden.extractedPhase,
  ProofForge.Golden.extractedFlag,
  ProofForge.Golden.extractedMaybe,
  ProofForge.Golden.extractedEvmCtx,
  ProofForge.Golden.extractedTipJar,
  ProofForge.Golden.extractedLang,
  ProofForge.Golden.extractedVault,
  ProofForge.Golden.extractedOwnable,
  ProofForge.Golden.extractedToken
]

private def u256Field (i : Nat) (limb : String) : Ops.Val :=
  .field (.arg i) limb

private def arith256Val (op limb a b : Nat) : Ops.Val :=
  .ext (.arith256 op limb) #[
    u256Field a "w0", u256Field a "w1", u256Field a "w2", u256Field a "w3",
    u256Field b "w0", u256Field b "w1", u256Field b "w2", u256Field b "w3"
  ]

private def return256 (mk : Nat → Ops.Val) : Array IR.Op :=
  #[.returnU64 (mk 0), .returnU64 (mk 1), .returnU64 (mk 2), .returnU64 (mk 3)]

private def view256 (ix : String) (paramCount : Nat) (widths : Array Nat)
    (ops : Array IR.Op) : IR.Method :=
  let widths := if widths.size == paramCount then widths else Array.replicate paramCount 8
  {
    kind := .get
    name := s!"Examples.Wide.{ix}"
    ixName := ix
    selector := Keccak.selectorOfWidths ix widths
    paramCount
    paramWidths := widths
    retWidths := #[32]
    retCount := 4
    ops
    view := true
  }

/-- Live extract of `Examples.Wide`; Legacy IR has no `arith256` leaf. -/
def extractedWide : IR.Program :=
  let ctor : IR.Method := {
    kind := .init
    name := "Examples.Wide.init"
    ixName := "initialize"
    paramCount := 1
    paramWidths := #[8]
    ops := #[.returnState (.lit 0)]
  }
  let touch : IR.Method := {
    kind := .increment
    name := "Examples.Wide.touch"
    ixName := "touch"
    selector := Keccak.selectorOfWidths "touch" #[]
    ops := #[
      .ite .ne (.lit 0) (.lit 1) #[.okState (.lit 0)] #[.errorOverflow]
    ]
  }
  let get : IR.Method := {
    kind := .get
    name := "Examples.Wide.get"
    ixName := "get"
    selector := Keccak.selectorOfWidths "get" #[]
    ops := #[.returnU64 (.lit 0)]
    view := true
  }
  {
    name := "Wide"
    slots := #[{ name := "dummy", index := 0, width := 8 }]
    constructor := ctor
    entries := #[
      touch,
      view256 "add" 2 #[32, 32] (return256 fun limb => arith256Val 0 limb 0 1),
      view256 "echo" 1 #[32] (return256 fun limb =>
        u256Field 0 (match limb with | 0 => "w0" | 1 => "w1" | 2 => "w2" | _ => "w3")),
      get,
      view256 "mul" 2 #[32, 32] (return256 fun limb => arith256Val 2 limb 0 1),
      view256 "sub" 2 #[32, 32] (return256 fun limb => arith256Val 1 limb 0 1)
    ]
  }

def programs : Array IR.Program :=
  (sources.filterMap fun src =>
    match IR.fromProgram src with
    | .ok p => some p
    | .error _ => none).push extractedWide

def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map IR.digestHex

end ProofForge.Evm.Golden
