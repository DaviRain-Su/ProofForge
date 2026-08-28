import Examples.Wide

namespace Tests.WideSpec

open Examples.Wide
open ProofForge.Evm.Runtime
open ProofForge.Core.Value

def one : UInt256 := ⟨1, 0, 0, 0⟩
def one128 : UInt128 := ⟨1, 2⟩
def bytes12 : FixedBytes 12 := ⟨0x0706050403020100, 0x0b0a0908, 0, 0⟩

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard echo (init 0) one == one
#guard echo128 (init 0) one128 == one128
#guard echoBytes12 (init 0) bytes12 == bytes12

-- Host stub does not model overflow; `evmAdd256 a b` returns `a`.
#guard add (init 0) one ⟨2, 0, 0, 0⟩ == one

-- Host comparison stubs are deliberately opaque; these guards establish the stable SDK surface.
#guard eq256 (init 0) one one
#guard lt256 (init 0) one one
#guard le256 (init 0) one one
#guard gt256 (init 0) one one
#guard ge256 (init 0) one one

#guard ProofForge.Evm.WideWord.Query.wellFormed (.compare256 .eq)
#guard ProofForge.Evm.WideWord.Query.wellFormed (.compare256 .lt)
#guard ProofForge.Evm.WideWord.Query.wellFormed (.compare256 .le)
#guard ProofForge.Evm.WideWord.Query.wellFormed (.compare256 .gt)
#guard ProofForge.Evm.WideWord.Query.wellFormed (.compare256 .ge)

private def mockContext : ProofForge.Evm.WideWord.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("", s!"x{st}", st + 1)
    fresh := fun st => (s!"v{st}", st + 1)
    rememberWide := fun st _ _ => st
    lookupWide := fun _ _ => none
    valKey := fun _ => "x"
    indent := "  " }

private def operands : Array ProofForge.Evm.Ops.Val :=
  Array.replicate 8 (.lit 0)

private def emitsComparison (comparison : ProofForge.Evm.WideWord.Comparison)
    (needle : String) : Bool :=
  match ProofForge.Evm.WideWord.Emit.emitQuery mockContext (.compare256 comparison) operands 0 with
  | .error _ => false
  | .ok (text, value, st) => text.contains needle && value == "v10" && st == 11

#guard emitsComparison .eq " := eq(v8, v9)"
#guard emitsComparison .lt " := lt(v8, v9)"
#guard emitsComparison .le " := iszero(gt(v8, v9))"
#guard emitsComparison .gt " := gt(v8, v9)"
#guard emitsComparison .ge " := iszero(lt(v8, v9))"

#guard
  match ProofForge.Evm.WideWord.Emit.emitQuery mockContext (.compare256 .eq)
      (Array.replicate 7 (.lit 0)) 0 with
  | .error reason => reason.contains "arity 7"
  | .ok _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.WideSpec
