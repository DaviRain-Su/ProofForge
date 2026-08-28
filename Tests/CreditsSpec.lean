import ProofForge
import ProofForge.Evm.Commands
import Examples.Credits

/-!
EVM-SDK-1 consumer B spec (independent of `Tests.TwoStepCounterSpec`). Host guards pin the
reference semantics under the documented host stubs; the `#pf_guard_credits` elab runs the
live extraction → EVM IR → Yul/ABI pipeline. On-chain behavior is verified by
`runtime-tests/evm/anvil_credits.sh`.

Not wired into `Tests.lean` yet: the coordinator owns the aggregate import. Run focused:
  lake env lean Tests/CreditsSpec.lean
-/

namespace Tests.CreditsSpec

open Examples.Credits
open ProofForge.Evm.Runtime
open ProofForge.Evm.Sdk

def sample : Addr20 := ⟨1, 2, 3⟩
def other : Addr20 := ⟨4, 5, 6⟩

def seven : UInt256 := ⟨7, 0, 0, 0⟩
def zero256 : UInt256 := ⟨0, 0, 0, 0⟩

#guard (init sample).owner == sample
#guard (init sample).paused == 0
#guard (init sample).total == zero256
#guard ownerOf (init sample) == sample
#guard totalOf (init sample) == zero256
#guard creditOf (init sample) other == zero256
#guard pendingOf (init sample) other == 0

/- Host: owner gate stub passes, paused gate is real, `isZero` stub is always true, so
    grant takes the zero-address terminal (0) and keeps state. -/
#guard
  match grant (init sample) other seven with
  | .ok (st, ret) => ret == 0 && st.total == zero256
  | .error _ => false

/- Host: map gets read 0 and `evmAdd256` returns its left operand, so claim keeps total. -/
#guard
  match claim (init sample) seven with
  | .ok (st, _) => st.total == zero256
  | .error _ => false

#guard
  match pause (init sample) with
  | .ok (st, ret) => ret == 1 && st.paused == 1 && pausedOf st == 1
  | .error _ => false

/- Host: claim while paused hits the running-gate terminal (revert stub evaluates to 0). -/
#guard
  match pause (init sample) with
  | .ok (st, _) =>
      (match claim st seven with
       | .ok (st', ret) => ret == 0 && st'.total == st.total
       | .error _ => false)
  | .error _ => false

#guard
  match unpause (init sample) with
  | .ok (st, ret) => ret == 0 && st.paused == 0
  | .error _ => false

/- Host: nominations read 0, so acceptOwnership keeps the owner. -/
#guard
  match acceptOwnership (init sample) with
  | .ok (st, ret) => ret == 0 && st.owner == sample
  | .error _ => false

#pf_evm_build Examples.Credits

open Lean Elab Command

/-- Live extraction → IR → Yul/ABI surface check for the Credits consumer. -/
elab "#pf_guard_credits" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Credits with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let entryNames := program.entries.map (·.ixName)
  for name in #["transferOwnership", "acceptOwnership", "grant", "claim",
      "pause", "unpause", "ownerOf", "creditOf", "pendingOf", "totalOf", "pausedOf"] do
    unless entryNames.contains name do
      throwError s!"missing Credits entry {name}"
  let some ownerM := program.entries.find? (·.ixName == "ownerOf")
    | throwError "missing Credits ownerOf"
  unless ownerM.view && ownerM.retWidths == #[20] do
    throwError s!"wrong Credits ownerOf: view={ownerM.view} retWidths={ownerM.retWidths}"
  let some pausedM := program.entries.find? (·.ixName == "pausedOf")
    | throwError "missing Credits pausedOf"
  unless pausedM.view && pausedM.retWidths == #[1] do
    throwError s!"wrong Credits pausedOf: view={pausedM.view} retWidths={pausedM.retWidths}"
  for name in #["creditOf", "pendingOf", "totalOf"] do
    let some m := program.entries.find? (·.ixName == name)
      | throwError s!"missing Credits view {name}"
    unless m.view do
      throwError s!"Credits {name} is not a view"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .error reason => throwError reason
    | .ok yul => pure yul
  unless yul.contains "revert(0, 36)" && yul.contains "revert(0, 4)" &&
      yul.contains "revert(0, 68)" do
    throwError "Credits yul missing Unauthorized/Paused/ZeroAddress/Insufficient payloads"
  let abi := ProofForge.Evm.Emit.emitAbi program
  for name in #["\"name\":\"Unauthorized\"", "\"name\":\"Paused\"", "\"name\":\"ZeroAddress\"",
      "\"name\":\"Insufficient\"", "\"name\":\"transferOwnership\"",
      "\"name\":\"acceptOwnership\"", "\"name\":\"grant\"", "\"name\":\"claim\"",
      "\"name\":\"creditOf\"", "\"name\":\"totalOf\""] do
    unless abi.contains name do
      throwError s!"Credits abi missing {name}"

#pf_guard_credits

end Tests.CreditsSpec
