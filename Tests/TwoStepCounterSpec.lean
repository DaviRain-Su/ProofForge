import ProofForge
import ProofForge.Evm.Commands
import Examples.Evm.TwoStepCounter

/-!
EVM-SDK-1 consumer A spec. Host guards pin the reference semantics (stubs make the owner
gate pass and address comparisons report equality); the `#pf_guard_twostep_counter` elab runs the live
extraction → EVM IR → Yul/ABI pipeline and checks the fail-closed surface. On-chain
behavior is verified by `runtime-tests/evm/anvil_twostep_counter.sh`.

Run focused:
  lake env lean Tests/TwoStepCounterSpec.lean
-/

namespace Tests.TwoStepCounterSpec

open Examples.Evm.TwoStepCounter
open ProofForge.Evm.Runtime
open ProofForge.Evm.Sdk

def sample : Addr20 := ⟨1, 2, 3⟩
def other : Addr20 := ⟨4, 5, 6⟩

#guard (init sample).owner == sample
#guard (init sample).paused == 0
#guard (init sample).count == 0
#guard ownerOf (init sample) == sample
#guard pausedOf (init sample) == 0
#guard get (init sample) == 0
#guard pendingOf (init sample) other == 0

/- Host: owner gate stub passes; bump does real checked UInt64 arithmetic. -/
#guard
  match bump (init sample) 5 with
  | .ok (st, ret) => ret == 5 && st.count == 5 && get st == 5
  | .error _ => false

#guard
  match bump (init sample) u64Max with
  | .ok (st, ret) => ret == u64Max && st.count == u64Max
  | .error _ => false

#guard
  match bump (init sample) u64Max with
  | .ok (st, _) => (match bump st 1 with | .error e => e == .overflow | .ok _ => false)
  | .error _ => false

#guard
  match pause (init sample) with
  | .ok (st, ret) => ret == 1 && st.paused == 1 && pausedOf st == 1
  | .error _ => false

/- Host: bump while paused hits the running-gate terminal (revert stub evaluates to 0). -/
#guard
  match pause (init sample) with
  | .ok (st, _) =>
      (match bump st 1 with
       | .ok (st', ret) => ret == 0 && st'.count == st.count
       | .error _ => false)
  | .error _ => false

#guard
  match unpause (init sample) with
  | .ok (st, ret) => ret == 0 && st.paused == 0
  | .error _ => false

/- Host runtime intrinsics are stubs, so ownership-policy behavior is pinned by the live IR and
    Anvil tests below rather than these executable reference guards. -/
#guard
  match acceptOwnership (init sample) with
  | .ok (st, ret) => ret == 0 && st.owner == sample
  | .error _ => false

/- Host: `Address.isZero` stub is always true, so transferOwnership takes the zero-address
    revert terminal (0) and keeps state; the explicit pending-address write is exercised on-chain. -/
#guard
  match transferOwnership (init sample) other with
  | .ok (st, ret) => ret == 0 && st.owner == sample
  | .error _ => false

#guard
  match cancelOwnership (init sample) other with
  | .ok (_, ret) => ret == 0
  | .error _ => false

#pf_evm_build Examples.Evm.TwoStepCounter

open Lean Elab Command

/-- Live extraction → IR → Yul/ABI surface check for the TwoStepCounter consumer. -/
elab "#pf_guard_twostep_counter" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Evm.TwoStepCounter with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let entryNames := program.entries.map (·.ixName)
  for name in #["transferOwnership", "cancelOwnership", "acceptOwnership", "bump",
      "pause", "unpause", "ownerOf", "pendingOf", "pausedOf", "get"] do
    unless entryNames.contains name do
      throwError s!"missing TwoStepCounter entry {name}"
  let rec storesField (fuel : Nat) (name : String)
      (ops : Array ProofForge.Evm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun op =>
        match op with
        | .storeField actual _ => actual == name
        | .ite _ _ _ thn els =>
            storesField fuel' name thn || storesField fuel' name els
        | .forBody _ body => storesField fuel' name body
        | _ => false
  let some pauseM := program.entries.find? (·.ixName == "pause")
    | throwError "missing TwoStepCounter pause"
  unless storesField 16 "paused" pauseM.ops do
    throwError "TwoStepCounter direct pause transition did not store paused"
  let some transferM := program.entries.find? (·.ixName == "transferOwnership")
    | throwError "missing TwoStepCounter transferOwnership"
  for (field, limb) in #[
      ("ownership_w0", "w0"), ("ownership_w1", "w1"), ("ownership_w2", "w2")] do
    let rec storesInputLimb (fuel : Nat) (ops : Array ProofForge.Evm.IR.Op) : Bool :=
      match fuel with
      | 0 => false
      | fuel' + 1 => ops.any fun op =>
          match op with
          | .storeField actual (.field (.arg 0) actualLimb) =>
              actual == field && actualLimb == limb
          | .ite _ _ _ thn els => storesInputLimb fuel' thn || storesInputLimb fuel' els
          | .forBody _ body => storesInputLimb fuel' body
          | _ => false
    unless storesInputLimb 16 transferM.ops do
      throwError s!"TwoStepCounter transferOwnership did not store candidate {limb} in {field}"
  let some acceptM := program.entries.find? (·.ixName == "acceptOwnership")
    | throwError "missing TwoStepCounter acceptOwnership"
  for field in #["owner_w0", "owner_w1", "owner_w2", "ownership_w0", "ownership_w1",
      "ownership_w2"] do
    unless storesField 16 field acceptM.ops do
      throwError s!"TwoStepCounter acceptOwnership did not store {field}"
  let rec storesZero (fuel : Nat) (name : String)
      (ops : Array ProofForge.Evm.IR.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 => ops.any fun op =>
        match op with
        | .storeField actual (.lit value) => actual == name && value == 0
        | .ite _ _ _ thn els => storesZero fuel' name thn || storesZero fuel' name els
        | .forBody _ body => storesZero fuel' name body
        | _ => false
  for field in #["ownership_w0", "ownership_w1", "ownership_w2"] do
    unless storesZero 16 field acceptM.ops do
      throwError s!"TwoStepCounter acceptOwnership did not clear {field}"
  let expectView (name : String) (widths : Array Nat) : CommandElabM Unit := do
    let some m := program.entries.find? (·.ixName == name)
      | throwError s!"missing TwoStepCounter view {name}"
    unless m.view && m.retWidths == widths do
      throwError s!"wrong TwoStepCounter view {name}: view={m.view} retWidths={m.retWidths}"
  expectView "ownerOf" #[20]
  expectView "pausedOf" #[1]
  -- UInt64 views leave retWidths empty (the default scalar width) under live extraction.
  for name in #["pendingOf", "get"] do
    let some m := program.entries.find? (·.ixName == name)
      | throwError s!"missing TwoStepCounter view {name}"
    unless m.view && (m.retWidths == #[] || m.retWidths == #[8]) do
      throwError s!"wrong TwoStepCounter view {name}: view={m.view} retWidths={m.retWidths}"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .error reason => throwError reason
    | .ok yul => pure yul
  unless yul.contains "revert(0, 36)" && yul.contains "revert(0, 4)" do
    throwError "TwoStepCounter yul missing Unauthorized(address)/Paused()/ZeroAddress() payloads"
  let abi := ProofForge.Evm.Emit.emitAbi program
  for name in #["\"name\":\"Unauthorized\"", "\"name\":\"Paused\"", "\"name\":\"ZeroAddress\"",
      "\"name\":\"transferOwnership\"", "\"name\":\"cancelOwnership\"",
      "\"name\":\"acceptOwnership\"", "\"name\":\"bump\"", "\"name\":\"pendingOf\""] do
    unless abi.contains name do
      throwError s!"TwoStepCounter abi missing {name}"

#pf_guard_twostep_counter

end Tests.TwoStepCounterSpec
