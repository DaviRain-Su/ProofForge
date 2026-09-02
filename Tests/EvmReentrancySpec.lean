import ProofForge
import Examples.Evm.EvmOrderedStorage
import Examples.Evm.GuardedPayout

/-!
R5-009 focused suite: OpenZeppelin-compatible sentinels, fail-closed policy, two independent SDK
consumers, and exact ordered effect extraction. The hostile nested callback and transaction
rollback matrix is owned by `runtime-tests/evm/anvil_reentrancy.sh`.
-/

namespace Tests.EvmReentrancySpec

open ProofForge.Evm
open ProofForge.Evm.Sdk
open Lean Elab Command

#guard Reentrancy.notEntered == 1
#guard Reentrancy.entered == 2
#guard Reentrancy.canEnter Reentrancy.notEntered
#guard !Reentrancy.canEnter Reentrancy.entered
#guard !Reentrancy.canEnter 0
#guard !Reentrancy.canEnter 3
#guard Reentrancy.isEntered Reentrancy.entered
#guard !Reentrancy.isEntered Reentrancy.notEntered

private def guardHandle : Storage.Static.Handle UInt64 :=
  (Storage.Static.Layout.root.uint64 "guard").handle

#guard Reentrancy.enter guardHandle == Reentrancy.entered
#guard Reentrancy.leave guardHandle == Reentrancy.notEntered
#guard Examples.Evm.GuardedPayout.layout.wellFormed
#guard Examples.Evm.GuardedPayout.layout.matchesFlattened [("guard", 8)]
#guard Examples.Evm.EvmOrderedStorage.layout.wellFormed

private partial def calls (ops : Array IR.Op) : Array (Component.Call Ops.Val) :=
  ops.foldl (init := #[]) fun acc op =>
    match op with
    | .component call => acc.push call
    | .ite _ _ _ thenOps elseOps => acc ++ calls thenOps ++ calls elseOps
    | .forBody _ body => acc ++ calls body
    | _ => acc

private partial def hasNamedError (name : String) (ops : Array IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .errorNamed found => found == name
    | .ite _ _ _ thenOps elseOps =>
        hasNamedError name thenOps || hasNamedError name elseOps
    | .forBody _ body => hasNamedError name body
    | _ => false

private def expectConsumer
    (moduleName : Name) (entryName fieldName errorName digest : String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env moduleName with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless IR.digestHex program == digest do
    throwError s!"{moduleName} digest drifted: {IR.digestHex program}"
  let some entry := program.entries.find? (·.ixName == entryName)
    | throwError s!"{moduleName}: missing {entryName}"
  let effects := calls entry.ops
  unless effects.size == 3 do
    throwError s!"{moduleName}: expected enter/CALL/leave, got {effects.size} effects"
  match effects[0]!, effects[1]!, effects[2]! with
  | .staticStorage (.storeU64 first (.lit 2)),
      .nativeFx (.sendEth256 ..),
      .staticStorage (.storeU64 last (.lit 1)) =>
      unless first == fieldName && last == fieldName do
        throwError s!"{moduleName}: ordered lock resolved to the wrong field"
  | first, second, third =>
      throwError s!"{moduleName}: effect order drifted: {repr first}; {repr second}; {repr third}"
  unless hasNamedError errorName entry.ops do
    throwError s!"{moduleName}: missing fail-closed {errorName} terminal"
  unless !IR.hasStoreField entry.ops do
    throwError s!"{moduleName}: guard was incorrectly lowered as final State writeback"

private def expectReentrancy : CommandElabM Unit := do
  expectConsumer `Examples.Evm.GuardedPayout "payout" "guard" "reentrantCall" "359f6025f96aa432"
  expectConsumer `Examples.Evm.EvmOrderedStorage "writeAroundSend" "status" "locked" "c37f9c0a33352f4"

elab "#pf_guard_evm_reentrancy" : command => expectReentrancy

#pf_guard_evm_reentrancy

end Tests.EvmReentrancySpec
