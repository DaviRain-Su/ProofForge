import ProofForge
import Examples.Evm.EvmStaticCounter
import Examples.Evm.EvmStaticRoster

/-!
EVM-SDK-3 roles focused suite: fixed-capacity shape, compile-time `Storage.Static` declaration
pins, and extraction-level proofs that both consumers' role entries and slots are exactly the
declared ones — with no vector entry for role storage.

Host note: the checked-runtime stubs keep `Address.eq`/`Address.isZero` host-`true`, so
host evaluation cannot test the real role decisions. Extraction pins their target form and the
focused Anvil matrices test membership, grant, full-set, and revoke semantics.
-/

namespace Tests.EvmRolesSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Set2 shape -/

#guard Roles.capacity == 2
#guard Roles.Set2.empty == ⟨Address.zero, Address.zero⟩
#guard Roles.Set2.empty.slot0 == Address.zero && Roles.Set2.empty.slot1 == Address.zero

/-! ## Empty consumer state -/

open Examples.Evm.EvmStaticCounter in
#guard (init 5 ⟨0, 0, 0⟩).operator0 == Address.zero &&
  (init 5 ⟨0, 0, 0⟩).operator1 == Address.zero

open Examples.Evm.EvmStaticRoster in
#guard (init ⟨1, 2, 3⟩).writer0 == Address.zero && (init ⟨1, 2, 3⟩).writer1 == Address.zero

/-! ## Storage.Static declaration pins for the explicit role fields -/

#guard Examples.Evm.EvmStaticCounter.declared.handle.operator0.baseSlot == 7
#guard Examples.Evm.EvmStaticCounter.declared.handle.operator0.wideLeaves? == some 3
#guard Examples.Evm.EvmStaticCounter.declared.handle.operator1.baseSlot == 10
#guard Examples.Evm.EvmStaticCounter.declared.handle.operator1.wideLeaves? == some 3
#guard Examples.Evm.EvmStaticCounter.layout.nextSlot == 13
#guard Examples.Evm.EvmStaticCounter.layout.wellFormed

#guard Examples.Evm.EvmStaticRoster.declared.handle.writer0.baseSlot == 10
#guard Examples.Evm.EvmStaticRoster.declared.handle.writer0.wideLeaves? == some 3
#guard Examples.Evm.EvmStaticRoster.declared.handle.writer1.baseSlot == 13
#guard Examples.Evm.EvmStaticRoster.declared.handle.writer1.wideLeaves? == some 3
#guard Examples.Evm.EvmStaticRoster.layout.nextSlot == 16
#guard Examples.Evm.EvmStaticRoster.layout.wellFormed

def counterRoleSlots : List (String × Nat) :=
  [("paused", 1), ("total_w0", 8), ("total_w1", 8), ("total_w2", 8), ("total_w3", 8),
    ("tally_count", 8), ("tally_window", 2),
    ("operator0_w0", 8), ("operator0_w1", 8), ("operator0_w2", 8),
    ("operator1_w0", 8), ("operator1_w1", 8), ("operator1_w2", 8)]

def rosterRoleSlots : List (String × Nat) :=
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
    ("seats_0_points", 8), ("seats_0_tier", 1),
    ("seats_1_points", 8), ("seats_1_tier", 1),
    ("seats_2_points", 8), ("seats_2_tier", 1), ("closed", 1),
    ("writer0_w0", 8), ("writer0_w1", 8), ("writer0_w2", 8),
    ("writer1_w0", 8), ("writer1_w1", 8), ("writer1_w2", 8)]

#guard Examples.Evm.EvmStaticCounter.layout.matchesFlattened counterRoleSlots
#guard Examples.Evm.EvmStaticRoster.layout.matchesFlattened rosterRoleSlots

/-! ## Extraction proof: role entries exist and slots match the declaration, with no
role-set vector entry -/

private def expectRolesLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVectors : List (String × Nat × Nat × Nat)) (expectedEntries : List String) :
    CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun s => (s.name, s.width)
  unless slots == expectedSlots do
    throwError s!"{module}: extracted static slots diverge from the declared layout: {slots}"
  let vectors := program.vectors.toList.map fun v => (v.name, v.baseSlot, v.length, v.strideSlots)
  unless vectors == expectedVectors do
    throwError s!"{module}: extracted vectors diverge (role sets must stay explicit fields): {vectors}"
  let entries := program.entries.toList.map (·.ixName)
  for entry in expectedEntries do
    unless entries.contains entry do
      throwError s!"{module}: missing extracted role entry {entry} in {entries}"
  for entry in ["operatorAt", "writerAt"] do
    if entries.contains entry then
      throwError s!"{module}: unsupported indexed Address view escaped fail-closed boundary"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let _abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  for (_, width) in expectedSlots do
    unless width == 1 || width == 2 || width == 4 || width == 8 do
      throwError s!"{module}: non-EVM leaf width survived extraction"
  unless yul.contains "sstore(" && yul.contains "sload(" do
    throwError s!"{module}: expected ordinary static slot accesses in emitted Yul"

elab "#pf_guard_evm_roles_counter" : command =>
  expectRolesLayout `Examples.Evm.EvmStaticCounter counterRoleSlots []
    ["grantOperator", "revokeOperator", "isOperator"]

elab "#pf_guard_evm_roles_roster" : command =>
  expectRolesLayout `Examples.Evm.EvmStaticRoster rosterRoleSlots [("seats", 3, 3, 2)]
    ["grantWriter", "revokeWriter", "isWriter"]

#pf_guard_evm_roles_counter
#pf_guard_evm_roles_roster

end Tests.EvmRolesSpec
