import Examples.NearMemory
import Lean
import ProofForge

/-! Focused model, extraction, and WAT checks for the NEAR invocation arena. -/

namespace Tests.NearMemorySpec

open Lean Elab Command
open ProofForge.Wasm.Near

#guard Memory.pageBytes == 65536
#guard Memory.alignmentValid 8
#guard !Memory.alignmentValid 3
#guard Memory.alignUp 4101 8 == 4104
#guard Memory.buffer64CapacityValid 1
#guard Memory.buffer64CapacityValid 4096
#guard !Memory.buffer64CapacityValid 0
#guard !Memory.buffer64CapacityValid 4097

private def model0 : Memory.State := Memory.initial 8192 1 2

#guard model0.wellFormed
#guard model0.reset == model0
#guard
  match Memory.allocate model0 16 8 with
  | some (allocation, next) =>
      allocation.pointer == 8192 && allocation.size == 16 &&
        next.cursor == 8208 && next.pages == 1
  | none => false
#guard
  match Memory.allocate model0 60000 8 with
  | some (_, next) => next.pages == 2
  | none => false
#guard (Memory.allocate model0 (2 * Memory.pageBytes) 8).isNone
#guard (Memory.allocate model0 8 3).isNone

private def arenaStep : ProofForge.Wasm.IR.Op
    ProofForge.Wasm.Near.Ops.ValKind ProofForge.Wasm.Near.Ops.OpExt → Option String
  | .ext (.transientBuffer64Begin capacity) => some s!"begin.{capacity}"
  | .ext (.transientBuffer64Set capacity _ _) => some s!"set.{capacity}"
  | .ext (.transientBuffer64Finish capacity) => some s!"finish.{capacity}"
  | .letLocal _ (.ext (.transientBuffer64Get capacity) #[_]) => some s!"get.{capacity}"
  | .returnU64 (.ext (.transientBuffer64Get capacity) #[_]) => some s!"get.{capacity}"
  | _ => none

private def extractArenaStep : ProofForge.Extract.IR.Op → Option String
  | .ext (.near (.transientBuffer64Begin capacity)) => some s!"begin.{capacity}"
  | .ext (.near (.transientBuffer64Set capacity _ _)) => some s!"set.{capacity}"
  | .ext (.near (.transientBuffer64Finish capacity)) => some s!"finish.{capacity}"
  | .letLocal _ (.ext (.near (.transientBuffer64Get capacity)) #[_]) => some s!"get.{capacity}"
  | .returnU64 (.ext (.near (.transientBuffer64Get capacity)) #[_]) => some s!"get.{capacity}"
  | _ => none

elab "#pf_near_memory_check" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearMemory with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Wasm.Near.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let methods := #[program.initializer] ++ program.entries
  let some roundTrip := methods.find? (·.ixName == "roundTrip")
    | throwError "missing NearMemory.roundTrip"
  unless roundTrip.ops.filterMap arenaStep == #["begin.4", "set.4", "get.4"] do
    let sourceOps := (source.methods.find? (·.ixName == "roundTrip")).map
      (·.ops.filterMap extractArenaStep) |>.getD #[]
    throwError s!"roundTrip arena order mismatch: extract={repr sourceOps}, near={repr (roundTrip.ops.filterMap arenaStep)}"
  let some grow := methods.find? (·.ixName == "growAndReuse")
    | throwError "missing NearMemory.growAndReuse"
  unless grow.ops.filterMap arenaStep ==
      #["begin.4096", "finish.4096", "begin.4096", "set.4096", "get.4096"] do
    throwError s!"growAndReuse arena order mismatch: {repr (grow.ops.filterMap arenaStep)}"
  let wat ←
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  let anchors := #[
    "(global $pf_arena_cursor (mut i64)",
    "(func $pf_arena_reset",
    "(func $pf_arena_alloc",
    "i64.extend_i32_u (memory.size)",
    "memory.grow",
    "(i32.const -1)",
    "(func $pf_buffer64_begin",
    "(func $pf_buffer64_set",
    "(func $pf_buffer64_get",
    "(func $pf_buffer64_finish",
    "(call $pf_arena_reset)",
    "(then unreachable)"
  ]
  for anchor in anchors do
    unless wat.contains anchor do
      throwError s!"NEAR arena WAT missing {anchor}"
  logInfo m!"proofforge-near-memory: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_near_memory_check

end Tests.NearMemorySpec
