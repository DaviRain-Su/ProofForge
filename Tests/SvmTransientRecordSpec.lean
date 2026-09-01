import Examples.TransientLedger
import Examples.TransientOrderTape
import Lean
import ProofForge

/-!
Focused lowering and emitter guards for the source-visible invocation-local fixed-width POD
`Record64` layer. Mollusk owns live heap mutation, bounds, stale-handle, and OOM behavior; this
spec owns the compile-time geometry truth tables, slot inheritance, the record alignment of
extracted effects, and the proof that everything still lowers through the existing
`transientVec` component bridge (no new Runtime leaf, Ops/IR op, component, or emitter recipe).
-/

namespace Tests.SvmTransientRecordSpec

open Lean Elab Command
open ProofForge.Svm
open ProofForge.Svm.Sdk.Transient

/-! ## Geometry truth tables -/

private def pair8 : Record64 := Record64.bounded 2 8
private def pair4Alt : Record64 := Record64.boundedAlt 2 4
private def triple4 : Record64 := Record64.bounded 3 4
private def edgeAlt : Record64 := Record64.boundedAlt 1 4095

#guard pair8.wellFormed
#guard pair4Alt.wellFormed
#guard triple4.wellFormed
#guard edgeAlt.wellFormed
#guard !(Record64.bounded 0 8).wellFormed
#guard !(Record64.bounded 2 0).wellFormed
#guard !(Record64.bounded 1 3000000000).wellFormed
#guard !(Record64.bounded 60000 100000).wellFormed
#guard !(Record64.boundedAlt 2 3000).wellFormed
-- There is no caller-supplied payload or numeric slot: constructors derive both from two values.
#guard pair8 == { limbs := 2, records := 8, alternate := false }
#guard pair4Alt == { limbs := 2, records := 4, alternate := true }

/-! ## Slot inheritance: the reusable R3-021 two-slot identity -/

#guard pair8.payload == 16 && pair8.words == 16 && handleSlot pair8.words == 0 &&
  handlePayload pair8.words == 16
#guard pair4Alt.words == secondSlotWord 8 && handleSlot pair4Alt.words == 1 &&
  handlePayload pair4Alt.words == 8
#guard ({ capacity := pair8.words } : ProofForge.Svm.TransientVec.Config) == { capacity := 16 }
#guard ({ capacity := pair4Alt.words } : ProofForge.Svm.TransientVec.Config) ==
  { capacity := secondSlotWord 8 }
#guard ({ capacity := pair8.words } : ProofForge.Svm.TransientVec.Config).wellFormed
#guard ({ capacity := pair4Alt.words } : ProofForge.Svm.TransientVec.Config).wellFormed
#guard ({ capacity := pair4Alt.words } : ProofForge.Svm.TransientVec.Config).fixedVec.buffer.capacityBytes == 64
#guard ({ capacity := edgeAlt.words } : ProofForge.Svm.TransientVec.Config).fixedVec.buffer.capacityBytes == 32760
#guard triple4.payload == 12 && handleSlot edgeAlt.words == 1
#guard !({ capacity := 0 } : ProofForge.Svm.TransientVec.Config).wellFormed
#guard !({ capacity := 2 * handleSlotBit } : ProofForge.Svm.TransientVec.Config).wellFormed

/-! ## No new low-level op/component contract -/

/-- A consumed record count reads the underlying component length; after the preflight guard the
query materializes as one scalar local, so its position in the op sequence is exactly the
position the consumer wrote. -/
private def touchesLength : ProofForge.Svm.Ops.Val → Bool
  | .ext (.component (.transientVec (.length _))) _ => true
  | .ext _ _ => false
  | .select _ a b c d =>
      touchesLength a || touchesLength b || touchesLength c || touchesLength d
  | .divU64 l r => touchesLength l || touchesLength r
  | _ => false

private def readStep? : ProofForge.Svm.Ops.Val → Option String
  | .ext (.component (.transientVec (.get _))) _ => some "get"
  | .ext _ _ => none
  | .select _ a _ _ _ => readStep? a
  | _ => none

private def recordStep : ProofForge.Svm.IR.Op → Option String
  | .component (.transientVec (.begin _)) => some "begin"
  | .component (.transientVec (.push _ _)) => some "push"
  | .component (.transientVec (.set _ _ _)) => some "set"
  | .component (.transientVec (.truncate _ _)) => some "truncate"
  | .component (.transientVec (.clear _)) => some "clear"
  | .component (.transientVec (.finish _)) => some "finish"
  | .letLocal _ value =>
      match readStep? value with
      | some step => some step
      | none => if touchesLength value then some "count" else none
  | _ => none

private partial def recordSteps (ops : Array ProofForge.Svm.IR.Op) : Array String :=
  ops.foldl (init := #[]) fun steps op =>
    match op with
    | .ite _ _ _ yes no =>
        steps ++ recordSteps yes ++ recordSteps no
    | op =>
        match recordStep op with
        | some step => steps.push step
        | none => steps

private def recordStepsOf (method : ProofForge.Svm.IR.Method) : Array String :=
  recordSteps method.ops

private partial def pushCount (ops : Array ProofForge.Svm.IR.Op) : Nat :=
  ops.foldl (init := 0) fun count op =>
    match op with
    | .component (.transientVec (.push _ _)) => count + 1
    | .ite _ _ _ yes no => count + pushCount yes + pushCount no
    | _ => count

/-- Every control-flow branch that contains pushes contains whole records of the expected arity;
the failure branch of each SDK append contains no partial push. -/
private partial def wholePushBranches (arity : Nat) (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.all fun op =>
    match op with
    | .ite _ _ _ yes no =>
        let yesPushes := pushCount yes
        let noPushes := pushCount no
        (yesPushes == 0 || yesPushes % arity == 0) &&
          (noPushes == 0 || noPushes % arity == 0) &&
          wholePushBranches arity yes && wholePushBranches arity no
    | _ => true

private partial def onlyTransientVecOps (ops : Array ProofForge.Svm.IR.Op) : Bool :=
  ops.all fun
    | .component (.transientVec _) => true
    | .component _ => false
    | .ite _ _ _ yes no => onlyTransientVecOps yes && onlyTransientVecOps no
    | _ => true

private def onlyTransientVecComponents (program : ProofForge.Svm.IR.Program) : Bool :=
  program.methods.all fun method => onlyTransientVecOps method.ops

#pf_build Examples.TransientLedger
#pf_build Examples.TransientOrderTape

elab "#pf_guard_transient_record" : command => do
  let env ← getEnv
  let decodeProgram (ns : Lean.Name) : Except String ProofForge.Svm.IR.Program := do
    let source ← match ProofForge.Extract.extractModuleIR env ns with
      | .ok program => pure program
      | .error reason => throw reason
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throw reason

  ----------------------------------------------------------------
  -- Consumer 1: Examples.TransientLedger (2-limb records)
  let program ←
    match decodeProgram `Examples.TransientLedger with
    | .ok program => pure program
    | .error reason => throwError reason
  unless onlyTransientVecComponents program do
    throwError "record effects did not stay behind the transientVec component bridge"
  let some appendEntry := program.methods.find? (·.ixName == "appendEntry")
    | throwError "missing appendEntry method"
  unless pushCount appendEntry.ops == 2 && wholePushBranches 2 appendEntry.ops do
    throwError s!"appendEntry did not keep its two pushes behind a whole-record preflight: {recordStepsOf appendEntry}"
  let appendBegin := appendEntry.ops.filterMap fun
    | .component (.transientVec (.begin config)) => some config
    | _ => none
  unless appendBegin.size == 1 && appendBegin[0]!.slot == 0 && appendBegin[0]!.payload == 16 do
    throwError "appendEntry did not open the slot-0 16-word ledger handle"
  let some rewrite := program.methods.find? (·.ixName == "rewriteAmount")
    | throwError "missing rewriteAmount method"
  let rewriteSteps := recordStepsOf rewrite
  unless pushCount rewrite.ops == 4 && wholePushBranches 2 rewrite.ops &&
      rewriteSteps.count "set" == 1 && rewriteSteps.count "finish" == 1 do
    throwError "rewriteAmount did not keep two atomic record appends and the aligned set"
  -- record alignment of the extracted truncate/pop counts comes from count reading the
  -- component length divided by the fixed stride.
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "official Solana downward bump allocation bytes=16 align=8" &&
      asm.contains "div64" && asm.contains "transient_vec_get_bounds_" &&
      asm.contains "transient_vec_push_room_" &&
      asm.contains "lddw r0, 0x1201" && asm.contains "lddw r0, 0x1202" &&
      asm.contains "lddw r0, 0x1203" do
    throwError "record lowering lost the existing component lifecycle, alignment, or failures"

  ----------------------------------------------------------------
  -- Consumer 2: Examples.TransientOrderTape (3-limb records, two slots)
  let tapeProgram ←
    match decodeProgram `Examples.TransientOrderTape with
    | .ok program => pure program
    | .error reason => throwError reason
  unless onlyTransientVecComponents tapeProgram do
    throwError "tape effects did not stay behind the transientVec component bridge"
  let some twin := tapeProgram.methods.find? (·.ixName == "twinTapes")
    | throwError "missing twinTapes method"
  unless pushCount twin.ops == 12 && wholePushBranches 3 twin.ops do
    throwError "twinTapes did not keep four complete three-limb appends behind SDK preflights"
  let tapeBegins := twin.ops.filterMap fun
    | .component (.transientVec (.begin config)) => some config
    | _ => none
  unless tapeBegins.size == 2 && tapeBegins[0]! != tapeBegins[1]! &&
      tapeBegins[0]!.slot == 0 && tapeBegins[1]!.slot == 1 &&
      tapeBegins[0]!.fixedVec.buffer.capacityBytes == 96 &&
      tapeBegins[1]!.fixedVec.buffer.capacityBytes == 48 do
    throwError "twinTapes did not decode two disjoint same-shape record handles"
  let some overwrite := tapeProgram.methods.find? (·.ixName == "appendOverwrite")
    | throwError "missing appendOverwrite method"
  unless pushCount overwrite.ops == 15 && wholePushBranches 3 overwrite.ops do
    throwError "appendOverwrite did not keep every append record-aligned across clear/reuse"
  let some rewind := tapeProgram.methods.find? (·.ixName == "oobAfterRewind")
    | throwError "missing oobAfterRewind method"
  let rewindSteps := recordStepsOf rewind
  unless pushCount rewind.ops == 6 && wholePushBranches 3 rewind.ops &&
      rewindSteps.count "truncate" == 1 do
    throwError "oobAfterRewind did not shorten whole records before the checked read"
  let some appendRoom := tapeProgram.methods.find? (·.ixName == "appendWithRoom")
    | throwError "missing appendWithRoom method"
  unless pushCount appendRoom.ops == 6 && wholePushBranches 3 appendRoom.ops do
    throwError "appendWithRoom lost its application policy or SDK record preflight"
  -- The alternate-slot geometry rides the same erased-word identity.
  let altBegin :=
    tapeProgram.methods.find? (·.ixName == "crossSlotOom")
  match altBegin with
  | some method =>
    let begins := method.ops.filterMap fun
      | .component (.transientVec (.begin config)) => some config
      | _ => none
    unless begins.size == 2 && begins[0]!.slot == 1 && begins[1]!.slot == 0 &&
        begins[0]!.payload == 4095 && begins[1]!.payload == 3 do
      throwError "crossSlotOom did not exhaust the heap from the alternate record slot"
  | none => throwError "missing crossSlotOom method"
  let tapeAsm ←
    match ProofForge.Svm.Emit.emitAsm tapeProgram with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless tapeAsm.contains "ldxdw r9, [r10 - 2536]" && tapeAsm.contains "ldxdw r2, [r10 - 2544]" &&
      tapeAsm.contains "lddw r0, 0x1201" && tapeAsm.contains "lddw r0, 0x1202" &&
      tapeAsm.contains "lddw r0, 0x1203" do
    throwError "alternate-slot record metadata cells or failure vocabulary are missing"

#pf_guard_transient_record

end Tests.SvmTransientRecordSpec
