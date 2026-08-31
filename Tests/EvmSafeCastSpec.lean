import ProofForge
import Examples.EvmSafeCastAccumulator
import Examples.EvmSafeCastConfig

/-!
Focused safe-cast suite: host truth tables for every discarded limb, two independent application
policies, and live extraction guards proving that the low limb is bound only in the success arm of
a guard that references every discarded limb. Anvil owns deployed revert and storage-atomicity
coverage.
-/

namespace Tests.EvmSafeCastSpec

open ProofForge.Core
open ProofForge.Core.Value
open ProofForge.Evm.Sdk
open Lean Elab Command

def u64Max : UInt64 := ~~~(0 : UInt64)
def u8Limit : UInt64 := UInt64.ofNat UInt8.size
def u8Max : UInt64 := u8Limit - 1
def u16Limit : UInt64 := UInt64.ofNat UInt16.size
def u16Max : UInt64 := u16Limit - 1
def u32Limit : UInt64 := UInt64.ofNat UInt32.size
def u32Max : UInt64 := u32Limit - 1

def max128 : UInt128 := ⟨u64Max, 0⟩
def justOver128 : UInt128 := ⟨0, 1⟩
def high128 : UInt128 := ⟨9, u64Max⟩
def max8In128 : UInt128 := ⟨u8Max, 0⟩
def justOver8In128 : UInt128 := ⟨u8Limit, 0⟩
def max16In128 : UInt128 := ⟨u16Max, 0⟩
def justOver16In128 : UInt128 := ⟨u16Limit, 0⟩
def max32In128 : UInt128 := ⟨u32Max, 0⟩
def justOver32In128 : UInt128 := ⟨u32Limit, 0⟩

def max256 : UInt256 := ⟨u64Max, 0, 0, 0⟩
def justOver256 : UInt256 := ⟨0, 1, 0, 0⟩
def middle256 : UInt256 := ⟨11, 0, 1, 0⟩
def high256 : UInt256 := ⟨13, 0, 0, 1⟩
def max8In256 : UInt256 := ⟨u8Max, 0, 0, 0⟩
def justOver8In256 : UInt256 := ⟨u8Limit, 0, 0, 0⟩
def max16In256 : UInt256 := ⟨u16Max, 0, 0, 0⟩
def justOver16In256 : UInt256 := ⟨u16Limit, 0, 0, 0⟩
def max32In256 : UInt256 := ⟨u32Max, 0, 0, 0⟩
def justOver32In256 : UInt256 := ⟨u32Limit, 0, 0, 0⟩

/-! ## Reusable policy truth tables -/

#guard match SafeCast.UInt128.toUInt64 (⟨0, 0⟩ : UInt128) false with
  | .ok value => value == 0
  | _ => false
#guard match SafeCast.UInt128.toUInt64 max128 false with
  | .ok value => value == u64Max
  | _ => false
#guard match SafeCast.UInt128.toUInt64 justOver128 false with
  | .error false => true
  | _ => false
#guard match SafeCast.UInt128.toUInt64 high128 false with
  | .error false => true
  | _ => false

#guard match SafeCast.UInt128.toUInt8 max8In128 false with
  | .ok value => value.toUInt64 == u8Max
  | _ => false
#guard (match SafeCast.UInt128.toUInt8 justOver8In128 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt128.toUInt8 justOver128 false with
  | .error false => true
  | _ => false)

#guard match SafeCast.UInt128.toUInt16 max16In128 false with
  | .ok value => value.toUInt64 == u16Max
  | _ => false
#guard (match SafeCast.UInt128.toUInt16 justOver16In128 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt128.toUInt16 justOver128 false with
  | .error false => true
  | _ => false)

#guard match SafeCast.UInt128.toUInt32 max32In128 false with
  | .ok value => value.toUInt64 == u32Max
  | _ => false
#guard (match SafeCast.UInt128.toUInt32 justOver32In128 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt128.toUInt32 justOver128 false with
  | .error false => true
  | _ => false)

#guard match SafeCast.UInt256.toUInt64 (⟨0, 0, 0, 0⟩ : UInt256) false with
  | .ok value => value == 0
  | _ => false
#guard match SafeCast.UInt256.toUInt64 max256 false with
  | .ok value => value == u64Max
  | _ => false
#guard match SafeCast.UInt256.toUInt64 justOver256 false with
  | .error false => true
  | _ => false
#guard match SafeCast.UInt256.toUInt64 middle256 false with
  | .error false => true
  | _ => false
#guard match SafeCast.UInt256.toUInt64 high256 false with
  | .error false => true
  | _ => false

#guard match SafeCast.UInt256.toUInt8 max8In256 false with
  | .ok value => value.toUInt64 == u8Max
  | _ => false
#guard (match SafeCast.UInt256.toUInt8 justOver8In256 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt256.toUInt8 middle256 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt256.toUInt8 high256 false with
  | .error false => true
  | _ => false)

#guard match SafeCast.UInt256.toUInt16 max16In256 false with
  | .ok value => value.toUInt64 == u16Max
  | _ => false
#guard (match SafeCast.UInt256.toUInt16 justOver16In256 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt256.toUInt16 middle256 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt256.toUInt16 high256 false with
  | .error false => true
  | _ => false)

#guard match SafeCast.UInt256.toUInt32 max32In256 false with
  | .ok value => value.toUInt64 == u32Max
  | _ => false
#guard (match SafeCast.UInt256.toUInt32 justOver32In256 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt256.toUInt32 middle256 false with
  | .error false => true
  | _ => false) &&
  (match SafeCast.UInt256.toUInt32 high256 false with
  | .error false => true
  | _ => false)

/-! ## Permissionless checked-accumulation policy -/

open Examples.EvmSafeCastAccumulator in
#guard match add (init 0) (⟨0, 0, 0, 0⟩ : UInt256) with
  | .ok (state, result) => state.total == 0 && result == 0
  | _ => false

open Examples.EvmSafeCastAccumulator in
#guard match add (init 0) max256 with
  | .ok (state, result) => state.total == u64Max && result == u64Max
  | _ => false

open Examples.EvmSafeCastAccumulator in
#guard (match add (init 5) justOver256 with
  | .error .amountTooWide => true
  | _ => false) &&
  (match add (init 5) high256 with
  | .error .amountTooWide => true
  | _ => false)

open Examples.EvmSafeCastAccumulator in
#guard match add (init u64Max) (⟨1, 0, 0, 0⟩ : UInt256) with
  | .error .sumOverflow => true
  | _ => false

open Examples.EvmSafeCastAccumulator in
#guard (init 9).checkpoint == 1 &&
  (match setCheckpoint (init 9) max32In256 with
  | .ok (state, result) => state.total == 9 && state.checkpoint.toUInt64 == u32Max &&
      result.toUInt64 == u32Max
  | _ => false) &&
  (match setCheckpoint (init 9) (⟨0, 0, 0, 0⟩ : UInt256) with
  | .error .checkpointZero => true
  | _ => false) &&
  (match setCheckpoint (init 9) justOver32In256 with
  | .error .checkpointTooWide => true
  | _ => false)

open Examples.EvmSafeCastAccumulator in
#guard (init 9).batch == 2 &&
  (match setBatch (init 9) max16In256 with
  | .ok (state, result) => state.total == 9 && state.checkpoint == 1 &&
      state.batch.toUInt64 == u16Max && result.toUInt64 == u16Max
  | _ => false) &&
  (match setBatch (init 9) (⟨0, 0, 0, 0⟩ : UInt256) with
  | .error .batchZero => true
  | _ => false) &&
  (match setBatch (init 9) justOver16In256 with
  | .error .batchTooWide => true
  | _ => false)

open Examples.EvmSafeCastAccumulator in
#guard (init 9).mode == 3 &&
  (match setMode (init 9) max8In256 with
  | .ok (state, result) => state.total == 9 && state.checkpoint == 1 && state.batch == 2 &&
      state.mode.toUInt64 == u8Max && result.toUInt64 == u8Max
  | _ => false) &&
  (match setMode (init 9) (⟨0, 0, 0, 0⟩ : UInt256) with
  | .error .modeZero => true
  | _ => false) &&
  (match setMode (init 9) justOver8In256 with
  | .error .modeTooWide => true
  | _ => false)

/-! ## Owner-gated, nonzero replacement policy -/

def sampleAdmin : Address := ⟨1, 2, 3⟩

open Examples.EvmSafeCastConfig in
#guard (init sampleAdmin).limit == 7 &&
  (match setLimit (init sampleAdmin) max128 with
  | .ok (state, result) => state.limit == u64Max && result == u64Max
  | _ => false)

open Examples.EvmSafeCastConfig in
#guard (match setLimit (init sampleAdmin) (⟨0, 0⟩ : UInt128) with
  | .error .zero => true
  | _ => false) &&
  (match setLimit (init sampleAdmin) justOver128 with
  | .error .invalidLimit => true
  | _ => false) &&
  (match setLimit (init sampleAdmin) high128 with
  | .error .invalidLimit => true
  | _ => false)

open Examples.EvmSafeCastConfig in
#guard (init sampleAdmin).window == 3 &&
  (match setWindow (init sampleAdmin) max32In128 with
  | .ok (state, result) => state.limit == 7 && state.window.toUInt64 == u32Max &&
      result.toUInt64 == u32Max
  | _ => false) &&
  (match setWindow (init sampleAdmin) (⟨0, 0⟩ : UInt128) with
  | .error .windowZero => true
  | _ => false) &&
  (match setWindow (init sampleAdmin) justOver32In128 with
  | .error .invalidWindow => true
  | _ => false)

open Examples.EvmSafeCastConfig in
#guard (init sampleAdmin).threshold == 5 &&
  (match setThreshold (init sampleAdmin) max16In128 with
  | .ok (state, result) => state.limit == 7 && state.window == 3 &&
      state.threshold.toUInt64 == u16Max && result.toUInt64 == u16Max
  | _ => false) &&
  (match setThreshold (init sampleAdmin) (⟨0, 0⟩ : UInt128) with
  | .error .thresholdZero => true
  | _ => false) &&
  (match setThreshold (init sampleAdmin) justOver16In128 with
  | .error .invalidThreshold => true
  | _ => false)

open Examples.EvmSafeCastConfig in
#guard (init sampleAdmin).level == 6 &&
  (match setLevel (init sampleAdmin) max8In128 with
  | .ok (state, result) => state.limit == 7 && state.window == 3 && state.threshold == 5 &&
      state.level.toUInt64 == u8Max && result == u8Max
  | _ => false) &&
  (match setLevel (init sampleAdmin) (⟨0, 0⟩ : UInt128) with
  | .error .levelZero => true
  | _ => false) &&
  (match setLevel (init sampleAdmin) justOver8In128 with
  | .error .invalidLevel => true
  | _ => false)

/-! ## Extraction: all discarded limbs guard the low-limb bind -/

private partial def mentionsField (wanted : String) : ProofForge.Evm.Ops.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base name => name == wanted || mentionsField wanted base
  | .bitNot value => mentionsField wanted value
  | .bitAnd left right | .bitOr left right | .bitXor left right
  | .shiftL left right | .shiftR left right
  | .addU64 left right | .subU64 left right | .mulU64 left right
  | .divU64 left right | .modU64 left right =>
      mentionsField wanted left || mentionsField wanted right
  | .indexGet base _ index _ _ =>
      mentionsField wanted base || mentionsField wanted index
  | .select _ left right yes no =>
      mentionsField wanted left || mentionsField wanted right ||
        mentionsField wanted yes || mentionsField wanted no
  | .ext _ operands => operands.any (mentionsField wanted)

private partial def hasError (wanted : String) (ops : Array ProofForge.Evm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .errorNamed name => name == wanted
    | .ite _ _ _ yes no => hasError wanted yes || hasError wanted no
    | .forBody _ body => hasError wanted body
    | _ => false

private partial def bindsLowLimb (ops : Array ProofForge.Evm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .setLocal _ (.field (.arg 0) "w0") => true
    | .ite _ _ _ yes no => bindsLowLimb yes || bindsLowLimb no
    | .forBody _ body => bindsLowLimb body
    | _ => false

private partial def hasCheckedNarrowing (highLimbs : List String) (error : String)
    (ops : Array ProofForge.Evm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .ite _ left right yes no =>
        let checksHigh := highLimbs.all fun limb =>
          mentionsField limb left || mentionsField limb right
        let guardHidesLow := !mentionsField "w0" left && !mentionsField "w0" right
        (checksHigh && guardHidesLow && bindsLowLimb yes && hasError error no) ||
          hasCheckedNarrowing highLimbs error yes || hasCheckedNarrowing highLimbs error no
    | .forBody _ body => hasCheckedNarrowing highLimbs error body
    | _ => false

private partial def hasRangeGate (rangeLimit : UInt64) (error : String)
    (ops : Array ProofForge.Evm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .ite .lt (.field (.arg 0) "w0") (.lit limit) yes no =>
        (limit == rangeLimit && bindsLowLimb yes && hasError error no) ||
          hasRangeGate rangeLimit error yes || hasRangeGate rangeLimit error no
    | .ite _ _ _ yes no =>
        hasRangeGate rangeLimit error yes || hasRangeGate rangeLimit error no
    | .forBody _ body => hasRangeGate rangeLimit error body
    | _ => false

private partial def hasComponent (ops : Array ProofForge.Evm.IR.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .component _ => true
    | .ite _ _ _ yes no => hasComponent yes || hasComponent no
    | .forBody _ body => hasComponent body
    | _ => false

private def expectSafeCastConsumer (module : Name) (expectedSlots : List (String × Nat))
    (entry inputType error : String) (highLimbs errors : List String)
    (requireScalarOnly : Bool) (rangeLimit : Option UInt64 := none) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun slot => (slot.name, slot.width)
  unless slots == expectedSlots do
    throwError s!"{module}: safe-cast state layout diverged: {slots}"
  let some method := program.entries.find? (·.ixName == entry)
    | throwError s!"{module}: missing safe-cast entry {entry}"
  unless hasCheckedNarrowing highLimbs error method.ops do
    throwError s!"{module}.{entry}: low limb is not dominated by checks for {highLimbs}"
  if let some limit := rangeLimit then
    unless hasRangeGate limit error method.ops do
      throwError s!"{module}.{entry}: result is not dominated by the exact {limit} range gate"
  if requireScalarOnly && hasComponent method.ops then
    throwError s!"{module}.{entry}: pure safe-cast consumer unexpectedly emitted a component"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  unless yul.contains "sstore(" do
    throwError s!"{module}: successful application branch omitted its literal state write"
  unless abi.contains s!"\"type\":\"{inputType}\"" do
    throwError s!"{module}: ABI omitted checked input type {inputType}"
  for errorName in errors do
    unless abi.contains s!"\"type\":\"error\",\"name\":\"{errorName}\",\"inputs\":[]" do
      throwError s!"{module}: ABI omitted application error {errorName}()"
  let actualDigest := ProofForge.Evm.IR.digestHex program
  unless ProofForge.Evm.Registry.digestOf program.name == some actualDigest do
    throwError s!"{module}: safe-cast registry digest is stale: {actualDigest}"

elab "#pf_guard_evm_safe_cast_accumulator" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastAccumulator
    [("total", 8), ("checkpoint", 4), ("batch", 2), ("mode", 1)]
    "add" "uint256" "amountTooWide" ["w1", "w2", "w3"]
    ["amountTooWide", "sumOverflow"] true

elab "#pf_guard_evm_safe_cast_config" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastConfig
    [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8), ("limit", 8), ("window", 4),
      ("threshold", 2), ("level", 1)]
    "setLimit" "uint128" "invalidLimit" ["w1"] ["invalidLimit", "zero"] false

elab "#pf_guard_evm_safe_cast_checkpoint" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastAccumulator
    [("total", 8), ("checkpoint", 4), ("batch", 2), ("mode", 1)]
    "setCheckpoint" "uint256" "checkpointTooWide" ["w1", "w2", "w3"]
    ["checkpointTooWide", "checkpointZero"] true (some u32Limit)

elab "#pf_guard_evm_safe_cast_window" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastConfig
    [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8), ("limit", 8), ("window", 4),
      ("threshold", 2), ("level", 1)]
    "setWindow" "uint128" "invalidWindow" ["w1"] ["invalidWindow", "windowZero"] false
    (some u32Limit)

elab "#pf_guard_evm_safe_cast_batch" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastAccumulator
    [("total", 8), ("checkpoint", 4), ("batch", 2), ("mode", 1)]
    "setBatch" "uint256" "batchTooWide" ["w1", "w2", "w3"]
    ["batchTooWide", "batchZero"] true (some u16Limit)

elab "#pf_guard_evm_safe_cast_threshold" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastConfig
    [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8), ("limit", 8), ("window", 4),
      ("threshold", 2), ("level", 1)]
    "setThreshold" "uint128" "invalidThreshold" ["w1"]
    ["invalidThreshold", "thresholdZero"] false (some u16Limit)

elab "#pf_guard_evm_safe_cast_mode" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastAccumulator
    [("total", 8), ("checkpoint", 4), ("batch", 2), ("mode", 1)]
    "setMode" "uint256" "modeTooWide" ["w1", "w2", "w3"]
    ["modeTooWide", "modeZero"] true (some u8Limit)

elab "#pf_guard_evm_safe_cast_level" : command =>
  expectSafeCastConsumer `Examples.EvmSafeCastConfig
    [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8), ("limit", 8), ("window", 4),
      ("threshold", 2), ("level", 1)]
    "setLevel" "uint128" "invalidLevel" ["w1"] ["invalidLevel", "levelZero"] false
    (some u8Limit)

#pf_guard_evm_safe_cast_accumulator
#pf_guard_evm_safe_cast_config
#pf_guard_evm_safe_cast_checkpoint
#pf_guard_evm_safe_cast_window
#pf_guard_evm_safe_cast_batch
#pf_guard_evm_safe_cast_threshold
#pf_guard_evm_safe_cast_mode
#pf_guard_evm_safe_cast_level

end Tests.EvmSafeCastSpec
