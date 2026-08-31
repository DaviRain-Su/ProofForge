import Examples.TransientWide128
import Examples.TransientWide256
import Lean
import ProofForge

/-!
Focused geometry and extraction proof for typed invocation-local UInt128/UInt256 vectors. Runtime
tests own live behavior; this spec proves the SDK erases exclusively to existing transient-vector
component operations and that every push control-flow branch contains either zero words or a
complete wide value.
-/

namespace Tests.SvmTransientWideVectorSpec

open Lean Elab Command
open ProofForge.Svm
open ProofForge.Svm.Sdk.Transient

private def v128x3 := Vector128.bounded 3
private def v128x2Alt := Vector128.boundedAlt 2
private def v256x2 := Vector256.bounded 2
private def v256EdgeAlt := Vector256.boundedAlt 1023

#guard v128x3.wellFormed
#guard v128x2Alt.wellFormed
#guard v256x2.wellFormed
#guard v256EdgeAlt.wellFormed
#guard !(Vector128.bounded 0).wellFormed
#guard !(Vector256.bounded 0).wellFormed
#guard !(Vector128.boundedAlt 2048).wellFormed
#guard !(Vector256.boundedAlt 1024).wellFormed
#guard v128x3 == { elements := 3, alternate := false }
#guard v128x2Alt == { elements := 2, alternate := true }
#guard v256EdgeAlt == { elements := 1023, alternate := true }

private partial def onlyTransientVecValue : Ops.Val → Bool
  | .field base _ | .bitNot base => onlyTransientVecValue base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      onlyTransientVecValue lhs && onlyTransientVecValue rhs
  | .indexGet base _ index _ _ =>
      onlyTransientVecValue base && onlyTransientVecValue index
  | .select _ lhs rhs thenValue elseValue =>
      onlyTransientVecValue lhs && onlyTransientVecValue rhs &&
        onlyTransientVecValue thenValue && onlyTransientVecValue elseValue
  | .ext (.component (.transientVec _)) operands => operands.all onlyTransientVecValue
  | .ext _ _ => false
  | _ => true

private partial def onlyTransientVecOps (ops : Array IR.Op) : Bool :=
  ops.all fun op =>
    let only := onlyTransientVecValue
    match op with
    | .letLocal _ value | .setLocal _ value | .forAccum _ value _
    | .storeField _ value | .okState value | .returnU64 value | .returnState value => only value
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .indexSet _ lhs rhs _ _ =>
        only lhs && only rhs
    | .ite _ lhs rhs thenOps elseOps =>
        only lhs && only rhs && onlyTransientVecOps thenOps && onlyTransientVecOps elseOps
    | .forBody _ body => onlyTransientVecOps body
    | .component (.transientVec call) => call.values.all only
    | .component _ | .invoke _ _ _ _ _ => false
    | _ => true

private partial def pushCount (ops : Array IR.Op) : Nat :=
  ops.foldl (init := 0) fun count op =>
    match op with
    | .component (.transientVec (.push _ _)) => count + 1
    | .ite _ _ _ yes no => count + pushCount yes + pushCount no
    | .forBody _ body => count + pushCount body
    | _ => count

/-- Every branch that can write payload words writes complete values; the failed preflight side has
zero pushes, so there is no partial wide-value push path. -/
private partial def wholePushBranches (arity : Nat) (ops : Array IR.Op) : Bool :=
  ops.all fun op =>
    match op with
    | .ite _ _ _ yes no =>
        pushCount yes % arity == 0 && pushCount no % arity == 0 &&
          wholePushBranches arity yes && wholePushBranches arity no
    | .forBody _ body => wholePushBranches arity body
    | _ => true

private def beginConfigs (method : IR.Method) : Array TransientVec.Config :=
  method.ops.filterMap fun
    | .component (.transientVec (.begin config)) => some config
    | _ => none

private partial def collectTransientCalls (ops : Array IR.Op) : Array String :=
  ops.foldl (init := #[]) fun calls op =>
    match op with
    | .component (.transientVec (.begin _)) => calls.push "begin"
    | .component (.transientVec (.push _ _)) => calls.push "push"
    | .component (.transientVec (.set _ _ _)) => calls.push "set"
    | .component (.transientVec (.truncate _ _)) => calls.push "truncate"
    | .component (.transientVec (.clear _)) => calls.push "clear"
    | .component (.transientVec (.finish _)) => calls.push "finish"
    | .ite _ _ _ yes no => calls ++ collectTransientCalls yes ++ collectTransientCalls no
    | .forBody _ body => calls ++ collectTransientCalls body
    | _ => calls

private def transientCalls (method : IR.Method) : Array String :=
  collectTransientCalls method.ops

private partial def hasTransientGet : Ops.Val → Bool
  | .field base _ | .bitNot base => hasTransientGet base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => hasTransientGet lhs || hasTransientGet rhs
  | .indexGet base _ index _ _ => hasTransientGet base || hasTransientGet index
  | .select _ lhs rhs thenValue elseValue =>
      hasTransientGet lhs || hasTransientGet rhs ||
        hasTransientGet thenValue || hasTransientGet elseValue
  | .ext (.component (.transientVec (.get _))) _ => true
  | .ext _ operands => operands.any hasTransientGet
  | _ => false

/-- Wide source returns materialize one queried local per logical limb. The assembly guard below
separately pins that the managed entry adapter serializes the complete logical frame. -/
private def topLevelGetLocals (method : IR.Method) : Array Nat :=
  method.ops.filterMap fun
    | .letLocal localIndex value => if hasTransientGet value then some localIndex else none
    | _ => none

#pf_build Examples.TransientWide128
#pf_build Examples.TransientWide256

elab "#pf_guard_transient_wide_vectors" : command => do
  let env ← getEnv
  let extract (moduleName : Name) : CommandElabM IR.Program := do
    let source ←
      match ProofForge.Extract.extractModuleIR env moduleName with
      | .ok source => pure source
      | .error reason => throwError reason
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason

  let wide128 ← extract `Examples.TransientWide128
  let wide256 ← extract `Examples.TransientWide256
  unless wide128.methods.all (onlyTransientVecOps ·.ops) &&
      wide256.methods.all (onlyTransientVecOps ·.ops) do
    throwError "typed wide vectors escaped the existing transientVec component bridge"
  for method in wide128.methods do
    unless wholePushBranches 2 method.ops do
      throwError s!"UInt128 method {method.ixName} contains a partial element push branch"
  for method in wide256.methods do
    unless wholePushBranches 4 method.ops do
      throwError s!"UInt256 method {method.ixName} contains a partial element push branch"

  let some exact128 := wide128.methods.find? (·.ixName == "pushExact")
    | throwError "missing TransientWide128.pushExact"
  let begins128 := beginConfigs exact128
  unless begins128.size == 1 && begins128[0]!.slot == 0 && begins128[0]!.payload == 6 &&
      pushCount exact128.ops == 6 do
    throwError "UInt128 exact-boundary geometry is not three two-word values"
  unless exact128.retCount == 2 && topLevelGetLocals exact128 == #[0, 1] do
    throwError "UInt128 typed last did not extract both queried return leaves"
  let some setGet128 := wide128.methods.find? (·.ixName == "setAndGet")
    | throwError "missing TransientWide128.setAndGet"
  let setGetLocals := topLevelGetLocals setGet128
  unless setGet128.retCount == 2 && setGetLocals.size ≥ 2 &&
      setGetLocals[setGetLocals.size - 2]! == 0 && setGetLocals[setGetLocals.size - 1]! == 1 do
    throwError "UInt128 typed get did not extract both queried return leaves"
  let some isolation := wide128.methods.find? (·.ixName == "twoSlotIsolation")
    | throwError "missing TransientWide128.twoSlotIsolation"
  let isolatedBegins := beginConfigs isolation
  unless isolatedBegins.size == 2 && isolatedBegins[0]!.slot == 0 &&
      isolatedBegins[0]!.payload == 6 && isolatedBegins[1]!.slot == 1 &&
      isolatedBegins[1]!.payload == 4 do
    throwError "UInt128 typed handles did not retain the two existing Vector64 slots"
  let some rewind128 := wide128.methods.find? (·.ixName == "rewindAndReuse")
    | throwError "missing TransientWide128.rewindAndReuse"
  let calls128 := transientCalls rewind128
  unless calls128.count "truncate" == 2 && calls128.count "clear" == 1 &&
      calls128.count "finish" == 0 do
    throwError "UInt128 drop/truncate/clear did not stay element-aligned"

  let some exact256 := wide256.methods.find? (·.ixName == "pushExact")
    | throwError "missing TransientWide256.pushExact"
  let begins256 := beginConfigs exact256
  unless begins256.size == 1 && begins256[0]!.slot == 0 && begins256[0]!.payload == 8 &&
      pushCount exact256.ops == 8 do
    throwError "UInt256 exact-boundary geometry is not two four-word values"
  let some clear256 := wide256.methods.find? (·.ixName == "clearWhenFull")
    | throwError "missing TransientWide256.clearWhenFull"
  unless (transientCalls clear256).count "clear" == 1 do
    throwError "UInt256 full policy lost its whole-vector clear"
  let some oom := wide256.methods.find? (·.ixName == "crossSlotOom")
    | throwError "missing TransientWide256.crossSlotOom"
  let oomBegins := beginConfigs oom
  unless oomBegins.size == 2 && oomBegins[0]!.slot == 1 && oomBegins[0]!.payload == 4092 &&
      oomBegins[1]!.slot == 0 && oomBegins[1]!.payload == 8 do
    throwError "UInt256 OOM evidence lost its inherited two-slot geometry"

  let asm128 ←
    match Emit.emitAsm wide128 with
    | .ok asm => pure asm
    | .error reason => throwError reason
  let asm256 ←
    match Emit.emitAsm wide256 with
    | .ok asm => pure asm
    | .error reason => throwError reason
  for asm in #[asm128, asm256] do
    unless asm.contains "transient_vec_push_room_" &&
        asm.contains "transient_vec_get_bounds_" && asm.contains "transient_vec_truncate_done_" &&
        asm.contains "lddw r0, 0x1201" && asm.contains "lddw r0, 0x1202" &&
        asm.contains "lddw r0, 0x1203" do
      throwError "typed wide-vector assembly lost inherited lifecycle or failure gates"
  unless asm128.contains "lddw r2, 16\n  call sol_set_return_data" &&
      asm256.contains "lddw r2, 32\n  call sol_set_return_data" do
    throwError "typed wide-vector assembly lost its complete 16-/32-byte return frame"

#pf_guard_transient_wide_vectors

end Tests.SvmTransientWideVectorSpec
