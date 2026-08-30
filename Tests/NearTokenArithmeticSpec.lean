import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.NearTokenArithmetic

/-! Lossless little-endian u128 checked predicates and modular carry/borrow limbs. -/

open Lean Elab Command

#guard ProofForge.Wasm.Near.Ops.ValKind.arity .nearTokenAddOk == 4
#guard ProofForge.Wasm.Near.Ops.ValKind.arity .nearTokenAddW1 == 4
#guard ProofForge.Wasm.Near.Ops.ValKind.arity .nearTokenSubOk == 4
#guard ProofForge.Wasm.Near.Ops.ValKind.arity .nearTokenSubW1 == 4

private partial def nearTokenValKinds : ProofForge.Extract.IR.Val → Array String
  | .ext (.near kind) operands =>
      (if operands.size == 4 then #[ProofForge.Wasm.Near.IR.extValCanon kind] else #[]) ++
        operands.flatMap nearTokenValKinds
  | .field base _ | .bitNot base => nearTokenValKinds base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      nearTokenValKinds lhs ++ nearTokenValKinds rhs
  | .indexGet base _ index _ _ => nearTokenValKinds base ++ nearTokenValKinds index
  | .select _ lhs rhs thn els => nearTokenValKinds lhs ++ nearTokenValKinds rhs ++
      nearTokenValKinds thn ++ nearTokenValKinds els
  | .ext _ operands => operands.flatMap nearTokenValKinds
  | _ => #[]

private partial def nearTokenKinds : Array ProofForge.Extract.IR.Op → Array String
  | ops => ops.foldl (init := #[]) fun kinds op =>
      kinds ++ match op with
      | .returnU64 value => nearTokenValKinds value
      | .ite _ lhs rhs thn els => nearTokenValKinds lhs ++ nearTokenValKinds rhs ++
          nearTokenKinds thn ++ nearTokenKinds els
      | _ => #[]

elab "#pf_guard_near_token_arithmetic" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.NearTokenArithmetic none with
    | .ok source => pure source
    | .error reason => throwError reason
  let kinds := source.methods.foldl (init := #[]) fun acc method => acc ++ nearTokenKinds method.ops
  for expected in #["nu128.add.ok", "nu128.add.w0", "nu128.add.w1",
      "nu128.sub.ok", "nu128.sub.w0", "nu128.sub.w1"] do
    unless kinds.contains expected do
      throwError s!"missing extracted {expected}: {kinds}"
  let program ←
    match ProofForge.Wasm.Near.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let wat ←
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok wat => pure wat
    | .error reason => throwError reason
  for anchor in #[
      "(func (export \"addCarryOk\")", "(func (export \"addOverflowOk\")",
      "(func (export \"subBorrowOk\")", "(func (export \"subUnderflowOk\")",
      "i64.add", "i64.sub", "i64.lt_u", "i64.gt_u", "i64.ge_u",
      "i64.extend_i32_u"] do
    unless wat.contains anchor do
      throwError s!"NEAR token arithmetic WAT missing {anchor}\n{wat}"
  logInfo m!"proofforge-near-token-arithmetic: digest = {ProofForge.Wasm.Near.IR.digestHex program}"

#pf_guard_near_token_arithmetic
#pf_near_build Examples.NearTokenArithmetic

#guard ProofForge.Wasm.Near.Registry.digestOf "NearTokenArithmetic" ==
  some "4257ab75e505d1f6"
