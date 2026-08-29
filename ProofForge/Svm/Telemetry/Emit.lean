import ProofForge.Svm.Ops
import ProofForge.Svm.Telemetry

namespace ProofForge.Svm.Telemetry.Emit

structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String

def emitQuery (query : Query) (operands : Array Ops.Val) (stackOff : Nat) :
    Except String String :=
  match query, operands with
  | .remainingComputeUnits, #[] =>
      .ok s!"  call sol_remaining_compute_units\n  stxdw [r10 - {stackOff}], r0\n"
  | .stackHeight, #[] =>
      .ok s!"  call sol_get_stack_height\n  stxdw [r10 - {stackOff}], r0\n"
  | _, _ => .error "extract/ir: malformed SVM telemetry query operands"

def emitCall (context : Context) (label : String) : Call Ops.Val → Except String String
  | .logComputeUnits => return "  call sol_log_compute_units_\n"
  | .log64 first second third fourth fifth => do
      let loadFirst ← context.loadValue first 8 0 s!"{label}_first"
      let loadSecond ← context.loadValue second 16 1 s!"{label}_second"
      let loadThird ← context.loadValue third 24 2 s!"{label}_third"
      let loadFourth ← context.loadValue fourth 32 3 s!"{label}_fourth"
      let loadFifth ← context.loadValue fifth 40 4 s!"{label}_fifth"
      return loadFirst ++ loadSecond ++ loadThird ++ loadFourth ++ loadFifth ++
        "  ldxdw r1, [r10 - 8]\n" ++
        "  ldxdw r2, [r10 - 16]\n" ++
        "  ldxdw r3, [r10 - 24]\n" ++
        "  ldxdw r4, [r10 - 32]\n" ++
        "  ldxdw r5, [r10 - 40]\n" ++
        "  call sol_log_64_\n"

end ProofForge.Svm.Telemetry.Emit
