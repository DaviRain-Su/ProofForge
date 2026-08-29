import Examples.Info
import Lean
import ProofForge

/-!
Focused contract and lowering guards for allocation-free SVM invocation telemetry. Runtime tests
own live stack-height, compute snapshot, and syscall execution behavior.
-/

namespace Tests.SvmTelemetrySpec

open Lean Elab Command
open ProofForge.Svm

#guard (Telemetry.Query.remainingComputeUnits).arity == 0
#guard (Telemetry.Query.stackHeight).wellFormed
#guard
  (Telemetry.Query.remainingComputeUnits).canonical (fun _ : UInt64 => "v") #[] ==
    "telemetry.remainingComputeUnits"
#guard
  (Telemetry.Call.log64 1 2 3 4 5 : Telemetry.Call UInt64).wellFormed (fun _ => true)
#guard
  (Telemetry.Call.log64 1 2 3 4 5 : Telemetry.Call UInt64).canonical toString ==
    "telemetry.log64(1,2,3,4,5)"

#pf_build Examples.Info

elab "#pf_guard_svm_telemetry" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Info with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let hasQuery (name : String) (query : Telemetry.Query) :=
    program.methods.any fun method => method.ixName == name && method.ops.any fun
      | .returnU64 (.ext (.component (.telemetry found)) #[]) => found == query
      | _ => false
  unless hasQuery "computeUnits" .remainingComputeUnits && hasQuery "stackDepth" .stackHeight do
    throwError "telemetry queries did not remain behind the generic component bridge"
  let hasCall (name : String) (predicate : Telemetry.Call Ops.Val → Bool) :=
    program.methods.any fun method => method.ixName == name && method.ops.any fun
      | .component (.telemetry call) => predicate call
      | _ => false
  unless hasCall "logUnits" (fun | .logComputeUnits => true | _ => false) &&
      hasCall "logValues" (fun
        | .log64 (.lit 1) (.lit 2) (.lit 3) (.lit 4) (.lit 5) => true
        | _ => false) do
    throwError "telemetry calls did not remain behind the generic component bridge"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "call sol_remaining_compute_units" &&
      asm.contains "call sol_get_stack_height" &&
      asm.contains "call sol_log_compute_units_" &&
      asm.contains "call sol_log_64_" do
    throwError "one or more official SVM telemetry syscall bindings are missing"

#pf_guard_svm_telemetry

end Tests.SvmTelemetrySpec
