import ProofForge.Attr
import ProofForge.Svm.Runtime
import ProofForge.Svm.Telemetry

/-!
# Source-facing SVM telemetry

Safe allocation-free wrappers for Solana's remaining-compute, invocation-stack, and numeric
logging syscalls. Host evaluation keeps Runtime's documented stubs; extracted SVM programs lower
through one target-owned Telemetry component.
-/

namespace ProofForge.Svm.Sdk.Telemetry

@[pf_inline] def remainingComputeUnits : UInt64 :=
  ProofForge.Svm.Runtime.remainingComputeUnits

/-- Transaction-level instructions observe height 1; each nested CPI increases it by one. -/
@[pf_inline] def stackHeight : UInt64 :=
  ProofForge.Svm.Runtime.stackHeight

/-- Emit Solana's standard compute-unit diagnostic line. It does not return the remaining value. -/
@[pf_inline] def logComputeUnits : UInt64 :=
  ProofForge.Svm.Runtime.logComputeUnits

/-- Emit five `UInt64` values with Solana's allocation-free hexadecimal numeric logger. -/
@[pf_inline] def log64
    (first second third fourth fifth : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.log64 first second third fourth fifth

end ProofForge.Svm.Sdk.Telemetry
