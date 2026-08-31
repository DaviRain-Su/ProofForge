import ProofForge.Attr
import ProofForge.Core.Value

namespace ProofForge.Core.SafeCast

/-!
# Checked narrowing of allocation-free wide values

These target-neutral helpers inspect every limb discarded by a `UInt64` result and return the
caller's explicit typed error when any discarded bit is set. The low limb becomes available only
through the successful `Except` branch, so target SDKs can compose narrowing with authorization,
arithmetic, and state-transition policy using ordinary Lean control flow.

There is no target Runtime leaf, operation, IR/emitter case, allocation, terminal, or state write
in this module. Extraction lowers each helper to scalar limb tests in the consuming application.
-/

namespace UInt128

/-- Narrow a two-limb UInt128 to UInt64. `error` is returned unless the entire discarded high limb
is zero. -/
@[pf_inline] def toUInt64 (value : Value.UInt128) (error : ε) : Except ε UInt64 :=
  if value.w1 == 0 then .ok value.w0 else .error error

end UInt128

namespace «UInt256»

/-- Narrow a four-limb UInt256 to UInt64. OR-ing all three discarded limbs checks every discarded
bit before the low limb can enter the successful branch. -/
@[pf_inline] def toUInt64 (value : Value.UInt256) (error : ε) : Except ε UInt64 :=
  if (value.w1 ||| value.w2 ||| value.w3) == 0 then .ok value.w0 else .error error

end «UInt256»

end ProofForge.Core.SafeCast
