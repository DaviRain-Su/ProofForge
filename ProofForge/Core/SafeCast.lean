import ProofForge.Attr
import ProofForge.Core.Value

namespace ProofForge.Core.SafeCast

/-!
# Checked narrowing of allocation-free wide values

These target-neutral helpers inspect every limb and low-limb high bit discarded by the target
width, then return the caller's explicit typed error when any discarded bit is set. The narrowed
value becomes available only through the successful `Except` branch, so target SDKs can compose
narrowing with authorization, arithmetic, and state-transition policy using ordinary Lean control
flow.

There is no target Runtime leaf, operation, IR/emitter case, allocation, terminal, or state write
in this module. Extraction lowers each helper to scalar limb tests in the consuming application.
-/

/-- First UInt64 value that does not fit in UInt8. Kept at the shared policy boundary so
applications never repeat a numeric width sentinel. -/
private def uint8Limit : UInt64 := 256

/-- First UInt64 value that does not fit in UInt16. Kept at the shared policy boundary so
applications never repeat a numeric width sentinel. -/
private def uint16Limit : UInt64 := 65536

/-- First UInt64 value that does not fit in UInt32. Kept at the shared policy boundary so
applications never repeat a numeric width sentinel. -/
private def uint32Limit : UInt64 := 4294967296

namespace UInt128

/-- Narrow a two-limb UInt128 to UInt8. The high limb must be zero and the low limb must fit below
the first non-representable UInt8 value before the explicit narrowing conversion is evaluated. -/
@[pf_inline] def toUInt8 (value : Value.UInt128) (error : ε) : Except ε UInt8 :=
  if value.w1 == 0 then
    if value.w0 < uint8Limit then .ok value.w0.toUInt8 else .error error
  else
    .error error

/-- Narrow a two-limb UInt128 to UInt16. The high limb must be zero and the low limb must fit below
the first non-representable UInt16 value before the explicit narrowing conversion is evaluated. -/
@[pf_inline] def toUInt16 (value : Value.UInt128) (error : ε) : Except ε UInt16 :=
  if value.w1 == 0 then
    if value.w0 < uint16Limit then .ok value.w0.toUInt16 else .error error
  else
    .error error

/-- Narrow a two-limb UInt128 to UInt32. The high limb must be zero and the low limb must fit below
the first non-representable UInt32 value before the explicit narrowing conversion is evaluated. -/
@[pf_inline] def toUInt32 (value : Value.UInt128) (error : ε) : Except ε UInt32 :=
  if value.w1 == 0 then
    if value.w0 < uint32Limit then .ok value.w0.toUInt32 else .error error
  else
    .error error

/-- Narrow a two-limb UInt128 to UInt64. `error` is returned unless the entire discarded high limb
is zero. -/
@[pf_inline] def toUInt64 (value : Value.UInt128) (error : ε) : Except ε UInt64 :=
  if value.w1 == 0 then .ok value.w0 else .error error

end UInt128

namespace «UInt256»

/-- Narrow a four-limb UInt256 to UInt8. Every upper limb and every bit above bit 7 in `w0` is
checked before the explicit narrowing conversion is evaluated. -/
@[pf_inline] def toUInt8 (value : Value.UInt256) (error : ε) : Except ε UInt8 :=
  if (value.w1 ||| value.w2 ||| value.w3) == 0 then
    if value.w0 < uint8Limit then .ok value.w0.toUInt8 else .error error
  else
    .error error

/-- Narrow a four-limb UInt256 to UInt16. Every upper limb and every bit above bit 15 in `w0` is
checked before the explicit narrowing conversion is evaluated. -/
@[pf_inline] def toUInt16 (value : Value.UInt256) (error : ε) : Except ε UInt16 :=
  if (value.w1 ||| value.w2 ||| value.w3) == 0 then
    if value.w0 < uint16Limit then .ok value.w0.toUInt16 else .error error
  else
    .error error

/-- Narrow a four-limb UInt256 to UInt32. Every upper limb and every bit above bit 31 in `w0` is
checked before the explicit narrowing conversion is evaluated. -/
@[pf_inline] def toUInt32 (value : Value.UInt256) (error : ε) : Except ε UInt32 :=
  if (value.w1 ||| value.w2 ||| value.w3) == 0 then
    if value.w0 < uint32Limit then .ok value.w0.toUInt32 else .error error
  else
    .error error

/-- Narrow a four-limb UInt256 to UInt64. OR-ing all three discarded limbs checks every discarded
bit before the low limb can enter the successful branch. -/
@[pf_inline] def toUInt64 (value : Value.UInt256) (error : ε) : Except ε UInt64 :=
  if (value.w1 ||| value.w2 ||| value.w3) == 0 then .ok value.w0 else .error error

end «UInt256»

end ProofForge.Core.SafeCast
