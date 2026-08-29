import ProofForge

namespace Examples.NearBytes

open ProofForge.Core.Value

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.value

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ value := 1 }, 1) else .error .overflow

/-- Canonical Borsh `Vec<u8>` input: `u32_le(length) || active bytes`. The last source slot
demonstrates that the target decoder zeroes inactive slots before source execution. -/
@[pf_entry]
def inspectBytes (_s : State) (bytes : BoundedBytes 8) : UInt64 :=
  bytes.length.toUInt64 + bytes.values[0].toUInt64 + bytes.values[7].toUInt64

/-- Canonical Borsh `String` input has the same frame and additionally requires strict UTF-8. -/
@[pf_entry]
def inspectString (_s : State) (text : BoundedString 8) : UInt64 :=
  text.length.toUInt64 + text.values[0].toUInt64 + text.values[7].toUInt64

end Examples.NearBytes
