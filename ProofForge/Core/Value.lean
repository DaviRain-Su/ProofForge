import ProofForge.Attr

namespace ProofForge.Core.Value

/-!
Target-neutral source values used at contract boundaries.

The wide/fixed-byte structures contain only fixed scalar limbs. `BoundedVec` is a compiler-known
capacity carrier: Extract erases its host `Vector` to a fixed scalar frame before target code runs.
These are logical values; SVM Borsh/account geometry and EVM ABI/storage layout remain target-owned.
No host collection or native pointer may be persisted in a target artifact.
-/

/-- A 128-bit unsigned value, least-significant limb first. -/
@[pf_boundary] structure UInt128 where
  w0 : UInt64
  w1 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A 256-bit unsigned value, least-significant limb first. -/
@[pf_boundary] structure UInt256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Typed source-level result for allocation-free lexicographic policies. Applications consume the
ordering in ordinary Lean and retain ownership of their public ABI/result policy. -/
inductive LexOrder where
  | less
  | equal
  | greater
  deriving Repr, DecidableEq, Inhabited, BEq

/--
Exactly `n` logical bytes in source byte order, packed into four little-endian `UInt64` limbs.

The fixed four-limb carrier keeps source values allocation-free. Extract requires `1 ≤ n ≤ 32`;
target adapters encode only `ceil(n / 8)` limbs and own canonical padding checks for the final
partial limb. The remaining carrier bits are not persistent data.
-/
structure FixedBytes (n : Nat) where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

def FixedBytes.validSize (n : Nat) : Bool :=
  1 ≤ n && n ≤ 32

def FixedBytes.limbCount (n : Nat) : Nat :=
  (n + 7) / 8

/--
A source boundary value with a compile-time capacity and a runtime `UInt32` length.

The `Vector` exists only while Lean elaborates and extracts the source program. Target adapters
lower all `capacity` elements to fixed scalar locals and must reject `length > capacity`; no target
heap object, collection header, backing pointer, or persistent allocation survives extraction.
Ordinary `Array` remains an unsupported unbounded boundary type.
-/
structure BoundedVec (α : Type) (capacity : Nat) where
  length : UInt32
  values : Vector α capacity

/-- A bounded byte sequence with a fixed source frame. Targets bind this logical type to their
native dynamic-byte wire format; the host Vector is not a target pointer or heap object. -/
structure BoundedBytes (capacity : Nat) where
  length : UInt32
  values : Vector UInt8 capacity

/-- A bounded UTF-8 string. `Core.Value.BoundedString.wellFormed` owns UTF-8 validity;
target decoders must enforce the same contract in addition to the capacity bound. -/
structure BoundedString (capacity : Nat) where
  length : UInt32
  values : Vector UInt8 capacity

end ProofForge.Core.Value
