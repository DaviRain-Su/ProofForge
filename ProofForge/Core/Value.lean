namespace ProofForge.Core.Value

/-!
Target-neutral, allocation-free source values used at contract boundaries.

These structures contain only fixed scalar limbs. They are logical values: SVM Borsh/account
geometry and EVM ABI/storage layout remain target-owned. In particular, none of these limbs is a
native pointer and no `Array`, `Map`, or heap-backed buffer may be persisted through them.
-/

/-- A 128-bit unsigned value, least-significant limb first. -/
structure UInt128 where
  w0 : UInt64
  w1 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/-- A 256-bit unsigned value, least-significant limb first. -/
structure UInt256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
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

end ProofForge.Core.Value
