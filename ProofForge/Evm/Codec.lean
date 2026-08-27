import ProofForge.Core.Codec

namespace ProofForge.Evm.Codec

open ProofForge.Core.Codec

/-- Decode the legacy width sentinels at one compatibility boundary.  New EVM
code consumes `Scalar` and must not interpret these numbers itself. -/
def scalarOfLegacyWidth : Nat → Except String Scalar
  | 1 => pure .uint8
  | 2 => pure .uint16
  | 4 => pure .uint32
  | 8 => pure .uint64
  | 20 => pure .address20
  | 32 => pure .uint256
  | 33 => pure .bytes32
  | width => throw s!"evm/codec: unsupported legacy width {width}"

def legacyWidthOfScalar : Scalar → Except String Nat
  | .boolean => throw "evm/codec: boolean has no legacy width"
  | .uint 8 => pure 1
  | .uint 16 => pure 2
  | .uint 32 => pure 4
  | .uint 64 => pure 8
  | .uint 256 => pure 32
  | .address 20 => pure 20
  | .fixedBytes 32 => pure 33
  | type => throw s!"evm/codec: no legacy width for {repr type}"

def abiType : Scalar → Except String String
  | .boolean => pure "bool"
  | .uint bits =>
      if Scalar.isWellFormed (.uint bits) then pure s!"uint{bits}"
      else throw s!"evm/codec: invalid uint width {bits}"
  | .address 20 => pure "address"
  | .address bytes => throw s!"evm/codec: address must be 20 bytes, got {bytes}"
  | .fixedBytes bytes =>
      if 1 ≤ bytes && bytes ≤ 32 then pure s!"bytes{bytes}"
      else throw s!"evm/codec: invalid fixed-bytes width {bytes}"

private partial def abiTypeOfSchemaAt : Schema → Except String String
  | .unit => throw "evm/codec: unit has no canonical ABI parameter type"
  | .scalar type => abiType type
  | .tuple items => do
      if items.isEmpty then throw "evm/codec: empty tuple is not supported"
      let types ← items.mapM abiTypeOfSchemaAt
      return "(" ++ String.intercalate "," types.toList ++ ")"
  | .record _ fields => do
      if fields.isEmpty then throw "evm/codec: empty record is not supported"
      let types ← fields.mapM fun field => abiTypeOfSchemaAt field.2
      return "(" ++ String.intercalate "," types.toList ++ ")"
  | .fixedArray length element => do
      if length == 0 then throw "evm/codec: zero-length fixed array is not supported"
      return (← abiTypeOfSchemaAt element) ++ "[" ++ toString length ++ "]"
  | .enumeration .. => throw "evm/codec: enum ABI tags require an explicit target policy"
  | .option _ => throw "evm/codec: option ABI tags require an explicit target policy"
  | .boundedArray .. => throw "evm/codec: bounded arrays require an explicit dynamic ABI policy"

/-- Canonical Solidity ABI spelling for one logical parameter or result. Nested records and Lean
products are tuples; literal vectors are fixed arrays. This target-owned function deliberately
does not expose ABI words or padding to Core. -/
def abiTypeOfSchema (schema : Schema) : Except String String := do
  let _ ← validate schema
  abiTypeOfSchemaAt schema

/-- One ABI word per statically present scalar leaf. Wide source values still occupy one ABI word;
their fixed source limbs are unpacked only when an operation projects `w0`..`w3`. -/
def staticAbiLeaves (schema : Schema) : Except String (Array StaticLeaf) := do
  let _ ← abiTypeOfSchema schema
  staticLeaves schema

inductive WordGuard where
  | boolean
  | unsignedMax (bits : Nat)
  | address160
  | fixedBytesLeftPadded (bytes : Nat)
  | fullWord
  deriving Repr, BEq, Inhabited

def wordGuard : Scalar → Except String WordGuard
  | .boolean => pure .boolean
  | .uint 256 => pure .fullWord
  | .uint bits =>
      if Scalar.isWellFormed (.uint bits) then pure (.unsignedMax bits)
      else throw s!"evm/codec: invalid uint width {bits}"
  | .address 20 => pure .address160
  | .address bytes => throw s!"evm/codec: address must be 20 bytes, got {bytes}"
  | .fixedBytes 32 => pure .fullWord
  | .fixedBytes bytes =>
      if 1 ≤ bytes && bytes < 32 then pure (.fixedBytesLeftPadded bytes)
      else throw s!"evm/codec: invalid fixed-bytes width {bytes}"

def isWideIntegerCarrier : Scalar → Bool
  | .uint bits => 64 < bits && bits ≤ 256 && bits % 64 == 0
  | _ => false

def isFixedBytesCarrier : Scalar → Bool
  | .fixedBytes bytes => 1 ≤ bytes && bytes ≤ 32
  | _ => false

def limbCount : Scalar → Nat
  | .uint bits => (bits + 63) / 64
  | .address bytes | .fixedBytes bytes => (bytes + 7) / 8
  | .boolean => 1

def isAddressCarrier : Scalar → Bool
  | .address 20 => true
  | _ => false

def isNarrowIntegerCarrier : Scalar → Bool
  | .boolean => true
  | .uint bits => bits ≤ 64
  | _ => false

/-- EVM word mask for a physical byte width. Storage layout and calldata
guards share this target-owned rendering primitive. -/
private def ffBytes : Nat → String
  | 0 => ""
  | count + 1 => "ff" ++ ffBytes count

def byteMask (bytes : Nat) : String :=
  if bytes == 0 || bytes > 32 then "0" else "0x" ++ ffBytes bytes

end ProofForge.Evm.Codec
