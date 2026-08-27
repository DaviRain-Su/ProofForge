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

def isFourLimbCarrier : Scalar → Bool
  | .uint 256 | .fixedBytes 32 => true
  | _ => false

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
