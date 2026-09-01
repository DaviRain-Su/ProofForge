import ProofForge

namespace Examples.NearOutput

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ marker := 1 }, 1) else .error .overflow

/-- Output-only specialized JSON scalar fixtures. These are not object methods or generic JSON. -/
@[pf_entry] def jsonU128Zero (_state : State) : UInt128 := ⟨0, 0⟩
@[pf_entry] def jsonU128Two64 (_state : State) : UInt128 := ⟨0, 1⟩
@[pf_entry] def jsonU128Two64PlusOne (_state : State) : UInt128 := ⟨1, 1⟩
@[pf_entry] def jsonU128Asymmetric (_state : State) : UInt128 := ⟨2, 1⟩
@[pf_entry] def jsonU128Max (_state : State) : UInt128 :=
  ⟨0xffffffffffffffff, 0xffffffffffffffff⟩

/-- Exact packed 0..31 byte sequence for the NEP-148 hash Base64 prerequisite. -/
@[pf_entry] def jsonBase64Hash32 (_state : State) :
    ProofForge.Wasm.Near.Runtime.Base64Hash32Result :=
  { w0 := 0x0706050403020100
    w1 := 0x0f0e0d0c0b0a0908
    w2 := 0x1716151413121110
    w3 := 0x1f1e1d1c1b1a1918 }

@[pf_entry] def jsonBase64Hash32Zero (_state : State) :
    ProofForge.Wasm.Near.Runtime.Base64Hash32Result :=
  { w0 := 0, w1 := 0, w2 := 0, w3 := 0 }

@[pf_entry] def jsonBase64Hash32Max (_state : State) :
    ProofForge.Wasm.Near.Runtime.Base64Hash32Result :=
  { w0 := 0xffffffffffffffff, w1 := 0xffffffffffffffff
    w2 := 0xffffffffffffffff, w3 := 0xffffffffffffffff }

syntax "metadataResult%(" term "," term "," term "," term "," term "," term ","
  term "," term "," term "," term "," term "," term "," term "," term "," term ","
  term "," term ")" : term

macro_rules
  | `(metadataResult%($nameLength, $nameW0, $nameW1, $symbolLength, $symbolW0,
      $iconPresent, $iconLength, $iconW0, $referencePresent, $referenceLength, $referenceW0,
      $hashPresent, $h0, $h1, $h2, $h3, $decimals)) =>
    `(({
        nameLength := $nameLength
        nameW0 := $nameW0
        nameW1 := $nameW1
        nameW2 := 0
        nameW3 := 0
        nameW4 := 0
        nameW5 := 0
        nameW6 := 0
        nameW7 := 0
        symbolLength := $symbolLength
        symbolW0 := $symbolW0
        symbolW1 := 0
        iconPresent := $iconPresent
        iconLength := $iconLength
        iconW0 := $iconW0
        iconW1 := 0
        iconW2 := 0
        iconW3 := 0
        iconW4 := 0
        iconW5 := 0
        iconW6 := 0
        iconW7 := 0
        iconW8 := 0
        iconW9 := 0
        iconW10 := 0
        iconW11 := 0
        iconW12 := 0
        iconW13 := 0
        iconW14 := 0
        iconW15 := 0
        iconW16 := 0
        iconW17 := 0
        iconW18 := 0
        iconW19 := 0
        iconW20 := 0
        iconW21 := 0
        iconW22 := 0
        iconW23 := 0
        iconW24 := 0
        iconW25 := 0
        iconW26 := 0
        iconW27 := 0
        iconW28 := 0
        iconW29 := 0
        iconW30 := 0
        iconW31 := 0
        referencePresent := $referencePresent
        referenceLength := $referenceLength
        referenceW0 := $referenceW0
        referenceW1 := 0
        referenceW2 := 0
        referenceW3 := 0
        referenceW4 := 0
        referenceW5 := 0
        referenceW6 := 0
        referenceW7 := 0
        referenceW8 := 0
        referenceW9 := 0
        referenceW10 := 0
        referenceW11 := 0
        referenceW12 := 0
        referenceW13 := 0
        referenceW14 := 0
        referenceW15 := 0
        referenceHashPresent := $hashPresent
        referenceHashW0 := $h0
        referenceHashW1 := $h1
        referenceHashW2 := $h2
        referenceHashW3 := $h3
        decimals := $decimals
      } :
      FungibleTokenMetadataResult))

/-- Diagnostic bounded NEP-148 fixtures; none exports the standard `ft_metadata` name. -/
@[pf_entry] def jsonMetadataDecimals (_state : State) (decimals : UInt64) :
    FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, decimals)

@[pf_entry] def jsonMetadataEscaped (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(10, 0x9ff0a9c3005c2241, 0x8098, 2, 0x5446, 1, 5, 0x0a6e6f6369,
    1, 6, 0x8380e8828fe5, 1, 0x0706050403020100, 0x0f0e0d0c0b0a0908,
    0x1716151413121110, 0x1f1e1d1c1b1a1918, 9)

@[pf_entry] def jsonMetadataMax (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(64, 0, 0, 16, 0, 1, 256, 0, 1, 128, 0, 1, 0xffffffffffffffff,
    0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 255)

@[pf_entry] def jsonMetadataReferenceOnly (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 10)

@[pf_entry] def jsonMetadataHashOnly (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 99)

@[pf_entry] def jsonMetadataBothEmpty (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 100)

@[pf_entry] def jsonMetadataNameLength (_state : State) (length : UInt64) :
    FungibleTokenMetadataResult :=
  metadataResult%(length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataSymbolLength (_state : State) (length : UInt64) :
    FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataIconLength (_state : State) (length : UInt64) :
    FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 1, length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataReferenceLength (_state : State) (length : UInt64) :
    FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 0, 1, length, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataPresence (_state : State) (present : UInt64) :
    FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, present, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataInactiveByte (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(1, 0x4241, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataNoneStaleHash (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataMalformedUtf8 (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(1, 0x80, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataOverlongUtf8 (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(2, 0xafc0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataSurrogateUtf8 (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(3, 0x80a0ed, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataAboveUnicodeUtf8 (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(4, 0x808090f4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataTruncatedUtf8 (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(2, 0x82e2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataNoneStaleIcon (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0)

@[pf_entry] def jsonMetadataNoneStaleReference (_state : State) : FungibleTokenMetadataResult :=
  metadataResult%(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0)

@[pf_entry]
def emptyBytes (_state : State) : BoundedBytes 8 :=
  { length := 0, values := #v[0, 0, 0, 0, 0, 0, 0, 0] }

@[pf_entry]
def staticBytes (_state : State) : BoundedBytes 8 :=
  { length := 3, values := #v[0, 1, 255, 0, 0, 0, 0, 0] }

@[pf_entry]
def staticString (_state : State) : BoundedString 8 :=
  { length := 4, values := #v[0xf0, 0x9f, 0x98, 0x80, 0, 0, 0, 0] }

@[pf_entry]
def staticValues (_state : State) : BoundedVec UInt16 4 :=
  { length := 3, values := #v[1, 513, 65535, 0] }

@[pf_entry]
def echoBytes (_state : State) (bytes : BoundedBytes 8) : BoundedBytes 8 :=
  bytes

@[pf_entry]
def echoString (_state : State) (text : BoundedString 8) : BoundedString 8 :=
  text

/-- A raw scalar can deliberately construct malformed UTF-8 for the String output guard. -/
@[pf_entry]
def stringWithByte (_state : State) (byte : UInt64) : BoundedString 8 :=
  { length := 1, values := #v[byte.toUInt8, 0, 0, 0, 0, 0, 0, 0] }

/-- The output adapter, not the source constructor, owns the runtime capacity check. -/
@[pf_entry]
def bytesWithLength (_state : State) (length : UInt64) : BoundedBytes 8 :=
  { length := length.toUInt32, values := #v[1, 2, 3, 4, 5, 6, 7, 8] }

end Examples.NearOutput
