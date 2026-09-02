import ProofForge

namespace Examples.Evm.EvmBounded
open ProofForge.Core.Value

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ dummy := 1 }, 1) else .error .rejected

/-- A standard-ABI `uint64[]` whose source representation remains a fixed five-word frame:
runtime length followed by four compile-time element slots. -/
@[pf_entry]
def boundedValues (_s : State) (items : BoundedVec UInt64 4) : UInt64 :=
  items.length.toUInt64 + items.values[0] + items.values[3]

/-- Static and bounded-dynamic parameters can share one canonical ABI head. Each dynamic offset is
the exact end of the preceding head/tail; inactive source slots stay zero. -/
@[pf_entry]
def combine (_s : State) (base : UInt32) (left : BoundedVec UInt64 2) (enabled : Bool)
    (right : BoundedVec UInt16 3) : UInt64 :=
  base.toUInt64 + left.length.toUInt64 + left.values[1] +
    (if enabled then (1 : UInt64) else 0) + right.length.toUInt64 +
    right.values[2].toUInt64

/-- Standard ABI `bytes` is decoded from a packed dynamic tail into an allocation-free fixed byte
frame. Inactive slots are zero before source execution. -/
@[pf_entry]
def boundedBytes (_s : State) (bytes : BoundedBytes 8) : UInt64 :=
  bytes.length.toUInt64 + bytes.values[0].toUInt64 + bytes.values[7].toUInt64

/-- Standard ABI `string` has the same packed geometry as bytes but requires strict UTF-8 before
source execution. -/
@[pf_entry]
def boundedString (_s : State) (text : BoundedString 8) : UInt64 :=
  text.length.toUInt64 + text.values[0].toUInt64 + text.values[7].toUInt64

/-- A bounded vector result uses an output-only standard-ABI plan. The fixed five-word source
frame is encoded as the canonical `uint16[]` active prefix. -/
@[pf_entry]
def echoBoundedValues (_s : State) (items : BoundedVec UInt16 4) : BoundedVec UInt16 4 := items

/-- Wide one-ABI-word dynamic return: each `UInt128` element expands to two source limbs and is
repacked into a single `uint128` ABI word at the publication boundary. -/
@[pf_entry]
def echoBoundedWide (_s : State) (items : BoundedVec UInt128 2) : BoundedVec UInt128 2 := items

/-- Constructed static-product dynamic return: each element is two one-limb ABI words
`(uint64,uint16)`. Nested dynamics remain fail closed. -/
@[pf_entry]
def echoBoundedPairs (_s : State) (items : BoundedVec (UInt64 × UInt16) 2) :
    BoundedVec (UInt64 × UInt16) 2 := items

/-- Tagged-in-array: each element is Tagged Tuple v1 `(bool,uint64)` for `Option UInt64`.
Absent elements require a zero payload; nested tagged/dynamic children stay fail closed. -/
@[pf_entry]
def echoBoundedOptions (_s : State) (items : BoundedVec (Option UInt64) 2) :
    BoundedVec (Option UInt64) 2 := items

/-- Payload enum used for tagged-in-array coverage. Constructors map to Tagged Tuple v1
`(uint8,uint64,uint64)` with zero inactive lanes (idle/one/pair). -/
inductive TaggedSlot where
  | idle
  | one (value : UInt64)
  | pair (left right : UInt64)

/-- Tagged-in-array enums: each element is Tagged Tuple v1 `(uint8,uint64,uint64)`. -/
@[pf_entry]
def echoBoundedEnums (_s : State) (items : BoundedVec TaggedSlot 2) :
    BoundedVec TaggedSlot 2 := items

@[pf_entry]
def echoBoundedBytes (_s : State) (bytes : BoundedBytes 8) : BoundedBytes 8 := bytes

@[pf_entry]
def echoBoundedString (_s : State) (text : BoundedString 8) : BoundedString 8 := text

/-- Arbitrary scalar bytes may construct a String source frame. The output codec must reject
malformed UTF-8 before publishing ABI returndata, even though no String input decoder ran. -/
@[pf_entry]
def makeBoundedString (_s : State) (length : UInt32)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : BoundedString 8 :=
  { length, values := #v[b0, b1, b2, b3, b4, b5, b6, b7] }

/-- Allocation-free equality observes only the canonical active byte prefixes. -/
@[pf_entry]
def bytesEqual (_s : State) (left right : BoundedBytes 4) : Bool :=
  left.equals right

/-- ABI strings are strictly validated before ordinary source-level byte equality. -/
@[pf_entry]
def stringsEqual (_s : State) (left right : BoundedString 4) : Bool :=
  left.equals right

/-- The application exposes one Bool policy while Core retains the typed three-way ordering. -/
@[pf_entry]
def bytesLess (_s : State) (left right : BoundedBytes 4) : Bool :=
  left.isLexLess right

/-- ABI UTF-8 gates precede the shared unsigned active-byte ordering policy. -/
@[pf_entry]
def stringsLess (_s : State) (left right : BoundedString 4) : Bool :=
  left.isLexLess right

end Examples.Evm.EvmBounded