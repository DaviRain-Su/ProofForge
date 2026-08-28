import ProofForge

namespace Examples.RawEntry

open ProofForge.Svm.Runtime
open ProofForge.Core.Value

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

structure AggregateMeta where
  side : UInt8
  enabled : Bool

structure AggregateRequest where
  amount : UInt64
  details : AggregateMeta

/-- An ordinary Lean tagged union used to prove that Borsh variant geometry comes from the SVM
codec plan rather than one annotation per variant. -/
inductive TaggedRequest where
  | idle
  | one (value : UInt64)
  | pair (left right : UInt64)

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ dummy := 0 }, 0)
  else
    .error .rejected

@[pf_entry]
def get (_s : State) : UInt64 :=
  0

/-- A protocol-owned wire entry: `07 || small:u8 || wide:u64`. Physical account 0 must be the
current executable program and account 1 must sign. The method is deliberately independent of the
generated `State`; persistent protocol data belongs in explicit account-storage components. -/
@[pf_entry, pf_svm_raw 7 2 0]
def packed (_s : State) (small : UInt8) (wide : UInt64) : UInt64 :=
  small.toUInt64 + wide + (signerKey 1 &&& 0)

/-- A reusable variable codec probe:
`08 || side:u8 || Option<u64> || Option<u32> || Option<u32>`. Each option lowers to a presence
scalar and a value scalar; absent values are zeroed by the adapter before the method CFG runs. -/
@[pf_entry, pf_svm_raw_borsh_options 8 2 0 1 [8, 4, 4]]
def borshOptions (_s : State) (side tickPresent : UInt8) (tick : UInt64)
    (searchPresent : UInt8) (search : UInt32) (cancelPresent : UInt8)
    (cancel : UInt32) : UInt64 :=
  side.toUInt64 + tickPresent.toUInt64 + tick + 2 * searchPresent.toUInt64 +
    search.toUInt64 + 4 * cancelPresent.toUInt64 + cancel.toUInt64 + (signerKey 1 &&& 0)

/-- An effectful raw handler returning two fixed scalar leaves. The pair lowers through generic
CFG `returnU64s`; it is not a runtime allocation and adds no protocol-specific operation. -/
@[pf_entry, pf_svm_raw 9 2 0]
def boundedPair (_s : State) (left right : UInt64) :
    Except Error (State × (UInt64 × UInt64)) :=
  if left ≤ right then
    .ok (_s, (left, right))
  else
    .error .rejected

/-- A fixed-width return-codec probe. The result is the exact Borsh bytes of a one-element
`Vec<(u64, u64)>`: `length:u32 || left:u64 || right:u64`. All values remain scalar leaves. -/
@[pf_entry, pf_svm_raw_return 10 2 0 [4, 8, 8]]
def borshSingletonPair (_s : State) (left right : UInt64) :
    Except Error (State × (UInt32 × (UInt64 × UInt64))) :=
  if left ≤ right then
    .ok (_s, ((1 : UInt32), (left, right)))
  else
    .error .rejected

/-- Two exact Borsh enum shapes share instruction tag 11. The adapter validates and consumes the
variant byte; each source handler receives only its own payload shape. -/
@[pf_entry, pf_svm_raw_variant_return 11 0 2 0 [8]]
def enumSmall (_s : State) (value : UInt8) : UInt64 := value.toUInt64

@[pf_entry, pf_svm_raw_variant_return 11 1 2 0 [8]]
def enumWide (_s : State) (value : UInt64) : UInt64 := value

/-- A variant may decide at runtime whether to set a fixed-width return payload. The presence leaf
is control data and never enters the payload; no invocation-local collection is constructed. -/
@[pf_entry, pf_svm_raw_variant_optional_return 11 2 2 0 [8]]
def enumOptional (_s : State) (present : UInt8) (value : UInt64) :
    Except Error (State × (UInt8 × UInt64)) :=
  if present ≤ 1 then .ok (_s, (present, value)) else .error .rejected

/-- The shared logical `UInt128` binds to exact 16-byte little-endian Borsh without a heap value. -/
@[pf_entry, pf_svm_raw 12 2 0]
def echo128 (_s : State) (value : UInt128) : UInt128 := value

/-- A partial final limb is decoded from and returned as exactly four bytes. -/
@[pf_entry, pf_svm_raw 13 2 0]
def echoBytes12 (_s : State) (value : FixedBytes 12) : FixedBytes 12 := value

/-- Ordinary Lean records, products, and fixed vectors share one logical source schema. The SVM
adapter derives the exact source-order Borsh leaves and fixed scratch locals without a heap value
or a protocol-specific Op: `0e || request || pair || levels`. -/
@[pf_entry, pf_svm_raw 14 2 0]
def aggregate (_s : State) (request : AggregateRequest) (pair : UInt32 × UInt64)
    (levels : Vector UInt16 3) : UInt64 :=
  request.amount + request.details.side.toUInt64 +
    (if request.details.enabled then (1 : UInt64) else 0) +
    pair.1.toUInt64 + pair.2 + levels[0].toUInt64 + levels[2].toUInt64 +
    (signerKey 1 &&& 0)

/-- Ordinary `Option UInt64` binds directly to canonical Borsh `0 | 1 || payload`. The source
method receives the logical Option; no presence/value pair appears in its public signature. -/
@[pf_entry, pf_svm_raw 15 2 0]
def optionValue (_s : State) (value : Option UInt64) : UInt64 :=
  match value with
  | none => 5
  | some amount => amount + 1

/-- Constructor ordinal and branch-dependent payload lengths are derived from `TaggedRequest`.
Inactive fixed payload locals are zeroed before the ordinary Lean matcher runs. -/
@[pf_entry, pf_svm_raw 16 2 0]
def taggedValue (_s : State) (request : TaggedRequest) : UInt64 :=
  match request with
  | .idle => 3
  | .one value => value + 10
  | .pair left right => left + right

/-- A canonical Borsh `Vec<u64>` with a compiler-known capacity. The u32 length and four payload
slots become fixed scalar locals; unused slots are zero and no Vector/Array backing pointer reaches
the SVM artifact. -/
@[pf_entry, pf_svm_raw 17 2 0]
def boundedValues (_s : State) (items : BoundedVec UInt64 4) : UInt64 :=
  items.length.toUInt64 + items.values[0] + items.values[3]

/-- Canonical Borsh `Vec<u8>` uses the same u32-length wire prefix as a generic vector, but keeps
distinct source/codec identity and an eight-byte fixed local frame. -/
@[pf_entry, pf_svm_raw 18 2 0]
def boundedBytes (_s : State) (bytes : BoundedBytes 8) : UInt64 :=
  bytes.length.toUInt64 + bytes.values[0].toUInt64 + bytes.values[7].toUInt64

/-- Canonical Borsh `String` additionally validates strict UTF-8 before the method can observe the
fixed local frame. Invalid, overlong, surrogate, truncated, and out-of-range encodings fail. -/
@[pf_entry, pf_svm_raw 19 2 0]
def boundedString (_s : State) (text : BoundedString 8) : UInt64 :=
  text.length.toUInt64 + text.values[0].toUInt64 + text.values[7].toUInt64

end Examples.RawEntry
