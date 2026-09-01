import ProofForge.Attr
import ProofForge.Core.Value

/-!
# Target-neutral bounded collections

Pure source operations over `Core.Value.BoundedVec`. The host `Vector` is an elaboration and
extraction carrier only: every operation preserves the compile-time capacity and changes at most
the runtime length and fixed element frame. Target adapters remain responsible for choosing Borsh,
ABI, account, memory, or storage geometry.

These helpers are `pf_inline` source combinators, not VM effects. They must lower to the existing
bounded comparisons and vector index reads/writes; adding another vector operation here must not
add a Vector-specific Core Op, target IR constructor, or Emit recipe.
-/

namespace ProofForge.Core.Value.BoundedVec

/-- The largest capacity representable by the `UInt32` length field. Target codec budgets normally
impose a much smaller limit before extraction. -/
@[pf_inline] def capacityIsRepresentable (n : Nat) : Bool :=
  n < UInt32.size

/-- The runtime length is canonical for this compile-time capacity. -/
@[pf_inline] def wellFormed {α : Type} {n : Nat} (items : BoundedVec α n) : Bool :=
  capacityIsRepresentable n && items.length.toNat ≤ n

/-- Compile-time capacity exposed as a scalar source value. The codec/profile gate rejects
capacities outside its much smaller resource ceiling before target lowering. -/
@[pf_inline] def capacity {α : Type} {n : Nat} (items : BoundedVec α n) : UInt64 :=
  let _ := items
  UInt64.ofNat n

/-- Runtime number of active elements. -/
@[pf_inline] def size {α : Type} {n : Nat} (items : BoundedVec α n) : UInt64 :=
  items.length.toUInt64

@[pf_inline] def isEmpty {α : Type} {n : Nat} (items : BoundedVec α n) : Bool :=
  items.length == 0

/-- Invalid over-capacity frames are treated as full. Canonical target decoders reject such a
frame before the source method runs. -/
@[pf_inline] def isFull {α : Type} {n : Nat} (items : BoundedVec α n) : Bool :=
  n ≤ items.length.toNat

/-- Checked active-prefix lookup. Inactive fixed-frame slots are never observable through this
API, even though target adapters may keep them zeroed as scratch locals. -/
@[pf_inline] def get? {α : Type} {n : Nat} (items : BoundedVec α n) (index : UInt64) : Option α :=
  if hcapacity : index.toNat < n then
    if index < items.length.toUInt64 then some (items.values[index.toNat]'hcapacity) else none
  else
    none

/-- Checked lookup with an explicit allocation-free fallback. -/
@[pf_inline] def getD {α : Type} {n : Nat}
    (items : BoundedVec α n) (index : UInt64) (fallback : α) : α :=
  if hcapacity : index.toNat < n then
    if index < items.length.toUInt64 then (items.values[index.toNat]'hcapacity) else fallback
  else
    fallback

/-- Replace one active element without changing the runtime length. -/
@[pf_inline] def set? {α : Type} {n : Nat}
    (items : BoundedVec α n) (index : UInt64) (value : α) : Option (BoundedVec α n) :=
  if hcapacity : index.toNat < n then
    if index < items.length.toUInt64 then
      some { items with values := items.values.set index.toNat value hcapacity }
    else
      none
  else
    none

/-- Append to the fixed frame. Full or malformed frames return `none` without changing any value.
The returned index is zero-based, matching Rust `Vec` indexing and both target boundary codecs. -/
@[pf_inline] def push? {α : Type} {n : Nat} (items : BoundedVec α n) (value : α) :
    Option (BoundedVec α n × UInt64) :=
  let index := items.length.toNat
  if _hcapacity : n < UInt32.size then
    if hslot : index < n then
      let next : BoundedVec α n :=
        { length := items.length + 1
          values := items.values.set index value hslot }
      some (next, items.length.toUInt64)
    else
      none
  else
    none

/-- Remove the last active element. The inactive backing slot is intentionally left unchanged:
logical length owns reachability, while a target may choose to zero storage as a separate policy. -/
@[pf_inline] def pop? {α : Type} {n : Nat}
    (items : BoundedVec α n) : Option (BoundedVec α n × α) :=
  if items.length = 0 then
    none
  else
    let index := items.length.toNat - 1
    if hcapacity : index < n then
      some ({ items with length := items.length - 1 }, (items.values[index]'hcapacity))
    else
      none

/-- Drop every logical element without allocating or rewriting the fixed backing frame. -/
@[pf_inline] def clear {α : Type} {n : Nat} (items : BoundedVec α n) : BoundedVec α n :=
  { items with length := 0 }

end ProofForge.Core.Value.BoundedVec

/-!
## Bounded bytes and UTF-8 strings

Both carriers reuse `BoundedVec UInt8` logical operations. They remain distinct source types so
SVM can select Borsh `Vec<u8>`/`String` and EVM can select standard ABI `bytes`/`string` without
pretending a generic vector determines either wire format.
-/

namespace ProofForge.Core.Value.BoundedBytes

private def asVec (bytes : BoundedBytes capacity) : BoundedVec UInt8 capacity :=
  { length := bytes.length, values := bytes.values }

private def ofVec (bytes : BoundedVec UInt8 capacity) : BoundedBytes capacity :=
  { length := bytes.length, values := bytes.values }

def wellFormed (bytes : BoundedBytes capacity) : Bool := bytes.asVec.wellFormed
def capacity {n : Nat} (bytes : BoundedBytes n) : UInt64 := bytes.asVec.capacity
def size {n : Nat} (bytes : BoundedBytes n) : UInt64 := bytes.asVec.size
def isEmpty {n : Nat} (bytes : BoundedBytes n) : Bool := bytes.asVec.isEmpty
def isFull {n : Nat} (bytes : BoundedBytes n) : Bool := bytes.asVec.isFull
def get? {n : Nat} (bytes : BoundedBytes n) (index : UInt64) : Option UInt8 := bytes.asVec.get? index
def getD {n : Nat} (bytes : BoundedBytes n) (index : UInt64) (fallback : UInt8) : UInt8 :=
  bytes.asVec.getD index fallback

def set? {n : Nat} (bytes : BoundedBytes n) (index : UInt64) (value : UInt8) :
    Option (BoundedBytes n) :=
  (bytes.asVec.set? index value).map ofVec

def push? {n : Nat} (bytes : BoundedBytes n) (value : UInt8) :
    Option (BoundedBytes n × UInt64) :=
  (bytes.asVec.push? value).map fun result => (ofVec result.1, result.2)

def pop? {n : Nat} (bytes : BoundedBytes n) : Option (BoundedBytes n × UInt8) :=
  (bytes.asVec.pop?).map fun result => (ofVec result.1, result.2)

def clear {n : Nat} (bytes : BoundedBytes n) : BoundedBytes n :=
  ofVec bytes.asVec.clear

/-- Active-prefix byte equality for one bounded byte type. Both frames must be canonical, inactive
backing bytes are ignored, and the scan is bounded by compile-time capacity rather than input. -/
@[pf_inline] def equals {capacity : Nat}
    (left right : BoundedBytes capacity) : Bool :=
  if UInt64.ofNat capacity < left.length.toUInt64 then false
  else if UInt64.ofNat capacity < right.length.toUInt64 then false
  else if left.length != right.length then false
  else Id.run do
    let mut equal : UInt64 := 1
    let mut visited : UInt64 := 0
    for i in [0:capacity] do
      let byteEqual : UInt64 := if left.values[i]! == right.values[i]! then 1 else 0
      equal := equal &&& if UInt64.ofNat i < left.length.toUInt64 then byteEqual else 1
      visited := visited + 1
    return equal == 1 && visited == UInt64.ofNat capacity

/-- One allocation-free static product scan shared by index/contains/prefix/suffix. `startMode` is
a private lowering detail: zero accepts any in-range candidate, one only start zero, and two only
the unique final start. The result uses private position+1 encoding so zero remains "not found". -/
@[pf_inline] private def searchIndexUnchecked {capacity needleCapacity : Nat}
    (haystack : BoundedBytes capacity) (needle : BoundedBytes needleCapacity)
    (startMode : UInt64) : UInt64 := Id.run do
  let haystackLength := haystack.length.toUInt64
  let needleLength := needle.length.toUInt64
  let lastStart := haystackLength - needleLength
  -- Bit zero records the current candidate; higher bits hold the first matched position+1.
  let mut scanState : UInt64 := 1
  let mut visited : UInt64 := 0
  for flat in [0:capacity * needleCapacity] do
    let start := flat / needleCapacity
    let offset := flat % needleCapacity
    let activeStart :=
      if startMode == 0 then UInt64.ofNat start ≤ lastStart
      else if startMode == 1 then start == 0
      else UInt64.ofNat start == lastStart
    let activeOffset := UInt64.ofNat offset < needleLength
    let byteEqual : UInt64 :=
      if activeStart && activeOffset then
        if haystack.values[start + offset]! == needle.values[offset]! then 1 else 0
      else 1
    let found := scanState >>> 1
    let candidate := scanState &&& 1
    let matched := candidate &&& byteEqual
    let candidateComplete := offset + 1 == needleCapacity
    let nextFound :=
      if found == 0 && candidateComplete && activeStart && matched == 1 then
        UInt64.ofNat start + 1
      else found
    let nextCandidate := if candidateComplete then 1 else matched
    scanState := nextCandidate ||| (nextFound <<< 1)
    visited := visited + 1
  return if visited == UInt64.ofNat (capacity * needleCapacity) then scanState >>> 1 else 0

@[pf_inline] private def searchUnchecked {capacity needleCapacity : Nat}
    (haystack : BoundedBytes capacity) (needle : BoundedBytes needleCapacity)
    (startMode : UInt64) : Bool :=
  let position := searchIndexUnchecked haystack needle startMode
  position != 0

/-- Allocation-free active-prefix substring search. Both frames must be canonical. Empty needles
match every canonical haystack; otherwise neither inactive tail can affect the shared static scan. -/
@[pf_inline] def contains {capacity needleCapacity : Nat}
    (haystack : BoundedBytes capacity) (needle : BoundedBytes needleCapacity) : Bool :=
  let haystackLength := haystack.length.toUInt64
  let needleLength := needle.length.toUInt64
  if UInt64.ofNat capacity < haystackLength then false
  else if UInt64.ofNat needleCapacity < needleLength then false
  else if needleLength == 0 then true
  else if haystackLength < needleLength then false
  else searchUnchecked haystack needle 0

/-- Return the first zero-based active-prefix byte position of a canonical needle. Empty needles
match at zero, invalid frames and longer needles return `none`, and inactive tails are ignored. -/
@[pf_inline] def findIndex? {capacity needleCapacity : Nat}
    (haystack : BoundedBytes capacity) (needle : BoundedBytes needleCapacity) : Option UInt64 :=
  let haystackLength := haystack.length.toUInt64
  let needleLength := needle.length.toUInt64
  if UInt64.ofNat capacity < haystackLength then none
  else if UInt64.ofNat needleCapacity < needleLength then none
  else if needleLength == 0 then some 0
  else if haystackLength < needleLength then none
  else
    let position := searchIndexUnchecked haystack needle 0
    if position == 0 then none else some (position - 1)

/-- Rust-style active-prefix test with independent fixed carrier capacities. Invalid frames and a
needle longer than the haystack fail closed; an empty canonical needle is a prefix. -/
@[pf_inline] def startsWith {capacity needleCapacity : Nat}
    (haystack : BoundedBytes capacity) (needle : BoundedBytes needleCapacity) : Bool :=
  let haystackLength := haystack.length.toUInt64
  let needleLength := needle.length.toUInt64
  if UInt64.ofNat capacity < haystackLength then false
  else if UInt64.ofNat needleCapacity < needleLength then false
  else if needleLength == 0 then true
  else if haystackLength < needleLength then false
  else searchUnchecked haystack needle 1

/-- Rust-style active-suffix test. The checked subtraction identifies the only possible suffix
start, then the same allocation-free bounded matcher owns byte comparison. -/
@[pf_inline] def endsWith {capacity needleCapacity : Nat}
    (haystack : BoundedBytes capacity) (needle : BoundedBytes needleCapacity) : Bool :=
  let haystackLength := haystack.length.toUInt64
  let needleLength := needle.length.toUInt64
  if UInt64.ofNat capacity < haystackLength then false
  else if UInt64.ofNat needleCapacity < needleLength then false
  else if needleLength == 0 then true
  else if haystackLength < needleLength then false
  else searchUnchecked haystack needle 2

/-- One compile-time bounded unsigned-byte scan. `ordering` is a private lowering detail:
zero remains undecided/equal, one means left is smaller, and two means right is smaller. The public
API exposes only Bool or `LexOrder`, never this scalar state. -/
@[pf_inline] private def lexLessUnchecked {capacity : Nat}
    (left right : BoundedBytes capacity) : Bool := Id.run do
  let leftLength := left.length.toUInt64
  let rightLength := right.length.toUInt64
  let commonLength := if leftLength < rightLength then leftLength else rightLength
  let mut ordering : UInt64 := 0
  let mut visited : UInt64 := 0
  for i in [0:capacity] do
    let active := UInt64.ofNat i < commonLength
    let undecided := ordering == 0
    let leftByte := left.values[i]!
    let rightByte := right.values[i]!
    ordering :=
      if active && undecided then
        if leftByte < rightByte then 1
        else if rightByte < leftByte then 2
        else 0
      else ordering
    visited := visited + 1
  return visited == UInt64.ofNat capacity &&
    (ordering == 1 || (ordering == 0 && leftLength < rightLength))

/-- Checked strict lexicographic ordering for contract policy. Invalid frames are never ordered,
and inactive fixed-frame slots cannot affect the result. -/
@[pf_inline] def isLexLess {capacity : Nat}
    (left right : BoundedBytes capacity) : Bool :=
  if UInt64.ofNat capacity < left.length.toUInt64 then false
  else if UInt64.ofNat capacity < right.length.toUInt64 then false
  else lexLessUnchecked left right

/-- Typed three-way source-level ordering. The first differing unsigned active byte decides; if one
active prefix exhausts first, the shorter value sorts first. Invalid frames return `none`. -/
@[pf_inline] def compareLex? {capacity : Nat}
    (left right : BoundedBytes capacity) : Option LexOrder :=
  if UInt64.ofNat capacity < left.length.toUInt64 then none
  else if UInt64.ofNat capacity < right.length.toUInt64 then none
  else if lexLessUnchecked left right then some .less
  else if lexLessUnchecked right left then some .greater
  else some .equal

private def isContinuation (byte : Nat) : Bool := 0x80 ≤ byte && byte ≤ 0xbf

/-- Strict Unicode scalar UTF-8 validation over the active prefix. It rejects truncated,
overlong, surrogate, and greater-than-U+10FFFF encodings. -/
def isValidUtf8 {n : Nat} (bytes : BoundedBytes n) : Bool := Id.run do
  unless bytes.wellFormed do return false
  let length := bytes.length.toNat
  let mut index := 0
  let mut valid := true
  for _ in [0:n] do
    if valid && index < length then
      let b0 := (bytes.getD (UInt64.ofNat index) 0).toNat
      if b0 ≤ 0x7f then
        index := index + 1
      else if 0xc2 ≤ b0 && b0 ≤ 0xdf then
        if index + 2 ≤ length then
          let b1 := (bytes.getD (UInt64.ofNat (index + 1)) 0).toNat
          if isContinuation b1 then index := index + 2 else valid := false
        else valid := false
      else if 0xe0 ≤ b0 && b0 ≤ 0xef then
        if index + 3 ≤ length then
          let b1 := (bytes.getD (UInt64.ofNat (index + 1)) 0).toNat
          let b2 := (bytes.getD (UInt64.ofNat (index + 2)) 0).toNat
          let firstContinuation :=
            if b0 == 0xe0 then 0xa0 ≤ b1 && b1 ≤ 0xbf
            else if b0 == 0xed then 0x80 ≤ b1 && b1 ≤ 0x9f
            else isContinuation b1
          if firstContinuation && isContinuation b2 then index := index + 3
          else valid := false
        else valid := false
      else if 0xf0 ≤ b0 && b0 ≤ 0xf4 then
        if index + 4 ≤ length then
          let b1 := (bytes.getD (UInt64.ofNat (index + 1)) 0).toNat
          let b2 := (bytes.getD (UInt64.ofNat (index + 2)) 0).toNat
          let b3 := (bytes.getD (UInt64.ofNat (index + 3)) 0).toNat
          let firstContinuation :=
            if b0 == 0xf0 then 0x90 ≤ b1 && b1 ≤ 0xbf
            else if b0 == 0xf4 then 0x80 ≤ b1 && b1 ≤ 0x8f
            else isContinuation b1
          if firstContinuation && isContinuation b2 && isContinuation b3 then
            index := index + 4
          else valid := false
        else valid := false
      else
        valid := false
  return valid && index == length

end ProofForge.Core.Value.BoundedBytes

namespace ProofForge.Core.Value.BoundedString

@[pf_inline] def asBytes (text : BoundedString capacity) : BoundedBytes capacity :=
  { length := text.length, values := text.values }

def wellFormed (text : BoundedString capacity) : Bool := text.asBytes.isValidUtf8
def size (text : BoundedString capacity) : UInt64 := text.length.toUInt64
def isEmpty (text : BoundedString capacity) : Bool := text.length == 0
def getByte? (text : BoundedString capacity) (index : UInt64) : Option UInt8 :=
  text.asBytes.get? index

/-- Unicode-string equality is active-prefix byte equality. As with Rust `String`, validity is a
carrier invariant enforced by checked constructors and boundary codecs, not work repeated by each
comparison. No normalization or locale policy is inferred. -/
@[pf_inline] def equals {capacity : Nat}
    (left right : BoundedString capacity) : Bool :=
  left.asBytes.equals right.asBytes

/-- Rust-style `String::contains` semantics over the validated UTF-8 byte carrier. The needle is a
byte substring rather than a Unicode-scalar or locale-aware pattern, and the shared bounded scan
performs no allocation. -/
@[pf_inline] def contains {capacity needleCapacity : Nat}
    (text : BoundedString capacity) (needle : BoundedString needleCapacity) : Bool :=
  text.asBytes.contains needle.asBytes

/-- First UTF-8 byte offset of an exact validated String needle. -/
@[pf_inline] def findIndex? {capacity needleCapacity : Nat}
    (text : BoundedString capacity) (needle : BoundedString needleCapacity) : Option UInt64 :=
  text.asBytes.findIndex? needle.asBytes

/-- Exact UTF-8 byte-prefix policy over the validated String carrier. -/
@[pf_inline] def startsWith {capacity needleCapacity : Nat}
    (text : BoundedString capacity) (prefixValue : BoundedString needleCapacity) : Bool :=
  text.asBytes.startsWith prefixValue.asBytes

/-- Exact UTF-8 byte-suffix policy over the validated String carrier. -/
@[pf_inline] def endsWith {capacity needleCapacity : Nat}
    (text : BoundedString capacity) (suffix : BoundedString needleCapacity) : Bool :=
  text.asBytes.endsWith suffix.asBytes

/-- Strict UTF-8 is a carrier/boundary invariant, so String ordering reuses the one unsigned-byte
lexicographic policy without normalization or locale-dependent collation. -/
@[pf_inline] def compareLex? {capacity : Nat}
    (left right : BoundedString capacity) : Option LexOrder :=
  left.asBytes.compareLex? right.asBytes

/-- Checked strict ordering shares the byte implementation and returns false for malformed frames. -/
@[pf_inline] def isLexLess {capacity : Nat}
    (left right : BoundedString capacity) : Bool :=
  left.asBytes.isLexLess right.asBytes

/-- Checked conversion keeps the byte and string carriers physically independent in source while
reusing one strict UTF-8 contract. -/
def ofBytes? (bytes : BoundedBytes capacity) : Option (BoundedString capacity) :=
  if bytes.isValidUtf8 then some { length := bytes.length, values := bytes.values } else none

end ProofForge.Core.Value.BoundedString

/-!
## Bounded key/value semantics

`BoundedMap` is the target-neutral *logical* contract for an enumerable finite map. It deliberately
uses the shared fixed-frame vector rather than Lean/Std hash maps. SVM account storage and EVM
hashed/static storage may implement these semantics with different physical layouts; this type is
never permission to persist its host representation or a pointer.
-/

namespace ProofForge.Core.Collections

open ProofForge.Core.Value

structure Entry (κ υ : Type) where
  key : κ
  value : υ
  deriving Repr, BEq

/-- An unordered finite map with compile-time capacity and explicit active-prefix length. -/
structure BoundedMap (κ υ : Type) (capacity : Nat) where
  entries : BoundedVec (Entry κ υ) capacity

inductive ExistingValuePolicy where
  | reject
  | replace
  deriving Repr, BEq, Inhabited

namespace BoundedMap

def size (map : BoundedMap κ υ capacity) : UInt64 :=
  map.entries.size

def isEmpty (map : BoundedMap κ υ capacity) : Bool :=
  map.entries.isEmpty

def isFull (map : BoundedMap κ υ capacity) : Bool :=
  map.entries.isFull

/-- Zero-based active-prefix position of `key`. The scan bound is the compile-time capacity, not
runtime input. -/
def findIndex? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) : Option UInt64 :=
  if !map.entries.wellFormed then none
  else
    Id.run do
      for i in [0:capacity] do
        if UInt64.ofNat i < map.entries.length.toUInt64 then
          if let some entry := map.entries.get? (UInt64.ofNat i) then
            if entry.key == key then return some (UInt64.ofNat i)
      return none

def contains [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) : Bool :=
  (map.findIndex? key).isSome

def get? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) : Option υ := do
  let index ← map.findIndex? key
  let entry ← map.entries.get? index
  return entry.value

/-- Insert a missing key, or apply the typed policy to an existing key. `none` means
duplicate-under-reject policy, full capacity, or a malformed input frame; no input value is mutated. -/
def insert? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) (value : υ)
    (existing : ExistingValuePolicy := .reject) : Option (BoundedMap κ υ capacity) :=
  match map.findIndex? key with
  | some index =>
      match existing with
      | .reject => none
      | .replace =>
          match map.entries.set? index { key, value } with
          | some entries => some { entries }
          | none => none
  | none =>
      match map.entries.push? { key, value } with
      | some (entries, _) => some { entries }
      | none => none

/-- Remove one key by moving the final active entry into its slot, then shrinking length. Ordering
is intentionally not part of the shared map contract. Returns the removed value with the new map. -/
def remove? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) :
    Option (BoundedMap κ υ capacity × υ) := do
  let index ← map.findIndex? key
  let removed ← map.entries.get? index
  let lastIndex := map.entries.size - 1
  let last ← map.entries.get? lastIndex
  let moved ← map.entries.set? index last
  let (entries, _) ← moved.pop?
  return ({ entries }, removed.value)

def clear (map : BoundedMap κ υ capacity) : BoundedMap κ υ capacity :=
  { entries := map.entries.clear }

/-- Canonical frames contain no duplicate active keys. This is a bounded semantic check, not a
target hash-table validator. -/
def wellFormed [BEq κ] (map : BoundedMap κ υ capacity) : Bool :=
  if !map.entries.wellFormed then false
  else Id.run do
    for i in [0:capacity] do
      if UInt64.ofNat i < map.entries.length.toUInt64 then
        let some left := map.entries.get? (UInt64.ofNat i) | return false
        for j in [i + 1:capacity] do
          if UInt64.ofNat j < map.entries.length.toUInt64 then
            let some right := map.entries.get? (UInt64.ofNat j) | return false
            if left.key == right.key then return false
    return true

end BoundedMap

/-- A finite set is the map contract with unit payload. It inherits the same explicit capacity,
active-prefix scan bound, and unordered removal policy. -/
abbrev BoundedSet (α : Type) (capacity : Nat) := BoundedMap α Unit capacity

namespace BoundedSet

def contains [BEq α] (set : BoundedSet α capacity) (value : α) : Bool :=
  BoundedMap.contains set value

def insert? [BEq α] (set : BoundedSet α capacity) (value : α) :
    Option (BoundedSet α capacity) :=
  BoundedMap.insert? set value ()

def remove? [BEq α] (set : BoundedSet α capacity) (value : α) :
    Option (BoundedSet α capacity) :=
  (BoundedMap.remove? set value).map (·.1)

/-! The operations below are the target-neutral position+1 policy for persistent enumerable-set
bindings. SVM account storage and EVM storage own different physical layouts, while both use `0`
as absent position evidence and swap-remove over a bounded active prefix. -/

@[pf_inline] def countWellFormed (capacity count : UInt64) : Bool :=
  count ≤ capacity

@[pf_inline] def isEmptyCount (count : UInt64) : Bool :=
  count == 0

@[pf_inline] def isFullCount (capacity count : UInt64) : Bool :=
  capacity ≤ count

@[pf_inline] def absentPosition (position : UInt64) : Bool :=
  position == 0

@[pf_inline] def positionLive (position count : UInt64) : Bool :=
  0 < position && position ≤ count

@[pf_inline] def forgedPosition (position count : UInt64) : Bool :=
  position != 0 && !positionLive position count

@[pf_inline] def isPresentAt (position count stored key : UInt64) : Bool :=
  positionLive position count && stored == key

@[pf_inline] def insertIndex (count : UInt64) : UInt64 := count
@[pf_inline] def insertPosition (count : UInt64) : UInt64 := count + 1
@[pf_inline] def insertedCount (count : UInt64) : UInt64 := count + 1

@[pf_inline] def canInsertAt (capacity count position : UInt64) : Bool :=
  countWellFormed capacity count && absentPosition position && !isFullCount capacity count

@[pf_inline] def indexOfPosition (position : UInt64) : UInt64 := position - 1
@[pf_inline] def lastIndex (count : UInt64) : UInt64 := count - 1
@[pf_inline] def movesLast (position count : UInt64) : Bool := position != count
@[pf_inline] def movedPosition (position : UInt64) : UInt64 := position
@[pf_inline] def removedCount (count : UInt64) : UInt64 := count - 1

@[pf_inline] def canRemoveAt (capacity count position : UInt64) : Bool :=
  countWellFormed capacity count && positionLive position count

@[pf_inline] def canValueAt (capacity count index : UInt64) : Bool :=
  countWellFormed capacity count && index < count

end BoundedSet

/-! ## FIFO semantics -/

/-- Fixed-frame FIFO ring. `head` and `length` are scalar indexes; inactive slots are unreachable
and may retain stale values. -/
structure BoundedQueue (α : Type) (capacity : Nat) where
  head : UInt32
  length : UInt32
  values : Vector α capacity

namespace BoundedQueue

def wellFormed (queue : BoundedQueue α capacity) : Bool :=
  0 < capacity && capacity < UInt32.size && queue.length.toNat ≤ capacity &&
    (if queue.length = 0 then queue.head = 0 else queue.head.toNat < capacity)

def size (queue : BoundedQueue α capacity) : UInt64 :=
  queue.length.toUInt64

def isEmpty (queue : BoundedQueue α capacity) : Bool :=
  queue.length == 0

def isFull (queue : BoundedQueue α capacity) : Bool :=
  capacity ≤ queue.length.toNat

private def physicalIndex? (queue : BoundedQueue α capacity) (offset : UInt64) : Option Nat :=
  if !queue.wellFormed || queue.length.toUInt64 ≤ offset then none
  else
    let index := (queue.head.toNat + offset.toNat) % capacity
    if index < capacity then some index else none

/-- Read a zero-based logical offset from the front. -/
def get? (queue : BoundedQueue α capacity) (offset : UInt64) : Option α := do
  let index ← queue.physicalIndex? offset
  if h : index < capacity then return queue.values[index]'h else none

def peek? (queue : BoundedQueue α capacity) : Option α :=
  queue.get? 0

/-- Append at the ring tail. Full or malformed queues return `none`. -/
def push? (queue : BoundedQueue α capacity) (value : α) : Option (BoundedQueue α capacity) :=
  if !queue.wellFormed || queue.isFull then none
  else
    let tail := (queue.head.toNat + queue.length.toNat) % capacity
    if h : tail < capacity then
      some { queue with
        length := queue.length + 1
        values := queue.values.set tail value h }
    else
      none

/-- Remove the front value and advance the ring head. An emptied queue returns to canonical
`head = length = 0`; the old payload remains unreachable. -/
def pop? (queue : BoundedQueue α capacity) : Option (BoundedQueue α capacity × α) := do
  if !queue.wellFormed || queue.isEmpty then none else pure ()
  let value ← queue.peek?
  let remaining := queue.length - 1
  let nextHead := if remaining = 0 then 0 else UInt32.ofNat ((queue.head.toNat + 1) % capacity)
  return ({ queue with head := nextHead, length := remaining }, value)

def clear (queue : BoundedQueue α capacity) : BoundedQueue α capacity :=
  { queue with head := 0, length := 0 }

end BoundedQueue

/-! ## Fixed bit-set semantics -/

@[pf_inline] def bitSetWordCount (capacity : Nat) : Nat :=
  (capacity + 63) / 64

/-- A compile-time-capacity bit set packed into fixed `UInt64` words. There is no runtime length,
allocation, or collection header. -/
structure BoundedBitSet (capacity : Nat) where
  words : Vector UInt64 (bitSetWordCount capacity)

namespace BoundedBitSet

/-! The packed-word operations below are target-neutral policy. SVM account storage and EVM
storage slots bind them independently; neither physical layout belongs in this namespace. -/

@[pf_inline] def inRange (capacity index : UInt64) : Bool :=
  index < capacity

@[pf_inline] def wordIndexOf (index : UInt64) : UInt64 :=
  index / 64

@[pf_inline] def maskOf (index : UInt64) : UInt64 :=
  (1 : UInt64) <<< (index % 64)

@[pf_inline] def containsOf (word index : UInt64) : Bool :=
  word &&& maskOf index != 0

@[pf_inline] def insertOf (word index : UInt64) : UInt64 :=
  word ||| maskOf index

@[pf_inline] def removeOf (word index : UInt64) : UInt64 :=
  word &&& ~~~(maskOf index)

@[pf_inline] def toggleOf (word index : UInt64) : UInt64 :=
  word ^^^ maskOf index

def empty (capacity : Nat) : BoundedBitSet capacity :=
  { words := Vector.replicate (bitSetWordCount capacity) 0 }

def contains (set : BoundedBitSet capacity) (index : UInt64) : Bool :=
  if index.toNat < capacity then
    let wordIndex := index.toNat / 64
    if h : wordIndex < bitSetWordCount capacity then
      containsOf (set.words[wordIndex]'h) index
    else
      false
  else
    false

/-- Set or clear one in-range bit. Out-of-range indexes return `none` and cannot alias a lower
word through modular arithmetic. -/
def update? (set : BoundedBitSet capacity) (index : UInt64) (present : Bool) :
    Option (BoundedBitSet capacity) :=
  if index.toNat < capacity then
    let wordIndex := index.toNat / 64
    if h : wordIndex < bitSetWordCount capacity then
      let word := set.words[wordIndex]'h
      let next := if present then insertOf word index else removeOf word index
      some { words := set.words.set wordIndex next h }
    else
      none
  else
    none

def insert? (set : BoundedBitSet capacity) (index : UInt64) : Option (BoundedBitSet capacity) :=
  set.update? index true

def remove? (set : BoundedBitSet capacity) (index : UInt64) : Option (BoundedBitSet capacity) :=
  set.update? index false

def clear (_set : BoundedBitSet capacity) : BoundedBitSet capacity :=
  empty capacity

end BoundedBitSet

end ProofForge.Core.Collections
