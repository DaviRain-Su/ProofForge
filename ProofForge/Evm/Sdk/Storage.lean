import ProofForge.Attr
import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Storage

/-!
# EVM SDK static storage declarations (EVM-SDK-2)

Compile-time descriptors for the *static* storage region: the consecutive zero-based slots the
extractor assigns when it flattens a contract `State` structure (`Extract` →
`Evm.IR.fromExtracted` keeps Core schema leaves in declaration order and numbers them `0, 1, …`).
The declarations are descriptor data that exist only before extraction. Contracts normally keep
reading and writing state through ordinary typed `State` field and `Vector` accesses. The one
effectful exception is `Handle.storeNow` for UInt64 fields: it composes the target-owned ordered
static-storage component needed around external calls while resolving the handle name against the
same extracted slot table. Focused tests validate declared layouts against the real slot/vector
tables of each consumer.

## Flattening contract mirrored here

- one scalar field → one slot; byte width ∈ {1, 2, 4, 8} (`Bool`/`UInt8` → 1, `UInt16` → 2,
  `UInt32` → 4, `UInt64` → 8); the leaf name is the field name;
- one machine-wide field → one 8-byte slot per leaf: `Address` = 3 leaves
  (`name_w0..name_w2`), `UInt256`/`Bytes32` = 4 leaves (`name_w0..name_w3`);
- a record field concatenates its fields in declaration order under `name_<field>` prefixes;
- a fixed array `Vector α n` repeats its element stride `n` times under `name_<i>` /
  `name_<i>_<field>` prefixes and produces one target vector entry `(base, length, stride)`;
- slots are numbered consecutively from `0` in declaration order.

Static slots are numbered independently of hashed-map namespaces: `Storage.Layout` bases and
`Static.Layout` slots never share a cursor, so declaring static fields cannot move a map base
and hashed-map hash/tag/payload geometry is untouched.

## Fail-closed policy

- descriptor validation (`Leaf.wellFormed`, `Spec.wellFormed`, `Layout.wellFormed`) rejects
  non-EVM widths, empty records/arrays, duplicate record field names, and non-consecutive
  cursor accumulation;
- consumers must declare fields in the exact declaration order of their `State` structure;
  `Tests/EvmStaticStorageSpec` proves the extracted slots of both consumers equal the declared
  leaves, so an order drift fails the focused suite;
- there is no runtime slot allocator, arbitrary slot-number API, generic handle read, or hidden
  final-state write. `Handle.storeNow` is UInt64-only, requires a compiler-static handle name, and
  fails if that name does not resolve to an actual 8-byte slot in the extracted program.
-/

namespace Static

/-- The only byte widths the EVM emitter accepts for one static slot (`Evm.IR.rejectSlot`). -/
@[pf_inline] def leafWidthValid (width : Nat) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

/-- Non-recursive leaf run: the only things one record field or vector element may contain in
the current EVM flattening — either one scalar slot or one machine-wide run of 8-byte slots. -/
inductive Leaf where
  | scalar (width : Nat)
  | wide (leaves : Nat)
  deriving BEq, Repr, Inhabited

namespace Leaf

@[pf_inline] def bool : Leaf := .scalar 1
@[pf_inline] def u8 : Leaf := .scalar 1
@[pf_inline] def u16 : Leaf := .scalar 2
@[pf_inline] def u32 : Leaf := .scalar 4
@[pf_inline] def u64 : Leaf := .scalar 8
/-- `Address` flattens to three 8-byte slots (`name_w0..name_w2`). -/
@[pf_inline] def address : Leaf := .wide 3
/-- `UInt256` flattens to four 8-byte slots (`name_w0..name_w3`). -/
@[pf_inline] def uint256 : Leaf := .wide 4
/-- `Bytes32` flattens to four 8-byte slots (`name_w0..name_w3`). -/
@[pf_inline] def bytes32 : Leaf := .wide 4

/-- Static slots consumed by this leaf. -/
@[pf_inline] def slots : Leaf → Nat
  | .scalar _ => 1
  | .wide leaves => leaves

/-- Descriptor-level validity. Current EVM state flattening exposes only three-limb `Address`
and four-limb `UInt256`/`Bytes32` wide values; arbitrary runs fail closed. -/
@[pf_inline] def wellFormed : Leaf → Bool
  | .scalar width => leafWidthValid width
  | .wide leaves => leaves == 3 || leaves == 4

end Leaf

/-- One concrete flattened slot: compatibility name, byte width, and zero-based index. This is
exactly the `(name, width, index)` triple the EVM IR assigns to a Core schema leaf. -/
structure FlatLeaf where
  name : String
  width : Nat
  slot : Nat
  deriving BEq, Repr, Inhabited

/-- Flatten one leaf under a name pfx at a base slot, using the extractor's `_w<i>`
suffixes for machine-wide runs. -/
def Leaf.flatten (pfx : String) (base : Nat) : Leaf → Array FlatLeaf
  | .scalar width => #[{ name := pfx, width, slot := base }]
  | .wide leaves =>
      (List.range leaves).toArray.map fun i =>
        { name := s!"{pfx}_w{i}", width := 8, slot := base + i }

/-- Static-storage element descriptor: one leaf, a flat record of leaves, or a fixed array of
leaves / flat records. Deeper nesting is not expressible, matching what the current EVM
flattening and emitter actually support. -/
inductive Spec where
  | leaf (leaf : Leaf)
  | record (fields : List (String × Leaf))
  | arrayLeaves (element : Leaf) (length : Nat)
  | arrayRecords (fields : List (String × Leaf)) (length : Nat)
  deriving BEq, Repr, Inhabited

/-- Static slots of a flat record field list, in declaration order. -/
def fieldListSlots : List (String × Leaf) → Nat
  | [] => 0
  | (_, leaf) :: rest => leaf.slots + fieldListSlots rest

/-- Total static slots consumed by one declared element. -/
def Spec.slots : Spec → Nat
  | .leaf l => l.slots
  | .record fields => fieldListSlots fields
  | .arrayLeaves element length => element.slots * length
  | .arrayRecords fields length => fieldListSlots fields * length

private def namesUnique (names : List String) : Bool :=
  names.eraseDups.length == names.length

private def fieldListWellFormed (fields : List (String × Leaf)) : Bool :=
  !fields.isEmpty && namesUnique (fields.map (·.1)) &&
    fields.all fun (name, leaf) => !name.isEmpty && leaf.wellFormed

/-- Descriptor-level validity. Invalid descriptors still allocate (the cursor is total), but
`Layout.wellFormed` and the focused tests reject them before any extraction is trusted. -/
def Spec.wellFormed : Spec → Bool
  | .leaf l => l.wellFormed
  | .record fields => fieldListWellFormed fields
  | .arrayLeaves element length => element.wellFormed && 0 < length
  | .arrayRecords fields length => fieldListWellFormed fields && 0 < length

/-- Flatten a flat record field list under `prefix_<field>` prefixes, threading the base slot
in declaration order. -/
def flattenFieldList (pfx : String) (base : Nat) : List (String × Leaf) → Array FlatLeaf
  | [] => #[]
  | (name, leaf) :: rest =>
      leaf.flatten s!"{pfx}_{name}" base ++
        flattenFieldList pfx (base + leaf.slots) rest

/-- Flatten one declared element to its concrete slots, using the extractor's `name_<i>` /
`name_<i>_<field>` array prefixes. -/
def Spec.flatten (pfx : String) (base : Nat) : Spec → Array FlatLeaf
  | .leaf l => l.flatten pfx base
  | .record fields => flattenFieldList pfx base fields
  | .arrayLeaves element length =>
      (List.range length).foldl (init := #[]) fun acc i =>
        acc ++ element.flatten s!"{pfx}_{i}" (base + i * element.slots)
  | .arrayRecords fields length =>
      (List.range length).foldl (init := #[]) fun acc i =>
        acc ++ flattenFieldList s!"{pfx}_{i}" (base + i * fieldListSlots fields) fields

/-- Slot offset of one direct record field inside its element, or `none` when absent. -/
def fieldListOffset? (wanted : String) : List (String × Leaf) → Nat → Option Nat
  | [], _ => none
  | (name, leaf) :: rest, offset =>
      if name == wanted then some offset
      else fieldListOffset? wanted rest (offset + leaf.slots)

/-- Compile-time cursor assigning consecutive static slots, mirroring the extractor's
declaration-order flattening of the contract `State` structure. The accumulated `leaves` are
descriptor data erased before extraction; nothing here exists at runtime. -/
structure Layout where
  nextSlot : Nat
  leaves : Array FlatLeaf
  valid : Bool := true
  deriving BEq, Repr, Inhabited

/-- A statically allocated handle and the cursor for the next declaration. -/
structure Allocated (α : Type) where
  handle : α
  next : Layout
  deriving Repr

/-- Typed handle to one statically allocated element. `α` is the source-level field type and
is phantom: the handle is compile-time descriptor data (name, base slot, element spec) erased
before extraction. Contracts access state through ordinary typed `State` fields; handles exist
so layout consumers and tests share one declaration instead of repeating slot arithmetic. -/
structure Handle (α : Type) where
  name : String
  baseSlot : Nat
  spec : Spec
  deriving Repr

attribute [pf_inline] Layout.nextSlot Layout.leaves Layout.valid Allocated.handle Allocated.next
  Handle.name Handle.baseSlot Handle.spec

/-- The empty static layout: slot `0` is the first static slot, disjoint from hashed-map
namespace base `0` (separate numbering). -/
@[pf_inline] def Layout.root : Layout := { nextSlot := 0, leaves := #[], valid := true }

/-- Allocate one element under `name`, appending its flattened leaves and advancing the cursor
by exactly the element's slot count. -/
@[pf_inline] def Layout.declare (layout : Layout) (name : String) (spec : Spec) :
    Allocated (Handle α) :=
  { handle := { name, baseSlot := layout.nextSlot, spec }
    next := { nextSlot := layout.nextSlot + spec.slots
              leaves := layout.leaves ++ spec.flatten name layout.nextSlot
              valid := layout.valid && !name.isEmpty && spec.wellFormed } }

@[pf_inline] def Layout.bool (layout : Layout) (name : String) : Allocated (Handle Bool) :=
  layout.declare name (.leaf .bool)

@[pf_inline] def Layout.uint8 (layout : Layout) (name : String) : Allocated (Handle UInt8) :=
  layout.declare name (.leaf .u8)

@[pf_inline] def Layout.uint16 (layout : Layout) (name : String) : Allocated (Handle UInt16) :=
  layout.declare name (.leaf .u16)

@[pf_inline] def Layout.uint32 (layout : Layout) (name : String) : Allocated (Handle UInt32) :=
  layout.declare name (.leaf .u32)

@[pf_inline] def Layout.uint64 (layout : Layout) (name : String) : Allocated (Handle UInt64) :=
  layout.declare name (.leaf .u64)

@[pf_inline] def Layout.address (layout : Layout) (name : String) : Allocated (Handle Address) :=
  layout.declare name (.leaf .address)

@[pf_inline] def Layout.uint256 (layout : Layout) (name : String) : Allocated (Handle UInt256) :=
  layout.declare name (.leaf .uint256)

@[pf_inline] def Layout.bytes32 (layout : Layout) (name : String) : Allocated (Handle Bytes32) :=
  layout.declare name (.leaf .bytes32)

/-- Allocate a flat record; `α` is the source record type. `fields` must list the record's
fields in declaration order. -/
@[pf_inline] def Layout.record (layout : Layout) (name : String)
    (fields : List (String × Leaf)) : Allocated (Handle α) :=
  layout.declare name (.record fields)

/-- Allocate a fixed array of scalar/wide elements; `α` is the source `Vector` type. -/
@[pf_inline] def Layout.array (layout : Layout) (name : String)
    (element : Leaf) (length : Nat) : Allocated (Handle α) :=
  layout.declare name (.arrayLeaves element length)

/-- Allocate a fixed array of flat records; `α` is the source `Vector` type. -/
@[pf_inline] def Layout.recordArray (layout : Layout) (name : String)
    (fields : List (String × Leaf)) (length : Nat) : Allocated (Handle α) :=
  layout.declare name (.arrayRecords fields length)

namespace Handle

/--
Immediately write this UInt64 field in lexical EVM effect order. This is intentionally distinct
from ordinary immutable Lean state return/writeback: it is the target effect used for locks and
other values that must become visible before an external CALL. The compiler resolves `name`
against the extracted static schema; no source-visible slot number survives.
-/
@[pf_inline] def storeNow (handle : Handle UInt64) (value : UInt64) : UInt64 :=
  StaticStorage.Source.storeU64 handle.name value

/-- Total static slots consumed by the handled element. -/
@[pf_inline] def slots (handle : Handle α) : Nat :=
  handle.spec.slots

/-- Re-flatten the handled element; equals the slice `Layout.leaves` contributed by its
declaration. -/
def leaves (handle : Handle α) : Array FlatLeaf :=
  handle.spec.flatten handle.name handle.baseSlot

/-- The single slot of a scalar handle; `none` for wide/record/array handles. -/
@[pf_inline] def slot? (handle : Handle α) : Option Nat :=
  match handle.spec with
  | .leaf (.scalar _) => some handle.baseSlot
  | _ => none

/-- The byte width of a scalar handle; `none` for wide/record/array handles. -/
@[pf_inline] def width? (handle : Handle α) : Option Nat :=
  match handle.spec with
  | .leaf (.scalar width) => some width
  | _ => none

/-- The leaf count of a machine-wide handle (3 for `Address`, 4 for `UInt256`/`Bytes32`). -/
@[pf_inline] def wideLeaves? (handle : Handle α) : Option Nat :=
  match handle.spec with
  | .leaf (.wide leaves) => some leaves
  | _ => none

/-- The fixed length of an array handle. -/
@[pf_inline] def length? (handle : Handle α) : Option Nat :=
  match handle.spec with
  | .arrayLeaves _ length => some length
  | .arrayRecords _ length => some length
  | _ => none

/-- The per-element slot stride of an array handle. -/
@[pf_inline] def elementSlots? (handle : Handle α) : Option Nat :=
  match handle.spec with
  | .arrayLeaves element _ => some element.slots
  | .arrayRecords fields _ => some (fieldListSlots fields)
  | _ => none

/-- Base slot of array element `i`, or `none` when out of range or not an array. This is the
same `base + i * stride` addressing the emitter derives from the target vector entry. -/
@[pf_inline] def slotOf? (handle : Handle α) (index : Nat) : Option Nat :=
  match handle.length?, handle.elementSlots? with
  | some length, some stride =>
      if index < length then some (handle.baseSlot + index * stride) else none
  | _, _ => none

/-- Base slot of a direct record field (also usable for array-of-record element `0`). -/
def fieldSlot? (handle : Handle α) (field : String) : Option Nat :=
  match handle.spec with
  | .record fields => (fieldListOffset? field fields 0).map (handle.baseSlot + ·)
  | .arrayRecords fields _ => (fieldListOffset? field fields 0).map (handle.baseSlot + ·)
  | _ => none

/-- Descriptor validity of the handled element. -/
@[pf_inline] def wellFormed (handle : Handle α) : Bool :=
  !handle.name.isEmpty && handle.spec.wellFormed

end Handle

/-- Whole-layout validation: every accumulated leaf has an EVM width, leaves occupy slots
`0..nextSlot-1` consecutively (declarations threaded through this cursor without gaps), and no
flattened name repeats. -/
def Layout.wellFormed (layout : Layout) : Bool :=
  layout.valid && layout.leaves.size == layout.nextSlot &&
    layout.leaves.all (fun leaf => leafWidthValid leaf.width) &&
    (List.range layout.leaves.size).all (fun i => layout.leaves[i]!.slot == i) &&
    namesUnique (layout.leaves.toList.map (·.name))

/-- Compare the accumulated declaration against a flattened slot table of `(name, width)`
pairs in slot order — e.g. `program.slots.map (fun s => (s.name, s.width))` from an extracted
EVM program. This is the bridge that proves a declared layout composes with the existing EVM
state flattening without any extractor change. -/
def Layout.matchesFlattened (layout : Layout) (slots : List (String × Nat)) : Bool :=
  layout.leaves.toList.map (fun leaf => (leaf.name, leaf.width)) == slots

end Static

end ProofForge.Evm.Sdk.Storage
