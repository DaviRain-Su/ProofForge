import ProofForge
import Examples.Evm.EvmStaticCounter
import Examples.Evm.EvmStaticRoster
import Examples.Evm.EvmAggregateStorage

/-!
EVM-SDK-2 focused suite: static storage descriptor units, cursor/allocation checks, and
extraction-level proofs that the consumers' declared layouts equal the real EVM state
flattening. Hashed-map namespace semantics are pinned unchanged alongside. Feature A nested
aggregate storage (`nestedRecord`) is covered by `EvmAggregateStorage`.
-/

namespace Tests.EvmStaticStorageSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Descriptor units -/

#guard leafWidthValid 1 && leafWidthValid 2 && leafWidthValid 4 && leafWidthValid 8
#guard !leafWidthValid 0 && !leafWidthValid 3 && !leafWidthValid 5 && !leafWidthValid 16

#guard Leaf.bool.slots == 1 && Leaf.u8.slots == 1 && Leaf.u16.slots == 1 &&
  Leaf.u32.slots == 1 && Leaf.u64.slots == 1
#guard Leaf.address.slots == 3 && Leaf.uint256.slots == 4 && Leaf.bytes32.slots == 4
#guard Leaf.u64.wellFormed && Leaf.address.wellFormed
#guard !(Leaf.scalar 3).wellFormed && !(Leaf.scalar 16).wellFormed &&
  !(Leaf.wide 0).wellFormed && !(Leaf.wide 2).wellFormed && !(Leaf.wide 5).wellFormed

/-! ## Spec arithmetic and fail-closed validation -/

#guard (Spec.leaf .u64).slots == 1
#guard (Spec.record [("count", .u64), ("window", .u16)]).slots == 2
#guard (Spec.nestedRecord
  [("amount", .leaf .u64), ("details", .record [("side", .u8), ("enabled", .bool)])]).slots == 3
#guard (Spec.arrayLeaves .u64 3).slots == 3
#guard (Spec.arrayLeaves .uint256 2).slots == 8
#guard (Spec.arrayRecords [("points", .u64), ("tier", .u8)] 3).slots == 6

#guard (Spec.leaf .u64).wellFormed
#guard (Spec.record [("count", .u64), ("window", .u16)]).wellFormed
#guard (Spec.nestedRecord
  [("amount", .leaf .u64), ("details", .record [("side", .u8), ("enabled", .bool)])]).wellFormed
#guard (Spec.arrayLeaves .u64 3).wellFormed
#guard (Spec.arrayRecords [("points", .u64), ("tier", .u8)] 3).wellFormed
-- fail closed: empty records, duplicate/empty field names, empty arrays, bad widths,
-- and depth ≥ 3 nested payloads
#guard !(Spec.record []).wellFormed
#guard !(Spec.record [("a", .u64), ("a", .u16)]).wellFormed
#guard !(Spec.record [("", .u64)]).wellFormed
#guard !(Spec.record [("bad", .scalar 5)]).wellFormed
#guard !(Spec.nestedRecord []).wellFormed
#guard !(Spec.nestedRecord [("a", .leaf .u64), ("a", .record [("b", .u8)])]).wellFormed
#guard !(Spec.nestedRecord [("deep", .nestedRecord [("x", .leaf .u64)])]).wellFormed
#guard !(Spec.nestedRecord [("arr", .arrayLeaves .u64 2)]).wellFormed
#guard !(Spec.arrayLeaves .u64 0).wellFormed
#guard !(Spec.arrayLeaves (.scalar 3) 2).wellFormed
#guard !(Spec.arrayRecords [] 2).wellFormed
#guard !(Spec.arrayRecords [("points", .u64)] 0).wellFormed

/-! ## Flattening names mirror the extractor -/

#guard (Spec.leaf .u64).flatten "value" 0 ==
  #[{ name := "value", width := 8, slot := 0 }]
#guard (Spec.leaf .uint256).flatten "cap" 2 ==
  #[{ name := "cap_w0", width := 8, slot := 2 },
    { name := "cap_w1", width := 8, slot := 3 },
    { name := "cap_w2", width := 8, slot := 4 },
    { name := "cap_w3", width := 8, slot := 5 }]
#guard (Spec.leaf .address).flatten "owner" 0 ==
  #[{ name := "owner_w0", width := 8, slot := 0 },
    { name := "owner_w1", width := 8, slot := 1 },
    { name := "owner_w2", width := 8, slot := 2 }]
#guard (Spec.record [("price", .u64), ("size", .u64)]).flatten "book" 0 ==
  #[{ name := "book_price", width := 8, slot := 0 },
    { name := "book_size", width := 8, slot := 1 }]
#guard (Spec.nestedRecord
  [("amount", .leaf .u64), ("details", .record [("side", .u8), ("enabled", .bool)])]).flatten
    "bundle" 0 ==
  #[{ name := "bundle_amount", width := 8, slot := 0 },
    { name := "bundle_details_side", width := 1, slot := 1 },
    { name := "bundle_details_enabled", width := 1, slot := 2 }]
#guard (Spec.arrayLeaves .u64 2).flatten "cells" 0 ==
  #[{ name := "cells_0", width := 8, slot := 0 },
    { name := "cells_1", width := 8, slot := 1 }]
#guard (Spec.arrayRecords [("price", .u64), ("size", .u16)] 2).flatten "books" 3 ==
  #[{ name := "books_0_price", width := 8, slot := 3 },
    { name := "books_0_size", width := 2, slot := 4 },
    { name := "books_1_price", width := 8, slot := 5 },
    { name := "books_1_size", width := 2, slot := 6 }]

/-! ## Cursor allocation and handle projections -/

def sampleAllocated :=
  let flag := Layout.root.uint8 "flag"
  let owner := flag.next.address "owner"
  let cells := owner.next.array (α := Vector UInt64 2) "cells" .u64 2
  (flag.handle, owner.handle, cells.handle, cells.next)

def sample : Layout := sampleAllocated.2.2.2

#guard sampleAllocated.1.baseSlot == 0
#guard sampleAllocated.2.1.baseSlot == 1
#guard sampleAllocated.2.2.1.baseSlot == 4
#guard sample.nextSlot == 6
#guard sample.wellFormed
#guard sample.matchesFlattened
  [("flag", 1), ("owner_w0", 8), ("owner_w1", 8), ("owner_w2", 8), ("cells_0", 8), ("cells_1", 8)]
#guard !sample.matchesFlattened [("flag", 1)]
#guard !sample.matchesFlattened
  [("flag", 1), ("owner_w0", 8), ("owner_w1", 8), ("owner_w2", 8), ("cells_1", 8), ("cells_0", 8)]

-- a cursor that skips accumulation cannot validate: leaf slots must be consecutive from 0
#guard !(Layout.mk 1 #[{ name := "x", width := 8, slot := 3 }] true).wellFormed
#guard !(Layout.mk 1 #[{ name := "x", width := 3, slot := 0 }] true).wellFormed

def invalidLayouts :=
  let emptyName := Layout.root.uint64 ""
  let badWide := Layout.root.declare (α := UInt64) "bad" (.leaf (.wide 2))
  (emptyName.next, badWide.next)

#guard !invalidLayouts.1.wellFormed && !invalidLayouts.2.wellFormed

#guard sampleAllocated.1.slot? == some 0
#guard sampleAllocated.1.width? == some 1
#guard sampleAllocated.2.1.slot? == none
#guard sampleAllocated.2.1.wideLeaves? == some 3
#guard sampleAllocated.2.2.1.length? == some 2
#guard sampleAllocated.2.2.1.elementSlots? == some 1
#guard sampleAllocated.2.2.1.slotOf? 1 == some 5
#guard sampleAllocated.2.2.1.slotOf? 2 == none
#guard sampleAllocated.2.2.1.fieldSlot? "x" == none

def recordHandles :=
  let tally := Layout.root.record (α := Examples.Evm.EvmStaticCounter.Tally)
    "tally" [("count", .u64), ("window", .u16)]
  let seats := tally.next.recordArray (α := Vector Examples.Evm.EvmStaticRoster.Seat 3)
    "seats" [("points", .u64), ("tier", .u8)] 3
  (tally.handle, seats.handle)

#guard recordHandles.1.fieldSlot? "count" == some 0
#guard recordHandles.1.fieldSlot? "window" == some 1
#guard recordHandles.1.fieldSlot? "missing" == none
#guard recordHandles.2.slotOf? 2 == some 6
#guard recordHandles.2.fieldSlot? "tier" == some 3
#guard recordHandles.1.wellFormed && recordHandles.2.wellFormed

def nestedHandles :=
  let bundle := Layout.root.nestedRecord (α := Examples.Evm.EvmAggregateStorage.Bundle)
    "bundle"
    [ ("amount", .leaf .u64)
    , ("details", .record [("side", .u8), ("enabled", .bool)]) ]
  bundle.handle

#guard nestedHandles.fieldSlot? "amount" == some 0
#guard nestedHandles.fieldSlot? "details" == some 1
#guard nestedHandles.slots == 3
#guard nestedHandles.wellFormed

/-! ## Hashed-map namespaces are untouched -/

-- The static cursor is a separate type with separate numbering; map bases still start at 0
-- and advance exactly as before this slice.
#guard Storage.Layout.root.u64Map.handle.base == 0
#guard (Storage.Layout.root.addressMap256.next.addressPairMap256).handle.base == 1
#guard (Storage.Layout.root.addressMap256.next.addressPairMap256).next.nextSlot == 2

/-! ## Consumer host behavior through ordinary typed state access -/

open Examples.Evm.EvmStaticCounter in
#guard (init 5 ⟨0, 0, 0⟩).paused == 0 &&
  (init 5 ⟨0, 0, 0⟩).total == ⟨5, 0, 0, 0⟩ &&
  (init 5 ⟨0, 0, 0⟩).tally.count == 0

/- Host stubs keep checked wide arithmetic identity-left (`evmAdd256` returns `a`), so the
host-visible change of a bump is the `tally.count` scalar; extraction owns the real 256-bit add. -/
open Examples.Evm.EvmStaticCounter in
#guard match bump (init 5 ⟨0, 0, 0⟩) 7 with
  | .ok (s, r) => s.tally.count == 7 && r == 7 && s.total == ⟨5, 0, 0, 0⟩
  | _ => false

open Examples.Evm.EvmStaticCounter in
#guard match bump (init 5 ⟨0, 0, 0⟩) 7 with
  | .ok (s, _) =>
      (match bump s u64Max with
       | .error .overflow => true
       | _ => false)
  | _ => false

open Examples.Evm.EvmStaticCounter in
#guard match pause (init 5 ⟨0, 0, 0⟩) with
  | .ok (s, _) =>
      -- host stubs treat the caller as the immutable owner, so pause commits;
      -- a paused bump reverts through the closed `Paused()` terminal without mutating state
      (match bump s 1 with
       | .ok (after, r) => s.paused == 1 && after.tally.count == 0 && r == 0
       | _ => false)
  | _ => false

open Examples.Evm.EvmStaticCounter in
#guard match setWindow (init 5 ⟨0, 0, 0⟩) 9 with
  | .ok (s, r) => s.tally.window == 9 && r == 9
  | _ => false

open Examples.Evm.EvmStaticRoster in
#guard (init ⟨1, 2, 3⟩).admin == ⟨1, 2, 3⟩ && !(init ⟨1, 2, 3⟩).closed &&
  seatPoints (init ⟨1, 2, 3⟩) 0 == 0 && seatPoints (init ⟨1, 2, 3⟩) 5 == 0

open Examples.Evm.EvmStaticRoster in
#guard match setSeat (init ⟨1, 2, 3⟩) 1 9 2 with
  | .ok (s, r) => s.seats[1]!.points == 9 && s.seats[1]!.tier == 2 && r == 9 &&
      seatPoints s 1 == 9 && seatTier s 1 == 2
  | _ => false

open Examples.Evm.EvmStaticRoster in
#guard match setSeat (init ⟨1, 2, 3⟩) 4 9 2 with
  | .error .overflow => true
  | _ => false

open Examples.Evm.EvmStaticRoster in
#guard match close (init ⟨0, 0, 0⟩) with
  | .ok (s, _) =>
      match setSeat s 0 9 2 with
      | .ok (after, r) => after == s && r == 0
      | _ => false
  | _ => false

open Examples.Evm.EvmStaticRoster in
#guard match close (init ⟨1, 2, 3⟩) with
  | .ok (s, r) => s.closed && r == 1 && closedOf s
  | _ => false

open Examples.Evm.EvmAggregateStorage in
#guard (init ⟨1, 2, 3⟩).bundle.amount == 0 &&
  !(init ⟨1, 2, 3⟩).bundle.details.enabled

open Examples.Evm.EvmAggregateStorage in
#guard match setBundle (init ⟨1, 2, 3⟩) 11 4 true with
  | .ok (s, r) =>
      s.bundle.amount == 11 && s.bundle.details.side == 4 && s.bundle.details.enabled &&
        r == 11 && bundleSignal s == (11, true) &&
        bundleView s == (11, (4, true)) && detailsView s == (4, true) &&
        amountOf s == 11 && sideOf s == 4 && enabledOf s &&
        (amountSidePairs s).length == 1 &&
        (amountSidePairs s).values[0]! == (11, (4 : UInt8))
  | _ => false

open Examples.Evm.EvmAggregateStorage in
#guard match setAmount (init ⟨1, 2, 3⟩) 9 with
  | .ok (s, r) =>
      s.bundle.amount == 9 && s.bundle.details.side == 0 && !s.bundle.details.enabled && r == 9 &&
        bundleView s == (9, (0, false)) && detailsView s == (0, false)
  | _ => false

/-! ## Consumer layouts pin the compile-time declaration -/

def layoutSlots (layout : Layout) : List (String × Nat) :=
  layout.leaves.toList.map fun leaf => (leaf.name, leaf.width)

def counterSlots : List (String × Nat) :=
  layoutSlots Examples.Evm.EvmStaticCounter.layout

def rosterSlots : List (String × Nat) :=
  layoutSlots Examples.Evm.EvmStaticRoster.layout

def aggregateSlots : List (String × Nat) :=
  layoutSlots Examples.Evm.EvmAggregateStorage.layout

def rosterVectors : List (String × Nat × Nat × Nat) :=
  let seats := Examples.Evm.EvmStaticRoster.declared.handle.seats
  [(seats.name, seats.baseSlot, seats.length?.getD 0, seats.elementSlots?.getD 0)]

#guard Examples.Evm.EvmStaticCounter.layout.wellFormed
#guard Examples.Evm.EvmStaticCounter.layout.matchesFlattened counterSlots
#guard Examples.Evm.EvmStaticCounter.declared.handle.paused.slot? == some 0
#guard Examples.Evm.EvmStaticCounter.declared.handle.total.wideLeaves? == some 4
#guard Examples.Evm.EvmStaticCounter.declared.handle.tally.fieldSlot? "window" == some 6

#guard Examples.Evm.EvmStaticRoster.layout.wellFormed
#guard Examples.Evm.EvmStaticRoster.layout.matchesFlattened rosterSlots
#guard Examples.Evm.EvmStaticRoster.declared.handle.admin.wideLeaves? == some 3
#guard Examples.Evm.EvmStaticRoster.declared.handle.seats.length? == some 3
#guard Examples.Evm.EvmStaticRoster.declared.handle.seats.elementSlots? == some 2
#guard Examples.Evm.EvmStaticRoster.declared.handle.seats.slotOf? 2 == some 7
#guard Examples.Evm.EvmStaticRoster.declared.handle.closed.slot? == some 9
#guard Examples.Evm.EvmStaticRoster.declared.handle.closed.width? == some 1

#guard Examples.Evm.EvmAggregateStorage.layout.wellFormed
#guard Examples.Evm.EvmAggregateStorage.layout.matchesFlattened aggregateSlots
#guard Examples.Evm.EvmAggregateStorage.layout.nextSlot == 6
#guard Examples.Evm.EvmAggregateStorage.declared.handle.admin.wideLeaves? == some 3
#guard Examples.Evm.EvmAggregateStorage.declared.handle.bundle.fieldSlot? "amount" == some 3
#guard Examples.Evm.EvmAggregateStorage.declared.handle.bundle.fieldSlot? "details" == some 4
#guard aggregateSlots ==
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
   ("bundle_amount", 8), ("bundle_details_side", 1), ("bundle_details_enabled", 1)]

/-! ## Extraction proof: declared layout == real EVM state flattening -/

private def expectStaticLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVectors : List (String × Nat × Nat × Nat)) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun s => (s.name, s.width)
  unless slots == expectedSlots do
    throwError s!"{module}: extracted static slots diverge from the declared layout: {slots}"
  let vectors := program.vectors.toList.map fun v => (v.name, v.baseSlot, v.length, v.strideSlots)
  unless vectors == expectedVectors do
    throwError s!"{module}: extracted vectors diverge from the declared layout: {vectors}"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let _abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  for (_, width) in expectedSlots do
    unless width == 1 || width == 2 || width == 4 || width == 8 do
      throwError s!"{module}: non-EVM leaf width survived extraction"
  unless yul.contains "sstore(" && yul.contains "sload(" do
    throwError s!"{module}: expected ordinary static slot accesses in emitted Yul"

elab "#pf_guard_evm_static_counter" : command =>
  expectStaticLayout `Examples.Evm.EvmStaticCounter counterSlots []

elab "#pf_guard_evm_static_roster" : command =>
  expectStaticLayout `Examples.Evm.EvmStaticRoster rosterSlots rosterVectors

elab "#pf_guard_evm_aggregate_storage" : command => do
  expectStaticLayout `Examples.Evm.EvmAggregateStorage aggregateSlots []
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Evm.EvmAggregateStorage with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let digest := ProofForge.Evm.IR.digestHex program
  logInfo m!"proofforge-evm-aggregate-storage: digest = {digest}"
  unless ProofForge.Evm.Registry.digestOf "EvmAggregateStorage" == some digest do
    throwError s!"EvmAggregateStorage registry digest is stale: {digest}"
  let some _bundleSignal := program.entries.find? (·.ixName == "bundleSignal")
    | throwError "missing bundleSignal entry"
  let some bundleView := program.entries.find? (·.ixName == "bundleView")
    | throwError "missing bundleView entry"
  let some detailsView := program.entries.find? (·.ixName == "detailsView")
    | throwError "missing detailsView entry"
  let some _amountOf := program.entries.find? (·.ixName == "amountOf")
    | throwError "missing amountOf entry"
  let some amountSidePairs := program.entries.find? (·.ixName == "amountSidePairs")
    | throwError "missing amountSidePairs entry"
  unless bundleView.retSchema ==
      .tuple #[.scalar .uint64, .tuple #[.scalar .uint8, .scalar .boolean]] do
    throwError s!"bundleView retSchema not nested product: {repr bundleView.retSchema}"
  unless detailsView.retSchema ==
      .tuple #[.scalar .uint8, .scalar .boolean] do
    throwError s!"detailsView retSchema not product: {repr detailsView.retSchema}"
  unless amountSidePairs.retSchema ==
      .boundedArray 1 (.tuple #[.scalar .uint64, .scalar .uint8]) do
    throwError s!"amountSidePairs retSchema not constructed bounded product array: {repr amountSidePairs.retSchema}"
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  unless abi.contains "\"name\":\"bundleSignal\"" &&
      abi.contains "\"name\":\"bundleView\"" &&
      abi.contains "\"name\":\"detailsView\"" &&
      abi.contains "\"name\":\"amountOf\"" &&
      abi.contains "\"name\":\"amountSidePairs\"" &&
      abi.contains "uint64" &&
      abi.contains "uint8" do
    throwError s!"EvmAggregateStorage ABI missing nested/product/bounded surface: {abi}"
  match ProofForge.Evm.Codec.abiTypeOfSchema bundleView.retSchema with
  | .ok type =>
      unless type == "(uint64,(uint8,bool))" do
        throwError s!"bundleView ABI type mismatch: {type}"
  | .error reason => throwError reason
  match ProofForge.Evm.Codec.abiTypeOfSchema detailsView.retSchema with
  | .ok type =>
      unless type == "(uint8,bool)" do
        throwError s!"detailsView ABI type mismatch: {type}"
  | .error reason => throwError reason
  match ProofForge.Evm.Codec.abiTypeOfSchema amountSidePairs.retSchema with
  | .ok type =>
      unless type == "(uint64,uint8)[]" do
        throwError s!"amountSidePairs ABI type mismatch: {type}"
  | .error reason => throwError reason

#pf_guard_evm_static_counter
#pf_guard_evm_static_roster
#pf_guard_evm_aggregate_storage

end Tests.EvmStaticStorageSpec
