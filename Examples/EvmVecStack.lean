import ProofForge

/-!
R5-010 consumer B: a permissionless bounded LIFO stack over the `Evm.Sdk.StorageVec` persistent
vector policy (capacity 3), with a different authorization and terminal policy than
`Examples.EvmVecLog` — no owner at all, and empty pops fail with the typed `empty` error instead
of a fallback.

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageVec.Descriptor` bundle is compile-time data erased before extraction. Every entry reads
and writes state through ordinary typed `State` field/`Vector` accesses: the SDK owns only the
length/index decisions (`canPush`/`canPop`), and each physical write is a visible literal field
update. `Tests/EvmStorageVecSpec` proves the extracted slots and the `items` vector entry equal
the declared layout, and `runtime-tests/evm/anvil_vec_stack.sh` covers the push/pop/clear and
failure matrix.
-/

namespace Examples.EvmVecStack

open ProofForge.Evm.Sdk

/-- Compile-time capacity of the stack's backing vector. -/
abbrev capacity : Nat := 3

/-- The same capacity as the compiler-erased scalar the SDK policy decisions consume in
extracted code. The fixed-vector compiler guards below use the plain literal `3`, matching the
existing `Vector` extraction contract (`EvmStaticRoster`, `Lang`). -/
@[pf_inline] def capU64 : UInt64 := 3

structure State where
  /-- Fixed backing field of the bounded stack; only the active prefix `items[0..depth)` is
  reachable. -/
  items : Vector UInt64 3
  /-- Explicit runtime depth of the stack. -/
  depth : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  stack : StorageVec.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let stack := StorageVec.declare Storage.Static.Layout.root "items" "depth" capacity
  { handle := { stack := stack.handle }, next := stack.next }

/-- The accumulated static layout: slots `0..3` (`items_<i>:8@0..2`, `depth:8@3`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | empty
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Constructor seeds one genesis element so deployment exercises the vector + length store. -/
@[pf_entry]
def init (first : UInt64) : State :=
  { items := #v[first, 0, 0], depth := 1 }

@[pf_entry]
def depthOf (s : State) : UInt64 :=
  s.depth

/-- Top-of-stack view: the last active element, or `0` when the stack is empty or the depth is
malformed. -/
@[pf_entry]
def topOf (s : State) : UInt64 :=
  if StorageVec.canPop capU64 s.depth then
    if h : s.depth.toNat - 1 < 3 then s.items[s.depth.toNat - 1] else 0
  else
    0

/-- Permissionless push; malformed depth gets the typed terminal and a canonical full stack uses
`CapExceeded()`. The physical write is the literal update of `items[depth]` plus `depth + 1`. -/
@[pf_entry]
def push (s : State) (value : UInt64) : Except Error (State × UInt64) :=
  if StorageVec.wellFormed capU64 s.depth then
    if StorageVec.canPush capU64 s.depth then
      if h : s.depth.toNat < 3 then
        let next := s.depth + 1
        .ok ({ s with items := s.items.set s.depth.toNat value h, depth := next }, next)
      else
        .error .malformed
    else
      .ok (s, Revert.capExceeded)
  else
    .error .malformed

/-- Permissionless pop: returns the last active element and stores `depth - 1`. An empty or
malformed stack has a distinct typed error before any store; the popped slot keeps its stale value
and stays unreachable. -/
@[pf_entry]
def pop (s : State) : Except Error (State × UInt64) :=
  if StorageVec.wellFormed capU64 s.depth then
    if StorageVec.canPop capU64 s.depth then
      let last := s.depth - 1
      if h : last.toNat < 3 then
        .ok ({ s with depth := last }, s.items[last.toNat])
      else
        .error .malformed
    else
      .error .empty
  else
    .error .malformed

/-- Permissionless clear: only the depth field resets to zero. Backing slots keep their stale
values and stay unreachable until future pushes overwrite them; malformed depth fails before the
store instead of being silently repaired. -/
@[pf_entry]
def clearAll (s : State) : Except Error (State × UInt64) :=
  if StorageVec.canClear capU64 s.depth then
    .ok ({ s with depth := StorageVec.clearedLength }, 0)
  else
    .error .malformed

end Examples.EvmVecStack
