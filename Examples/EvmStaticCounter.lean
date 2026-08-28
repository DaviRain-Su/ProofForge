import ProofForge

/-!
EVM-SDK-2 consumer A: scalar/wide/record static storage declarations.

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`;
the handles are compile-time descriptor data erased before extraction, and every entry below
reads and writes state through ordinary typed `State` field access. `Tests/EvmStaticStorageSpec`
proves the extracted slots equal `layout.leaves`, so the declaration and the real flattening
cannot drift apart.
-/

namespace Examples.EvmStaticCounter

open ProofForge.Evm.Sdk

/-- Flat record: flattens to `tally_count` / `tally_window`. -/
structure Tally where
  count : UInt64
  window : UInt16
  deriving Repr, DecidableEq, Inhabited

structure State where
  paused : UInt8
  total : UInt256
  tally : Tally
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  paused : Storage.Static.Handle UInt8
  total : Storage.Static.Handle UInt256
  tally : Storage.Static.Handle Tally

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let paused := Storage.Static.Layout.root.uint8 "paused"
  let total := paused.next.uint256 "total"
  let tally := total.next.record (α := Tally) "tally" [("count", .u64), ("window", .u16)]
  { handle := { paused := paused.handle, total := total.handle, tally := tally.handle }
    next := tally.next }

/-- The accumulated static layout: slots `0..6` (`paused:1@0`, `total_w0..w3:8@1..4`,
`tally_count:8@5`, `tally_window:2@6`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (seed : UInt64) (_owner : Address) : State :=
  { paused := 0, total := ⟨seed, 0, 0, 0⟩, tally := { count := 0, window := 0 } }

/-- Running-gated increment. Paused → `Paused()` revert value; overflow → typed error. -/
@[pf_entry]
def bump (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if Access.requireRunning s.paused then
    if s.tally.count ≤ u64Max - delta then
      let next := s.tally.count + delta
      .ok ({ s with total := UInt256.add s.total ⟨delta, 0, 0, 0⟩,
                    tally := { s.tally with count := next } }, next)
    else
      .error .overflow
  else
    .ok (s, Access.runningViolation)

/-- Owner-only window update; the owner is a constructor immutable. -/
@[pf_entry]
def setWindow (s : State) (window : UInt16) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    .ok ({ s with tally := { s.tally with window } }, window.toUInt64)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    .ok ({ s with paused := 1 }, 1)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    .ok ({ s with paused := 0 }, 0)
  else
    .ok (s, Revert.unauthorized Context.caller)

@[pf_entry]
def countOf (s : State) : UInt64 :=
  s.tally.count

@[pf_entry]
def windowOf (s : State) : UInt16 :=
  s.tally.window

@[pf_entry]
def totalOf (s : State) : UInt256 :=
  s.total

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

end Examples.EvmStaticCounter
