import ProofForge

namespace Examples.Near.NearStorageEconomics
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Storage

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def shortKey : BoundedBytes 4 :=
  { length := 3, values := #v[1, 2, 3, 0] }

@[pf_inline] def longKey : BoundedBytes 8 :=
  { length := 7, values := #v[1, 2, 3, 4, 5, 6, 7, 0] }

@[pf_inline] def missingKey : BoundedBytes 4 :=
  { length := 2, values := #v[9, 9, 0, 0] }

@[pf_inline] def value4a : BoundedBytes 8 :=
  { length := 4, values := #v[10, 11, 12, 13, 0, 0, 0, 0] }

@[pf_inline] def value4b : BoundedBytes 8 :=
  { length := 4, values := #v[20, 21, 22, 23, 0, 0, 0, 0] }

@[pf_inline] def value8 : BoundedBytes 8 :=
  { length := 8, values := #v[30, 31, 32, 33, 34, 35, 36, 37] }

@[pf_entry]
def init : State := ⟨0⟩

@[pf_entry]
def get (state : State) : UInt64 := state.marker

@[pf_entry]
def usage (_state : State) : UInt64 := Context.storageUsage

@[pf_entry]
def insertShort4 (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.write shortKey value4a
  let after := Context.storageUsage
  let delta := after - before
  .ok (⟨delta⟩, delta)

@[pf_entry]
def replaceShort4 (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.write shortKey value4b
  let after := Context.storageUsage
  let delta := after - before
  .ok (⟨delta⟩, delta)

@[pf_entry]
def growShort8 (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.write shortKey value8
  let after := Context.storageUsage
  let delta := after - before
  .ok (⟨delta⟩, delta)

@[pf_entry]
def removeShort (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.remove shortKey
  let after := Context.storageUsage
  let reclaimed := before - after
  .ok (⟨reclaimed⟩, reclaimed)

@[pf_entry]
def removeMissing (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.remove missingKey
  let after := Context.storageUsage
  let reclaimed := before - after
  .ok (⟨reclaimed⟩, reclaimed)

@[pf_entry]
def insertLong4 (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.write longKey value4a
  let after := Context.storageUsage
  let delta := after - before
  .ok (⟨delta⟩, delta)

@[pf_entry]
def removeLong (_state : State) : Except Error (State × UInt64) :=
  let before := Context.storageUsage
  let result : ResultBuffer := 8
  let _ := result.remove longKey
  let after := Context.storageUsage
  let reclaimed := before - after
  .ok (⟨reclaimed⟩, reclaimed)

end Examples.Near.NearStorageEconomics