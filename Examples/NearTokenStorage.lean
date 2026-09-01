import ProofForge

namespace Examples.NearTokenStorage

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def tokenKey : BoundedBytes 4 :=
  { length := 4, values := #v[0x54, 0x4f, 0x4b, 0x31] }

@[pf_inline] def missingKey : BoundedBytes 4 :=
  { length := 4, values := #v[0x4d, 0x49, 0x53, 0x53] }

@[pf_entry] def init : State := ⟨0⟩

@[pf_entry] def get (state : State) : UInt64 := state.marker

@[pf_entry] def has (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.hasKey tokenKey
  result.status

@[pf_entry] def readW0 (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.read tokenKey
  resultNearTokenW0D 0xfedcba9876543210

@[pf_entry] def readW1 (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.read tokenKey
  resultNearTokenW1D 0x0123456789abcdef

@[pf_entry] def readStatus (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.read tokenKey
  result.status

@[pf_entry] def readLength (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.read tokenKey
  result.length

@[pf_entry] def readFits (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.read tokenKey
  if result.fits then 1 else 0

@[pf_entry] def staleAfterMissW0 (_state : State) : UInt64 :=
  let result : ResultBuffer := 16
  let _ := result.read tokenKey
  let _ := result.read missingKey
  resultNearTokenW0D 0xfedcba9876543210

@[pf_entry] def putMixed (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 16
  let _ := result.write tokenKey (borshNearToken ⟨0x0102030405060708, 0x1112131415161718⟩)
  .ok (⟨result.status⟩, result.status)

@[pf_entry] def putMax (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 16
  let _ := result.write tokenKey (borshNearToken ⟨0xffffffffffffffff, 0xffffffffffffffff⟩)
  .ok (⟨result.status⟩, result.status)

@[pf_entry] def putZero (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 16
  let _ := result.write tokenKey (borshNearToken ⟨0, 0⟩)
  .ok (⟨result.status⟩, result.status)

@[pf_entry] def putShort (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 16
  let _ := result.write tokenKey (borshUInt64 0x8877665544332211)
  .ok (⟨result.status⟩, result.status)

@[pf_entry] def putOversized
    (_state : State) (value : BoundedBytes 20) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 16
  let _ := result.write tokenKey value
  .ok (⟨result.status⟩, result.status)

@[pf_entry] def remove (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 16
  let _ := result.remove tokenKey
  .ok (⟨result.status⟩, result.status)

end Examples.NearTokenStorage
