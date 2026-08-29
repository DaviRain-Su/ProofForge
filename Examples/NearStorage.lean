import ProofForge

namespace Examples.NearStorage

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def binaryKey : BoundedBytes 4 :=
  { length := 3, values := #v[0, 255, 1, 0] }

@[pf_inline] def emptyKey : BoundedBytes 1 :=
  { length := 0, values := #v[0] }

@[pf_inline] def missingKey : BoundedBytes 2 :=
  { length := 1, values := #v[127, 0] }

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def put (_state : State) (value : BoundedBytes 8) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 8
  let _ := result.write binaryKey value
  .ok ({ marker := result.status }, result.status)

@[pf_entry]
def putOldFirst (_state : State) (value : BoundedBytes 8) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 8
  let _ := result.write binaryKey value
  .ok ({ marker := (result.byte 0).toUInt64 }, (result.byte 0).toUInt64)

@[pf_entry]
def putEmptyKey (_state : State) (value : BoundedBytes 8) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 8
  let _ := result.write emptyKey value
  .ok ({ marker := result.status }, result.status)

@[pf_entry]
def has (_state : State) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.hasKey binaryKey
  result.status

@[pf_entry]
def hasEmptyKey (_state : State) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.hasKey emptyKey
  result.status

@[pf_entry]
def readStatus (_state : State) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read binaryKey
  result.status

@[pf_entry]
def readLength (_state : State) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read binaryKey
  result.length

@[pf_entry]
def readByte (_state : State) (index : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read binaryKey
  (result.byte index).toUInt64

@[pf_entry]
def staleByteAfterMiss (_state : State) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read binaryKey
  let _ := result.read missingKey
  (result.byte 0).toUInt64

@[pf_entry]
def readSmallFits (_state : State) : UInt64 :=
  let result : ResultBuffer := 4
  let _ := result.read binaryKey
  if result.fits then 1 else 0

@[pf_entry]
def readSmallStatus (_state : State) : UInt64 :=
  let result : ResultBuffer := 4
  let _ := result.read binaryKey
  result.status

@[pf_entry]
def readSmallLength (_state : State) : UInt64 :=
  let result : ResultBuffer := 4
  let _ := result.read binaryKey
  result.length

@[pf_entry]
def readSmallByte (_state : State) (index : UInt64) : UInt64 :=
  let result : ResultBuffer := 4
  let _ := result.read binaryKey
  (result.byte index).toUInt64

@[pf_entry]
def remove (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 8
  let _ := result.remove binaryKey
  .ok ({ marker := result.status }, result.status)

@[pf_entry]
def removeOldFirst (_state : State) : Except Error (State × UInt64) :=
  let result : ResultBuffer := 8
  let _ := result.remove binaryKey
  .ok ({ marker := (result.byte 0).toUInt64 }, (result.byte 0).toUInt64)

end Examples.NearStorage
