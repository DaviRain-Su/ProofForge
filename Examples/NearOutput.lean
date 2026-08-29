import ProofForge

namespace Examples.NearOutput

open ProofForge.Core.Value

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ marker := 1 }, 1) else .error .overflow

@[pf_entry]
def emptyBytes (_state : State) : BoundedBytes 8 :=
  { length := 0, values := #v[0, 0, 0, 0, 0, 0, 0, 0] }

@[pf_entry]
def staticBytes (_state : State) : BoundedBytes 8 :=
  { length := 3, values := #v[0, 1, 255, 0, 0, 0, 0, 0] }

@[pf_entry]
def staticString (_state : State) : BoundedString 8 :=
  { length := 4, values := #v[0xf0, 0x9f, 0x98, 0x80, 0, 0, 0, 0] }

@[pf_entry]
def staticValues (_state : State) : BoundedVec UInt16 4 :=
  { length := 3, values := #v[1, 513, 65535, 0] }

@[pf_entry]
def echoBytes (_state : State) (bytes : BoundedBytes 8) : BoundedBytes 8 :=
  bytes

@[pf_entry]
def echoString (_state : State) (text : BoundedString 8) : BoundedString 8 :=
  text

/-- A raw scalar can deliberately construct malformed UTF-8 for the String output guard. -/
@[pf_entry]
def stringWithByte (_state : State) (byte : UInt64) : BoundedString 8 :=
  { length := 1, values := #v[byte.toUInt8, 0, 0, 0, 0, 0, 0, 0] }

/-- The output adapter, not the source constructor, owns the runtime capacity check. -/
@[pf_entry]
def bytesWithLength (_state : State) (length : UInt64) : BoundedBytes 8 :=
  { length := length.toUInt32, values := #v[1, 2, 3, 4, 5, 6, 7, 8] }

end Examples.NearOutput
