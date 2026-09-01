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

/-- Output-only specialized JSON scalar fixtures. These are not object methods or generic JSON. -/
@[pf_entry] def jsonU128Zero (_state : State) : UInt128 := ⟨0, 0⟩
@[pf_entry] def jsonU128Two64 (_state : State) : UInt128 := ⟨0, 1⟩
@[pf_entry] def jsonU128Two64PlusOne (_state : State) : UInt128 := ⟨1, 1⟩
@[pf_entry] def jsonU128Asymmetric (_state : State) : UInt128 := ⟨2, 1⟩
@[pf_entry] def jsonU128Max (_state : State) : UInt128 :=
  ⟨0xffffffffffffffff, 0xffffffffffffffff⟩

/-- Exact packed 0..31 byte sequence for the NEP-148 hash Base64 prerequisite. -/
@[pf_entry] def jsonBase64Hash32 (_state : State) :
    ProofForge.Wasm.Near.Runtime.Base64Hash32Result :=
  { w0 := 0x0706050403020100
    w1 := 0x0f0e0d0c0b0a0908
    w2 := 0x1716151413121110
    w3 := 0x1f1e1d1c1b1a1918 }

@[pf_entry] def jsonBase64Hash32Zero (_state : State) :
    ProofForge.Wasm.Near.Runtime.Base64Hash32Result :=
  { w0 := 0, w1 := 0, w2 := 0, w3 := 0 }

@[pf_entry] def jsonBase64Hash32Max (_state : State) :
    ProofForge.Wasm.Near.Runtime.Base64Hash32Result :=
  { w0 := 0xffffffffffffffff, w1 := 0xffffffffffffffff
    w2 := 0xffffffffffffffff, w3 := 0xffffffffffffffff }

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
