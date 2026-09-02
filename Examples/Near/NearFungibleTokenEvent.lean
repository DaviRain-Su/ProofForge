import ProofForge

namespace Examples.Near.NearFungibleTokenEvent
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | event
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State := { value := 0 }

@[pf_entry]
def get (s : State) : UInt64 := s.value

@[pf_entry]
def mintZero (s : State) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.mint Context.caller { w0 := 0, w1 := 0 }
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def mintTwo64 (s : State) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.mint Context.caller { w0 := 0, w1 := 1 }
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def mintTwo64PlusOne (s : State) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.mint Context.caller { w0 := 1, w1 := 1 }
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def mintMax (s : State) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.mint Context.caller
    { w0 := 18446744073709551615, w1 := 18446744073709551615 }
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def transferMax (s : State) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.transfer Context.caller Context.self
    { w0 := 18446744073709551615, w1 := 18446744073709551615 }
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def burnTwo64 (s : State) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.burn Context.caller { w0 := 0, w1 := 1 }
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def mintMemo (s : State) (memo : BoundedString 16) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.mintWithMemo Context.caller { w0 := 0, w1 := 0 } 16 memo
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def transferMemo (s : State) (memo : BoundedString 16) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.transferWithMemo Context.caller Context.self
    { w0 := 1, w1 := 1 } 16 memo
  .ok ({ value := s.value + 1 }, 0)

@[pf_entry]
def burnMemo (s : State) (memo : BoundedString 16) : Except Error (State × UInt64) :=
  let _ := Events.FungibleToken.burnWithMemo Context.caller
    { w0 := 18446744073709551615, w1 := 18446744073709551615 } 16 memo
  .ok ({ value := s.value + 1 }, 0)

end Examples.Near.NearFungibleTokenEvent