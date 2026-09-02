import ProofForge

namespace Examples.Evm.EvmFindIndex
open ProofForge.Core.Value

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | rejected
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { marker := 0 }

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) == 0 then .ok ({ marker := 1 }, 1) else .error .rejected

/-- Typed first-match policy returns `none` rather than a sentinel; the EVM codec owns its tagged
tuple output and Core keeps the position+1 lowering detail private. -/
@[pf_entry]
def bytesFindIndex (_state : State) (haystack needle : BoundedBytes 3) : Option UInt64 :=
  haystack.findIndex? needle

/-- String search returns a UTF-8 byte offset after both canonical ABI tails pass validation. -/
@[pf_entry]
def stringsFindIndex (_state : State) (text needle : BoundedString 3) : Option UInt64 :=
  text.findIndex? needle

end Examples.Evm.EvmFindIndex