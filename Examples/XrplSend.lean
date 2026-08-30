import ProofForge

/-!
Credit another AccountID's ContractData card. Destination is three UINT64
limbs via `function_param` (little-endian bytes 0..7 / 8..15 / 16..19).
`Context.storeOwner` rewrites persist Owner before the store. Not a Map,
not `setUserData`.
-/
namespace Examples.XrplSend

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Write `dest.w2` onto the card owned by `(w0,w1,w2)`. Caller pays. -/
@[pf_entry]
def credit (_s : State) (w0 w1 w2 : UInt64) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ bal := Context.storeOwnerLimbs w0 w1 w2 }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplSend
