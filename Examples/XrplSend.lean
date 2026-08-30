import ProofForge

/-!
Credit another AccountID's ContractData card with a UINT64 amount.
Destination is three UINT64 limbs (little-endian bytes 0..7 / 8..15 / 16..19)
plus `amount`. `Context.storeOwnerLimbs` rewrites persist Owner before the
store. Not a Map, not `setUserData`, not a Payment.
-/
namespace Examples.XrplSend

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Write `amount` onto the card owned by `(w0,w1,w2)`. Caller pays.
Evaluating `storeOwnerLimbs` rewrites persist Owner before the store. -/
@[pf_entry]
def credit (_s : State) (w0 w1 w2 amount : UInt64) : Except Error (State × UInt64) :=
  if Context.storeOwnerLimbs w0 w1 w2 ≤ u64Max then
    .ok ({ bal := amount }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplSend
