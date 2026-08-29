import ProofForge

/-!
Credit a compile-time other AccountID's ContractData card.
Live AlphaNet: `set_data_object_field` with that 20-byte Owner writes the
other user's shard (probe-other). Public RPC still has no AccountID parameter
(502), so the destination is a hex literal.

Second-wallet fixture rLpgximdBvEHy8TxUwyj6mjCRNcJju5qGG =
`d0bc2a540b15411f44a24dfb58d23ad5d9d9b350`.
-/
namespace Examples.XrplSend

open ProofForge.Wasm.Xrpl.Sdk

structure State where
  bal : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Compile-time destination. Mentioning it rewrites mem[0..19] before persist. -/
@[pf_inline] def dest : AccountId :=
  Context.accountLit "d0bc2a540b15411f44a24dfb58d23ad5d9d9b350"

@[pf_entry]
def init : State :=
  { bal := 0 }

/-- Write bal=1 onto `dest`'s card. Caller pays the ContractCall.
Mentioning `dest.w2` rewrites mem[0..19] to that AccountID before persist. -/
@[pf_entry]
def credit (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ bal := dest.w2 }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplSend
