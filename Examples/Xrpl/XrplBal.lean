import ProofForge

/-!
Per-caller JSON card. AlphaNet `set_data_object_field` writes under
`tx_field(sfAccount)` (the caller), not the contract account (-22).
Each wallet that calls `credit` therefore owns its own `ContractData`
with key `bal`. That is the XLS-0101 user-data shard, not a NEAR trie
and not a single-user contract vault.

`credit` takes one UINT64 via `function_param`. Each wallet still owns
its own `ContractData` (Owner = caller). Not a Map.
-/
namespace Examples.Xrpl.XrplBal
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

/-- Add `delta` to *this caller's* card. Another wallet has a different Owner. -/
@[pf_entry]
def credit (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - delta then
    .ok ({ bal := s.bal + delta }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.Xrpl.XrplBal