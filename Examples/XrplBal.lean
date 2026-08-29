import ProofForge

/-!
Per-caller JSON card. AlphaNet `set_data_object_field` writes under
`tx_field(sfAccount)` (the caller), not the contract account (-22).
Each wallet that calls `credit` therefore owns its own `ContractData`
with key `bal`. That is the XLS-0101 user-data shard, not a NEAR trie
and not a single-user contract vault.

Zero function parameters: public AlphaNet 502s ContractCall Parameters.
-/
namespace Examples.XrplBal

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

/-- Add 1 to *this caller's* card. Another wallet has a different Owner. -/
@[pf_entry]
def credit (s : State) : Except Error (State × UInt64) :=
  if s.bal ≤ u64Max - 1 then
    .ok ({ bal := s.bal + 1 }, (0 : UInt64))
  else
    .error .overflow

@[pf_entry]
def get (s : State) : UInt64 :=
  s.bal

end Examples.XrplBal
