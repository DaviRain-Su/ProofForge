import ProofForge

namespace Examples.Svm.AccountViewMutation

open ProofForge.Svm.Sdk

/--
`svm-rt-003` fixture: bounded remaining-account view + checked lamport mutation on the same
static account prefix. State account 0 is authenticated ProofForge state; `window` names physical
accounts 1..2; `vault`/`recipient` are fixed handles for those same accounts. The combined program
selects the variable+aliasing Loader-v3 walk so a backward duplicate of a prefix account resolves
instead of failing the view-only `0xff` check, while same-canonical transfer still fails closed.
-/
structure State where
  moved : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Remaining-account window over physical accounts 1 and 2. -/
@[pf_inline] def window : Account.View := Account.View.bounded 1 2

/-- Program-owned vault: physical account 1. -/
@[pf_inline] def vault : Account.Handle := Account.Handle.at 1

/-- Credit destination: physical account 2. -/
@[pf_inline] def recipient : Account.Handle := Account.Handle.at 2

@[pf_entry]
def init (initial : UInt64) : State :=
  { moved := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.moved

/-- View-only read of vault lamports through the remaining-account window (`index = 0`). -/
@[pf_entry]
def peekVault (_s : State) (index : UInt64) : UInt64 :=
  window.peekLamports index

/--
Transfer `amount` from vault to recipient, then return the vault's lamports as seen through the
remaining-account view at `index` (typically 0). The transfer preflight and the alias-aware walk
run before the view read of the post-debit balance.
-/
@[pf_entry]
def moveAndPeek (s : State) (amount : UInt64) (index : UInt64) : Except Error (State × UInt64) :=
  if s.moved ≤ u64Max - amount then
    let _ := vault.transferLamports recipient amount
    let next := s.moved + amount
    .ok ({ moved := next }, window.peekLamports index)
  else
    .error .overflow

end Examples.Svm.AccountViewMutation
