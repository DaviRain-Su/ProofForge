import ProofForge.Svm.Sdk

/-!
Independent consumer for canonical SVM program identities and allocation-free SPL Token state
views. Physical account 0 is ProofForge state; 1 is the executable Token program, 2 is a token
account, 3 is its mint, and 4 is its authority. All geometry is compiler-static.
-/

namespace Examples.Svm.TokenStateView
open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | invalid
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] def tokenProgram : Account.Handle := .at 1
@[pf_inline] def tokenAccount : Token.AccountState :=
  .classic (.at 2) tokenProgram
@[pf_inline] def mintAccount : Token.MintState :=
  .classic (.at 3) tokenProgram
@[pf_inline] def authority : Account.Handle := .at 4

@[pf_entry]
def init (_seed : UInt64) : State := { dummy := 0 }

@[pf_entry]
def touch (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then .ok ({ dummy := 0 }, 0) else .error .invalid

@[pf_entry]
def get (_s : State) : UInt64 := 0

@[pf_entry]
def programValid (_s : State) : UInt64 :=
  if Program.classicToken.matches tokenProgram then 1 else 0

@[pf_entry]
def accountValid (_s : State) : UInt64 :=
  if tokenAccount.packedValid then 1 else 0

@[pf_entry]
def accountInitialized (_s : State) : UInt64 :=
  if tokenAccount.isInitialized then 1 else 0

@[pf_entry]
def accountFrozen (_s : State) : UInt64 :=
  if tokenAccount.isFrozen then 1 else 0

@[pf_entry]
def mintMatches (_s : State) : UInt64 :=
  if tokenAccount.mintIs mintAccount.account then 1 else 0

@[pf_entry]
def authorityMatches (_s : State) : UInt64 :=
  if tokenAccount.authorityIs authority then 1 else 0

@[pf_entry]
def amount (_s : State) : UInt64 := tokenAccount.amount

@[pf_entry]
def mintValid (_s : State) : UInt64 :=
  if mintAccount.packedValid then 1 else 0

@[pf_entry]
def mintInitialized (_s : State) : UInt64 :=
  if mintAccount.isInitialized then 1 else 0

@[pf_entry]
def supply (_s : State) : UInt64 := mintAccount.supply

@[pf_entry]
def decimals (_s : State) : UInt64 := mintAccount.decimals

end Examples.Svm.TokenStateView