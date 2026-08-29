import ProofForge.Svm.AccountStorage

/-!
# SVM checked physical lamport transfer

Target-owned component vocabulary for moving lamports between two statically addressed account
headers. This is a physical header mutation, not a CPI: the runtime preflights both writable
flags, the source's current-program ownership, the source balance, the destination addition
overflow, and canonical-header distinctness (duplicate aliases fail closed) before performing
exactly one debit and one credit. The destination may be foreign-owned; there is no executable
prohibition. Amount zero is a validated no-op. Generic SVM Ops/IR/CFG use only the existing
Component bridge; no top-level operation is added.
-/

namespace ProofForge.Svm.Lamports

/-- One checked lamport movement between two compile-time physical account indexes. The indexes
must be statically distinct; canonical-pointer equality at runtime (including Loader-v3 duplicate
aliases) is rejected before any write. `amount` stays an ordinary dynamic operand. -/
inductive Call (V : Type) where
  | transfer (source destination : Nat) (amount : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .transfer source destination amount =>
      .transfer source destination (mapValue amount)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .transfer source destination amount =>
      return .transfer source destination (← mapValue amount)

def Call.values : Call V → Array V
  | .transfer _ _ amount => #[amount]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

/-- Both header words are read and written exactly once; the signed total delta is zero. -/
def Call.effects : Call V → AccountStorage.EffectSummary
  | .transfer source destination _ =>
      { reads := #[source, destination]
        writes := #[source, destination] }

def Call.minAccounts (measure : V → Nat) : Call V → Nat
  | .transfer source destination amount =>
      Nat.max (Nat.max source destination + 1) (measure amount)

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .transfer source destination amount =>
      source < accountLimit && destination < accountLimit && source != destination &&
        valueWellFormed amount

/-- Stable target-IR spelling. -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .transfer source destination amount =>
      s!"lamports.transfer.{source}.{destination}({renderValue amount})"

end ProofForge.Svm.Lamports
