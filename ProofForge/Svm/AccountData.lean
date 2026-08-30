import ProofForge.Svm.AccountStorage
import ProofForge.Svm.Memory

/-!
# SVM checked fixed-account data resize

Target-owned component vocabulary for the current Solana `AccountInfo::resize` contract. This is
not a heap allocation and never exposes the serialized account pointer: Loader-v3 already reserves
`MAX_PERMITTED_DATA_INCREASE` bytes after every unique account's input data, and the operation only
changes one fixed account's current length after bounded preflight. Growth is zero-initialized,
including shrink-then-grow in the same invocation.

The managed ProofForge state account at physical index zero has a static extracted schema and is
therefore not resizeable through this component. An external fixed handle also fails closed if its
runtime account aliases that managed state account. Duplicate aliases among external positions
resolve to their shared canonical header, matching the account ABI without copying account data.
Generic SVM Ops/IR/CFG use only the existing Component bridge; no top-level operation is added.
-/

namespace ProofForge.Svm.AccountData

/-- Solana's per-account increase above the invocation's original data length. -/
def maxPermittedDataIncrease : Nat := 10 * 1024

/-- One zero-initializing resize of a compile-time fixed external account. -/
inductive Call (V : Type) where
  | resize (account : Nat) (newLength : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .resize account newLength => .resize account (mapValue newLength)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .resize account newLength => return .resize account (← mapValue newLength)

def Call.values : Call V → Array V
  | .resize _ newLength => #[newLength]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

/-- Resize reads the account header/original length and may write its length plus newly exposed
data bytes. The payload prefix remains byte-identical. -/
def Call.effects : Call V → AccountStorage.EffectSummary
  | .resize account _ => { reads := #[account], writes := #[account] }

def Call.minAccounts (measure : V → Nat) : Call V → Nat
  | .resize account newLength => Nat.max (account + 1) (measure newLength)

/-- Account zero is the fixed-schema managed state account. Dynamic length remains a normal value;
the target checks it against the 10 MiB account ceiling and the 10,240-byte original-length growth
budget before changing memory. -/
def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .resize account newLength =>
      0 < account && account < accountLimit && valueWellFormed newLength

/-- Stable target-IR spelling. -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .resize account newLength =>
      s!"account-data.resize.{account}({renderValue newLength})"

end ProofForge.Svm.AccountData
