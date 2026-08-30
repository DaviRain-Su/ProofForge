import ProofForge

namespace Examples.LamportTransfer

open ProofForge.Svm.Sdk

/--
Application fixture for the checked SVM lamport-transfer effect. State account 0 is authenticated
ProofForge state; the compile-time `vault`/`recipient` handles name physical accounts 1 and 2 once
and every entry moves lamports between their walked canonical headers. The target preflights both
writable flags, vault ownership by the current program, balance, destination overflow, and
canonical-header distinctness (Loader-v3 duplicate aliases fail closed) before either store; any
violation is `Custom(1)` with no writes and no state change. Amount zero is a validated no-op.
-/
structure State where
  moved : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- 2^64 - 1。Lean 4.31 无 `UInt64.max`。 -/
def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Program-owned vault funding every transfer: physical account 1. -/
@[pf_inline] def vault : Account.Handle := Account.Handle.at 1

/-- Credit destination: physical account 2. It may be foreign-owned but must be writable. -/
@[pf_inline] def recipient : Account.Handle := Account.Handle.at 2

@[pf_entry]
def init (initial : UInt64) : State :=
  { moved := initial }

@[pf_entry]
def get (s : State) : UInt64 :=
  s.moved

/--
Move `amount` lamports from the vault to the recipient and record the cumulative moved total in
state, returning the amount actually moved. The lamport effect runs before the state store, so a
rejected transfer (non-writable account, foreign-owned vault, insufficient balance, crediting
overflow, or duplicate alias) leaves both balances and the committed state byte-identical.
-/
@[pf_entry]
def move (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if s.moved ≤ u64Max - amount then
    let _ := vault.transferLamports recipient amount
    let next := s.moved + amount
    .ok ({ moved := next }, amount)
  else
    .error .overflow

/-- Read the vault's remaining lamports after moving `amount` to the recipient. -/
@[pf_entry]
def moveAndPeek (s : State) (amount : UInt64) : Except Error (State × UInt64) :=
  if s.moved ≤ u64Max - amount then
    let _ := vault.transferLamports recipient amount
    let next := s.moved + amount
    .ok ({ moved := next }, vault.lamports)
  else
    .error .overflow

/--
Close the program-owned vault and refund its complete lamport balance to the recipient. The
reusable SDK snapshots the balance, shrinks account data to zero, and drains the account through
the existing checked transfer. This entry adds no application-specific low-level operation and
does not change managed state.
-/
@[pf_entry]
def closeVault (_s : State) : UInt64 :=
  vault.closeTo recipient

end Examples.LamportTransfer
