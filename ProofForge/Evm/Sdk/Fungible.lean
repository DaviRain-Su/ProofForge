import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Fungible

/-!
# EVM SDK fungible balance ledger

Reusable O(1) operations over one explicit `Storage.AddressMap256` balance namespace. The handle
selects persistent EVM hashed storage at compile time; no runtime layout object or heap allocation
is introduced. Authorization, pause policy, zero-address policy, supply/cap accounting, allowance
spending, and events remain visible in the consuming contract.

`debit` must be called only after `canDebit` succeeds. Keeping the gate in application control
lets the caller compose its own failure ordering while this component owns the exact map read,
subtraction, write, and `Insufficient(held,wanted)` terminal. Credit and transfer are deliberately
not exposed until their overflow and same-address contracts are closed.
-/

/-- Compile-time handle to one persistent address-keyed UInt256 balance namespace. -/
abbrev Balances := Storage.AddressMap256

namespace Balances

@[pf_inline] def balanceOf (balances : Balances) (owner : Address) : UInt256 :=
  balances.get owner

@[pf_inline] def canDebit (balances : Balances) (owner : Address) (amount : UInt256) : Bool :=
  balances.containsAtLeast owner amount

/-- Subtract and persist `amount`. Precondition: `canDebit balances owner amount`. -/
@[pf_inline] def debit (balances : Balances) (owner : Address) (amount : UInt256) : UInt64 :=
  balances.put owner (balances.nextSub owner amount)

@[pf_inline] def insufficient (balances : Balances) (owner : Address)
    (amount : UInt256) : UInt64 :=
  balances.revertInsufficient owner amount

end Balances

end ProofForge.Evm.Sdk.Fungible
