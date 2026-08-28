import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Fungible

/-!
# EVM SDK fungible balance ledger

Reusable O(1) operations over one explicit `Storage.AddressMap256` balance namespace. The handle
selects persistent EVM hashed storage at compile time; no runtime layout object or heap allocation
is introduced. Authorization, pause policy, zero-address policy, supply/cap accounting, allowance
spending, and events remain visible in the consuming contract.

Mutation methods have explicit checked preconditions so applications keep control of failure and
event ordering: `debit` follows `canDebit`, `credit` follows `canCredit`, and `transfer` follows
`canTransfer`. Credit rejects UInt256 wraparound. Transfer treats equal source/destination addresses
as a successful no-op after the debit gate, rather than writing the same map key twice.
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

@[pf_inline] def canCredit (balances : Balances) (owner : Address) (amount : UInt256) : Bool :=
  UInt256.ge (balances.nextAdd owner amount) (balances.balanceOf owner)

/-- Add and persist `amount` without UInt256 wraparound. Precondition:
`canCredit balances owner amount`. -/
@[pf_inline] def credit (balances : Balances) (owner : Address) (amount : UInt256) : UInt64 :=
  balances.put owner (balances.nextAdd owner amount)

/-- A transfer is valid when the source covers the debit and either both handles alias or the
destination addition cannot wrap. -/
@[pf_inline] def canTransfer (balances : Balances) (source destination : Address)
    (amount : UInt256) : Bool :=
  balances.canDebit source amount &&
    (Address.eq source destination || balances.canCredit destination amount)

/-- Persist one checked movement. Equal source/destination addresses are a no-op, avoiding two
writes through the same hashed key. Precondition: `canTransfer balances source destination amount`. -/
@[pf_inline] def transfer (balances : Balances) (source destination : Address)
    (amount : UInt256) : UInt64 :=
  if Address.eq source destination then
    0
  else
    balances.debit source amount ||| balances.credit destination amount

@[pf_inline] def insufficient (balances : Balances) (owner : Address)
    (amount : UInt256) : UInt64 :=
  balances.revertInsufficient owner amount

end Balances

end ProofForge.Evm.Sdk.Fungible
