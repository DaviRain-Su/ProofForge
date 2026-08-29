import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Fungible

/-!
# EVM SDK fungible ledgers

Reusable O(1) operations over explicit `Storage.AddressMap256` balance and
`Storage.AddressPairMap256` allowance namespaces. Each handle selects persistent EVM hashed storage
at compile time; no runtime layout object or heap allocation is introduced. Authorization, pause
policy, zero-address policy, supply/cap accounting, permit ownership, and events remain visible in
the consuming contract.

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


/-- **transfer 前置蕴含 debit 前置**。 -/
theorem canTransfer_canDebit (balances : Balances) (source destination : Address)
    (amount : UInt256) (h : canTransfer balances source destination amount = true) :
    canDebit balances source amount = true := by
  unfold canTransfer at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- **transfer 前置蕴含 credit 前置**（source ≠ destination 时）。 -/
theorem canTransfer_canCredit (balances : Balances) (source destination : Address)
    (amount : UInt256) (h : canTransfer balances source destination amount = true)
    (hne : Address.eq source destination = false) :
    canCredit balances destination amount = true := by
  unfold canTransfer at h
  simp only [Bool.and_eq_true, Bool.or_eq_true] at h
  rw [hne] at h
  cases h.2 with
  | inl hf => exact absurd hf (by simp)
  | inr hc => exact hc

end Balances

/-- Compile-time handle to one persistent owner/spender UInt256 allowance namespace. -/
abbrev Allowances := Storage.AddressPairMap256

namespace Allowances

@[pf_inline] def allowanceOf (allowances : Allowances) (owner spender : Address) : UInt256 :=
  allowances.get owner spender

/-- Set and persist an allowance. Authorization and event policy remain application-owned. -/
@[pf_inline] def approve (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt64 :=
  allowances.put owner spender amount

@[pf_inline] def nextIncrease (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt256 :=
  allowances.nextAdd owner spender amount

@[pf_inline] def canIncrease (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : Bool :=
  UInt256.ge (allowances.nextIncrease owner spender amount)
    (allowances.allowanceOf owner spender)

/-- Add and persist `amount` without UInt256 wraparound. Precondition:
`canIncrease allowances owner spender amount`. -/
@[pf_inline] def increase (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt64 :=
  allowances.approve owner spender (allowances.nextIncrease owner spender amount)

@[pf_inline] def canDecrease (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : Bool :=
  allowances.containsAtLeast owner spender amount

@[pf_inline] def nextDecrease (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt256 :=
  allowances.nextSub owner spender amount

/-- Subtract and persist `amount`. Precondition:
`canDecrease allowances owner spender amount`. -/
@[pf_inline] def decrease (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt64 :=
  allowances.approve owner spender (allowances.nextDecrease owner spender amount)

@[pf_inline] def canSpend (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : Bool :=
  allowances.canDecrease owner spender amount

/-- Consume a delegated allowance. Precondition: `canSpend allowances owner spender amount`. -/
@[pf_inline] def spend (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt64 :=
  allowances.decrease owner spender amount

@[pf_inline] def insufficient (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) : UInt64 :=
  allowances.revertInsufficient owner spender amount


/-- **spend 前置蕴含 decrease 前置**。 -/
theorem canSpend_canDecrease (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) (h : canSpend allowances owner spender amount = true) :
    canDecrease allowances owner spender amount = true := by
  unfold canSpend at h
  exact h

/-- **increase 前置蕴含 nextIncrease ≥ 旧值**（UInt256 不回绕蕴含）。 -/
theorem canIncrease_ge (allowances : Allowances) (owner spender : Address)
    (amount : UInt256) (h : canIncrease allowances owner spender amount = true) :
    UInt256.ge (nextIncrease allowances owner spender amount)
      (allowanceOf allowances owner spender) = true := by
  unfold canIncrease at h
  exact h

end Allowances

end ProofForge.Evm.Sdk.Fungible
