import ProofForge
import ProofForge.Evm.Sdk.Access

/-!
EVM-SDK-1 module surface tests for `ProofForge.Evm.Sdk.Access`. Host stubs make
`Context.caller` comparisons trivially true and map reads 0; the behavioral gates are
verified on-chain by `runtime-tests/evm/anvil_twostep_counter.sh` and
`anvil_credits.sh`, and extraction/emission by `Tests.TwoStepCounterSpec` /
`Tests.CreditsSpec`.

Not wired into `Tests.lean` yet: the coordinator owns the aggregate import. Run focused:
  lake env lean Tests/AccessSdkSpec.lean
-/

namespace Tests.AccessSdkSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Access

def sample : Address := ⟨1, 2, 3⟩

/-- Layout cursor: one namespace per Ownership, disjoint from what follows. -/
def firstOwnership : Storage.Allocated Ownership :=
  Ownership.allocate Storage.Layout.root

def afterMap : Storage.Allocated Storage.AddressMap256 :=
  firstOwnership.next.addressMap256

#guard firstOwnership.handle.pending.base == 0
#guard firstOwnership.next.nextSlot == 1
#guard afterMap.handle.base == 1
#guard afterMap.next.nextSlot == 2

/- Flag values are explicit, documented UInt8 constants. -/
#guard runningFlag == 0
#guard pausedFlag == 1

/- Gates over explicit handles. -/
#guard requireRunning runningFlag == true
#guard requireRunning pausedFlag == false
-- Host stub: `Address.eq`/`Context.caller` evaluate true; extraction owns the real gate.
#guard requireOwner sample == true

/- Two-step nomination host semantics: absent reads 0, nominate/cancel are raw writes. -/
#guard firstOwnership.handle.isPending sample == false
#guard firstOwnership.handle.nominate sample == 1
#guard firstOwnership.handle.cancel sample == 0
#guard firstOwnership.handle.consume == 0
#guard firstOwnership.handle.nominationOf sample == 0

/- Revert terminals evaluate to 0 under host stubs. -/
#guard ownerViolation == 0
#guard runningViolation == 0

end Tests.AccessSdkSpec
