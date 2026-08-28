import ProofForge

/-!
EVM-SDK-1 module surface tests for `ProofForge.Evm.Sdk.Access`. Host stubs make
`Context.caller` comparisons trivially true and zero-address checks true; the behavioral gates are
verified on-chain by `runtime-tests/evm/anvil_twostep_counter.sh` and
`anvil_credits.sh`, and extraction/emission by `Tests.TwoStepCounterSpec` /
`Tests.CreditsSpec`.

The aggregate `Tests.lean` imports this module.
-/

namespace Tests.AccessSdkSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Access

def sample : Address := ⟨1, 2, 3⟩

/-- One fixed pending address, with no map namespace or runtime storage geometry. -/
def emptyOwnership : Ownership := Ownership.none
def nominatedOwnership : Ownership := emptyOwnership.nominate sample

#guard emptyOwnership == Address.zero
#guard nominatedOwnership == sample
#guard nominatedOwnership.cancel == Ownership.none
#guard nominatedOwnership.consume == Ownership.none

/- Flag values are explicit, documented UInt8 constants. -/
#guard runningFlag == 0
#guard pausedFlag == 1

/- Gates over explicit handles. -/
#guard requireRunning runningFlag == true
#guard requireRunning pausedFlag == false
-- Host stub: `Address.eq`/`Context.caller` evaluate true; extraction owns the real gate.
#guard requireOwner sample == true

/- Host stubs report every address as zero, so nomination gates remain false; Anvil owns the real
address behavior. Replacement/clear semantics above are ordinary structural values. -/
#guard emptyOwnership.isPending sample == false
#guard nominatedOwnership.isPending sample == false
#guard nominatedOwnership.nominationOf sample == 0

/- Revert terminals evaluate to 0 under host stubs. -/
#guard ownerViolation == 0
#guard runningViolation == 0

end Tests.AccessSdkSpec
