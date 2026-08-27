import ProofForge
import Examples.Token
import Examples.Capped

namespace Tests.EvmSdkSpec

open ProofForge.Evm.Sdk

def firstMap : Storage.Allocated Storage.AddressMap256 :=
  Storage.Layout.root.addressMap256

def secondMap : Storage.Allocated Storage.AddressPairMap256 :=
  firstMap.next.addressPairMap256

def thirdMap : Storage.Allocated Storage.AddressMap256 :=
  secondMap.next.addressMap256

#guard firstMap.handle.base == 0
#guard secondMap.handle.base == 1
#guard thirdMap.handle.base == 2
#guard thirdMap.next.nextSlot == 3
#guard Address.zero == ⟨0, 0, 0⟩
#guard UInt256.zero == ⟨0, 0, 0, 0⟩

/-- Compile-time surface check for the typed map API. Runtime stubs intentionally evaluate to zero
on the Lean host; extraction assigns their EVM behavior. -/
def mapSurface (address : Address) (amount : UInt256) : UInt64 :=
  let balances := firstMap.handle
  let allowances := secondMap.handle
  balances.put address (balances.nextAdd address amount) |||
    allowances.put address Context.caller
      (allowances.nextSub address Context.caller amount)

#guard ProofForge.Evm.IR.digestHex ProofForge.Evm.Golden.extractedToken == "4da7ac248a0fb556"
#guard ProofForge.Evm.IR.digestHex ProofForge.Evm.Golden.extractedCapped == "cb058e662f968f65"

end Tests.EvmSdkSpec
