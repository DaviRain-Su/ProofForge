import ProofForge
import Examples.Token
import Examples.Capped
import Examples.TipJar
import Examples.Vault
import Examples.Ownable

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

def paymentAddress : Address := ⟨1, 2, 3⟩
def paymentAmount : UInt256 := ⟨9, 0, 0, 0⟩

#guard Ether.accept paymentAmount == 9
#guard Ether.send paymentAddress paymentAmount == 9
#guard Ether.receive == 0
#guard ERC20.transfer paymentAddress paymentAddress paymentAmount == 9
#guard ERC20.balanceOfSelf paymentAddress == UInt256.zero
#guard ERC20.approve paymentAddress paymentAddress paymentAmount == 9
#guard ERC20.transferFrom paymentAddress paymentAddress paymentAddress paymentAmount == 9
#guard ERC20.allowance paymentAddress paymentAddress paymentAddress == UInt256.zero
#guard ERC20.permit paymentAddress paymentAddress paymentAddress paymentAmount paymentAmount
  27 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ == 9
#guard WETH.deposit paymentAddress paymentAmount == 9
#guard WETH.withdraw paymentAddress paymentAmount == 9
#guard UniswapV2.swapExact2 paymentAddress paymentAddress paymentAddress paymentAmount UInt256.zero == 9
#guard UniswapV2.swapExact3 paymentAddress paymentAddress paymentAddress paymentAddress
  paymentAmount UInt256.zero == 9

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
#guard ProofForge.Evm.IR.digestHex ProofForge.Evm.Golden.extractedTipJar == "754276e8063a7d08"
#guard ProofForge.Evm.IR.digestHex ProofForge.Evm.Golden.extractedVault == "a3ea1b5b2a69c0e3"
#guard ProofForge.Evm.IR.digestHex ProofForge.Evm.Golden.extractedOwnable == "ce6397521bd115fa"

end Tests.EvmSdkSpec
