import ProofForge
import Examples.MultiToken
import Examples.CraftToken

/-!
EVM-SDK-8 focused suite: bounded ERC-1155 key envelope, predicate surface, and two independent
consumers with stable extracted digests. Live mint/burn/transfer/operator matrices live in
`runtime-tests/evm/anvil_multitoken.sh` and `anvil_crafttoken.sh`; the aggregate EVM gate builds and
runs both consumers.
-/

namespace Tests.EvmErc1155Spec

open ProofForge.Evm
open ProofForge.Evm.Sdk
open Lean Elab Command

-- Key envelope: only ids with a zero top limb are encodable; tokenKey truncates, so every
-- consumer path must gate first.
#guard Erc1155.canEncode ⟨1, 0, 0, 0⟩
#guard Erc1155.canEncode ⟨0, 1, 0, 0⟩
#guard Erc1155.canEncode ⟨0, 0, 1, 0⟩
#guard !Erc1155.canEncode ⟨0, 0, 0, 1⟩
#guard !Erc1155.canEncode ⟨1, 0, 0, 1⟩
#guard Erc1155.tokenKey ⟨7, 8, 9, 0⟩ == (⟨7, 8, 9⟩ : Address)
#guard Erc1155.tokenKey ⟨7, 8, 9, 1⟩ == (⟨7, 8, 9⟩ : Address)

def specBalances : Erc1155.Balances := Storage.Layout.root.addressPairMap256.handle
def specOperators : Erc1155.Operators :=
  Storage.Layout.root.addressPairMap256.next.addressPairMap.handle
def specOwner : Address := ⟨1, 2, 3⟩
def specOther : Address := ⟨4, 5, 6⟩
def specId : UInt256 := ⟨7, 0, 0, 0⟩
def specAliasId : UInt256 := ⟨7, 0, 0, 1⟩
def specAmount : UInt256 := ⟨9, 0, 0, 0⟩

-- Disjoint compile-time namespaces for both consumers.
#guard Examples.MultiToken.balances.base == 0
#guard Examples.MultiToken.operators.base == 1
#guard Examples.CraftToken.balances.base == 0
#guard Examples.CraftToken.operators.base == 1
#guard Examples.CraftToken.supply.base == 2
#guard Examples.CraftToken.maxPerId == (⟨1000, 0, 0, 0⟩ : UInt256)

-- Pre-view gate at consumer entry level: the unencodable alias reads zero in both consumers.
-- `canEncode` is honest Bool arithmetic, so these guards are kernel-checkable on host; the
-- hashed-map load itself host-evaluates to zero (empty map).
#guard Examples.MultiToken.balanceOf ⟨0⟩ specOwner specId == UInt256.zero
#guard Examples.MultiToken.balanceOf ⟨0⟩ specOwner specAliasId == UInt256.zero
#guard Examples.CraftToken.balanceOf ⟨0⟩ specOwner specAliasId == UInt256.zero
#guard Examples.CraftToken.supplyOf ⟨0⟩ specAliasId == UInt256.zero

-- Pre-write/pre-auth envelope gates: unencodable ids fail every mutation and authorization
-- predicate. These guards are honest on host because `canEncode` is the first `&&` conjunct and
-- short-circuits before the comparison leaves. Positive encodable-id predicate semantics are NOT
-- host-checkable: `Runtime.evmGe256`/`evmEq20` are placeholder constants (`true`) whose real
-- behavior is an extraction contract, covered end-to-end by the Anvil fixtures.
#guard !Erc1155.Balances.canCredit specBalances specOwner specAliasId specAmount
#guard !Erc1155.Balances.canDebit specBalances specOwner specAliasId specAmount
#guard !Erc1155.Balances.canTransfer specBalances specOwner specOther specAliasId specAmount
#guard !Erc1155.canMint specBalances specOwner specAliasId specAmount
#guard !Erc1155.canBurn specBalances specOwner specAliasId specAmount
#guard !Erc1155.isApprovedOrOwner specOperators specOwner specOwner specAliasId
#guard !Erc1155.isApprovedOrOwner specOperators specOther specOwner specAliasId

/-- Compile-time surface check for the checked mint/burn/transfer branches. Map/comparison
Runtime leaves are extraction contracts and are not assigned host-evaluation semantics. -/
def erc1155TransferSurface (source to : Address) (tokenId amount : UInt256) : UInt64 :=
  if Erc1155.Balances.canTransfer specBalances source to tokenId amount then
    Erc1155.Balances.transfer specBalances source to tokenId amount
  else
    0

private def expectDigest (moduleName : Name) (digest : String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env moduleName with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless IR.digestHex program == digest do
    throwError s!"{moduleName} digest drifted: {IR.digestHex program}"

private def expectErc1155 : CommandElabM Unit := do
  expectDigest `Examples.MultiToken "9f4ed1a356c0a3be"
  expectDigest `Examples.CraftToken "12c90da14cef2729"

elab "#pf_guard_evm_erc1155" : command => expectErc1155

#pf_guard_evm_erc1155

end Tests.EvmErc1155Spec
