import ProofForge
import Examples.Evm.Collectible
import Examples.Evm.Badge

/-!
EVM-SDK-7a focused suite: ERC-721 core predicates, token-id encoding limits, and two independent
consumers with stable extracted digests. Live mint/approve/transfer/burn matrices live in
`runtime-tests/evm/anvil_collectible.sh` and `anvil_badge.sh`.
-/

namespace Tests.EvmErc721Spec

open ProofForge.Evm
open ProofForge.Evm.Sdk
open Lean Elab Command

#guard Erc721.canEncode ⟨1, 0, 0, 0⟩
#guard Erc721.canEncode ⟨0, 1, 0, 0⟩
#guard Erc721.canEncode ⟨0, 0, 1, 0⟩
#guard !Erc721.canEncode ⟨0, 0, 0, 1⟩
#guard !Erc721.canEncode ⟨1, 0, 0, 1⟩
#guard Erc721.tokenKey ⟨7, 8, 9, 0⟩ == (⟨7, 8, 9⟩ : Address)
#guard Erc721.tokenKey ⟨7, 8, 9, 1⟩ == (⟨7, 8, 9⟩ : Address)
#guard Erc721.packAddress ⟨1, 2, 3⟩ == (⟨1, 2, 3, 0⟩ : UInt256)
#guard Erc721.unpackAddress ⟨1, 2, 3, 9⟩ == (⟨1, 2, 3⟩ : Address)
#guard Erc721.one == (⟨1, 0, 0, 0⟩ : UInt256)

#guard Examples.Evm.Collectible.owners.base == 0
#guard Examples.Evm.Collectible.approvals.base == 1
#guard Examples.Evm.Collectible.operators.base == 2
#guard Examples.Evm.Collectible.balances.base == 3
#guard Examples.Evm.Badge.owners.base == 0
#guard Examples.Evm.Badge.approvals.base == 1
#guard Examples.Evm.Badge.operators.base == 2
#guard Examples.Evm.Badge.balances.base == 3

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

private def expectErc721 : CommandElabM Unit := do
  expectDigest `Examples.Evm.Collectible "d520f4e720c2fb7b"
  expectDigest `Examples.Evm.Badge "c15c71dbbc936fc7"

elab "#pf_guard_evm_erc721" : command => expectErc721

#pf_guard_evm_erc721

end Tests.EvmErc721Spec
