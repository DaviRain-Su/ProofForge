import ProofForge
import ProofForge.Svm.Commands
import ProofForge.Evm.Commands
import ProofForge.Wasm.Near.Commands
import Examples.Svm.TokenApprove
import Examples.Svm.TokenXfer
import Examples.EvmTokenErgonomics
import Examples.Near.NearFungibleLedger

/-!
# Cross-target Token-shaped conformance (N15 follow-up / wsm-near-conformance-001)

Unlike `Examples.Counter`, Token fixtures are **target-local**:
SVM SPL CPI stubs (`TokenApprove` / `TokenXfer`), EVM ERC-20-shaped ergonomics
(`EvmTokenErgonomics`), and NEAR NEP-141 ledger (`NearFungibleLedger`). Digests differ by
design; this spec pins the approve/transfer-shaped digest table and checks method-name
surfaces, documenting the shared conceptual subset and naming gaps.

Runtime engineering gates (not digests):
- SVM Mollusk: `runtime-tests/solana/tests/token_approve.rs`, `token_xfer.rs`
- EVM Anvil (full Token): `runtime-tests/evm/anvil_token.sh`
- NEAR sandbox: `runtime-tests/near/ledger.sh` → `ledger.py` (+ `ft_event.sh`, JSON FT input scripts)

See `docs/plan/tasks/wsm-near-conformance-001.md` for the full matrix.
-/

namespace Tests.CrossTargetTokenSpec

open ProofForge

-- Canonical Token-shaped registry digests (approve / transfer slice).
#guard ProofForge.Svm.Registry.digestOf "TokenApprove" == some "e99f2008d320e15c"
#guard ProofForge.Svm.Registry.digestOf "TokenXfer" == some "c9edc88528b425dd"
#guard ProofForge.Evm.Registry.digestOf "EvmTokenErgonomics" == some "138c08a82e1ad205"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearFungibleLedger" == some "e1e290ddec221fa5"

open Lean Elab Command

private def containsAll (hay : Array String) (needles : Array String) : Bool :=
  needles.all (fun n => hay.contains n)

elab "#pf_cross_target_token_check" : command => do
  let env ← getEnv
  -- SVM approve fixture
  let svmApprove ←
    match Extract.extractModuleIR env `Examples.Svm.TokenApprove none >>=
        ProofForge.Svm.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let svmApproveDigest := ProofForge.Svm.IR.digestHex svmApprove
  let svmApproveMethods := svmApprove.methods.map (·.ixName) |>.qsort (· < ·)
  unless svmApproveDigest == "e99f2008d320e15c" do
    throwError s!"TokenApprove digest mismatch: {svmApproveDigest}"
  unless containsAll svmApproveMethods #["approve", "get", "initialize"] do
    throwError s!"TokenApprove method surface missing approve/get/initialize: {svmApproveMethods}"
  -- SVM transfer-shaped fixture (`send`, not `transfer`)
  let svmXfer ←
    match Extract.extractModuleIR env `Examples.Svm.TokenXfer none >>=
        ProofForge.Svm.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let svmXferDigest := ProofForge.Svm.IR.digestHex svmXfer
  let svmXferMethods := svmXfer.methods.map (·.ixName) |>.qsort (· < ·)
  unless svmXferDigest == "c9edc88528b425dd" do
    throwError s!"TokenXfer digest mismatch: {svmXferDigest}"
  unless containsAll svmXferMethods #["get", "initialize", "send"] do
    throwError s!"TokenXfer method surface missing send/get/initialize: {svmXferMethods}"
  -- EVM approve / transfer / transferFrom ergonomics
  let evm ←
    match Extract.extractModuleIR env `Examples.EvmTokenErgonomics none >>=
        ProofForge.Evm.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let evmDigest := ProofForge.Evm.IR.digestHex evm
  let evmMethods :=
    (#[evm.constructor.ixName] ++ evm.entries.map (·.ixName)) |>.qsort (· < ·)
  unless evmDigest == "138c08a82e1ad205" do
    throwError s!"EvmTokenErgonomics digest mismatch: {evmDigest}"
  unless containsAll evmMethods #["approve", "flagOf", "initialize", "transfer", "transferFrom"] do
    throwError s!"EvmTokenErgonomics method surface diverged: {evmMethods}"
  -- NEAR NEP-141 transfer surface (no approve / allowance)
  let near ←
    match Extract.extractModuleIR env `Examples.Near.NearFungibleLedger none >>=
        ProofForge.Wasm.Near.IR.fromExtracted with
    | .ok program => pure program
    | .error reason => throwError reason
  let nearDigest := ProofForge.Wasm.Near.IR.digestHex near
  let nearMethods :=
    (#[near.initializer.ixName] ++ near.entries.map (·.ixName)) |>.qsort (· < ·)
  unless nearDigest == "e1e290ddec221fa5" do
    throwError s!"NearFungibleLedger digest mismatch: {nearDigest}"
  unless containsAll nearMethods #["ft_transfer", "ft_transfer_call", "ft_balance_of", "initialize"] do
    throwError
      s!"NearFungibleLedger missing transfer-shaped FT surface: {nearMethods}"
  -- Shared conceptual subset (names differ by target ABI):
  --   transfer-shaped: SVM `send` | EVM `transfer` | NEAR `ft_transfer`
  --   approve-shaped:  SVM `approve` | EVM `approve` | NEAR — gap (NEP-141)
  unless svmApproveMethods.contains "approve" &&
      evmMethods.contains "approve" &&
      !nearMethods.contains "approve" do
    throwError "approve surface expectation failed (SVM+EVM present, NEAR absent)"
  unless svmXferMethods.contains "send" &&
      evmMethods.contains "transfer" &&
      nearMethods.contains "ft_transfer" do
    throwError "transfer-shaped surface expectation failed"
  logInfo
    m!"cross-target-token: approve svm={svmApproveDigest} evm={evmDigest}; \
transfer svm={svmXferDigest} near={nearDigest}; \
gaps=NEAR.approve SVM.transfer_name(EVM.transfer↔SVM.send↔NEAR.ft_transfer)"

#pf_cross_target_token_check

#pf_build Examples.Svm.TokenApprove
#pf_build Examples.Svm.TokenXfer
#pf_evm_build Examples.EvmTokenErgonomics
#pf_near_build Examples.Near.NearFungibleLedger

end Tests.CrossTargetTokenSpec
