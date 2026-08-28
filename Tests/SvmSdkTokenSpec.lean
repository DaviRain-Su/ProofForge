import ProofForge.Svm.Sdk.Token
import Examples.TokenXfer
import Examples.TokenMint
import Examples.TokenMint2
import Examples.TokenAcc
import Examples.TokenApprove
import Examples.TokenFreeze
import Examples.TokenAuth
import Examples.TokenOwner
import Examples.TokenNative
import Examples.TokenSize
import Examples.TokenMs
import Examples.Seat
import Examples.Phoenix
import Examples.PhoenixV1Profile

open Lean Elab Command

namespace Tests.SvmSdkTokenSpec

open ProofForge.Svm.Sdk

#guard Token.transferChecked 7 6 == 0
#guard Token.mintToChecked 7 6 == 0
#guard Token.burnChecked 7 6 == 0
#guard Token.initializeAccount == 0
#guard Token.initializeMint6 == 0
#guard Token.closeAccount == 0
#guard Token.approve 7 == 0
#guard Token.approveChecked 7 6 == 0
#guard Token.revoke == 0
#guard Token.freezeAccount == 0
#guard Token.thawAccount == 0
#guard Token.setMintAuthority == 0
#guard Token.setAccountAuthority == 0
#guard Token.syncNative == 0
#guard Token.initializeMultisig2 == 0
#guard Token.baseAccountDataSize == 0

private def checkedAccounts : Token.CheckedTransferAccounts := .at 7 1 3 5 0
private def uncheckedAccounts : Token.UncheckedTransferAccounts := .at 7 5 3 5

#guard checkedAccounts.wellFormed
#guard uncheckedAccounts.wellFormed
#guard (CpiAccount.Handle.at 62).wellFormed
#guard !(CpiAccount.Handle.at 63).wellFormed
#guard !(Token.CheckedTransferAccounts.at 63 1 2 3 0).wellFormed
#guard Token.transferCheckedWith checkedAccounts 7 6 == 0
#guard Token.transferCheckedSignedWith checkedAccounts 7 6 #[] 0 == 0
#guard Token.transferSignedWith uncheckedAccounts 7 #[] 0 == 0

#guard Examples.Phoenix.baseDepositTokenAccounts.wellFormed
#guard Examples.Phoenix.quoteDepositTokenAccounts.wellFormed
#guard Examples.Phoenix.baseWithdrawTokenAccounts.wellFormed
#guard Examples.Phoenix.quoteWithdrawTokenAccounts.wellFormed
#guard Examples.PhoenixV1Profile.baseWithdrawTokenAccounts.wellFormed
#guard Examples.PhoenixV1Profile.quoteWithdrawTokenAccounts.wellFormed

private def expectCanonical (module : Name) (expected : String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let actual := ProofForge.Svm.IR.digestHex program
  unless actual == expected do
    throwError s!"{module}: SDK facade changed canonical IR: {actual}"

elab "#pf_guard_svm_token_facades" : command => do
  expectCanonical `Examples.TokenXfer "c9edc88528b425dd"
  expectCanonical `Examples.TokenMint "f7535d90750f9692"
  expectCanonical `Examples.TokenMint2 "89ae474933102cb4"
  expectCanonical `Examples.TokenAcc "53013fc1bc2e0753"
  expectCanonical `Examples.TokenApprove "e99f2008d320e15c"
  expectCanonical `Examples.TokenFreeze "6d4fceb52be9cf0a"
  expectCanonical `Examples.TokenAuth "bf3d403346f51b82"
  expectCanonical `Examples.TokenOwner "d29884f00e7311b7"
  expectCanonical `Examples.TokenNative "5bc920f79c3711f0"
  expectCanonical `Examples.TokenSize "fa48e892121ea415"
  expectCanonical `Examples.TokenMs "672b83a54f057f79"
  expectCanonical `Examples.Seat "831f313077f89947"

#pf_guard_svm_token_facades

end Tests.SvmSdkTokenSpec
