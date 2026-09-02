import ProofForge
import Examples.Svm.TokenStateView

namespace Tests.SvmSdkTokenStateSpec

open Lean Elab Command
open ProofForge.Svm
open ProofForge.Svm.Sdk

/-! ## Canonical 32-byte program identities -/

#guard Program.system.key == Pubkey.ofWords 0 0 0 0
#guard Program.classicToken.key ==
  Pubkey.ofWords 10637895772709248262 12428223917890587609
    10463932726783620124 12178014311288245306
#guard Program.token2022.key ==
  Pubkey.ofWords 16037166466943343878 15766377600162546200
    2814109315776649910 18197816669093084670
#guard Program.associatedToken.key ==
  Pubkey.ofWords 17404482154777646988 9443360210905218491
    9516387326969993739 6483188794038914564
#guard Program.memoV4.key ==
  Pubkey.ofWords 15117832056309238277 1726465464192650243
    13549895254235327634 13996149263823438487
#guard Program.memoV3.key ==
  Pubkey.ofWords 441679977081162245 8951144367161615437
    9348226791408743804 10179266835579936740

#guard Examples.Svm.TokenStateView.tokenAccount.wellFormed
#guard Examples.Svm.TokenStateView.mintAccount.wellFormed
#guard !(Token.AccountState.classic (.at 64) (.at 1)).wellFormed
#guard !(Token.MintState.token2022 (.at 3) (.at 64)).wellFormed

/-! ## Descriptor erasure to existing account leaves -/

private partial def valHas
    (predicate : Ops.ValKind → Bool) : Ops.Val → Bool
  | .field base _ | .bitNot base => valHas predicate base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHas predicate lhs || valHas predicate rhs
  | .indexGet base _ index _ _ => valHas predicate base || valHas predicate index
  | .select _ lhs rhs thenValue elseValue =>
      valHas predicate lhs || valHas predicate rhs ||
        valHas predicate thenValue || valHas predicate elseValue
  | .ext kind operands => predicate kind || operands.any (valHas predicate)
  | _ => false

private partial def opsHave
    (predicate : Ops.ValKind → Bool) (ops : Array IR.Op) : Bool :=
  ops.any fun op =>
    let has := valHas predicate
    let here :=
      match op with
      | .letLocal _ value | .setLocal _ value | .forAccum _ value _
      | .storeField _ value | .okState value | .returnU64 value | .returnState value => has value
      | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
      | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
      | .indexSet _ lhs rhs _ _ => has lhs || has rhs
      | .invoke _ _ data _ bump =>
          data.any (fun item => item.value?.any has) || bump.any has
      | .component call => call.values.any has
      | _ => false
    here ||
      match op with
      | .ite _ _ _ thenOps elseOps => opsHave predicate thenOps || opsHave predicate elseOps
      | .forBody _ body => opsHave predicate body
      | _ => false

private def expectTokenStateViews : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.TokenStateView with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless IR.digestHex program == "79e777b300b87504" do
    throwError s!"TokenStateView digest drifted: {IR.digestHex program}"
  let method (name : String) : CommandElabM IR.Method := do
    let some found := program.methods.find? (·.ixName == name)
      | throwError s!"missing {name}"
    pure found
  let programValid ← method "programValid"
  unless opsHave (· == .isExecutableN 1) programValid.ops &&
      (List.range 4).all (fun word => opsHave (· == .accKeyWord 1 word) programValid.ops) do
    throwError "canonical program-id policy did not erase to executable + four key words"
  let accountValid ← method "accountValid"
  unless opsHave (· == .accDataLenN 2) accountValid.ops &&
      opsHave (· == .accDataWord 2 13) accountValid.ops &&
      (List.range 4).all (fun word =>
        opsHave (· == .accKeyWord 1 word) accountValid.ops &&
          opsHave (· == .accOwnerWord 2 word) accountValid.ops) do
    throwError "token account view lost exact length, state, program id, or owner authentication"
  let amount ← method "amount"
  unless opsHave (· == .accDataWord 2 8) amount.ops do
    throwError "token amount did not use the official aligned offset 64"
  let mintMatches ← method "mintMatches"
  unless (List.range 4).all (fun word =>
      opsHave (· == .accDataWord 2 word) mintMatches.ops &&
        opsHave (· == .accKeyWord 3 word) mintMatches.ops) do
    throwError "token mint relationship did not compare all 32 bytes"
  let authorityMatches ← method "authorityMatches"
  unless (List.range 4).all (fun word =>
      opsHave (· == .accDataWord 2 (word + 4)) authorityMatches.ops &&
        opsHave (· == .accKeyWord 4 word) authorityMatches.ops) do
    throwError "token authority relationship did not compare all 32 bytes"
  let mintValid ← method "mintValid"
  unless opsHave (· == .accDataLenN 3) mintValid.ops &&
      opsHave (· == .accDataWord 3 0) mintValid.ops &&
      opsHave (· == .accDataWord 3 5) mintValid.ops &&
      opsHave (· == .accDataWord 3 6) mintValid.ops do
    throwError "mint view lost exact length, COption tags, or initialized-byte validation"
  let supply ← method "supply"
  unless opsHave (· == .accDataWord 3 4) supply.ops &&
      opsHave (· == .accDataWord 3 5) supply.ops do
    throwError "unaligned mint supply did not use both official packed words"

elab "#pf_guard_svm_token_state_views" : command => expectTokenStateViews

#pf_guard_svm_token_state_views

end Tests.SvmSdkTokenStateSpec
