import Examples.Svm.PubkeyGate
import Lean
import ProofForge

/-!
Focused SVM SDK `Pubkey` gates. `Examples.Svm.PubkeyGate` independently consumes the first-class
Pubkey value: fixed keys, keys/owners projected from statically selected accounts, keys built
once from runtime scalar words, and complete-key/owner equality, inequality, and canonical
matching, all through named APIs with no word-level magic at application sites.

These guards pin descriptor erasure (every Pubkey reduces to the existing four account
key/owner word queries), prove no new operation/IR/component/emitter vocabulary is needed, and
pin the emitted sBPF comparisons for all four limbs. Behavioral equal/different coverage,
differences outside word0, owner-vs-key matching, and the fail-closed gated mutation are locked
by the Mollusk matrix in `runtime-tests/solana/tests/pubkey_gate.rs`.
-/

namespace Tests.SvmSdkPubkeySpec

open Lean Elab Command
open Examples.Svm.PubkeyGate
open ProofForge.Svm.Sdk

#pf_build Examples.Svm.PubkeyGate
#pf_build Examples.Svm.PubkeyGate

-- Construction is literal and projections are exact, with no word magic at call sites.
#guard Pubkey.ofWords 1 2 3 4 == { word0 := 1, word1 := 2, word2 := 3, word3 := 4 }
#guard expectedAuthority.word0 == 4363037911745304074
#guard expectedAuthority.word1 == 7049941761903427640
#guard expectedAuthority.word2 == 2783927094010722786
#guard expectedAuthority.word3 == 9388334143586028085
#guard expectedOwner.word0 == 9206327822447524757
#guard expectedOwner.word3 == 11478135293500621328

-- Complete-value equality/inequality cover all four limbs, including differences outside word0.
#guard (Pubkey.ofWords 1 2 3 4).equals (Pubkey.ofWords 1 2 3 4)
#guard !(Pubkey.ofWords 1 2 3 4).equals (Pubkey.ofWords 0 2 3 4)
#guard !(Pubkey.ofWords 1 2 3 4).equals (Pubkey.ofWords 1 0 3 4)
#guard !(Pubkey.ofWords 1 2 3 4).equals (Pubkey.ofWords 1 2 0 4)
#guard !(Pubkey.ofWords 1 2 3 4).equals (Pubkey.ofWords 1 2 3 0)
#guard (Pubkey.ofWords 1 2 3 4).notEquals (Pubkey.ofWords 1 2 3 0)
#guard !(Pubkey.ofWords 1 2 3 4).notEquals (Pubkey.ofWords 1 2 3 4)

-- Host stubs are irreducible zeros: a projected account key is the zero Pubkey on the host,
-- so `grants` accepts exactly the all-zero key and rejects the fixed authority key.
#guard authority.key == Pubkey.ofWords 0 0 0 0
#guard authority.owner == Pubkey.ofWords 0 0 0 0
#guard grants (Pubkey.ofWords 0 0 0 0) authority
#guard !grants expectedAuthority authority
#guard authority.sameKey peer
#guard authority.ownerIsKeyOf programAccount

-- Static handle bounds still hold for every fixed account.
#guard authority.wellFormed && peer.wellFormed && programAccount.wellFormed
#guard !(Account.Handle.at 64).wellFormed

/-- Collect the SVM value extensions used anywhere in an op tree. -/
partial def svmValKinds (ops : Array ProofForge.Extract.IR.Op) :
    Array ProofForge.Svm.Ops.ValKind :=
  let rec goVal (v : ProofForge.Extract.IR.Val) : Array ProofForge.Svm.Ops.ValKind :=
    match v with
    | .ext kind operands =>
      let here := match kind with
        | .svm k => #[k]
        | .evm _ | .xrpl _ | .near _ => #[]
      here ++ operands.foldl (fun acc o => acc ++ goVal o) #[]
    | .field base _ => goVal base
    | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
    | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
      goVal l ++ goVal r
    | .bitNot x => goVal x
    | .indexGet base _ idx _ => goVal base ++ goVal idx
    | .select _ l r t e => goVal l ++ goVal r ++ goVal t ++ goVal e
    | _ => #[]
  ops.foldl (init := #[]) fun acc op =>
    acc ++
      match op with
      | .letLocal _ v | .setLocal _ v | .storeField _ v | .okState v
      | .returnU64 v | .returnState v => goVal v
      | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
      | .checkedDivU64 l r | .checkedModU64 l r => goVal l ++ goVal r
      | .ite _ l r thn els =>
        goVal l ++ goVal r ++ svmValKinds thn ++ svmValKinds els
      | .forBody _ body => svmValKinds body
      | _ => #[]

/-- True when an op tree contains no ext op payload (no component call and no CPI invoke). -/
partial def noExtOps (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.all fun op =>
    match op with
    | .ext _ => false
    | .ite _ _ _ thn els => noExtOps thn && noExtOps els
    | .forBody _ body => noExtOps body
    | _ => true

/-- Extraction and emission contract for the whole example. -/
elab "#pf_guard_pubkey_gate" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.Svm.PubkeyGate with
    | .ok program => pure program
    | .error reason => throwError reason
  let program ←
    match ProofForge.Svm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let names := source.methods.map (·.ixName)
  for expected in
      ["initialize", "accept", "authorityMatches", "get", "keyDiffers", "keysEqual",
        "ownerAuthenticated", "ownerIsPeerKey", "ownerMatches", "peerKeyAccepted",
        "suppliedMatches"] do
    unless names.contains expected do
      throwError s!"missing method {expected}"
  -- SDK composition only: no component call, no CPI invoke, no allocation primitive anywhere.
  for method in source.methods do
    unless noExtOps method.ops do
      throwError s!"{method.ixName}: unexpected ext op payload"
  -- Fixed-key matching reads exactly the four key words of physical account 1.
  let authMethod ←
    match source.methods.find? (·.ixName == "authorityMatches") with
    | some m => pure m
    | none => throwError "missing authorityMatches"
  let authKinds := svmValKinds authMethod.ops
  for word in [0, 1, 2, 3] do
    unless authKinds.contains (.accKeyWord 1 word) do
      throwError s!"authorityMatches did not read acc1 key word {word}"
  -- Owner matching reads the four owner words; key-vs-key reads both accounts.
  let ownerMethod ←
    match source.methods.find? (·.ixName == "ownerMatches") with
    | some m => pure m
    | none => throwError "missing ownerMatches"
  let ownerKinds := svmValKinds ownerMethod.ops
  for word in [0, 1, 2, 3] do
    unless ownerKinds.contains (.accOwnerWord 1 word) do
      throwError s!"ownerMatches did not read acc1 owner word {word}"
  let keysMethod ←
    match source.methods.find? (·.ixName == "keysEqual") with
    | some m => pure m
    | none => throwError "missing keysEqual"
  let keysKinds := svmValKinds keysMethod.ops
  for word in [0, 1, 2, 3] do
    unless keysKinds.contains (.accKeyWord 1 word) && keysKinds.contains (.accKeyWord 2 word) do
      throwError s!"keysEqual did not read both accounts at word {word}"
  -- The runtime-supplied key stays four scalar parameters; no aggregate input appears.
  let suppliedMethod ←
    match source.methods.find? (·.ixName == "suppliedMatches") with
    | some m => pure m
    | none => throwError "missing suppliedMatches"
  unless suppliedMethod.paramCount == 4 && suppliedMethod.paramTypes.size == 4 do
    throwError "suppliedMatches must keep four scalar u64 parameters"
  unless ProofForge.Svm.IR.cpiAccountCount program == 4 do
    throwError "static account prefix must be exactly the four named accounts"
  let asm ←
    match ProofForge.Svm.Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  -- Every limb of the fixed authority key is materialized once as a literal comparison.
  unless asm.contains "; load lit 4363037911745304074" &&
      asm.contains "; load lit 7049941761903427640" &&
      asm.contains "; load lit 2783927094010722786" &&
      asm.contains "; load lit 9388334143586028085" do
    throwError "missing fixed authority key limbs"
  -- Key words live at +8..+32 and owner words at +40..+64 of each walked account header.
  unless asm.contains "; load walked acc1 +8" && asm.contains "; load walked acc1 +16" &&
      asm.contains "; load walked acc1 +24" && asm.contains "; load walked acc1 +32" &&
      asm.contains "; load walked acc1 +40" && asm.contains "; load walked acc1 +48" &&
      asm.contains "; load walked acc1 +56" && asm.contains "; load walked acc1 +64" do
    throwError "missing complete acc1 key/owner walks"
  unless asm.contains "; load walked acc2 +8" && asm.contains "; load walked acc2 +32" &&
      asm.contains "; load walked acc3 +8" && asm.contains "; load walked acc3 +32" &&
      asm.contains "; load walked acc3 flag +3" do
    throwError "missing peer/program account walks or executable flag"
  -- No allocation, no heap bump, no CPI, no crypto syscall, no dynamic account index.
  if asm.contains "alloc" || asm.contains "sol_invoke" || asm.contains "sol_sha256" ||
      asm.contains "sol_keccak" then
    throwError "unexpected allocation, CPI, or crypto vocabulary"
  unless asm.contains "call sol_set_return_data" do
    throwError "missing return-data publication"

#pf_guard_pubkey_gate

end Tests.SvmSdkPubkeySpec
