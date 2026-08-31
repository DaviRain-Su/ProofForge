import ProofForge
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Emit
import ProofForge.Wasm.Xrpl.Commands
import Examples.Counter
import Examples.Clock
import Examples.EvmCtx
import Examples.XrplCtx
import Examples.XrplOwn
import Examples.Hash
import Examples.XrplHash
import Examples.XrplRt2
import Examples.XrplVec
import Examples.XrplSmoke
import Examples.XrplGate
import Examples.XrplHold
import Examples.XrplMark
import Examples.XrplBal
import Examples.XrplBalRt
import Examples.XrplRoot
import Examples.XrplTx
import Examples.XrplSend
import Examples.XrplPay
import Examples.XrplMint
import Examples.XrplLock
import Examples.XrplCard
import Examples.XrplVault
import Examples.XrplEmit
import Examples.XrplTip
import Examples.XrplGift
import Examples.XrplCash
import Examples.XrplBank
import Examples.XrplSafe
import Examples.XrplPool
import Examples.XrplFund
import Examples.XrplTreasury
import Examples.XrplToken
import Examples.XrplShare
import Examples.XrplTake
import Examples.XrplHoldEsc
import Examples.XrplVest
import Examples.XrplClaim
import Examples.XrplPayout
import Examples.XrplDual
import Examples.XrplLatch
import Examples.XrplEscape
import Examples.XrplNest
import Examples.XrplStep
import Examples.XrplRole
import Examples.XrplPeer
import Examples.XrplFlag
import Examples.XrplTab
import Examples.XrplHand
import Examples.XrplCrew

/-!
# XRPL Bedrock target tests (WASM family)

v0: registration rejects foreign leaves; digest is pinned; emitted WAT carries
`host_lib` imports and exported entries.
-/

open ProofForge

#guard !ProofForge.Wasm.Xrpl.Ops.Op.wellFormed (.ext .reserved)
#guard !(ProofForge.Wasm.Xrpl.Ops.OpExt.wellFormed
  (.reserved : ProofForge.Wasm.Xrpl.Ops.OpExt ProofForge.Wasm.Xrpl.Ops.Val))
#guard ProofForge.Wasm.Xrpl.Ops.ValKind.arity .reserved == 0

#guard ProofForge.Wasm.Xrpl.Registry.digestOf "Counter" == some "e029f72296e320be"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplCtx" == some "f483be9d20810b57"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplOwn" == some "d452894f75c0ff96"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplHash" == some "ce42ea8b4607843e"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplRt2" == some "1d6d712500b8daf0"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplVec" == some "e47db263444f8c7e"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplSmoke" == some "f8f474cfdfa499f6"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplGate" == some "c2495d166a25c8e0"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplHold" == some "e99965ac007e0da8"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplMark" == some "20c54e937ffbf0fc"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplBal" == some "3177150879f2b85a"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplBalRt" == some "dd80a5af3243dec2"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplRoot" == some "a8e6569035ec2d13"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplTx" == some "2a9d4e10cd7ecec9"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplSend" == some "a8e5e47454812f03"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplNest" == some "860982785dab0d6d"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplStep" == some "8273bd4064e4745a"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplRole" == some "bae46704480482ee"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplPeer" == some "b808c0cc3278fb10"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplFlag" == some "d71a13301ce82878"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplTab" == some "95e92ed0121f53e9"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplHand" == some "5c6813950576cdda"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplCrew" == some "ca03e80ef4a8218a"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplPay" == some "5f2a9ac1b78e08de"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplMint" == some "86625b1e737a9f82"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplLock" == some "d2c4673c64a8d0c"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplCard" == some "3b84bf36c5c309d7"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplVault" == some "6b6e2791d63443d8"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplEmit" == some "5d97e10e9319e9e1"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplTip" == some "7e760f9ff6b668e6"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplGift" == some "e722061475dea65e"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplCash" == some "86367a05030e0c5a"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplBank" == some "6a344e3db8cdf235"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplSafe" == some "317c295ada5d467c"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplPool" == some "57814a14c17161a5"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplFund" == some "8cc80156ad30a85c"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplTreasury" == some "4ace63cdcef0446b"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplToken" == some "d03a887e6b52e7a8"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplShare" == some "e53efc71c6393ba4"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplTake" == some "e31f80dc4c97ee66"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplHoldEsc" == some "2d5fcf19a07dfde1"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplVest" == some "9ccd6e0b0e597393"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplClaim" == some "4857c33431f624cb"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplPayout" == some "4d769f5622556277"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplDual" == some "d8b9fb0c4ce39299"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplLatch" == some "d65b586272018aed"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplEscape" == some "396ce61f0cb686e"
#guard ProofForge.Wasm.Xrpl.Registry.names == #["Counter", "XrplCtx", "XrplOwn", "XrplHash", "XrplRt2", "XrplVec", "XrplSmoke", "XrplGate", "XrplHold", "XrplMark", "XrplBal", "XrplBalRt", "XrplRoot", "XrplTx", "XrplSend", "XrplNest", "XrplStep", "XrplRole", "XrplPeer", "XrplFlag", "XrplTab", "XrplHand", "XrplCrew", "XrplPay", "XrplMint", "XrplLock", "XrplCard", "XrplVault", "XrplEmit", "XrplTip", "XrplGift", "XrplCash", "XrplBank", "XrplSafe", "XrplPool", "XrplFund", "XrplTreasury", "XrplToken", "XrplShare", "XrplTake", "XrplHoldEsc", "XrplVest", "XrplClaim", "XrplPayout", "XrplDual", "XrplLatch", "XrplEscape"]

open Lean Elab Command in
elab "#pf_xrpl_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .ok _ => throwError "expected xrpl to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "xrpl rejects" do
        throwError "unexpected xrpl rejection reason: {reason}"

#pf_xrpl_reject Examples.Clock

#pf_xrpl_reject Examples.EvmCtx

#pf_xrpl_reject Examples.Hash

#pf_xrpl_build Examples.Counter

#pf_xrpl_build Examples.XrplCtx

#pf_xrpl_build Examples.XrplOwn

#pf_xrpl_build Examples.XrplHash

#pf_xrpl_build Examples.XrplRt2

#pf_xrpl_build Examples.XrplVec

#pf_xrpl_build Examples.XrplSmoke

#pf_xrpl_build Examples.XrplGate

#pf_xrpl_build Examples.XrplHold

#pf_xrpl_build Examples.XrplMark

#pf_xrpl_build Examples.XrplBal

#pf_xrpl_build Examples.XrplBalRt

#pf_xrpl_build Examples.XrplRoot

#pf_xrpl_build Examples.XrplTx

#pf_xrpl_build Examples.XrplSend

#pf_xrpl_build Examples.XrplNest

#pf_xrpl_build Examples.XrplStep

#pf_xrpl_build Examples.XrplRole

#pf_xrpl_build Examples.XrplPeer

#pf_xrpl_build Examples.XrplFlag

#pf_xrpl_build Examples.XrplTab

#pf_xrpl_build Examples.XrplHand

#pf_xrpl_build Examples.XrplCrew

#pf_xrpl_build Examples.XrplPay

#pf_xrpl_build Examples.XrplMint

#pf_xrpl_build Examples.XrplLock

#pf_xrpl_build Examples.XrplCard

#pf_xrpl_build Examples.XrplVault

#pf_xrpl_build Examples.XrplEmit

#pf_xrpl_build Examples.XrplTip

#pf_xrpl_build Examples.XrplGift

#pf_xrpl_build Examples.XrplCash

#pf_xrpl_build Examples.XrplBank

#pf_xrpl_build Examples.XrplSafe

#pf_xrpl_build Examples.XrplPool

#pf_xrpl_build Examples.XrplFund

#pf_xrpl_build Examples.XrplTreasury

#pf_xrpl_build Examples.XrplToken

#pf_xrpl_build Examples.XrplShare

#pf_xrpl_build Examples.XrplTake

#pf_xrpl_build Examples.XrplHoldEsc

#pf_xrpl_build Examples.XrplVest

#pf_xrpl_build Examples.XrplClaim

#pf_xrpl_build Examples.XrplPayout

#pf_xrpl_build Examples.XrplDual

#pf_xrpl_build Examples.XrplLatch

#pf_xrpl_build Examples.XrplEscape

open Lean Elab Command in
elab "#pf_xrpl_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"get_current_ledger_obj_field\"",
          "(import \"host_lib\" \"get_data_object_field\"",
          "(import \"host_lib\" \"set_data_object_field\"",
          "(import \"host_lib\" \"function_param\"",
          "(import \"host_lib\" \"get_tx_field\"",
          "(import \"host_lib\" \"get_ledger_sqn\"",
          "(import \"host_lib\" \"get_parent_ledger_time\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"increment\") (result i32)",
          "(func (export \"get\")",
          "(func (export \"nonzero\")",
          "(i32.const 524290)",
          "(data (i32.const 64) \"value\")",
          "(return (i32.const 1))",
          "(return (i32.const 2))",
          "i64.add",
          "i64.sub",
          "i64.mul",
          "i64.div_u",
          "i64.rem_u",
          ";; digest=e029f72296e320be"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "xrpl_wasm_std" do
          throwError "wasm emit still mentions xrpl_wasm_std"
        unless !source.contains "get_current_contract_call" do
          throwError "wasm emit still mentions get_current_contract_call"
        unless !source.contains "\"get_data\"" do
          throwError "wasm emit still mentions get_data"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "wasm emit still uses wasm i64 params; XRPL fetches UINT64 via function_param"
        unless !source.contains "update_data" do
          throwError "wasm emit still uses update_data; this Bedrock image does not persist it"
        logInfo m!"proofforge-xrpl-test: {source.length} bytes of WAT passed anchor check"

#pf_xrpl_emit_check Examples.Counter

open Lean Elab Command in
elab "#pf_xrpl_own_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"get_tx_field\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "(func (export \"get\")",
          "(func (export \"ownerLo\")",
          "i64.eq",
          "(i32.const 3)",
          "(data (i32.const 64) \"owner0owner1owner2value\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing own anchor: {anchor}\n{source}"
        -- `splitOn` yields n+1 parts for n occurrences.
        let eqCount := (source.splitOn "i64.eq").length - 1
        unless eqCount ≥ 3 do
          throwError s!"wasm emit wants ≥3 i64.eq for three-limb compare, got {eqCount}\n{source}"
        unless !source.contains "eq_account" do
          throwError "wasm emit must not add eq_account host"
        logInfo m!"proofforge-xrpl-own: {source.length} bytes of WAT passed own anchor check"

#pf_xrpl_own_emit_check Examples.XrplOwn

open Lean Elab Command in
elab "#pf_xrpl_gate_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "(func (export \"renounce\") (result i32)",
          "(func (export \"get\")",
          "i64.eq",
          "(i32.const 3)",
          "(data (i32.const 64) \"owner0owner1owner2value\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing gate anchor: {anchor}\n{source}"
        unless !source.contains "eq_account" do
          throwError "wasm emit must not add eq_account host"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplGate must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-gate: {source.length} bytes of WAT passed gate anchor check"

#pf_xrpl_gate_emit_check Examples.XrplGate

open Lean Elab Command in
elab "#pf_xrpl_hold_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(func (export \"unpause\") (result i32)",
          "(func (export \"get\")",
          "i64.eq",
          "(i32.const 3)",
          "(i32.const 4)",
          "(data (i32.const 64) \"owner0owner1owner2pausedvalue\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing hold anchor: {anchor}\n{source}"
        unless !source.contains "eq_account" do
          throwError "wasm emit must not add eq_account host"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplHold must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-hold: {source.length} bytes of WAT passed hold anchor check"

#pf_xrpl_hold_emit_check Examples.XrplHold

open Lean Elab Command in
elab "#pf_xrpl_mark_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"compute_sha512_half\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"stamp\") (result i32)",
          "(func (export \"renounce\") (result i32)",
          "(func (export \"get\")",
          "i64.eq",
          "(i32.const 3)",
          "(i32.const 118)",
          "(i32.const 97)",
          "(i32.const 117)",
          "(i32.const 108)",
          "(i32.const 116)",
          "(call $compute_sha512_half",
          "(data (i32.const 64) \"owner0owner1owner2hashed\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing mark anchor: {anchor}\n{source}"
        unless !source.contains "eq_account" do
          throwError "wasm emit must not add eq_account host"
        unless !source.contains "sha256Lit" do
          throwError "wasm emit must not mention sha256Lit"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplMark must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-mark: {source.length} bytes of WAT passed mark anchor check"

#pf_xrpl_mark_emit_check Examples.XrplMark

open Lean Elab Command in
elab "#pf_xrpl_bal_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"credit\") (result i32)",
          "(func (export \"get\")",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(data (i32.const 64) \"bal\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing bal anchor: {anchor}\n{source}"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplBal must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-bal: {source.length} bytes of WAT passed bal anchor check"

#pf_xrpl_bal_emit_check Examples.XrplBal

open Lean Elab Command in
elab "#pf_xrpl_balrt_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"accountroot_id\"",
          "(import \"host_lib\" \"cache_le\"",
          "(import \"host_lib\" \"le_field\"",
          "(func (export \"stamp\") (result i32)",
          "(i32.const 393218)",
          "(i64.const 144115188075855871)",
          "(data (i32.const 64) \"drops\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing balrt anchor: {anchor}\n{source}"
        logInfo m!"proofforge-xrpl-balrt: {source.length} bytes of WAT passed balrt anchor check"

#pf_xrpl_balrt_alphanet_emit_check Examples.XrplBalRt

open Lean Elab Command in
elab "#pf_xrpl_root_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"accountroot_id\"",
          "(import \"host_lib\" \"cache_le\"",
          "(import \"host_lib\" \"le_field\"",
          "(func (export \"stamp\") (result i32)",
          "(i32.const 131076)",
          "(i32.const 131074)",
          "(i32.const 131085)",
          "(data (i32.const 64) \"seqflagsownc\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing root anchor: {anchor}\n{source}"
        logInfo m!"proofforge-xrpl-root: {source.length} bytes of WAT passed root anchor check"

#pf_xrpl_root_alphanet_emit_check Examples.XrplRoot

open Lean Elab Command in
elab "#pf_xrpl_tx_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"tx_field\"",
          "(func (export \"stamp\") (result i32)",
          "(i32.const 131076)",
          "(i32.const 393224)",
          "(i64.const 144115188075855871)",
          "(data (i32.const 64) \"tseqtfee\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing tx anchor: {anchor}\n{source}"
        logInfo m!"proofforge-xrpl-tx: {source.length} bytes of WAT passed tx anchor check"

#pf_xrpl_tx_alphanet_emit_check Examples.XrplTx

open Lean Elab Command in
elab "#pf_xrpl_send_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(i64.store (i32.const 0)",
          "(i64.store (i32.const 8)",
          "(i32.store (i32.const 16)",
          "(data (i32.const 64) \"bal\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing send anchor: {anchor}\n{source}"
        unless !source.contains "setUserData" do
          throwError "wasm emit must not mention setUserData"
        logInfo m!"proofforge-xrpl-send: {source.length} bytes of WAT passed send anchor check"

#pf_xrpl_send_alphanet_emit_check Examples.XrplSend

open Lean Elab Command in
elab "#pf_xrpl_nest_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"set_data_nested_object_field\"",
          "(import \"host_lib\" \"get_data_nested_object_field\"",
          "(func (export \"credit\") (result i32)",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(data (i32.const 64) \"userbal\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing nest anchor: {anchor}\\n{source}"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-nest: {source.length} bytes of WAT passed nest anchor check"

#pf_xrpl_nest_alphanet_emit_check Examples.XrplNest

open Lean Elab Command in
elab "#pf_xrpl_step_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "(func (export \"propose\") (result i32)",
          "(func (export \"accept\") (result i32)",
          "(func (export \"get\")",
          "i64.eq",
          "(i32.const 3)",
          "(data (i32.const 64) \"owner0owner1owner2pend0pend1pend2value\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing step anchor: {anchor}\n{source}"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplStep must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-step: {source.length} bytes of WAT passed step anchor check"

#pf_xrpl_step_emit_check Examples.XrplStep

open Lean Elab Command in
elab "#pf_xrpl_role_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "(func (export \"setOp\") (result i32)",
          "(func (export \"get\")",
          "i64.eq",
          "(i32.const 3)",
          "(data (i32.const 64) \"owner0owner1owner2op0op1op2value\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing role anchor: {anchor}\n{source}"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplRole must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-role: {source.length} bytes of WAT passed role anchor check"

#pf_xrpl_role_emit_check Examples.XrplRole

open Lean Elab Command in
elab "#pf_xrpl_peer_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"accountroot_id\"",
          "(import \"host_lib\" \"cache_le\"",
          "(import \"host_lib\" \"le_field\"",
          "(func (export \"stamp\") (result i32)",
          "(i32.const 240)",
          "(i32.const 1)",
          "(i32.const 393218)",
          "(i64.const 144115188075855871)",
          "(data (i32.const 64) \"drops\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing peer anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-peer: {source.length} bytes of WAT passed peer anchor check"

#pf_xrpl_peer_alphanet_emit_check Examples.XrplPeer

open Lean Elab Command in
elab "#pf_xrpl_flag_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"tx_field\"",
          "(func (export \"stamp\") (result i32)",
          "(i32.const 131074)",
          "(data (i32.const 64) \"flags\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing flag anchor: {anchor}\n{source}"
        logInfo m!"proofforge-xrpl-flag: {source.length} bytes of WAT passed flag anchor check"

#pf_xrpl_flag_alphanet_emit_check Examples.XrplFlag

open Lean Elab Command in
elab "#pf_xrpl_tab_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"setAt\") (result i32)",
          "(func (export \"sum4\")",
          "(func (export \"get0\")",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(data (i32.const 64) \"xs_0xs_1xs_2xs_3\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing tab anchor: {anchor}\n{source}"
        unless !source.contains "(loop" do
          throwError "wasm emit must not contain wasm loop"
        unless !source.contains "loopIx" do
          throwError "wasm emit must not mention loopIx"
        logInfo m!"proofforge-xrpl-tab: {source.length} bytes of WAT passed tab anchor check"

#pf_xrpl_tab_emit_check Examples.XrplTab

open Lean Elab Command in
elab "#pf_xrpl_hand_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"propose\") (result i32)",
          "(func (export \"accept\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "i64.eq",
          "(i32.const 3)",
          "(data (i32.const 64) \"owner0owner1owner2pend0pend1pend2value\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing hand anchor: {anchor}\n{source}"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplHand must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-hand: {source.length} bytes of WAT passed hand anchor check"

#pf_xrpl_hand_emit_check Examples.XrplHand

open Lean Elab Command in
elab "#pf_xrpl_crew_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"setOp\") (result i32)",
          "(func (export \"bump\") (result i32)",
          "(func (export \"get\")",
          "i64.eq",
          "(i32.const 3)",
          "(data (i32.const 64) \"owner0owner1owner2op0op1op2value\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing crew anchor: {anchor}\n{source}"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "XrplCrew must not take wasm i64 params"
        logInfo m!"proofforge-xrpl-crew: {source.length} bytes of WAT passed crew anchor check"

#pf_xrpl_crew_emit_check Examples.XrplCrew

open Lean Elab Command in
elab "#pf_xrpl_pay_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"pay\") (result i32)",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(call $set_data_object_field",
          "(call $get_data_object_field",
          "(i64.store (i32.const 0)",
          "(data (i32.const 64) \"bal\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing pay anchor: {anchor}\\n{source}"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        unless !source.contains "setUserData" do
          throwError "wasm emit must not mention setUserData"
        logInfo m!"proofforge-xrpl-pay: {source.length} bytes of WAT passed pay anchor check"

#pf_xrpl_pay_alphanet_emit_check Examples.XrplPay

open Lean Elab Command in
elab "#pf_xrpl_mint_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"mint\") (result i32)",
          "(func (export \"mintTo\") (result i32)",
          "(func (export \"pay\") (result i32)",
          "(func (export \"burn\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(func (export \"unpause\") (result i32)",
          "(func (export \"setCap\") (result i32)",
          "(func (export \"approve\") (result i32)",
          "(func (export \"takeFrom\") (result i32)",
          "(func (export \"burnFrom\") (result i32)",
          "(func (export \"clawback\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(func (export \"unfreeze\") (result i32)",
          "(func (export \"freezeOf\") (result i32)",
          "(func (export \"unfreezeOf\") (result i32)",
          "(i32.const 3)",
          "(i32.const 4)",
          "(i32.const 5)",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(data (i32.const 64) \"bal\")",
          "(i32.store8 (i32.const 88) (i32.const 115))",
          "(i32.store8 (i32.const 72) (i32.const 99))",
          "(i32.store8 (i32.const 92) (i32.const 97))",
          "(i32.store8 (i32.const 96) (i32.const 108))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing mint anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-mint: {source.length} bytes of WAT passed mint anchor check"

#pf_xrpl_mint_alphanet_emit_check Examples.XrplMint

open Lean Elab Command in
elab "#pf_xrpl_lock_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"pay\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(func (export \"unfreeze\") (result i32)",
          "(call $function_param (i32.const 0) (i32.const 3) (i32.const 20) (i32.const 8))",
          "(call $set_data_object_field",
          "(call $get_data_object_field",
          "(data (i32.const 64) \"bal\")",
          "(i32.store8 (i32.const 96) (i32.const 108))",
          "(i32.const 5)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing lock anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        unless !source.contains "setUserData" do
          throwError "wasm emit must not mention setUserData"
        logInfo m!"proofforge-xrpl-lock: {source.length} bytes of WAT passed lock anchor check"

#pf_xrpl_lock_alphanet_emit_check Examples.XrplLock

#pf_xrpl_lock_alphanet_emit_check Examples.XrplCard

open Lean Elab Command in
elab "#pf_xrpl_vault_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(call $get_current_ledger_obj_field",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 88) (i32.const 115))",
          "(data (i32.const 64) \"bal\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing vault anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-vault: {source.length} bytes of WAT passed vault anchor check"

#pf_xrpl_vault_emit_check Examples.XrplVault

open Lean Elab Command in
elab "#pf_xrpl_payemit_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"ping\") (result i32)",
          "(import \"host_lib\" \"build_txn\"",
          "(import \"host_lib\" \"add_txn_field\"",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.const 393217)",
          "(i32.const 524291)",
          "(i32.const 0xF7)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing payemit anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        logInfo m!"proofforge-xrpl-payemit: {source.length} bytes of WAT passed payemit anchor check"

#pf_xrpl_payemit_emit_check Examples.XrplEmit

open Lean Elab Command in
elab "#pf_xrpl_tip_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"ping\") (result i32)",
          "(import \"host_lib\" \"build_txn\"",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i64.const 4611686018427387904)",
          "(i64.const 384)",
          "(i32.const 393217)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing tip anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        logInfo m!"proofforge-xrpl-tip: {source.length} bytes of WAT passed tip anchor check"

#pf_xrpl_tip_emit_check Examples.XrplTip

open Lean Elab Command in
elab "#pf_xrpl_gift_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"ping\") (result i32)",
          "(import \"host_lib\" \"build_txn\"",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.const 208)",
          "(i32.const 188)",
          "(i32.const 80)",
          "(i32.const 393217)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing gift anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        logInfo m!"proofforge-xrpl-gift: {source.length} bytes of WAT passed gift anchor check"

#pf_xrpl_gift_emit_check Examples.XrplGift

open Lean Elab Command in
elab "#pf_xrpl_cash_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"cash\") (result i32)",
          "(call $get_current_ledger_obj_field",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.store8 (i32.const 88) (i32.const 115))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing cash anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-cash: {source.length} bytes of WAT passed cash anchor check"

#pf_xrpl_cash_emit_check Examples.XrplCash

open Lean Elab Command in
elab "#pf_xrpl_bank_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"cash\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(func (export \"unpause\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.store8 (i32.const 80) (i32.const 104))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing bank anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-bank: {source.length} bytes of WAT passed bank anchor check"

#pf_xrpl_bank_emit_check Examples.XrplBank

open Lean Elab Command in
elab "#pf_xrpl_safe_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"cash\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(func (export \"unfreeze\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.store8 (i32.const 96) (i32.const 108))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing safe anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-safe: {source.length} bytes of WAT passed safe anchor check"

#pf_xrpl_safe_emit_check Examples.XrplSafe

open Lean Elab Command in
elab "#pf_xrpl_pool_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"sendToB\") (result i32)",
          "(func (export \"cashToB\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.const 208)",
          "(i32.store8 (i32.const 96) (i32.const 108))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing pool anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-pool: {source.length} bytes of WAT passed pool anchor check"

#pf_xrpl_pool_emit_check Examples.XrplPool

open Lean Elab Command in
elab "#pf_xrpl_fund_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"sendToB\") (result i32)",
          "(func (export \"cashToB\") (result i32)",
          "(func (export \"setCap10\") (result i32)",
          "(func (export \"grantOp\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.store8 (i32.const 72) (i32.const 99))",
          "(i32.store8 (i32.const 92) (i32.const 97))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing fund anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-fund: {source.length} bytes of WAT passed fund anchor check"

#pf_xrpl_fund_emit_check Examples.XrplFund

open Lean Elab Command in
elab "#pf_xrpl_treasury_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"sendToB\") (result i32)",
          "(func (export \"cashSelf\") (result i32)",
          "(func (export \"clawB\") (result i32)",
          "(func (export \"burn\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\""
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing treasury anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-treasury: {source.length} bytes of WAT passed treasury anchor check"

#pf_xrpl_treasury_emit_check Examples.XrplTreasury

open Lean Elab Command in
elab "#pf_xrpl_token_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"sendToB\") (result i32)",
          "(func (export \"cashSelf\") (result i32)",
          "(func (export \"clawB\") (result i32)",
          "(func (export \"burn\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\""
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing token anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-token: {source.length} bytes of WAT passed token anchor check"

#pf_xrpl_token_emit_check Examples.XrplToken

open Lean Elab Command in
elab "#pf_xrpl_share_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"mintToB\") (result i32)",
          "(func (export \"cashToB\") (result i32)",
          "(func (export \"clawB\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\""
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing share anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-share: {source.length} bytes of WAT passed share anchor check"

#pf_xrpl_share_emit_check Examples.XrplShare

open Lean Elab Command in
elab "#pf_xrpl_take_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"grant\") (result i32)",
          "(func (export \"takeB\") (result i32)",
          "(func (export \"pause\") (result i32)",
          "(func (export \"freeze\") (result i32)",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 92) (i32.const 97))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing take anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-take: {source.length} bytes of WAT passed take anchor check"

#pf_xrpl_take_emit_check Examples.XrplTake

open Lean Elab Command in
elab "#pf_xrpl_holdesc_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"lockIn\") (result i32)",
          "(func (export \"releaseToB\") (result i32)",
          "(func (export \"refund\") (result i32)",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing holdesc anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-holdesc: {source.length} bytes of WAT passed holdesc anchor check"

#pf_xrpl_holdesc_emit_check Examples.XrplHoldEsc

open Lean Elab Command in
elab "#pf_xrpl_vest_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"lockIn\") (result i32)",
          "(func (export \"refund\") (result i32)",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 76) (i32.const 100))",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing vest anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-vest: {source.length} bytes of WAT passed vest anchor check"

#pf_xrpl_vest_emit_check Examples.XrplVest

open Lean Elab Command in
elab "#pf_xrpl_claim_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"lockIn\") (result i32)",
          "(func (export \"claimB\") (result i32)",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 76) (i32.const 100))",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing claim anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-claim: {source.length} bytes of WAT passed claim anchor check"

#pf_xrpl_claim_emit_check Examples.XrplClaim

open Lean Elab Command in
elab "#pf_xrpl_payout_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"lockIn\") (result i32)",
          "(func (export \"cashB\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.store8 (i32.const 76) (i32.const 100))",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing payout anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-payout: {source.length} bytes of WAT passed payout anchor check"

#pf_xrpl_payout_emit_check Examples.XrplPayout

open Lean Elab Command in
elab "#pf_xrpl_dual_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"lockIn\") (result i32)",
          "(func (export \"cancel\") (result i32)",
          "(func (export \"claimB\") (result i32)",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 76) (i32.const 100))",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing dual anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-dual: {source.length} bytes of WAT passed dual anchor check"

#pf_xrpl_dual_emit_check Examples.XrplDual

open Lean Elab Command in
elab "#pf_xrpl_latch_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"latch\") (result i32)",
          "(func (export \"unlatch\") (result i32)",
          "(i32.const 524313)",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing latch anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        unless !source.contains "bitAnd" do
          throwError "wasm emit must not mention bitAnd"
        logInfo m!"proofforge-xrpl-latch: {source.length} bytes of WAT passed latch anchor check"

#pf_xrpl_latch_emit_check Examples.XrplLatch

open Lean Elab Command in
elab "#pf_xrpl_escape_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"credit\") (result i32)",
          "(func (export \"lockIn\") (result i32)",
          "(func (export \"cancel\") (result i32)",
          "(func (export \"cashB\") (result i32)",
          "(i32.const 524313)",
          "(import \"host_lib\" \"emit_built_txn\"",
          "(i32.store8 (i32.const 76) (i32.const 100))",
          "(i32.store8 (i32.const 100) (i32.const 101))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing escape anchor: {anchor}\n{source}"
        unless !source.contains "Sdk.Payments" do
          throwError "wasm emit must not mention Sdk.Payments"
        unless !source.contains "Sdk.Map" do
          throwError "wasm emit must not mention Sdk.Map"
        logInfo m!"proofforge-xrpl-escape: {source.length} bytes of WAT passed escape anchor check"

#pf_xrpl_escape_emit_check Examples.XrplEscape

open Lean Elab Command in
elab "#pf_xrpl_hash_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"compute_sha512_half\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"stamp\") (result i32)",
          "(func (export \"get\")",
          "(i32.const 118)",
          "(i32.const 97)",
          "(i32.const 117)",
          "(i32.const 108)",
          "(i32.const 116)",
          "(call $compute_sha512_half"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing hash anchor: {anchor}\n{source}"
        unless !source.contains "sha256Lit" do
          throwError "wasm emit must not mention sha256Lit"
        unless !source.contains "keccak256" do
          throwError "wasm emit must not mention keccak256"
        unless !source.contains "\"sha512_half\"" do
          throwError "wasm emit must use compute_sha512_half, not sha512_half"
        logInfo m!"proofforge-xrpl-hash: {source.length} bytes of WAT passed hash anchor check"

#pf_xrpl_hash_emit_check Examples.XrplHash

open Lean Elab Command in
elab "#pf_xrpl_rt2_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"get_parent_ledger_hash\"",
          "(import \"host_lib\" \"get_base_fee\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"stamp\") (result i32)",
          "(func (export \"getHash\")",
          "(func (export \"getFee\")",
          "(call $get_parent_ledger_hash",
          "(call $get_base_fee)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing rt2 anchor: {anchor}\n{source}"
        unless !source.contains "blockhash" do
          throwError "wasm emit must not mention blockhash"
        logInfo m!"proofforge-xrpl-rt2: {source.length} bytes of WAT passed rt2 anchor check"

#pf_xrpl_rt2_emit_check Examples.XrplRt2

open Lean Elab Command in
elab "#pf_xrpl_vec_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(func (export \"initialize\") (result i32)",
          "(func (export \"setAt\") (result i32)",
          "(func (export \"get0\")",
          "(func (export \"get1\")",
          "(func (export \"get2\")",
          "(data (i32.const 64) \"xs_0xs_1xs_2\")"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing vec anchor: {anchor}\n{source}"
        unless !source.contains "set_data_array_element_field" do
          throwError "wasm emit must not use set_data_array_element_field"
        unless !source.contains "indexGet" do
          throwError "wasm emit must not mention indexGet"
        logInfo m!"proofforge-xrpl-vec: {source.length} bytes of WAT passed vec anchor check"

#pf_xrpl_vec_emit_check Examples.XrplVec

open Lean Elab Command in
elab "#pf_xrpl_alphanet_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emitAlphaNet program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"host_lib\" \"home_le_field\"",
          "(import \"host_lib\" \"tx_field\"",
          "(import \"host_lib\" \"ldgr_index\"",
          "(import \"host_lib\" \"sha512_half\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"get\") (result i32)",
          "(i32.const 524289)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"alphanet emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "(import \"host_lib\" \"get_current_ledger_obj_field\"" do
          throwError "alphanet emit still imports Bedrock get_current_ledger_obj_field"
        unless !source.contains "(import \"host_lib\" \"get_ledger_sqn\"" do
          throwError "alphanet emit still imports Bedrock get_ledger_sqn"
        unless !source.contains "(func (export \"get\") (result i64)" do
          throwError "alphanet views must return i32, not i64"
        logInfo m!"proofforge-xrpl-alphanet: {source.length} bytes of WAT passed alphanet anchor check"

#pf_xrpl_alphanet_emit_check Examples.Counter
