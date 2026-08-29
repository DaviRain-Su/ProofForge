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
import Examples.XrplNest
import Examples.XrplStep
import Examples.XrplRole
import Examples.XrplPeer
import Examples.XrplFlag

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
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplBal" == some "cfae015ada92cdc9"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplBalRt" == some "dd80a5af3243dec2"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplRoot" == some "a8e6569035ec2d13"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplTx" == some "2a9d4e10cd7ecec9"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplSend" == some "64eb128e0be5a2c6"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplNest" == some "5deed02b57389d2"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplStep" == some "8273bd4064e4745a"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplRole" == some "bae46704480482ee"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplPeer" == some "b808c0cc3278fb10"
#guard ProofForge.Wasm.Xrpl.Registry.digestOf "XrplFlag" == some "d71a13301ce82878"
#guard ProofForge.Wasm.Xrpl.Registry.names == #["Counter", "XrplCtx", "XrplOwn", "XrplHash", "XrplRt2", "XrplVec", "XrplSmoke", "XrplGate", "XrplHold", "XrplMark", "XrplBal", "XrplBalRt", "XrplRoot", "XrplTx", "XrplSend", "XrplNest", "XrplStep", "XrplRole", "XrplPeer", "XrplFlag"]

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
          "(i32.store8 (i32.const 0) (i32.const 208))",
          "(i32.store8 (i32.const 19) (i32.const 80))",
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
