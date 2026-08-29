import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import ProofForge.Wasm.Xrpl.IR
import Examples.NearCtx
import Examples.Clock
import Examples.EvmCtx

open ProofForge
open Lean Elab Command

private def accountA : ProofForge.Wasm.Near.Runtime.AccountId :=
  { length := 9, w0 := 1, w1 := 2, w2 := 0, w3 := 0, w4 := 0,
    w5 := 0, w6 := 0, w7 := 0 }

private def accountB : ProofForge.Wasm.Near.Runtime.AccountId :=
  { accountA with w7 := 3 }

#guard ProofForge.Wasm.Near.Sdk.AccountId.eq accountA accountA
#guard !ProofForge.Wasm.Near.Sdk.AccountId.eq accountA accountB
#guard !ProofForge.Wasm.Near.Sdk.AccountId.eq accountA { accountA with length := 8 }

elab "#pf_near_ctx_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .ok _ => throwError "expected near to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "near rejects" do
        throwError "unexpected near rejection reason: {reason}"

#pf_near_ctx_reject Examples.Clock

#pf_near_ctx_reject Examples.EvmCtx

open Lean Elab Command in
elab "#pf_xrpl_reject_near " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .ok _ => throwError "expected xrpl to reject {n.getId} (near leaf)"
  | .error reason =>
      unless reason.contains "xrpl rejects near" || reason.contains "xrpl rejects" do
        throwError "unexpected xrpl rejection reason: {reason}"

#pf_xrpl_reject_near Examples.NearCtx

#pf_near_build Examples.NearCtx

open Lean Elab Command in
elab "#pf_near_ctx_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"env\" \"block_index\"",
          "(import \"env\" \"block_timestamp\"",
          "(import \"env\" \"predecessor_account_id\"",
          "(import \"env\" \"attached_deposit\"",
          "(import \"env\" \"account_balance\"",
          "(import \"env\" \"current_account_id\"",
          "(func (export \"height\")",
          "(func (export \"seconds\")",
          "(func (export \"selfBal\")",
          "(func (export \"selfId\")",
          "(func (export \"selfIdLength\")",
          "(func (export \"selfIdWord1\")",
          "(func (export \"checkSelfCall\")",
          "(call $pf_block_index)",
          "i64.div_u (call $pf_block_timestamp)",
          "(call $pf_current_account_id",
          "(local $pf_self_len i64)",
          "(local $pf_self7 i64)",
          "(local $pf_pred_len i64)",
          "(local $pf_pred7 i64)",
          "(i64.store (i32.const 64) (i64.const 0))",
          "(i64.store (i32.const 128) (i64.const 0))",
          "(i64.gt_u (local.get $pf_self_len) (i64.const 64))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"near ctx emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "host_lib" do
          throwError "near ctx emit mentions XRPL host_lib"
        logInfo m!"proofforge-near-ctx-test: digest = {ProofForge.Wasm.Near.IR.digestHex program}"
        logInfo m!"proofforge-near-ctx-test: {source.length} bytes of WAT passed anchor check"

#pf_near_ctx_emit_check Examples.NearCtx

namespace Tests.NearViewCaller

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { value := 0 }

@[pf_entry]
def set (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ value := 1 }, 1) else .error .overflow

@[pf_entry]
def callerLength (_s : State) : UInt64 :=
  ProofForge.Wasm.Near.Sdk.Context.caller.length

end Tests.NearViewCaller

open Lean Elab Command in
elab "#pf_near_view_caller_reject" : command => do
  let env ← getEnv
  match Extract.extractModuleIR env `Tests.NearViewCaller none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok _ => throwError "near view unexpectedly admitted predecessor AccountId"
    | .error reason =>
        unless reason.contains "view cannot read predecessor" do
          throwError s!"unexpected predecessor-view rejection: {reason}"

#pf_near_view_caller_reject

/- A user declaration that merely shares a Runtime leaf's final name must stay an ordinary
constant. In particular, it must not become `env.block_index`. -/
namespace Tests.NearNameCollision

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { value := 0 }

def blockIndex : UInt64 := 7

@[pf_entry]
def set (s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then .ok ({ s with value := 1 }, 1) else .error .overflow

@[pf_entry]
def get (_s : State) : UInt64 := blockIndex

end Tests.NearNameCollision

open Lean Elab Command in
elab "#pf_near_name_collision_check" : command => do
  let env ← getEnv
  match Extract.extractModuleIR env `Tests.NearNameCollision none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        unless source.contains "(i64.const 7)" do
          throwError s!"near user blockIndex did not remain literal 7:\n{source}"
        unless !source.contains "(call $pf_block_index)" do
          throwError s!"near user blockIndex was mistaken for Runtime.blockIndex:\n{source}"

#pf_near_name_collision_check
