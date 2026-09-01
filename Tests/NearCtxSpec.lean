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
          "(import \"env\" \"log_utf8\"",
          "(func (export \"height\")",
          "(func (export \"seconds\")",
          "(func (export \"selfBal\")",
          "(func (export \"selfBalHigh\")",
          "(func (export \"takeDepositHigh\")",
          "(func (export \"takeDepositLegacy\")",
          "(func (export \"logReady\")",
          "(func (export \"logView\")",
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
          "(local $pf_dep_hi i64)",
          "(local $pf_bal_hi i64)",
          "(local.set $pf_dep_hi (i64.load (i32.const 32)))",
          "(local.set $pf_bal_hi (i64.load (i32.const 48)))",
          "(data (i32.const 4096) \"\\4e\\45\\41\\52\\20\\e2\\9c\\93\")",
          "(call $pf_log_utf8 (i64.const 8) (i64.const 4096))",
          "(data (i32.const 4104) \"\\76\\69\\65\\77\\20\\e2\\9c\\93\")",
          "(call $pf_log_utf8 (i64.const 8) (i64.const 4104))",
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

namespace Tests.NearTokenFull

open ProofForge.Wasm.Near.Sdk

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { value := 0 }

@[pf_entry]
def depositLow (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then
    .ok ({ value := Context.attachedDeposit.w0 }, Context.attachedDeposit.w0)
  else .error .overflow

@[pf_entry]
def depositHigh (_s : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then
    .ok ({ value := Context.attachedDeposit.w1 }, Context.attachedDeposit.w1)
  else .error .overflow

@[pf_entry]
def balanceHigh (_s : State) : UInt64 := Context.balanceOfSelf.w1

end Tests.NearTokenFull

open Lean Elab Command in
elab "#pf_near_token_full_check" : command => do
  let env ← getEnv
  match Extract.extractModuleIR env `Tests.NearTokenFull none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"env\" \"attached_deposit\"",
          "(import \"env\" \"account_balance\"",
          "(local.set $pf_dep (i64.load (i32.const 24)))",
          "(local.set $pf_dep_hi (i64.load (i32.const 32)))",
          "(local.set $pf_bal_hi (i64.load (i32.const 48)))"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"full NearToken emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "(if (i64.ne (i64.load (i32.const 32))" do
          throwError s!"full attached deposit unexpectedly retained UInt64 trap:\n{source}"
        unless !source.contains "(if (i64.ne (i64.load (i32.const 48))" do
          throwError s!"full account balance unexpectedly retained UInt64 trap:\n{source}"

#pf_near_token_full_check

namespace Tests.NearTokenLegacy

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { value := 0 }

@[pf_entry]
def deposit (_s : State) : Except Error (State × UInt64) :=
  let value := ProofForge.Wasm.Near.Sdk.Context.attachedDepositLo
  if (0 : UInt64) != 1 then .ok ({ value }, value) else .error .overflow

@[pf_entry]
def balance (_state : State) : UInt64 :=
  ProofForge.Wasm.Near.Sdk.Context.balanceOfSelfLo

end Tests.NearTokenLegacy

open Lean Elab Command in
elab "#pf_near_token_legacy_check" : command => do
  let env ← getEnv
  match Extract.extractModuleIR env `Tests.NearTokenLegacy none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source =>
        unless source.contains "(if (i64.ne (i64.load (i32.const 32))" do
          throwError s!"legacy UInt64 deposit is missing its high-word trap:\n{source}"
        unless source.contains "(if (i64.ne (i64.load (i32.const 48))" do
          throwError s!"legacy UInt64 balance is missing its high-word trap:\n{source}"

#pf_near_token_legacy_check

namespace Tests.NearViewDeposit

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State := { value := 0 }

@[pf_entry]
def set (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) != 1 then .ok ({ value := 1 }, 1) else .error .overflow

@[pf_entry]
def depositHigh (_s : State) : UInt64 :=
  ProofForge.Wasm.Near.Sdk.Context.attachedDeposit.w1

end Tests.NearViewDeposit

open Lean Elab Command in
elab "#pf_near_view_deposit_reject" : command => do
  let env ← getEnv
  match Extract.extractModuleIR env `Tests.NearViewDeposit none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .ok _ => throwError "near view unexpectedly admitted full attached deposit"
    | .error reason =>
        unless reason.contains "view cannot read attachedDeposit" do
          throwError s!"unexpected deposit-view rejection: {reason}"

#pf_near_view_deposit_reject

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
