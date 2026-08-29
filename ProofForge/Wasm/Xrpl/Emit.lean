import ProofForge.Wasm.Emit
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Host

/-!
# XRPL target emitter

共享 WAT 发射器注入 XRPL host。环境叶子在每个 export 序言里从 `host_lib`
读入 `$pf_x_*` locals。
-/

namespace ProofForge.Wasm.Xrpl.Emit

open ProofForge.Wasm.Host (Contract)

private def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

/-- Scratch after account (0..19) and param (20..27) and store (28..36). -/
private def envOff : Nat := 40

/-- Load caller 20B, self 20B, ledger sqn, parent time into `$pf_x_*`. -/
def loadEnv (host : Contract) (level : Nat) (view : Bool) : Array String :=
  if host.getTxField.isEmpty then #[]
  else
    let err :=
      if view then #[]
      else #[
        indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
        indent (level + 2) "(then (return (local.get $st))))"
      ]
    let caller := #[
      indent level ("(local.set $st (call $" ++ host.getTxField ++
        " (i32.const " ++ toString host.sfieldTxAccount ++
        ") (i32.const " ++ toString envOff ++ ") (i32.const 20)))")
    ] ++ err ++ #[
      indent level ("(local.set $pf_x_xc0 (i64.load (i32.const " ++
        toString envOff ++ ")))"),
      indent level ("(local.set $pf_x_xc1 (i64.load (i32.const " ++
        toString (envOff + 8) ++ ")))"),
      indent level ("(local.set $pf_x_xc2 (i64.extend_i32_u (i32.load (i32.const " ++
        toString (envOff + 16) ++ "))))")
    ]
    let self := #[
      indent level ("(local.set $st (call $" ++ host.homeLeField ++
        " (i32.const " ++ toString host.sfieldContractAccount ++
        ") (i32.const " ++ toString envOff ++ ") (i32.const 20)))")
    ] ++ err ++ #[
      indent level ("(local.set $pf_x_xs0 (i64.load (i32.const " ++
        toString envOff ++ ")))"),
      indent level ("(local.set $pf_x_xs1 (i64.load (i32.const " ++
        toString (envOff + 8) ++ ")))"),
      indent level ("(local.set $pf_x_xs2 (i64.extend_i32_u (i32.load (i32.const " ++
        toString (envOff + 16) ++ "))))")
    ]
    let sqn :=
      if host.getLedgerSqn.isEmpty then #[]
      else #[
        indent level ("(local.set $st (call $" ++ host.getLedgerSqn ++ "))"),
        indent level "(local.set $pf_x_xsqn (i64.extend_i32_u (local.get $st)))"
      ]
    let time :=
      if host.getParentTime.isEmpty then #[]
      else #[
        indent level ("(local.set $st (call $" ++ host.getParentTime ++ "))"),
        indent level "(local.set $pf_x_xtime (i64.extend_i32_u (local.get $st)))"
      ]
    let hash :=
      if host.getParentHash.isEmpty then #[]
      else #[
        indent level ("(local.set $st (call $" ++ host.getParentHash ++
          " (i32.const 160) (i32.const 32)))")
      ] ++ err ++ #[
        indent level "(local.set $pf_x_xhash0 (i64.load (i32.const 160)))"
      ]
    let fee :=
      if host.getBaseFee.isEmpty then #[]
      else #[
        indent level ("(local.set $st (call $" ++ host.getBaseFee ++ "))"),
        indent level "(local.set $pf_x_xfee (i64.extend_i32_u (local.get $st)))"
      ]
    caller ++ self ++ sqn ++ time ++ hash ++ fee

def extraImports (host : Contract) : Array String :=
  let tx :=
    if host.getTxField.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getTxField ++
        "\" (func $" ++ host.getTxField ++
        " (param i32 i32 i32) (result i32)))"
    ]
  let sqn :=
    if host.getLedgerSqn.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getLedgerSqn ++
        "\" (func $" ++ host.getLedgerSqn ++ " (result i32)))"
    ]
  let time :=
    if host.getParentTime.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getParentTime ++
        "\" (func $" ++ host.getParentTime ++ " (result i32)))"
    ]
  let hash :=
    if host.computeSha512Half.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.computeSha512Half ++
        "\" (func $" ++ host.computeSha512Half ++
        " (param i32 i32 i32 i32) (result i32)))"
    ]
  let parentHash :=
    if host.getParentHash.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getParentHash ++
        "\" (func $" ++ host.getParentHash ++
        " (param i32 i32) (result i32)))"
    ]
  let fee :=
    if host.getBaseFee.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getBaseFee ++
        "\" (func $" ++ host.getBaseFee ++ " (result i32)))"
    ]
  tx ++ sqn ++ time ++ hash ++ parentHash ++ fee

/-- Render one XRPL program as WAT. The digest line pins the canonical IR identity. -/
def emit (p : IR.Program) : Except String String :=
  Wasm.Emit.emit Host.contract IR.extValCanon IR.extOpCanon p loadEnv (extraImports Host.contract)

end ProofForge.Wasm.Xrpl.Emit
