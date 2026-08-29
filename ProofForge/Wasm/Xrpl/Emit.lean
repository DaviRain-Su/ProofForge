import ProofForge.Wasm.Emit
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Host
import ProofForge.Wasm.Xrpl.Ops

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

private def usesKind (ops : Array Ops.Op) (want : Ops.ValKind) : Bool :=
  let rec val (fuel : Nat) (v : Ops.Val) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match v with
      | .ext k _ => k == want
      | .field base _ => val fuel' base
      | .select _ a b c d => val fuel' a || val fuel' b || val fuel' c || val fuel' d
      | .addU64 a b | .subU64 a b | .mulU64 a b | .divU64 a b | .modU64 a b
      | .bitAnd a b | .bitOr a b | .bitXor a b | .shiftL a b | .shiftR a b =>
          val fuel' a || val fuel' b
      | .bitNot a => val fuel' a
      | .indexGet base _ idx _ _ => val fuel' base || val fuel' idx
      | _ => false
  let rec op (fuel : Nat) (x : Ops.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match x with
      | .checkedAddU64 a b | .checkedSubU64 a b | .checkedMulU64 a b
      | .checkedDivU64 a b | .checkedModU64 a b => val 32 a || val 32 b
      | .ite _ a b thn els =>
          val 32 a || val 32 b || thn.any (op fuel') || els.any (op fuel')
      | .storeField _ v | .okState v | .returnState v | .returnU64 v => val 32 v
      | _ => false
  ops.any (op 32)

/-- Load only the env leaves this method actually reads. Unused AlphaNet
`home_le_field(sfContractAccount)` returns -10 LedgerObjNotFound. -/
def loadEnv (host : Contract) (method : IR.Method) (level : Nat) (view : Bool) : Array String :=
  if host.getTxField.isEmpty then #[]
  else
    let needCaller :=
      usesKind method.ops .callerW0 || usesKind method.ops .callerW1 || usesKind method.ops .callerW2
    let needSelf :=
      usesKind method.ops .selfW0 || usesKind method.ops .selfW1 || usesKind method.ops .selfW2
    let needSqn := usesKind method.ops .ledgerSqn
    let needTime := usesKind method.ops .parentTime
    let needHash := usesKind method.ops .parentHashW0
    let needFee := usesKind method.ops .baseFee
    let needBal := usesKind method.ops .callerBalanceDrops
    if !(needCaller || needSelf || needSqn || needTime || needHash || needFee || needBal) then #[]
    else
    let err :=
      if view then #[]
      else #[
        indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
        indent (level + 2) "(then (return (local.get $st))))"
      ]
    let caller :=
      if !needCaller then #[]
      else
        #[
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
    let self :=
      if !needSelf then #[]
      else
        #[
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
      if !needSqn || host.getLedgerSqn.isEmpty then #[]
      else if host.ledgerSqnBuffer then
        #[
          indent level ("(local.set $st (call $" ++ host.getLedgerSqn ++
            " (i32.const 160) (i32.const 4)))")
        ] ++ err ++ #[
          indent level "(local.set $pf_x_xsqn (i64.extend_i32_u (i32.load (i32.const 160))))"
        ]
      else
        #[
          indent level ("(local.set $st (call $" ++ host.getLedgerSqn ++ "))"),
          indent level "(local.set $pf_x_xsqn (i64.extend_i32_u (local.get $st)))"
        ]
    let time :=
      if !needTime || host.getParentTime.isEmpty then #[]
      else if host.ledgerSqnBuffer then
        #[
          indent level ("(local.set $st (call $" ++ host.getParentTime ++
            " (i32.const 160) (i32.const 4)))")
        ] ++ err ++ #[
          indent level "(local.set $pf_x_xtime (i64.extend_i32_u (i32.load (i32.const 160))))"
        ]
      else
        #[
          indent level ("(local.set $st (call $" ++ host.getParentTime ++ "))"),
          indent level "(local.set $pf_x_xtime (i64.extend_i32_u (local.get $st)))"
        ]
    let hash :=
      if !needHash || host.getParentHash.isEmpty then #[]
      else #[
        indent level ("(local.set $st (call $" ++ host.getParentHash ++
          " (i32.const 160) (i32.const 32)))")
      ] ++ err ++ #[
        indent level "(local.set $pf_x_xhash0 (i64.load (i32.const 160)))"
      ]
    let fee :=
      if !needFee || host.getBaseFee.isEmpty then #[]
      else if host.ledgerSqnBuffer then
        #[
          indent level ("(local.set $st (call $" ++ host.getBaseFee ++
            " (i32.const 160) (i32.const 4)))")
        ] ++ err ++ #[
          indent level "(local.set $pf_x_xfee (i64.extend_i32_u (i32.load (i32.const 160))))"
        ]
      else
        #[
          indent level ("(local.set $st (call $" ++ host.getBaseFee ++ "))"),
          indent level "(local.set $pf_x_xfee (i64.extend_i32_u (local.get $st)))"
        ]
    let bal :=
      if !needBal || host.accountRootId.isEmpty || host.cacheLe.isEmpty || host.leField.isEmpty then #[]
      else
        -- Account at 0..19 from loadAccount; index 176; amount 208.
        -- STAmount XRP big-endian; drops = packed & 0x01FFFFFFFFFFFFFF.
        let be :=
          (Array.range 8).foldl (fun acc i =>
            let byte := "(i64.extend_i32_u (i32.load8_u (i32.const " ++
              toString (208 + i) ++ ")))"
            if acc.isEmpty then byte
            else "(i64.or (i64.shl " ++ acc ++ " (i64.const 8)) " ++ byte ++ ")") ""
        #[
          indent level ("(local.set $st (call $" ++ host.accountRootId ++
            " (i32.const 0) (i32.const 20) (i32.const 176) (i32.const 32)))")
        ] ++ err ++ #[
          indent level ("(local.set $st (call $" ++ host.cacheLe ++
            " (i32.const 176) (i32.const 32) (i32.const 0)))")
        ] ++ err ++ #[
          indent level ("(local.set $st (call $" ++ host.leField ++
            " (local.get $st) (i32.const 393218) (i32.const 208) (i32.const 48)))")
          -- `$st` still holds the cache slot from cache_le until this call.
        ] ++ err ++ #[
          indent level ("(local.set $pf_x_xbal (i64.and " ++ be ++
            " (i64.const 144115188075855871)))")
        ]
    caller ++ self ++ sqn ++ time ++ hash ++ fee ++ bal

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
    else if host.ledgerSqnBuffer then
      #[
        "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getLedgerSqn ++
          "\" (func $" ++ host.getLedgerSqn ++ " (param i32 i32) (result i32)))"
      ]
    else
      #[
        "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getLedgerSqn ++
          "\" (func $" ++ host.getLedgerSqn ++ " (result i32)))"
      ]
  let time :=
    if host.getParentTime.isEmpty then #[]
    else if host.ledgerSqnBuffer then
      #[
        "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getParentTime ++
          "\" (func $" ++ host.getParentTime ++ " (param i32 i32) (result i32)))"
      ]
    else
      #[
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
    else if host.ledgerSqnBuffer then
      #[
        "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getBaseFee ++
          "\" (func $" ++ host.getBaseFee ++ " (param i32 i32) (result i32)))"
      ]
    else
      #[
        "  (import \"" ++ host.importModule ++ "\" \"" ++ host.getBaseFee ++
          "\" (func $" ++ host.getBaseFee ++ " (result i32)))"
      ]
  let rootId :=
    if host.accountRootId.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.accountRootId ++
        "\" (func $" ++ host.accountRootId ++
        " (param i32 i32 i32 i32) (result i32)))"
    ]
  let cache :=
    if host.cacheLe.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.cacheLe ++
        "\" (func $" ++ host.cacheLe ++
        " (param i32 i32 i32) (result i32)))"
    ]
  let field :=
    if host.leField.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.leField ++
        "\" (func $" ++ host.leField ++
        " (param i32 i32 i32 i32) (result i32)))"
    ]
  tx ++ sqn ++ time ++ hash ++ parentHash ++ fee ++ rootId ++ cache ++ field

/-- Render one XRPL program as WAT. The digest line pins the canonical IR identity. -/
def emitWith (host : Contract) (p : IR.Program) : Except String String :=
  Wasm.Emit.emit host IR.extValCanon IR.extOpCanon p loadEnv (extraImports host)

/-- Bedrock local host names. -/
def emit (p : IR.Program) : Except String String :=
  emitWith Host.contract p

/-- AlphaNet / XLS-0102 host names. -/
def emitAlphaNet (p : IR.Program) : Except String String :=
  emitWith Host.alphanet p

end ProofForge.Wasm.Xrpl.Emit
