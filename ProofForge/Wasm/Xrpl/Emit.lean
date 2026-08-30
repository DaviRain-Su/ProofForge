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

private def hexBytes (hex : String) : Option (Array Nat) :=
  let rec nibble (c : Char) : Option Nat :=
    let n := c.toNat
    if n ≥ 48 && n ≤ 57 then some (n - 48)
    else if n ≥ 97 && n ≤ 102 then some (n - 87)
    else if n ≥ 65 && n ≤ 70 then some (n - 55)
    else none
  let rec go (cs : List Char) (acc : Array Nat) : Option (Array Nat) :=
    match cs with
    | c0 :: c1 :: rest =>
      match nibble c0, nibble c1 with
      | some hi, some lo => go rest (acc.push (hi * 16 + lo))
      | _, _ => none
    | [] => some acc
    | _ => none
  go hex.toList #[]

private def accountLitHexFromKind : Ops.ValKind → Option String
  | .accountLitW0 h | .accountLitW1 h | .accountLitW2 h | .litBalanceDrops h => some h
  | _ => none

private def accountLitHex (ops : Array Ops.Op) : Option String :=
  let rec val (fuel : Nat) (v : Ops.Val) : Option String :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match v with
      | .ext k ops => accountLitHexFromKind k <|> ops.findSome? (val fuel')
      | .field base _ => val fuel' base
      | .select _ a b c d => val fuel' a <|> val fuel' b <|> val fuel' c <|> val fuel' d
      | .addU64 a b | .subU64 a b | .mulU64 a b | .divU64 a b | .modU64 a b
      | .bitAnd a b | .bitOr a b | .bitXor a b | .shiftL a b | .shiftR a b =>
          val fuel' a <|> val fuel' b
      | .bitNot a => val fuel' a
      | .indexGet base _ idx _ _ => val fuel' base <|> val fuel' idx
      | _ => none
  let rec op (fuel : Nat) (x : Ops.Op) : Option String :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      match x with
      | .checkedAddU64 a b | .checkedSubU64 a b | .checkedMulU64 a b
      | .checkedDivU64 a b | .checkedModU64 a b => val 32 a <|> val 32 b
      | .ite _ a b thn els =>
          val 32 a <|> val 32 b <|> thn.findSome? (op fuel') <|> els.findSome? (op fuel')
      | .storeField _ v | .okState v | .returnState v | .returnU64 v => val 32 v
      | _ => none
  ops.findSome? (op 32)

private def usesKind (ops : Array Ops.Op) (want : Ops.ValKind) : Bool :=
  let rec val (fuel : Nat) (v : Ops.Val) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match v with
      | .ext k ops => k == want || ops.any (val fuel')
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
    let needSeq := usesKind method.ops .callerSequence
    let needFlags := usesKind method.ops .callerFlags
    let needOwnc := usesKind method.ops .callerOwnerCount
    let needTxSeq := usesKind method.ops .txSequence
    let needTxFee := usesKind method.ops .txFeeDrops
    let needTxFlags := usesKind method.ops .txFlags
    let needLitBal :=
      let rec has (fuel : Nat) (v : Ops.Val) : Bool :=
        match fuel with
        | 0 => false
        | fuel' + 1 =>
          match v with
          | .ext (.litBalanceDrops _) _ => true
          | .ext _ ops => ops.any (has fuel')
          | .field base _ => has fuel' base
          | .select _ a b c d => has fuel' a || has fuel' b || has fuel' c || has fuel' d
          | .addU64 a b | .subU64 a b | .mulU64 a b | .divU64 a b | .modU64 a b
          | .bitAnd a b | .bitOr a b | .bitXor a b | .shiftL a b | .shiftR a b =>
              has fuel' a || has fuel' b
          | .bitNot a => has fuel' a
          | .indexGet base _ idx _ _ => has fuel' base || has fuel' idx
          | _ => false
      let rec op (fuel : Nat) (x : Ops.Op) : Bool :=
        match fuel with
        | 0 => false
        | fuel' + 1 =>
          match x with
          | .checkedAddU64 a b | .checkedSubU64 a b | .checkedMulU64 a b
          | .checkedDivU64 a b | .checkedModU64 a b => has 32 a || has 32 b
          | .ite _ a b thn els =>
              has 32 a || has 32 b || thn.any (op fuel') || els.any (op fuel')
          | .storeField _ v | .okState v | .returnState v | .returnU64 v => has 32 v
          | _ => false
      method.ops.any (op 32)
    let needRoot := needBal || needSeq || needFlags || needOwnc || needLitBal
    let otherHex := accountLitHex method.ops
    if !(needCaller || needSelf || needSqn || needTime || needHash || needFee || needRoot || needTxSeq || needTxFee || needTxFlags) && otherHex.isNone then #[]
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
    let rootReady :=
      !host.accountRootId.isEmpty && !host.cacheLe.isEmpty && !host.leField.isEmpty
    let cache :=
      if !needRoot || !rootReady then #[]
      else
        -- Account at 0..19 from loadAccount; index 176. Slot stays in $st.
        #[
          indent level ("(local.set $st (call $" ++ host.accountRootId ++
            " (i32.const 0) (i32.const 20) (i32.const 176) (i32.const 32)))")
        ] ++ err ++ #[
          indent level ("(local.set $st (call $" ++ host.cacheLe ++
            " (i32.const 176) (i32.const 32) (i32.const 0)))")
        ] ++ err
    let u32Field (sfield : Nat) (dest : String) : Array String :=
      if !rootReady then #[]
      else
        #[
          indent level ("(drop (call $" ++ host.leField ++
            " (local.get $st) (i32.const " ++ toString sfield ++
            ") (i32.const 208) (i32.const 8)))"),
          indent level ("(local.set $" ++ dest ++
            " (i64.extend_i32_u (i32.load (i32.const 208))))")
        ]
    let seq := if !needSeq then #[] else u32Field 131076 "pf_x_xseq"
    let flags := if !needFlags then #[] else u32Field 131074 "pf_x_xflags"
    let ownc := if !needOwnc then #[] else u32Field 131085 "pf_x_xownc"
    let bal :=
      if !needBal || !rootReady then #[]
      else
        -- STAmount XRP big-endian; drops = packed & 0x01FFFFFFFFFFFFFF.
        let be :=
          (Array.range 8).foldl (fun acc i =>
            let byte := "(i64.extend_i32_u (i32.load8_u (i32.const " ++
              toString (208 + i) ++ ")))"
            if acc.isEmpty then byte
            else "(i64.or (i64.shl " ++ acc ++ " (i64.const 8)) " ++ byte ++ ")") ""
        #[
          indent level ("(drop (call $" ++ host.leField ++
            " (local.get $st) (i32.const 393218) (i32.const 208) (i32.const 48)))")
        ] ++ #[
          indent level ("(local.set $pf_x_xbal (i64.and " ++ be ++
            " (i64.const 144115188075855871)))")
        ]
    let txSeq :=
      if !needTxSeq || host.getTxField.isEmpty then #[]
      else
        #[
          indent level ("(local.set $st (call $" ++ host.getTxField ++
            " (i32.const 131076) (i32.const 208) (i32.const 8)))")
        ] ++ err ++ #[
          indent level "(local.set $pf_x_xtseq (i64.extend_i32_u (i32.load (i32.const 208))))"
        ]
    let txFee :=
      if !needTxFee || host.getTxField.isEmpty then #[]
      else
        let be :=
          (Array.range 8).foldl (fun acc i =>
            let byte := "(i64.extend_i32_u (i32.load8_u (i32.const " ++
              toString (208 + i) ++ ")))"
            if acc.isEmpty then byte
            else "(i64.or (i64.shl " ++ acc ++ " (i64.const 8)) " ++ byte ++ ")") ""
        #[
          indent level ("(local.set $st (call $" ++ host.getTxField ++
            " (i32.const 393224) (i32.const 208) (i32.const 48)))")
        ] ++ err ++ #[
          indent level ("(local.set $pf_x_xtfee (i64.and " ++ be ++
            " (i64.const 144115188075855871)))")
        ]
    let txFlags :=
      if !needTxFlags || host.getTxField.isEmpty then #[]
      else
        -- Default ContractCall omits Flags; host -2 FIELD_NOT_FOUND is 0, not a trap.
        #[
          indent level ("(local.set $st (call $" ++ host.getTxField ++
            " (i32.const 131074) (i32.const 208) (i32.const 8)))"),
          indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
          indent (level + 2) "(then (local.set $pf_x_xtflags (i64.const 0)))",
          indent (level + 2) "(else (local.set $pf_x_xtflags (i64.extend_i32_u (i32.load (i32.const 208))))))"
        ]
    let litBal :=
      if !needLitBal || !rootReady then #[]
      else
        match otherHex.bind hexBytes with
        | some bs =>
          if bs.size != 20 then #[]
          else
            let stores :=
              (Array.range 20).map fun i =>
                indent level ("(i32.store8 (i32.const " ++ toString (240 + i) ++
                  ") (i32.const " ++ toString bs[i]! ++ "))")
            let be :=
              (Array.range 8).foldl (fun acc i =>
                let byte := "(i64.extend_i32_u (i32.load8_u (i32.const " ++
                  toString (208 + i) ++ ")))"
                if acc.isEmpty then byte
                else "(i64.or (i64.shl " ++ acc ++ " (i64.const 8)) " ++ byte ++ ")") ""
            stores ++ #[
              indent level ("(local.set $st (call $" ++ host.accountRootId ++
                " (i32.const 240) (i32.const 20) (i32.const 176) (i32.const 32)))")
            ] ++ err ++ #[
              indent level ("(local.set $st (call $" ++ host.cacheLe ++
                " (i32.const 176) (i32.const 32) (i32.const 1)))")
            ] ++ err ++ #[
              indent level ("(drop (call $" ++ host.leField ++
                " (local.get $st) (i32.const 393218) (i32.const 208) (i32.const 48)))"),
              indent level ("(local.set $pf_x_xlitbal (i64.and " ++ be ++
                " (i64.const 144115188075855871)))")
            ]
        | none => #[]
    let other :=
      match otherHex.bind hexBytes with
      | some bs =>
        if bs.size != 20 || needLitBal then #[]
        else
          (Array.range 20).map fun i =>
            indent level ("(i32.store8 (i32.const " ++ toString i ++
              ") (i32.const " ++ toString bs[i]! ++ "))")
      | none => #[]
    caller ++ self ++ sqn ++ time ++ hash ++ fee ++ cache ++ seq ++ flags ++ ownc ++ bal ++ txSeq ++ txFee ++ txFlags ++ litBal ++ other

def extraImports (host : Contract) (p : IR.Program) : Array String :=
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
  let rec isPayKind : Ops.ValKind → Bool
    | .emitPay | .emitPayDrops | .emitPayToLit _ => true
    | _ => false
  let rec usesPay (fuel : Nat) (v : Ops.Val) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match v with
      | .ext k ops => isPayKind k || ops.any (usesPay fuel')
      | .field base _ => usesPay fuel' base
      | .select _ a b c d => usesPay fuel' a || usesPay fuel' b || usesPay fuel' c || usesPay fuel' d
      | .addU64 a b | .subU64 a b | .mulU64 a b | .divU64 a b | .modU64 a b
      | .bitAnd a b | .bitOr a b | .bitXor a b | .shiftL a b | .shiftR a b =>
          usesPay fuel' a || usesPay fuel' b
      | .bitNot a => usesPay fuel' a
      | .indexGet base _ idx _ _ => usesPay fuel' base || usesPay fuel' idx
      | _ => false
  let rec usesPayOp (fuel : Nat) (x : Ops.Op) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match x with
      | .checkedAddU64 a b | .checkedSubU64 a b | .checkedMulU64 a b
      | .checkedDivU64 a b | .checkedModU64 a b => usesPay 32 a || usesPay 32 b
      | .ite _ a b thn els =>
          usesPay 32 a || usesPay 32 b || thn.any (usesPayOp fuel') || els.any (usesPayOp fuel')
      | .storeField _ v | .okState v | .returnState v | .returnU64 v => usesPay 32 v
      | _ => false
  let needPay :=
    p.initializer.ops.any (usesPayOp 32) || p.entries.any (fun m => m.ops.any (usesPayOp 32))
  let pay :=
    if !needPay || host.buildTxn.isEmpty || host.addTxnField.isEmpty || host.emitBuiltTxn.isEmpty then #[]
    else #[
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.buildTxn ++
        "\" (func $" ++ host.buildTxn ++ " (param i32) (result i32)))",
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.addTxnField ++
        "\" (func $" ++ host.addTxnField ++ " (param i32 i32 i32 i32) (result i32)))",
      "  (import \"" ++ host.importModule ++ "\" \"" ++ host.emitBuiltTxn ++
        "\" (func $" ++ host.emitBuiltTxn ++ " (param i32) (result i32)))"
    ]
  tx ++ sqn ++ time ++ hash ++ parentHash ++ fee ++ rootId ++ cache ++ field ++ pay

/-- Render one XRPL program as WAT. The digest line pins the canonical IR identity. -/
def emitWith (host : Contract) (p : IR.Program) : Except String String :=
  Wasm.Emit.emit host IR.extValCanon IR.extOpCanon p loadEnv (extraImports host p)

/-- Bedrock local host names. -/
def emit (p : IR.Program) : Except String String :=
  emitWith Host.contract p

/-- AlphaNet / XLS-0102 host names. -/
def emitAlphaNet (p : IR.Program) : Except String String :=
  emitWith Host.alphanet p

end ProofForge.Wasm.Xrpl.Emit
