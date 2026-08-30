import ProofForge.Wasm.IR
import ProofForge.Wasm.Near.Ops
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Host
import ProofForge.Wasm.Near.Memory

/-!
# NEAR target emitter

Core IR → WAT with the NEAR `env` host table (near-wasm-raw-u64-v1).

Family `Wasm.Emit` injects XRPL's Data-blob `host_lib` contract; NEAR storage
and ABI do not fit that shape, so this file owns the env import table, scalar/raw
KV layout, guest arena, and raw-u64 entry ABI. Control-flow lowering (checked i64, `if`)
mirrors the family emitter. Do not reuse XRPL's `host_lib` /
`home_le_field` / `set_data`.
-/

namespace ProofForge.Wasm.Near.Emit

open ProofForge.Wasm.IR (Program Method Val Op Cmp)
open ProofForge.Wasm.Near.Host
open ProofForge.Wasm.Near.Ops (ValKind OpExt)

private def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

private def cmpInstr : Cmp → String
  | .eq => "i64.eq" | .ne => "i64.ne" | .lt => "i64.lt_u"
  | .le => "i64.le_u" | .gt => "i64.gt_u" | .ge => "i64.ge_u"

private structure EState where
  paramCount : Nat
  initializer : Bool := false
  fresh : Nat := 0
  last : Option String := none
  pendingDest : Option String := none
  lastStored : Bool := false
  pendingPromiseReturn : Option String := none
  deriving Inhabited

private def fieldOf : Val ValKind → Option String
  | .field (.arg _) name => some name
  | _ => none

private def localOfArg (i : Nat) : String := "$pf_p" ++ toString i

private def localOfSlot (name : String) : String := "$" ++ name

private def localOfTemp (i : Nat) : String := "$pf_r" ++ toString i

private def localOfSource (i : Nat) : String := "$pf_v" ++ toString i

/-- Packed ASCII keys start at this linear-memory offset. -/
private def keyBase : Nat := 1024

/-- Historical proof_forge canonicalRegisters: input=0, storage=1, evicted=2. -/
private def inputReg : Nat := 0
private def storageReg : Nat := 1
private def evictedReg : Nat := 2
/-- Dedicated bounded raw-storage register; status 0 is always branched before consulting it. -/
private def rawStorageReg : Nat := 3
/-- Dedicated callback-result register; only status 1 may be consulted. -/
private def promiseResultReg : Nat := 4
/-- Dedicated STATE-envelope register. A missing storage read leaves registers stale, so this must
not alias scalar/raw/callback reads and its status is always checked before its length. -/
private def stateMetadataReg : Nat := 5

private def panicOverflowOff : Nat := 2048
private def panicDivOff : Nat := 2057
private def panicInputOff : Nat := 2072
private def panicAccountIdOff : Nat := 2080
private def stateKeyOff : Nat := 2096
private def panicInitializedOff : Nat := 2101

private def stateKey : String := "STATE"

private def panicInitialized : String := "The contract has already been initialized"

private def panicUninitialized : String := "The contract is not initialized"

private def panicStateIncompatible : String := "The contract state version is incompatible"

/-- Dedicated zero-padded buffers prevent a shorter second account id from
observing bytes left by another register read. -/
private def predecessorAccountOff : Nat := 64
private def currentAccountOff : Nat := 128

/-- Exact 16-byte `PFNRST01 || schemaDigestLE` STATE envelope scratch. The preceding account-id
range ends at 192 and bounded input starts at 256. -/
private def stateMetadataOff : Nat := 192
private def stateMetadataLength : Nat := 16
private def stateMetadataMagic : UInt64 := 0x31305453524e4650

/-- Canonical Borsh input is copied only after its register length is bounded. The largest frame
is 68 bytes and therefore remains disjoint from context scratch and storage keys. -/
private def boundedInputOff : Nat := 256

private def predecessorWordLocal : Nat → String
  | 0 => "$pf_pred"
  | i => "$pf_pred" ++ toString i

private def currentAccountWordLocal : Nat → String
  | 0 => "$pf_self"
  | i => "$pf_self" ++ toString i

private def keyLayout (p : Program ValKind OpExt) : Array (String × Nat × Nat) :=
  Id.run do
    let mut off := keyBase
    let mut acc : Array (String × Nat × Nat) := #[]
    for slot in p.slots do
      acc := acc.push (slot.name, off, slot.name.length)
      off := off + slot.name.length
    return acc

private def keyOf (p : Program ValKind OpExt) (name : String) : Nat × Nat :=
  match (keyLayout p).find? (fun t => t.1 == name) with
  | some (_, off, len) => (off, len)
  | none => (keyBase, 0)

private def logDataBase : Nat := 4096
private def maxLogDataBytes : Nat := 4096
private def promiseDataBase : Nat := 8192
private def maxPromiseDataBytes : Nat := 4096
private def lifecycleDataBase : Nat := 12288
private def maxLifecycleDataBytes : Nat := 4096

private partial def logsOfOps (ops : Array (Op ValKind OpExt)) : Array String :=
  ops.foldl (init := #[]) fun messages op =>
    messages ++ match op with
      | .ext (.logUtf8 message) => #[message]
      | .ext (.logUtf8Bounded _ _) => #[]
      | .ext (.nep297StringData _ _ _ _ _) => #[]
      | .ext (.nep141FtMint _ _ _) => #[]
      | .ext (.nep141FtTransfer _ _ _ _) => #[]
      | .ext (.nep141FtBurn _ _ _) => #[]
      | .ext (.nep141FtMintMemo _ _ _ _ _) => #[]
      | .ext (.nep141FtTransferMemo _ _ _ _ _ _) => #[]
      | .ext (.nep141FtBurnMemo _ _ _ _ _) => #[]
      | .ext (.promiseFunctionCallDetached _ _ _ _ _ _ _) => #[]
      | .ext (.promiseFunctionCallReturned _ _ _ _ _ _ _) => #[]
      | .ext (.promiseTransferDetached _ _ _)
      | .ext (.promiseTransferReturned _ _ _) => #[]
      | .ext (.promiseFunctionCallThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _) => #[]
      | .ext (.promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => #[]
      | .ext (.promiseResultRead _ _) => #[]
      | .ext (.transientBuffer64Begin _)
      | .ext (.transientBuffer64Set _ _ _)
      | .ext (.transientBuffer64Finish _)
      | .ext (.storageRead _ _ _)
      | .ext (.storageWrite _ _ _ _ _)
      | .ext (.storageRemove _ _ _)
      | .ext (.storageHasKey _ _ _) => #[]
      | .ite _ _ _ thn els => logsOfOps thn ++ logsOfOps els
      | .forBody _ body => logsOfOps body
      | _ => #[]

private def logMessages (p : Program ValKind OpExt) : Array String :=
  let all := logsOfOps p.initializer.ops ++ p.entries.flatMap (logsOfOps ·.ops)
  all.foldl (init := #[]) fun unique message =>
    if unique.contains message then unique else unique.push message

private partial def hasBoundedLogOps (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun
    | .ext (.logUtf8Bounded _ _) => true
    | .ext (.nep297StringData _ _ _ _ _) => true
    | .ext (.nep141FtMint _ _ _) => true
    | .ext (.nep141FtTransfer _ _ _ _) => true
    | .ext (.nep141FtBurn _ _ _) => true
    | .ext (.nep141FtMintMemo _ _ _ _ _) => true
    | .ext (.nep141FtTransferMemo _ _ _ _ _ _) => true
    | .ext (.nep141FtBurnMemo _ _ _ _ _) => true
    | .ite _ _ _ thn els => hasBoundedLogOps thn || hasBoundedLogOps els
    | .forBody _ body => hasBoundedLogOps body
    | _ => false

private def programHasBoundedLog (p : Program ValKind OpExt) : Bool :=
  hasBoundedLogOps p.initializer.ops || p.entries.any (hasBoundedLogOps ·.ops)

private partial def hasFtEventOps (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun
    | .ext (.nep141FtMint _ _ _) => true
    | .ext (.nep141FtTransfer _ _ _ _) => true
    | .ext (.nep141FtBurn _ _ _) => true
    | .ext (.nep141FtMintMemo _ _ _ _ _) => true
    | .ext (.nep141FtTransferMemo _ _ _ _ _ _) => true
    | .ext (.nep141FtBurnMemo _ _ _ _ _) => true
    | .ite _ _ _ thn els => hasFtEventOps thn || hasFtEventOps els
    | .forBody _ body => hasFtEventOps body
    | _ => false

private def programHasFtEvent (p : Program ValKind OpExt) : Bool :=
  hasFtEventOps p.initializer.ops || p.entries.any (hasFtEventOps ·.ops)

private def logLayout (p : Program ValKind OpExt) : Array (String × Nat × Nat) :=
  (logMessages p).foldl (init := #[]) fun layout message =>
    let next := match layout.back? with
      | some (_, off, len) => off + len
      | none => logDataBase
    layout.push (message, next, message.toUTF8.size)

private def logOf (p : Program ValKind OpExt) (message : String) : Except String (Nat × Nat) :=
  match (logLayout p).find? (fun item => item.1 == message) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near log literal is missing from static layout"

private partial def promiseLiteralsOfOps
    (ops : Array (Op ValKind OpExt)) : Array String :=
  ops.foldl (init := #[]) fun literals op =>
    literals ++ match op with
      | .ext (.promiseFunctionCallDetached receiver method _ _ _ _ _) => #[receiver, method]
      | .ext (.promiseFunctionCallReturned receiver method _ _ _ _ _) => #[receiver, method]
      | .ext (.promiseTransferDetached receiver _ _)
      | .ext (.promiseTransferReturned receiver _ _) => #[receiver]
      | .ext (.promiseFunctionCallThenReturned receiver childMethod callbackMethod
          _ _ _ _ _ _ _ _ _ _) => #[receiver, childMethod, callbackMethod]
      | .ext (.promiseFunctionCallAndThenReturned
          leftReceiver leftMethod rightReceiver rightMethod callbackMethod
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) =>
          #[leftReceiver, leftMethod, rightReceiver, rightMethod, callbackMethod]
      | .ite _ _ _ thn els => promiseLiteralsOfOps thn ++ promiseLiteralsOfOps els
      | .forBody _ body => promiseLiteralsOfOps body
      | _ => #[]

private def promiseLiterals (p : Program ValKind OpExt) : Array String :=
  let all := promiseLiteralsOfOps p.initializer.ops ++
    p.entries.flatMap (promiseLiteralsOfOps ·.ops)
  all.foldl (init := #[]) fun unique literal =>
    if unique.contains literal then unique else unique.push literal

private partial def opsReturnPromise (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.promiseFunctionCallReturned _ _ _ _ _ _ _) => true
    | .ext (.promiseTransferReturned _ _ _) => true
    | .ext (.promiseFunctionCallThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ext (.promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ite _ _ _ thn els => opsReturnPromise thn || opsReturnPromise els
    | .forBody _ body => opsReturnPromise body
    | _ => false

private def programReturnsPromise (p : Program ValKind OpExt) : Bool :=
  opsReturnPromise p.initializer.ops || p.entries.any (opsReturnPromise ·.ops)

private partial def opsCallPromiseFunction (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.promiseFunctionCallDetached _ _ _ _ _ _ _)
    | .ext (.promiseFunctionCallReturned _ _ _ _ _ _ _)
    | .ext (.promiseFunctionCallThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ext (.promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ite _ _ _ thn els => opsCallPromiseFunction thn || opsCallPromiseFunction els
    | .forBody _ body => opsCallPromiseFunction body
    | _ => false

private def programCallsPromiseFunction (p : Program ValKind OpExt) : Bool :=
  opsCallPromiseFunction p.initializer.ops || p.entries.any (opsCallPromiseFunction ·.ops)

private partial def opsTransferPromise (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.promiseTransferDetached _ _ _)
    | .ext (.promiseTransferReturned _ _ _) => true
    | .ite _ _ _ thn els => opsTransferPromise thn || opsTransferPromise els
    | .forBody _ body => opsTransferPromise body
    | _ => false

private def programTransfersPromise (p : Program ValKind OpExt) : Bool :=
  opsTransferPromise p.initializer.ops || p.entries.any (opsTransferPromise ·.ops)

private partial def opsChainPromise (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.promiseFunctionCallThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ext (.promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ite _ _ _ thn els => opsChainPromise thn || opsChainPromise els
    | .forBody _ body => opsChainPromise body
    | _ => false

private def programChainsPromise (p : Program ValKind OpExt) : Bool :=
  opsChainPromise p.initializer.ops || p.entries.any (opsChainPromise ·.ops)

private partial def opsJoinPromise (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => true
    | .ite _ _ _ thn els => opsJoinPromise thn || opsJoinPromise els
    | .forBody _ body => opsJoinPromise body
    | _ => false

private def programJoinsPromise (p : Program ValKind OpExt) : Bool :=
  opsJoinPromise p.initializer.ops || p.entries.any (opsJoinPromise ·.ops)

private partial def opsReadPromiseResult (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.promiseResultRead _ _) => true
    | .ite _ _ _ thn els => opsReadPromiseResult thn || opsReadPromiseResult els
    | .forBody _ body => opsReadPromiseResult body
    | _ => false

private def programReadsPromiseResult (p : Program ValKind OpExt) : Bool :=
  opsReadPromiseResult p.initializer.ops || p.entries.any (opsReadPromiseResult ·.ops)

private def promiseLayout (p : Program ValKind OpExt) : Array (String × Nat × Nat) :=
  (promiseLiterals p).foldl (init := #[]) fun layout literal =>
    let next := match layout.back? with
      | some (_, off, len) => off + len
      | none => promiseDataBase
    layout.push (literal, next, literal.toUTF8.size)

private def promiseLiteralOf
    (p : Program ValKind OpExt) (literal : String) : Except String (Nat × Nat) :=
  match (promiseLayout p).find? (fun item => item.1 == literal) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near promise literal is missing from static layout"

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat ('0'.toNat + value)
  else Char.ofNat ('a'.toNat + value - 10)

private def watBytes (message : String) : String :=
  message.toUTF8.data.foldl (init := "") fun encoded byte =>
    encoded ++ "\\" ++ String.singleton (hexDigit (byte.toNat / 16)) ++
      String.singleton (hexDigit (byte.toNat % 16))

private def jsonEscapedBytes (value : String) : Array UInt8 := Id.run do
  let mut escaped := #[]
  for byte in value.toUTF8.data do
    match byte.toNat with
    | 34 => escaped := escaped ++ #[92, 34]
    | 92 => escaped := escaped ++ #[92, 92]
    | 8 => escaped := escaped ++ #[92, 98]
    | 9 => escaped := escaped ++ #[92, 116]
    | 10 => escaped := escaped ++ #[92, 110]
    | 12 => escaped := escaped ++ #[92, 102]
    | 13 => escaped := escaped ++ #[92, 114]
    | n =>
        if n < 32 then
          escaped := escaped ++ #[92, 117, 48, 48,
            UInt8.ofNat (hexDigit (n / 16)).toNat,
            UInt8.ofNat (hexDigit (n % 16)).toNat]
        else
          escaped := escaped.push byte
  return escaped

private def eventStringPrefix (standard version event : String) : Array UInt8 :=
  "EVENT_JSON:{\"standard\":\"".toUTF8.data ++ jsonEscapedBytes standard ++
    "\",\"version\":\"".toUTF8.data ++ jsonEscapedBytes version ++
    "\",\"event\":\"".toUTF8.data ++ jsonEscapedBytes event ++
    "\",\"data\":\"".toUTF8.data

private def eventStringSuffix : Array UInt8 := "\"}".toUTF8.data

/-- Strict fixed-width Borsh decode over the active callback-result descriptor. Descriptor helper
calls validate the compile-time capacity; byte reads occur only in the exact-success branch. -/
private def promiseResultBorshUInt64D (capacity : Nat) (fallback : String) : String :=
  let status := "(call $pf_promise_result_status (i64.const " ++ toString capacity ++ "))"
  let fits := "(call $pf_promise_result_fits (i64.const " ++ toString capacity ++ "))"
  let length := "(call $pf_promise_result_length (i64.const " ++ toString capacity ++ "))"
  let byte (index : Nat) :=
    "(call $pf_promise_result_byte (i64.const " ++ toString capacity ++
      ") (i64.const " ++ toString index ++ "))"
  let lane (index : Nat) :=
    if index == 0 then byte index
    else "(i64.shl " ++ byte index ++ " (i64.const " ++ toString (index * 8) ++ "))"
  let value := (List.range 8).foldl (init := "") fun value index =>
    if value.isEmpty then lane index else "(i64.or " ++ value ++ " " ++ lane index ++ ")"
  "(if (result i64) (i32.and (i64.eq " ++ status ++ " (i64.const 1)) " ++
    "(i32.and (i64.ne " ++ fits ++ " (i64.const 0)) " ++
    "(i64.eq " ++ length ++ " (i64.const 8)))) " ++
    "(then " ++ value ++ ") (else " ++ fallback ++ "))"

private def logDataSection (p : Program ValKind OpExt) : Except String (Array String) := do
  if (keyLayout p).any fun (_, off, len) => logDataBase < off + len then
    throw "extract/unsupported: near static storage keys overlap log data"
  let layout := logLayout p
  let total := match layout.back? with
    | some (_, off, len) => off + len - logDataBase
    | none => 0
  if maxLogDataBytes < total then
    throw s!"extract/unsupported: near static log data {total} exceeds {maxLogDataBytes} bytes"
  return layout.map fun (message, off, _) =>
    "  (data (i32.const " ++ toString off ++ ") \"" ++ watBytes message ++ "\")"

private def promiseDataSection (p : Program ValKind OpExt) : Except String (Array String) := do
  let layout := promiseLayout p
  let total := match layout.back? with
    | some (_, off, len) => off + len - promiseDataBase
    | none => 0
  if maxPromiseDataBytes < total then
    throw s!"extract/unsupported: near static promise data {total} exceeds {maxPromiseDataBytes} bytes"
  return layout.map fun (literal, off, _) =>
    "  (data (i32.const " ++ toString off ++ ") \"" ++ watBytes literal ++ "\")"

private partial def renderVal (st : EState) (v : Val ValKind) : Except String String :=
  match v with
  | .lit n => .ok ("(i64.const " ++ toString n.toNat ++ ")")
  | .arg i =>
      if i < st.paramCount then .ok ("(local.get " ++ localOfArg i ++ ")")
      else .error "extract/unsupported: near v0 rejects bare state argument"
  | .field (.arg i) name =>
      if i < st.paramCount then
        .error "extract/unsupported: near v0 rejects aggregate parameter projections"
      else .ok ("(local.get " ++ localOfSlot name ++ ")")
  | .select cmp lhs rhs thn els => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      let t ← renderVal st thn
      let f ← renderVal st els
      return ("(if (result i64) (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++
        ") (then " ++ t ++ ") (else " ++ f ++ "))")
  | .addU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.add " ++ l ++ " " ++ r ++ ")")
  | .subU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.sub " ++ l ++ " " ++ r ++ ")")
  | .mulU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.mul " ++ l ++ " " ++ r ++ ")")
  | .bitAnd lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.and " ++ l ++ " " ++ r ++ ")")
  | .bitOr lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.or " ++ l ++ " " ++ r ++ ")")
  | .bitXor lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.xor " ++ l ++ " " ++ r ++ ")")
  | .bitNot value => do
      let rendered ← renderVal st value
      return ("(i64.xor " ++ rendered ++ " (i64.const -1))")
  | .shiftL lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.shl " ++ l ++ " " ++ r ++ ")")
  | .shiftR lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.shr_u " ++ l ++ " " ++ r ++ ")")
  | .ext .blockIndex #[] => .ok "(call $pf_block_index)"
  | .ext .blockTimestamp #[] =>
      .ok "(i64.div_u (call $pf_block_timestamp) (i64.const 1000000000))"
  | .ext .predecessor #[] => .ok "(local.get $pf_pred)"
  | .ext .predecessorLen #[] => .ok "(local.get $pf_pred_len)"
  | .ext .predecessorW1 #[] => .ok "(local.get $pf_pred1)"
  | .ext .predecessorW2 #[] => .ok "(local.get $pf_pred2)"
  | .ext .predecessorW3 #[] => .ok "(local.get $pf_pred3)"
  | .ext .predecessorW4 #[] => .ok "(local.get $pf_pred4)"
  | .ext .predecessorW5 #[] => .ok "(local.get $pf_pred5)"
  | .ext .predecessorW6 #[] => .ok "(local.get $pf_pred6)"
  | .ext .predecessorW7 #[] => .ok "(local.get $pf_pred7)"
  | .ext .attachedDeposit #[] => .ok "(local.get $pf_dep)"
  | .ext .attachedDepositW0 #[] => .ok "(local.get $pf_dep)"
  | .ext .attachedDepositW1 #[] => .ok "(local.get $pf_dep_hi)"
  | .ext .accountBalance #[] => .ok "(local.get $pf_bal)"
  | .ext .accountBalanceW0 #[] => .ok "(local.get $pf_bal)"
  | .ext .accountBalanceW1 #[] => .ok "(local.get $pf_bal_hi)"
  | .ext .currentAccountId #[] => .ok "(local.get $pf_self)"
  | .ext .currentAccountIdLen #[] => .ok "(local.get $pf_self_len)"
  | .ext .currentAccountIdW1 #[] => .ok "(local.get $pf_self1)"
  | .ext .currentAccountIdW2 #[] => .ok "(local.get $pf_self2)"
  | .ext .currentAccountIdW3 #[] => .ok "(local.get $pf_self3)"
  | .ext .currentAccountIdW4 #[] => .ok "(local.get $pf_self4)"
  | .ext .currentAccountIdW5 #[] => .ok "(local.get $pf_self5)"
  | .ext .currentAccountIdW6 #[] => .ok "(local.get $pf_self6)"
  | .ext .currentAccountIdW7 #[] => .ok "(local.get $pf_self7)"
  | .ext (.transientBuffer64Get capacity) #[index] => do
      let i ← renderVal st index
      return "(call $pf_buffer64_get (i64.const " ++ toString capacity ++ ") " ++ i ++ ")"
  | .ext (.storageResultStatus capacity) #[] =>
      .ok ("(call $pf_storage_result_status (i64.const " ++ toString capacity ++ "))")
  | .ext (.storageResultLength capacity) #[] =>
      .ok ("(call $pf_storage_result_length (i64.const " ++ toString capacity ++ "))")
  | .ext (.storageResultFits capacity) #[] =>
      .ok ("(call $pf_storage_result_fits (i64.const " ++ toString capacity ++ "))")
  | .ext (.storageResultByte capacity) #[index] => do
      let i ← renderVal st index
      return "(call $pf_storage_result_byte (i64.const " ++ toString capacity ++ ") " ++ i ++ ")"
  | .ext .promiseResultsCount #[] => .ok "(call $pf_promise_results_count)"
  | .ext (.promiseResultStatus capacity) #[] =>
      .ok ("(call $pf_promise_result_status (i64.const " ++ toString capacity ++ "))")
  | .ext (.promiseResultLength capacity) #[] =>
      .ok ("(call $pf_promise_result_length (i64.const " ++ toString capacity ++ "))")
  | .ext (.promiseResultFits capacity) #[] =>
      .ok ("(call $pf_promise_result_fits (i64.const " ++ toString capacity ++ "))")
  | .ext (.promiseResultByte capacity) #[index] => do
      let i ← renderVal st index
      return "(call $pf_promise_result_byte (i64.const " ++ toString capacity ++ ") " ++ i ++ ")"
  | .ext (.promiseResultBorshUInt64D capacity) #[fallback] => do
      return promiseResultBorshUInt64D capacity (← renderVal st fallback)
  | .local index => .ok ("(local.get " ++ localOfSource index ++ ")")
  | .ext kind operands =>
      .error s!"extract/unsupported: near v0 value extension {repr kind}/{operands.size}"
  | _ => .error "extract/unsupported: near v0 value"

private def isExitOp : Op ValKind OpExt → Bool
  | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
  | _ => false

private def collectReturnU64s (first : Val ValKind)
    (rest : List (Op ValKind OpExt)) :
    Array (Val ValKind) × List (Op ValKind OpExt) :=
  let rec go (acc : Array (Val ValKind))
      (rest : List (Op ValKind OpExt)) :=
    match rest with
    | .returnU64 next :: more => go (acc.push next) more
    | _ => (acc, rest)
  go #[first] rest

private def panicOverflow (level : Nat) : String :=
  indent level ("(call $pf_panic_utf8 (i64.const 8) (i64.const " ++
    toString panicOverflowOff ++ "))")

private def panicDiv (level : Nat) : String :=
  indent level ("(call $pf_panic_utf8 (i64.const 14) (i64.const " ++
    toString panicDivOff ++ "))")

private def storeSlot (p : Program ValKind OpExt)
    (name expr : String) (level : Nat) : Array String :=
  let (off, len) := keyOf p name
  #[
    indent level ("(i64.store (i32.const 8) " ++ expr ++ ")"),
    indent level ("(drop (call $pf_storage_write (i64.const " ++ toString len ++
      ") (i64.const " ++ toString off ++ ") (i64.const 8) (i64.const 8) (i64.const " ++
      toString evictedReg ++ ")))")
  ]

private def initializedGuard (p : Program ValKind OpExt) (level : Nat) : Array String :=
  let panic := indent (level + 4) ("(call $pf_panic_utf8 (i64.const " ++
    toString panicInitialized.length ++ ") (i64.const " ++
    toString panicInitializedOff ++ "))")
  let guard (off len : Nat) := #[
    indent level ("(if (i64.eq (call $pf_storage_has_key (i64.const " ++ toString len ++
      ") (i64.const " ++ toString off ++ ")) (i64.const 1))"),
    indent (level + 2) "(then",
    panic,
    indent (level + 2) "))"
  ]
  (keyLayout p).foldl
    (init := guard stateKeyOff stateKey.length)
    fun lines (_, off, len) => lines ++ guard off len

private def markInitialized (p : Program ValKind OpExt) (level : Nat) : Array String := #[
  indent level ("(i64.store (i32.const " ++ toString stateMetadataOff ++ ") (i64.const " ++
    toString stateMetadataMagic ++ "))"),
  indent level ("(i64.store (i32.const " ++ toString (stateMetadataOff + 8) ++
    ") (i64.const " ++ toString (IR.stateSchemaDigest p) ++ "))"),
  indent level ("(drop (call $pf_storage_write (i64.const " ++ toString stateKey.length ++
    ") (i64.const " ++ toString stateKeyOff ++ ") (i64.const " ++
    toString stateMetadataLength ++ ") (i64.const " ++ toString stateMetadataOff ++
    ") (i64.const " ++ toString evictedReg ++ ")))")
]

private def returnU64Instr (expr : String) (level : Nat) : Array String :=
  #[
    indent level ("(i64.store (i32.const 0) " ++ expr ++ ")"),
    indent level "(call $pf_value_return (i64.const 8) (i64.const 0))"
  ]

private def outputPlanOf (method : Method ValKind OpExt) :
    Except String (Option Codec.BorshOutputPlan) := do
  match method.outputSchema with
  | none =>
      unless method.outputPolicy.isEmpty do
        throw s!"near/codec: {method.ixName} output policy has no schema"
      pure none
  | some schema =>
      let plan ← Codec.outputPlan schema
      unless method.outputPolicy == plan.canonical do
        throw s!"near/codec: {method.ixName} output policy does not match its schema"
      pure (some plan)

private def narrowMax : Nat → Option UInt64
  | 1 => some 255
  | 2 => some 65535
  | 4 => some 4294967295
  | 8 => none
  | _ => none

private def storeOutputElement (width offset : Nat) (value : String) : String :=
  let op := match width with
    | 1 => "i64.store8"
    | 2 => "i64.store16"
    | 4 => "i64.store32"
    | _ => "i64.store"
  "(" ++ op ++ " (i32.add (local.get $pf_output_ptr) (i32.const " ++
    toString offset ++ ")) " ++ value ++ ")"

/-- Serialize the fixed extractor frame into one canonical active Borsh prefix. Narrow scalar
lanes are checked before stores so target lowering never silently truncates a malformed frame. -/
private def returnBorshInstr (st : EState) (plan : Codec.BorshOutputPlan)
    (values : Array (Val ValKind)) (level : Nat) : Except String (Array String) := do
  unless values.size == plan.sourceValueCount do
    throw "near/codec: bounded output plan does not match result leaves"
  let length ← renderVal st values[0]!
  let mut lines : Array String := #[
    indent level ("(local.set $pf_output_length " ++ length ++ ")"),
    indent level ("(if (i64.gt_u (local.get $pf_output_length) (i64.const " ++
      toString plan.capacity ++ "))"),
    indent (level + 2) "(then unreachable))",
    indent level ("(local.set $pf_output_ptr (call $pf_arena_alloc (i64.const " ++
      toString plan.maxBytes ++ ") (i64.const 8)))"),
    indent level "(i32.store (local.get $pf_output_ptr) (i32.wrap_i64 (local.get $pf_output_length)))"
  ]
  for i in [0:plan.capacity] do
    let value ← renderVal st values[i + 1]!
    lines := lines ++ #[
      indent level ("(if (i64.lt_u (i64.const " ++ toString i ++
        ") (local.get $pf_output_length))"),
      indent (level + 2) "(then"
    ]
    if let some maximum := narrowMax plan.elementWidth then
      lines := lines ++ #[
        indent (level + 4) ("(if (i64.gt_u " ++ value ++ " (i64.const " ++
          toString maximum ++ "))"),
        indent (level + 6) "(then unreachable))"
      ]
    lines := lines ++ #[
      indent (level + 4) (storeOutputElement plan.elementWidth
        (4 + i * plan.elementWidth) value),
      indent (level + 2) "))"
    ]
  if plan.validateUtf8 then
    lines := lines ++ #[
      indent level "(if (i32.eqz (call $pf_utf8_valid (i32.add (local.get $pf_output_ptr) (i32.const 4)) (i32.wrap_i64 (local.get $pf_output_length))))",
      indent (level + 2) "(then unreachable))"
    ]
  lines := lines.push (indent level
    ("(call $pf_value_return (i64.add (i64.const 4) (i64.mul (local.get $pf_output_length) " ++
      "(i64.const " ++ toString plan.elementWidth ++ "))) " ++
      "(i64.extend_i32_u (local.get $pf_output_ptr)))"))
  return lines

private def emitChecked (st : EState) (kind : String) (lhs rhs : String) (level : Nat) :
    Except String (Array String × EState) := do
  let temp := localOfTemp st.fresh
  let st' := { st with fresh := st.fresh + 1, last := some temp }
  match kind with
  | "add" =>
      return (#[
        indent level ("(local.set " ++ temp ++ " (i64.add " ++ lhs ++ " " ++ rhs ++ "))"),
        indent level ("(if (i64.lt_u (local.get " ++ temp ++ ") " ++ lhs ++ ")"),
        indent (level + 2) "(then",
        panicOverflow (level + 4),
        indent (level + 2) "))"
      ], st')
  | "sub" =>
      return (#[
        indent level ("(if (i64.lt_u " ++ lhs ++ " " ++ rhs ++ ")"),
        indent (level + 2) "(then",
        panicOverflow (level + 4),
        indent (level + 2) "))",
        indent level ("(local.set " ++ temp ++ " (i64.sub " ++ lhs ++ " " ++ rhs ++ "))")
      ], st')
  | "mul" =>
      return (#[
        indent level ("(if (i64.eqz " ++ lhs ++ ")"),
        indent (level + 2) ("(then (local.set " ++ temp ++ " (i64.const 0)))"),
        indent (level + 2) "(else",
        indent (level + 4) ("(if (i64.gt_u " ++ rhs ++ " (i64.div_u (i64.const -1) " ++ lhs ++ "))"),
        indent (level + 6) "(then",
        panicOverflow (level + 8),
        indent (level + 6) ")",
        indent (level + 6) ("(else (local.set " ++ temp ++ " (i64.mul " ++ lhs ++ " " ++ rhs ++ "))))"),
        indent (level + 2) "))"
      ], st')
  | "div" =>
      return (#[
        indent level ("(if (i64.eqz " ++ rhs ++ ")"),
        indent (level + 2) "(then",
        panicDiv (level + 4),
        indent (level + 2) "))",
        indent level ("(local.set " ++ temp ++ " (i64.div_u " ++ lhs ++ " " ++ rhs ++ "))")
      ], st')
  | "rem" =>
      return (#[
        indent level ("(if (i64.eqz " ++ rhs ++ ")"),
        indent (level + 2) "(then",
        panicDiv (level + 4),
        indent (level + 2) "))",
        indent level ("(local.set " ++ temp ++ " (i64.rem_u " ++ lhs ++ " " ++ rhs ++ "))")
      ], st')
  | _ => throw "extract/unsupported: near v0 checked operation"

private def checkedKind : Op ValKind OpExt → Option String
  | .checkedAddU64 .. => some "add"
  | .checkedSubU64 .. => some "sub"
  | .checkedMulU64 .. => some "mul"
  | .checkedDivU64 .. => some "div"
  | .checkedModU64 .. => some "rem"
  | _ => none

private structure StagedStorageFrame where
  lines : Array String
  pointer : String
  length : String
  st : EState

/-- Materialize one bounded source frame before invalidating the previous raw-storage result.
Only active bytes are narrowed/stored; capacity bytes are allocated so length zero still passes a
valid guest pointer to nearcore. -/
private def stageStorageFrame (st : EState) (capacity : Nat)
    (values : Array (Val ValKind)) (level : Nat) : Except String StagedStorageFrame := do
  unless Codec.storageCapacityValid capacity && values.size == capacity + 1 do
    throw "extract/unsupported: near raw storage frame geometry"
  let length ← renderVal st values[0]!
  let lengthLocal := localOfTemp st.fresh
  let pointerLocal := localOfTemp (st.fresh + 1)
  let st' := { st with fresh := st.fresh + 2 }
  let mut lines := #[
    indent level ("(local.set " ++ lengthLocal ++ " " ++ length ++ ")"),
    indent level ("(if (i64.gt_u (local.get " ++ lengthLocal ++ ") (i64.const " ++
      toString capacity ++ ")) (then unreachable))"),
    indent level ("(local.set " ++ pointerLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const " ++ toString capacity ++
      ") (i64.const 1))))")
  ]
  for index in [0:capacity] do
    let value ← renderVal st values[index + 1]!
    lines := lines ++ #[
      indent level ("(if (i64.lt_u (i64.const " ++ toString index ++ ") (local.get " ++
        lengthLocal ++ "))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(if (i64.gt_u " ++ value ++ " (i64.const 255)) (then unreachable))"),
      indent (level + 4) ("(i64.store8 (i32.add (i32.wrap_i64 (local.get " ++ pointerLocal ++
        ")) (i32.const " ++ toString index ++ ")) " ++ value ++ ")"),
      indent (level + 2) "))"
    ]
  let pointer := "(local.get " ++ pointerLocal ++ ")"
  let length := "(local.get " ++ lengthLocal ++ ")"
  return { lines := lines, pointer := pointer, length := length, st := st' }

private structure StagedEvent where
  lines : Array String
  pointer : String
  length : String
  st : EState

private def appendEventByte (pointerLocal lengthLocal value : String) (level : Nat) : Array String := #[
  indent level ("(i64.store8 (i32.add (i32.wrap_i64 (local.get " ++ pointerLocal ++
    ")) (i32.wrap_i64 (local.get " ++ lengthLocal ++ "))) " ++ value ++ ")"),
  indent level ("(local.set " ++ lengthLocal ++ " (i64.add (local.get " ++ lengthLocal ++
    ") (i64.const 1)))")
]

private def dynamicHexDigit (nibble : String) : String :=
  "(if (result i64) (i64.lt_u " ++ nibble ++ " (i64.const 10)) " ++
    "(then (i64.add " ++ nibble ++ " (i64.const 48))) " ++
    "(else (i64.add " ++ nibble ++ " (i64.const 87))))"

/-- Serialize one closed NEP-297 string-data envelope into a checked arena allocation. The
allocation is the exact worst case: fixed escaped metadata plus six bytes per dynamic source byte
plus the closing quote/object. Active UTF-8 bytes are transformed exactly once. -/
private def stageNep297StringData (st : EState) (standard version event : String)
    (capacity : Nat) (data : Array (Val ValKind)) (level : Nat) : Except String StagedEvent := do
  unless Codec.storageCapacityValid capacity && data.size == capacity + 1 do
    throw "extract/unsupported: near NEP-297 string frame geometry"
  let sourceLength ← renderVal st data[0]!
  let sourceLengthLocal := localOfTemp st.fresh
  let pointerLocal := localOfTemp (st.fresh + 1)
  let outputLengthLocal := localOfTemp (st.fresh + 2)
  let byteLocal := localOfTemp (st.fresh + 3)
  let st' := { st with fresh := st.fresh + 4 }
  let eventPrefix := eventStringPrefix standard version event
  let suffix := eventStringSuffix
  let allocation := eventPrefix.size + capacity * 6 + suffix.size
  let mut lines := #[
    indent level ("(local.set " ++ sourceLengthLocal ++ " " ++ sourceLength ++ ")"),
    indent level ("(if (i64.gt_u (local.get " ++ sourceLengthLocal ++ ") (i64.const " ++
      toString capacity ++ ")) (then unreachable))"),
    indent level ("(local.set " ++ pointerLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const " ++ toString allocation ++
      ") (i64.const 1))))")
  ]
  for index in [0:eventPrefix.size] do
    lines := lines.push (indent level
      ("(i64.store8 (i32.add (i32.wrap_i64 (local.get " ++ pointerLocal ++
        ")) (i32.const " ++ toString index ++ ")) (i64.const " ++
        toString eventPrefix[index]!.toNat ++ "))"))
  lines := lines.push (indent level ("(local.set " ++ outputLengthLocal ++ " (i64.const " ++
    toString eventPrefix.size ++ "))"))
  for index in [0:capacity] do
    let value ← renderVal st data[index + 1]!
    let byte := "(local.get " ++ byteLocal ++ ")"
    let highNibble := "(i64.shr_u " ++ byte ++ " (i64.const 4))"
    let lowNibble := "(i64.and " ++ byte ++ " (i64.const 15))"
    lines := lines ++ #[
      indent level ("(if (i64.lt_u (i64.const " ++ toString index ++ ") (local.get " ++
        sourceLengthLocal ++ "))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(local.set " ++ byteLocal ++ " " ++ value ++ ")"),
      indent (level + 4) ("(if (i64.gt_u " ++ byte ++ " (i64.const 255)) (then unreachable))"),
      indent (level + 4) ("(if (i32.or (i64.eq " ++ byte ++ " (i64.const 34)) " ++
        "(i64.eq " ++ byte ++ " (i64.const 92)))"),
      indent (level + 6) "(then"
    ] ++ appendEventByte pointerLocal outputLengthLocal "(i64.const 92)" (level + 8) ++
      appendEventByte pointerLocal outputLengthLocal byte (level + 8) ++ #[
      indent (level + 6) "))"
    ]
    for short in #[(8, 98), (9, 116), (10, 110), (12, 102), (13, 114)] do
      lines := lines ++ #[
        indent (level + 4) ("(if (i64.eq " ++ byte ++ " (i64.const " ++
          toString short.1 ++ "))"),
        indent (level + 6) "(then"
      ] ++ appendEventByte pointerLocal outputLengthLocal "(i64.const 92)" (level + 8) ++
        appendEventByte pointerLocal outputLengthLocal
          ("(i64.const " ++ toString short.2 ++ ")") (level + 8) ++ #[
        indent (level + 6) "))"
      ]
    lines := lines ++ #[
      indent (level + 4) ("(if (i32.and (i64.lt_u " ++ byte ++ " (i64.const 32)) " ++
        "(i32.and (i64.ne " ++ byte ++ " (i64.const 8)) " ++
        "(i32.and (i64.ne " ++ byte ++ " (i64.const 9)) " ++
        "(i32.and (i64.ne " ++ byte ++ " (i64.const 10)) " ++
        "(i32.and (i64.ne " ++ byte ++ " (i64.const 12)) " ++
        "(i64.ne " ++ byte ++ " (i64.const 13)))))))"),
      indent (level + 6) "(then"
    ] ++ appendEventByte pointerLocal outputLengthLocal "(i64.const 92)" (level + 8) ++
      appendEventByte pointerLocal outputLengthLocal "(i64.const 117)" (level + 8) ++
      appendEventByte pointerLocal outputLengthLocal "(i64.const 48)" (level + 8) ++
      appendEventByte pointerLocal outputLengthLocal "(i64.const 48)" (level + 8) ++
      appendEventByte pointerLocal outputLengthLocal (dynamicHexDigit highNibble) (level + 8) ++
      appendEventByte pointerLocal outputLengthLocal (dynamicHexDigit lowNibble) (level + 8) ++ #[
      indent (level + 6) "))",
      indent (level + 4) ("(if (i32.and (i64.ge_u " ++ byte ++ " (i64.const 32)) " ++
        "(i32.and (i64.ne " ++ byte ++ " (i64.const 34)) " ++
        "(i64.ne " ++ byte ++ " (i64.const 92))))"),
      indent (level + 6) "(then"
    ] ++ appendEventByte pointerLocal outputLengthLocal byte (level + 8) ++ #[
      indent (level + 6) "))",
      indent (level + 2) "))"
    ]
  for byte in suffix do
    lines := lines ++ appendEventByte pointerLocal outputLengthLocal
      ("(i64.const " ++ toString byte.toNat ++ ")") level
  return {
    lines
    pointer := "(local.get " ++ pointerLocal ++ ")"
    length := "(local.get " ++ outputLengthLocal ++ ")"
    st := st' }

private def ftMintPrefix : Array UInt8 :=
  "EVENT_JSON:{\"standard\":\"nep141\",\"version\":\"1.0.0\",\"event\":\"ft_mint\",\"data\":[{\"owner_id\":\"".toUTF8.data

private def ftTransferPrefix : Array UInt8 :=
  "EVENT_JSON:{\"standard\":\"nep141\",\"version\":\"1.0.0\",\"event\":\"ft_transfer\",\"data\":[{\"old_owner_id\":\"".toUTF8.data

private def ftTransferNewOwnerPrefix : Array UInt8 := "\",\"new_owner_id\":\"".toUTF8.data

private def ftBurnPrefix : Array UInt8 :=
  "EVENT_JSON:{\"standard\":\"nep141\",\"version\":\"1.0.0\",\"event\":\"ft_burn\",\"data\":[{\"owner_id\":\"".toUTF8.data

private def ftAmountPrefix : Array UInt8 := "\",\"amount\":\"".toUTF8.data
private def ftMemoPrefix : Array UInt8 := "\",\"memo\":\"".toUTF8.data
private def ftEventSuffix : Array UInt8 := "\"}]}".toUTF8.data

private structure FtEventBuffer where
  lines : Array String
  pointerLocal : String
  outputLengthLocal : String
  st : EState

private def startFtEvent (st : EState) (bytesPrefix : Array UInt8)
    (allocation level : Nat) : FtEventBuffer := Id.run do
  let pointerLocal := localOfTemp st.fresh
  let outputLengthLocal := localOfTemp (st.fresh + 1)
  let st' := { st with fresh := st.fresh + 2 }
  let mut lines := #[indent level ("(local.set " ++ pointerLocal ++
    " (i64.extend_i32_u (call $pf_arena_alloc (i64.const " ++ toString allocation ++
    ") (i64.const 1))))")]
  for index in [0:bytesPrefix.size] do
    lines := lines.push (indent level
      ("(i64.store8 (i32.add (i32.wrap_i64 (local.get " ++ pointerLocal ++
        ")) (i32.const " ++ toString index ++ ")) (i64.const " ++
        toString bytesPrefix[index]!.toNat ++ "))"))
  lines := lines.push (indent level ("(local.set " ++ outputLengthLocal ++ " (i64.const " ++
    toString bytesPrefix.size ++ "))"))
  return { lines, pointerLocal, outputLengthLocal, st := st' }

/-- Append every active byte of one complete AccountId frame through the closed JSON escaper. -/
private def appendFtAccount (buffer : FtEventBuffer) (owner : Array (Val ValKind))
    (level : Nat) : Except String FtEventBuffer := do
  unless owner.size == 9 do
    throw "extract/unsupported: near NEP-141 owner frame geometry"
  let ownerLength ← renderVal buffer.st owner[0]!
  let ownerLengthLocal := localOfTemp buffer.st.fresh
  let st' := { buffer.st with fresh := buffer.st.fresh + 1 }
  let mut lines := buffer.lines ++ #[
    indent level ("(local.set " ++ ownerLengthLocal ++ " " ++ ownerLength ++ ")"),
    indent level ("(if (i64.gt_u (local.get " ++ ownerLengthLocal ++
      ") (i64.const 64)) (then unreachable))")
  ]
  for index in [0:64] do
    let word ← renderVal buffer.st owner[index / 8 + 1]!
    let byte := "(i64.and (i64.shr_u " ++ word ++ " (i64.const " ++
      toString ((index % 8) * 8) ++ ")) (i64.const 255))"
    lines := lines ++ #[
      indent level ("(if (i64.lt_u (i64.const " ++ toString index ++ ") (local.get " ++
        ownerLengthLocal ++ "))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(local.set " ++ buffer.outputLengthLocal ++
        " (call $pf_json_escape_byte " ++ byte ++ " (i32.wrap_i64 (local.get " ++
        buffer.pointerLocal ++ ")) (local.get " ++ buffer.outputLengthLocal ++ ")))") ,
      indent (level + 2) "))"
    ]
  return { buffer with lines, st := st' }

private def appendFtLiteral (buffer : FtEventBuffer) (bytes : Array UInt8)
    (level : Nat) : FtEventBuffer := Id.run do
  let mut lines := buffer.lines
  for byte in bytes do
    lines := lines ++ appendEventByte buffer.pointerLocal buffer.outputLengthLocal
      ("(i64.const " ++ toString byte.toNat ++ ")") level
  return { buffer with lines }

/-- Append one full-u128 quoted decimal payload using the single shared 39-digit routine. -/
private def appendFtAmount (buffer : FtEventBuffer) (amountLo amountHi : Val ValKind)
    (level : Nat) : Except String FtEventBuffer := do
  let amountLo ← renderVal buffer.st amountLo
  let amountHi ← renderVal buffer.st amountHi
  let digitsPointerLocal := localOfTemp buffer.st.fresh
  let decimalLengthLocal := localOfTemp (buffer.st.fresh + 1)
  let st' := { buffer.st with fresh := buffer.st.fresh + 2 }
  let lines := buffer.lines ++ #[
    indent level ("(local.set " ++ digitsPointerLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const 39) (i64.const 1))))"),
    indent level ("(local.set " ++ decimalLengthLocal ++ " (call $pf_u128_decimal " ++
      amountLo ++ " " ++ amountHi ++ " (i32.wrap_i64 (local.get " ++ digitsPointerLocal ++
      ")) (i32.add (i32.wrap_i64 (local.get " ++ buffer.pointerLocal ++
      ")) (i32.wrap_i64 (local.get " ++ buffer.outputLengthLocal ++ ")))))"),
    indent level ("(local.set " ++ buffer.outputLengthLocal ++ " (i64.add (local.get " ++
      buffer.outputLengthLocal ++ ") (local.get " ++ decimalLengthLocal ++ ")))")
  ]
  return { buffer with lines, st := st' }

/-- Append the active prefix of one bounded UTF-8 memo through the same serde_json-compatible
byte escaper. Inactive frame leaves are never inspected or serialized. -/
private def appendFtMemo (buffer : FtEventBuffer) (capacity : Nat)
    (memo : Array (Val ValKind)) (level : Nat) : Except String FtEventBuffer := do
  unless Codec.nep141MemoCapacityValid capacity && memo.size == capacity + 1 do
    throw "extract/unsupported: near NEP-141 memo frame geometry"
  let sourceLength ← renderVal buffer.st memo[0]!
  let sourceLengthLocal := localOfTemp buffer.st.fresh
  let st' := { buffer.st with fresh := buffer.st.fresh + 1 }
  let mut lines := buffer.lines ++ #[
    indent level ("(local.set " ++ sourceLengthLocal ++ " " ++ sourceLength ++ ")"),
    indent level ("(if (i64.gt_u (local.get " ++ sourceLengthLocal ++ ") (i64.const " ++
      toString capacity ++ ")) (then unreachable))")
  ]
  for index in [0:capacity] do
    let value ← renderVal buffer.st memo[index + 1]!
    lines := lines ++ #[
      indent level ("(if (i64.lt_u (i64.const " ++ toString index ++ ") (local.get " ++
        sourceLengthLocal ++ "))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(if (i64.gt_u " ++ value ++ " (i64.const 255)) (then unreachable))"),
      indent (level + 4) ("(local.set " ++ buffer.outputLengthLocal ++
        " (call $pf_json_escape_byte " ++ value ++ " (i32.wrap_i64 (local.get " ++
        buffer.pointerLocal ++ ")) (local.get " ++ buffer.outputLengthLocal ++ ")))") ,
      indent (level + 2) "))"
    ]
  return { buffer with lines, st := st' }

private def finishFtEvent (buffer : FtEventBuffer) : StagedEvent := {
  lines := buffer.lines
  pointer := "(local.get " ++ buffer.pointerLocal ++ ")"
  length := "(local.get " ++ buffer.outputLengthLocal ++ ")"
  st := buffer.st
}

/-- Stage one exact no-memo NEP-141 `ft_mint` envelope. -/
private def stageNep141FtMint (st : EState) (owner : Array (Val ValKind))
    (amountLo amountHi : Val ValKind) (level : Nat) : Except String StagedEvent := do
  let allocation := ftMintPrefix.size + 64 * 6 + ftAmountPrefix.size + 39 + ftEventSuffix.size
  let buffer := startFtEvent st ftMintPrefix allocation level
  let buffer ← appendFtAccount buffer owner level
  let buffer := appendFtLiteral buffer ftAmountPrefix level
  let buffer ← appendFtAmount buffer amountLo amountHi level
  return finishFtEvent (appendFtLiteral buffer ftEventSuffix level)

/-- Stage one exact no-memo NEP-141 `ft_transfer` envelope in official record-field order. -/
private def stageNep141FtTransfer (st : EState) (oldOwner newOwner : Array (Val ValKind))
    (amountLo amountHi : Val ValKind) (level : Nat) : Except String StagedEvent := do
  let allocation := ftTransferPrefix.size + 64 * 6 + ftTransferNewOwnerPrefix.size +
    64 * 6 + ftAmountPrefix.size + 39 + ftEventSuffix.size
  let buffer := startFtEvent st ftTransferPrefix allocation level
  let buffer ← appendFtAccount buffer oldOwner level
  let buffer := appendFtLiteral buffer ftTransferNewOwnerPrefix level
  let buffer ← appendFtAccount buffer newOwner level
  let buffer := appendFtLiteral buffer ftAmountPrefix level
  let buffer ← appendFtAmount buffer amountLo amountHi level
  return finishFtEvent (appendFtLiteral buffer ftEventSuffix level)

/-- Stage one exact no-memo NEP-141 `ft_burn` envelope. -/
private def stageNep141FtBurn (st : EState) (owner : Array (Val ValKind))
    (amountLo amountHi : Val ValKind) (level : Nat) : Except String StagedEvent := do
  let allocation := ftBurnPrefix.size + 64 * 6 + ftAmountPrefix.size + 39 + ftEventSuffix.size
  let buffer := startFtEvent st ftBurnPrefix allocation level
  let buffer ← appendFtAccount buffer owner level
  let buffer := appendFtLiteral buffer ftAmountPrefix level
  let buffer ← appendFtAmount buffer amountLo amountHi level
  return finishFtEvent (appendFtLiteral buffer ftEventSuffix level)

/-- Stage one exact NEP-141 `ft_mint` envelope with the memo field present after amount. -/
private def stageNep141FtMintMemo (st : EState) (memoCapacity : Nat)
    (owner : Array (Val ValKind)) (amountLo amountHi : Val ValKind)
    (memo : Array (Val ValKind)) (level : Nat) : Except String StagedEvent := do
  let allocation := ftMintPrefix.size + 64 * 6 + ftAmountPrefix.size + 39 +
    ftMemoPrefix.size + memoCapacity * 6 + ftEventSuffix.size
  let buffer := startFtEvent st ftMintPrefix allocation level
  let buffer ← appendFtAccount buffer owner level
  let buffer := appendFtLiteral buffer ftAmountPrefix level
  let buffer ← appendFtAmount buffer amountLo amountHi level
  let buffer := appendFtLiteral buffer ftMemoPrefix level
  let buffer ← appendFtMemo buffer memoCapacity memo level
  return finishFtEvent (appendFtLiteral buffer ftEventSuffix level)

/-- Stage one exact NEP-141 `ft_transfer` envelope with the memo field present after amount. -/
private def stageNep141FtTransferMemo (st : EState) (memoCapacity : Nat)
    (oldOwner newOwner : Array (Val ValKind)) (amountLo amountHi : Val ValKind)
    (memo : Array (Val ValKind)) (level : Nat) : Except String StagedEvent := do
  let allocation := ftTransferPrefix.size + 64 * 6 + ftTransferNewOwnerPrefix.size +
    64 * 6 + ftAmountPrefix.size + 39 + ftMemoPrefix.size + memoCapacity * 6 + ftEventSuffix.size
  let buffer := startFtEvent st ftTransferPrefix allocation level
  let buffer ← appendFtAccount buffer oldOwner level
  let buffer := appendFtLiteral buffer ftTransferNewOwnerPrefix level
  let buffer ← appendFtAccount buffer newOwner level
  let buffer := appendFtLiteral buffer ftAmountPrefix level
  let buffer ← appendFtAmount buffer amountLo amountHi level
  let buffer := appendFtLiteral buffer ftMemoPrefix level
  let buffer ← appendFtMemo buffer memoCapacity memo level
  return finishFtEvent (appendFtLiteral buffer ftEventSuffix level)

/-- Stage one exact NEP-141 `ft_burn` envelope with the memo field present after amount. -/
private def stageNep141FtBurnMemo (st : EState) (memoCapacity : Nat)
    (owner : Array (Val ValKind)) (amountLo amountHi : Val ValKind)
    (memo : Array (Val ValKind)) (level : Nat) : Except String StagedEvent := do
  let allocation := ftBurnPrefix.size + 64 * 6 + ftAmountPrefix.size + 39 +
    ftMemoPrefix.size + memoCapacity * 6 + ftEventSuffix.size
  let buffer := startFtEvent st ftBurnPrefix allocation level
  let buffer ← appendFtAccount buffer owner level
  let buffer := appendFtLiteral buffer ftAmountPrefix level
  let buffer ← appendFtAmount buffer amountLo amountHi level
  let buffer := appendFtLiteral buffer ftMemoPrefix level
  let buffer ← appendFtMemo buffer memoCapacity memo level
  return finishFtEvent (appendFtLiteral buffer ftEventSuffix level)

private structure StagedPromiseCall where
  lines : Array String
  promiseLocal : String
  st : EState

/-- Stage one bounded function-call action and retain its concrete Promise index. Detached and
returned calls share this ABI sequence; only the caller decides whether to link the index with
`promise_return`. -/
private def stagePromiseCall (p : Program ValKind OpExt) (st : EState)
    (receiver method : String) (argsCapacity : Nat) (arguments : Array (Val ValKind))
    (depositLo depositHi gas : Val ValKind) (level : Nat) : Except String StagedPromiseCall := do
  let (receiverOff, receiverLen) ← promiseLiteralOf p receiver
  let (methodOff, methodLen) ← promiseLiteralOf p method
  let staged ← stageStorageFrame st argsCapacity arguments level
  let depositLo ← renderVal staged.st depositLo
  let depositHi ← renderVal staged.st depositHi
  let gas ← renderVal staged.st gas
  let depositPtrLocal := localOfTemp staged.st.fresh
  let promiseLocal := localOfTemp (staged.st.fresh + 1)
  let st' := { staged.st with fresh := staged.st.fresh + 2 }
  let lines := staged.lines ++ #[
    indent level ("(local.set " ++ depositPtrLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const 16) (i64.const 8))))"),
    indent level ("(i64.store (i32.wrap_i64 (local.get " ++ depositPtrLocal ++ ")) " ++
      depositLo ++ ")"),
    indent level ("(i64.store (i32.add (i32.wrap_i64 (local.get " ++ depositPtrLocal ++
      ")) (i32.const 8)) " ++ depositHi ++ ")"),
    indent level ("(local.set " ++ promiseLocal ++
      " (call $pf_promise_batch_create (i64.const " ++ toString receiverLen ++
      ") (i64.const " ++ toString receiverOff ++ ")))"),
    indent level ("(call $pf_promise_batch_action_function_call (local.get " ++
      promiseLocal ++ ") (i64.const " ++ toString methodLen ++ ") (i64.const " ++
      toString methodOff ++ ") " ++ staged.length ++ " " ++ staged.pointer ++
      " (local.get " ++ depositPtrLocal ++ ") " ++ gas ++ ")")
  ]
  return { lines, promiseLocal, st := st' }

/-- Join exactly two concrete Promise indices in caller order. The two stores are immediately
followed by `promise_and`, keeping this temporary frame local to the host operation that consumes
it. -/
private def stagePromiseAnd (st : EState) (leftPromiseLocal rightPromiseLocal : String)
    (level : Nat) : StagedPromiseCall :=
  let pointerLocal := localOfTemp st.fresh
  let jointPromiseLocal := localOfTemp (st.fresh + 1)
  let st' := { st with fresh := st.fresh + 2 }
  let lines := #[
    indent level ("(local.set " ++ pointerLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const 16) (i64.const 8))))"),
    indent level ("(i64.store (i32.wrap_i64 (local.get " ++ pointerLocal ++
      ")) (local.get " ++ leftPromiseLocal ++ "))"),
    indent level ("(i64.store (i32.add (i32.wrap_i64 (local.get " ++ pointerLocal ++
      ")) (i32.const 8)) (local.get " ++ rightPromiseLocal ++ "))"),
    indent level ("(local.set " ++ jointPromiseLocal ++ " (call $pf_promise_and (local.get " ++
      pointerLocal ++ ") (i64.const 2)))")
  ]
  { lines, promiseLocal := jointPromiseLocal, st := st' }

/-- Stage one transfer-only receipt. The amount is an exact little-endian u128 at a fresh
16-byte arena span; no method, arguments, or gas value belongs to a native transfer action. -/
private def stagePromiseTransfer (p : Program ValKind OpExt) (st : EState)
    (receiver : String) (amountLo amountHi : Val ValKind)
    (level : Nat) : Except String StagedPromiseCall := do
  let (receiverOff, receiverLen) ← promiseLiteralOf p receiver
  let amountLo ← renderVal st amountLo
  let amountHi ← renderVal st amountHi
  let amountPtrLocal := localOfTemp st.fresh
  let promiseLocal := localOfTemp (st.fresh + 1)
  let st' := { st with fresh := st.fresh + 2 }
  let lines := #[
    indent level ("(local.set " ++ amountPtrLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const 16) (i64.const 8))))"),
    indent level ("(i64.store (i32.wrap_i64 (local.get " ++ amountPtrLocal ++ ")) " ++
      amountLo ++ ")"),
    indent level ("(i64.store (i32.add (i32.wrap_i64 (local.get " ++ amountPtrLocal ++
      ")) (i32.const 8)) " ++ amountHi ++ ")"),
    indent level ("(local.set " ++ promiseLocal ++
      " (call $pf_promise_batch_create (i64.const " ++ toString receiverLen ++
      ") (i64.const " ++ toString receiverOff ++ ")))"),
    indent level ("(call $pf_promise_batch_action_transfer (local.get " ++ promiseLocal ++
      ") (local.get " ++ amountPtrLocal ++ "))")
  ]
  return { lines, promiseLocal, st := st' }

/-- Stage one static callback action dependent on `childPromiseLocal`. The callback receiver is the
current contract account copied by the entry prelude; its normal arguments remain independent of
the dependency result channel. -/
private def stagePromiseThen (p : Program ValKind OpExt) (st : EState)
    (childPromiseLocal callbackMethod : String)
    (argsCapacity : Nat) (arguments : Array (Val ValKind))
    (depositLo depositHi gas : Val ValKind) (level : Nat) : Except String StagedPromiseCall := do
  let (methodOff, methodLen) ← promiseLiteralOf p callbackMethod
  let staged ← stageStorageFrame st argsCapacity arguments level
  let depositLo ← renderVal staged.st depositLo
  let depositHi ← renderVal staged.st depositHi
  let gas ← renderVal staged.st gas
  let depositPtrLocal := localOfTemp staged.st.fresh
  let callbackPromiseLocal := localOfTemp (staged.st.fresh + 1)
  let st' := { staged.st with fresh := staged.st.fresh + 2 }
  let lines := staged.lines ++ #[
    indent level ("(local.set " ++ depositPtrLocal ++
      " (i64.extend_i32_u (call $pf_arena_alloc (i64.const 16) (i64.const 8))))"),
    indent level ("(i64.store (i32.wrap_i64 (local.get " ++ depositPtrLocal ++ ")) " ++
      depositLo ++ ")"),
    indent level ("(i64.store (i32.add (i32.wrap_i64 (local.get " ++ depositPtrLocal ++
      ")) (i32.const 8)) " ++ depositHi ++ ")"),
    indent level ("(local.set " ++ callbackPromiseLocal ++
      " (call $pf_promise_batch_then (local.get " ++ childPromiseLocal ++
      ") (local.get $pf_self_len) (i64.const " ++ toString currentAccountOff ++ ")))"),
    indent level ("(call $pf_promise_batch_action_function_call (local.get " ++
      callbackPromiseLocal ++ ") (i64.const " ++ toString methodLen ++ ") (i64.const " ++
      toString methodOff ++ ") " ++ staged.length ++ " " ++ staged.pointer ++
      " (local.get " ++ depositPtrLocal ++ ") " ++ gas ++ ")")
  ]
  return { lines, promiseLocal := callbackPromiseLocal, st := st' }

private def resetStorageResult (capacity level : Nat) : Array String := #[
  indent level "(global.set $pf_storage_result_active (i32.const 1))",
  indent level ("(global.set $pf_storage_result_capacity (i64.const " ++
    toString capacity ++ "))"),
  indent level "(global.set $pf_storage_result_status (i64.const 0))",
  indent level "(global.set $pf_storage_result_length (i64.const 0))",
  indent level "(global.set $pf_storage_result_fits (i64.const 1))",
  indent level "(global.set $pf_storage_result_ptr (i32.const 0))"
]

/-- Preserve the exact host 0/1 status. A status-1 register is length-checked before allocation and
copied in full only when bounded. Status 0 never consults the possibly stale register. -/
private def finishStorageResult (capacity : Nat) (status : String)
    (register : Option Nat) (level : Nat) : Array String :=
  let head := #[
    indent level ("(global.set $pf_storage_result_status " ++ status ++ ")"),
    indent level "(if (i64.gt_u (global.get $pf_storage_result_status) (i64.const 1))",
    indent (level + 2) "(then unreachable))"
  ]
  match register with
  | none => head
  | some register => head ++ #[
      indent level "(if (i64.eq (global.get $pf_storage_result_status) (i64.const 1))",
      indent (level + 2) "(then",
      indent (level + 4) ("(global.set $pf_storage_result_length (call $pf_register_len (i64.const " ++
        toString register ++ ")) )"),
      indent (level + 4) "(if (i64.eq (global.get $pf_storage_result_length) (i64.const -1))",
      indent (level + 6) "(then unreachable))",
      indent (level + 4) ("(if (i64.gt_u (global.get $pf_storage_result_length) (i64.const " ++
        toString capacity ++ "))"),
      indent (level + 6) "(then (global.set $pf_storage_result_fits (i64.const 0)))",
      indent (level + 6) "(else",
      indent (level + 8) "(if (i64.ne (global.get $pf_storage_result_length) (i64.const 0))",
      indent (level + 10) "(then",
      indent (level + 12) "(global.set $pf_storage_result_ptr",
      indent (level + 14) "(call $pf_arena_alloc (global.get $pf_storage_result_length) (i64.const 1)))",
      indent (level + 12) ("(call $pf_read_register (i64.const " ++ toString register ++
        ") (i64.extend_i32_u (global.get $pf_storage_result_ptr)))"),
      indent (level + 10) "))",
      indent (level + 6) "))",
      indent (level + 2) "))"
    ]

private def resetPromiseResult (capacity level : Nat) : Array String := #[
  indent level "(global.set $pf_promise_result_active (i32.const 1))",
  indent level ("(global.set $pf_promise_result_capacity (i64.const " ++
    toString capacity ++ "))"),
  indent level "(global.set $pf_promise_result_status (i64.const 0))",
  indent level "(global.set $pf_promise_result_length (i64.const 0))",
  indent level "(global.set $pf_promise_result_fits (i64.const 1))",
  indent level "(global.set $pf_promise_result_ptr (i32.const 0))"
]

/-- Preserve nearcore's exact 0/1/2 result status. Only status 1 writes the selected host register,
so not-ready and failed results leave neutral metadata and never inspect stale register bytes. -/
private def finishPromiseResult (capacity : Nat) (status : String) (level : Nat) : Array String := #[
  indent level ("(global.set $pf_promise_result_status " ++ status ++ ")"),
  indent level "(if (i64.gt_u (global.get $pf_promise_result_status) (i64.const 2))",
  indent (level + 2) "(then unreachable))",
  indent level "(if (i64.eq (global.get $pf_promise_result_status) (i64.const 1))",
  indent (level + 2) "(then",
  indent (level + 4) ("(global.set $pf_promise_result_length (call $pf_register_len (i64.const " ++
    toString promiseResultReg ++ ")) )"),
  indent (level + 4) "(if (i64.eq (global.get $pf_promise_result_length) (i64.const -1))",
  indent (level + 6) "(then unreachable))",
  indent (level + 4) ("(if (i64.gt_u (global.get $pf_promise_result_length) (i64.const " ++
    toString capacity ++ "))"),
  indent (level + 6) "(then (global.set $pf_promise_result_fits (i64.const 0)))",
  indent (level + 6) "(else",
  indent (level + 8) "(if (i64.ne (global.get $pf_promise_result_length) (i64.const 0))",
  indent (level + 10) "(then",
  indent (level + 12) "(global.set $pf_promise_result_ptr",
  indent (level + 14) "(call $pf_arena_alloc (global.get $pf_promise_result_length) (i64.const 1)))",
  indent (level + 12) ("(call $pf_read_register (i64.const " ++
    toString promiseResultReg ++
    ") (i64.extend_i32_u (global.get $pf_promise_result_ptr)))"),
  indent (level + 10) "))",
  indent (level + 6) "))",
  indent (level + 2) "))"
]

private structure Region where
  lines : Array String := #[]
  st : EState
  terminal : Bool := false

private partial def emitRegion (p : Program ValKind OpExt)
    (outputPlan : Option Codec.BorshOutputPlan) (view : Bool) (echo : Bool)
    (level : Nat) (defaultSlot : String)
    (ops : List (Op ValKind OpExt)) (st : EState) : Except String Region := do
  match ops with
  | [] =>
      if view then
        throw "extract/unsupported: near v0 view region must end in a return"
      else
        throw "extract/unsupported: near v0 mutating region must end in a state or error exit"
  | op :: tail =>
    match op with
    | .letLocal index value | .setLocal index value =>
        let rendered ← renderVal st value
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { st with last := some (localOfSource index) }
        return {
          lines := #[indent level ("(local.set " ++ localOfSource index ++ " " ++
            rendered ++ ")")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .joinLocal index =>
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { st with last := none }
        return {
          lines := #[indent level ("(local.set " ++ localOfSource index ++
            " (i64.const 0))")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
        if view then throw "extract/unsupported: near v0 view cannot fail"
        match checkedKind op with
        | some kind =>
            let l ← renderVal st lhs
            let r ← renderVal st rhs
            let (lines, st1) ← emitChecked st kind l r level
            let dest' := (fieldOf lhs).orElse (fun _ => st.pendingDest)
            let st' := { st1 with pendingDest := dest', lastStored := false }
            let region ← emitRegion p outputPlan view echo level defaultSlot tail st'
            return { lines := lines ++ region.lines, st := region.st, terminal := true }
        | none => throw "extract/unsupported: near v0 checked operation"
    | .ite cmp lhs rhs thn els =>
        let l ← renderVal st lhs
        let r ← renderVal st rhs
        let thenRegion ← emitRegion p outputPlan view echo (level + 4) defaultSlot thn.toList
          { st with last := none, pendingDest := none }
        unless thenRegion.terminal do
          throw "extract/unsupported: near v0 ite branch must end in a terminal"
        let elseRegion ← emitRegion p outputPlan view echo (level + 4) defaultSlot els.toList
          { st with fresh := thenRegion.st.fresh, last := none, pendingDest := none }
        unless elseRegion.terminal do
          throw "extract/unsupported: near v0 ite branch must end in a terminal"
        let head := indent level ("(if (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++ ")")
        let iteLines :=
          #[head, indent (level + 2) "(then"] ++ thenRegion.lines ++
          #[indent (level + 2) ")", indent (level + 2) "(else"] ++ elseRegion.lines ++
          #[indent (level + 2) "))"]
        if tail.isEmpty || tail.all isExitOp then
          return { lines := iteLines, st := elseRegion.st, terminal := true }
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { st with fresh := elseRegion.st.fresh, last := none, pendingDest := none }
        return { lines := iteLines ++ region.lines, st := region.st, terminal := true }
    | .storeField name value =>
        if view then throw "extract/unsupported: near v0 view cannot write state"
        let v ← renderVal st value
        let lines :=
          #[indent level ("(local.set " ++ localOfSlot name ++ " " ++ v ++ ")")] ++
          storeSlot p name ("(local.get " ++ localOfSlot name ++ ")") level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { st with last := some (localOfSlot name), pendingDest := some name, lastStored := true }
        return { lines := lines ++ region.lines, st := region.st, terminal := true }
    | .okState value | .returnState value =>
        if view then throw "extract/unsupported: near v0 view cannot write state"
        if st.lastStored then
          match value with
          | .local _ =>
              -- The state field was already persisted by `storeField`; an explicitly materialized
              -- tuple result is a separate return channel and must not overwrite that field.
              unless tail.all isExitOp do
                throw "extract/unsupported: near v0 instructions follow terminal operation"
              let v ← renderVal st value
              let mut lines : Array String := #[]
              if st.initializer then lines := lines ++ markInitialized p level
              match st.pendingPromiseReturn with
              | some promiseLocal =>
                  lines := lines.push (indent level
                    ("(call $pf_promise_return (local.get " ++ promiseLocal ++ "))"))
              | none =>
                  if echo then lines := lines ++ returnU64Instr v level
              return { lines, st, terminal := true }
          | _ => pure ()
        let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
        let v ← match st.last with
          | some e => .ok ("(local.get " ++ e ++ ")")
          | none => renderVal st value
        unless tail.all isExitOp do
          throw "extract/unsupported: near v0 instructions follow terminal operation"
        let mut lines :=
          #[indent level ("(local.set " ++ localOfSlot dest ++ " " ++ v ++ ")")] ++
          storeSlot p dest ("(local.get " ++ localOfSlot dest ++ ")") level
        if st.initializer then lines := lines ++ markInitialized p level
        match st.pendingPromiseReturn with
        | some promiseLocal =>
            lines := lines.push (indent level
              ("(call $pf_promise_return (local.get " ++ promiseLocal ++ "))"))
        | none =>
            if echo then
              lines := lines ++ returnU64Instr ("(local.get " ++ localOfSlot dest ++ ")") level
        return { lines, st, terminal := true }
    | .errorOverflow =>
        if view then throw "extract/unsupported: near v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: near v0 instructions follow terminal operation"
        return { lines := #[panicOverflow level], st, terminal := true }
    | .ext (.logUtf8 message) =>
        let (off, len) ← logOf p message
        let region ← emitRegion p outputPlan view echo level defaultSlot tail st
        return {
          lines := #[indent level ("(call $pf_log_utf8 (i64.const " ++ toString len ++
            ") (i64.const " ++ toString off ++ "))")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.logUtf8Bounded capacity message) =>
        let staged ← stageStorageFrame st capacity message level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep297StringData standard version event capacity data) =>
        let staged ← stageNep297StringData st standard version event capacity data level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep141FtMint owner amountLo amountHi) =>
        let staged ← stageNep141FtMint st owner amountLo amountHi level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep141FtTransfer oldOwner newOwner amountLo amountHi) =>
        let staged ← stageNep141FtTransfer st oldOwner newOwner amountLo amountHi level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep141FtBurn owner amountLo amountHi) =>
        let staged ← stageNep141FtBurn st owner amountLo amountHi level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep141FtMintMemo memoCapacity owner amountLo amountHi memo) =>
        let staged ← stageNep141FtMintMemo st memoCapacity owner amountLo amountHi memo level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo) =>
        let staged ← stageNep141FtTransferMemo st memoCapacity oldOwner newOwner
          amountLo amountHi memo level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.nep141FtBurnMemo memoCapacity owner amountLo amountHi memo) =>
        let staged ← stageNep141FtBurnMemo st memoCapacity owner amountLo amountHi memo level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ #[indent level
            ("(call $pf_log_utf8 " ++ staged.length ++ " " ++ staged.pointer ++ ")")] ++
            region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseFunctionCallDetached receiver method argsCapacity arguments
        depositLo depositHi gas) =>
        if view then throw "extract/unsupported: near view cannot create a promise"
        let staged ← stagePromiseCall p st receiver method argsCapacity arguments
          depositLo depositHi gas level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseFunctionCallReturned receiver method argsCapacity arguments
        depositLo depositHi gas) =>
        if view then throw "extract/unsupported: near view cannot create a promise"
        if st.pendingPromiseReturn.isSome then
          throw "extract/unsupported: near method cannot return more than one promise"
        let staged ← stagePromiseCall p st receiver method argsCapacity arguments
          depositLo depositHi gas level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { staged.st with pendingPromiseReturn := some staged.promiseLocal }
        return {
          lines := staged.lines ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseTransferDetached receiver amountLo amountHi) =>
        if view then throw "extract/unsupported: near view cannot create a promise"
        let staged ← stagePromiseTransfer p st receiver amountLo amountHi level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return {
          lines := staged.lines ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseTransferReturned receiver amountLo amountHi) =>
        if view then throw "extract/unsupported: near view cannot create a promise"
        if st.pendingPromiseReturn.isSome then
          throw "extract/unsupported: near method cannot return more than one promise"
        let staged ← stagePromiseTransfer p st receiver amountLo amountHi level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { staged.st with pendingPromiseReturn := some staged.promiseLocal }
        return {
          lines := staged.lines ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseFunctionCallThenReturned receiver childMethod callbackMethod
        childArgsCapacity callbackArgsCapacity childArguments callbackArguments
        childDepositLo childDepositHi childGas
        callbackDepositLo callbackDepositHi callbackGas) =>
        if view then throw "extract/unsupported: near view cannot create a promise"
        if st.pendingPromiseReturn.isSome then
          throw "extract/unsupported: near method cannot return more than one promise"
        let child ← stagePromiseCall p st receiver childMethod childArgsCapacity childArguments
          childDepositLo childDepositHi childGas level
        let callback ← stagePromiseThen p child.st child.promiseLocal callbackMethod
          callbackArgsCapacity callbackArguments callbackDepositLo callbackDepositHi callbackGas level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { callback.st with pendingPromiseReturn := some callback.promiseLocal }
        return {
          lines := child.lines ++ callback.lines ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseFunctionCallAndThenReturned
        leftReceiver leftMethod rightReceiver rightMethod callbackMethod
        leftArgsCapacity rightArgsCapacity callbackArgsCapacity
        leftArguments rightArguments callbackArguments
        leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
        callbackDepositLo callbackDepositHi callbackGas) =>
        if view then throw "extract/unsupported: near view cannot create a promise"
        if st.pendingPromiseReturn.isSome then
          throw "extract/unsupported: near method cannot return more than one promise"
        let left ← stagePromiseCall p st leftReceiver leftMethod leftArgsCapacity leftArguments
          leftDepositLo leftDepositHi leftGas level
        let right ← stagePromiseCall p left.st rightReceiver rightMethod
          rightArgsCapacity rightArguments rightDepositLo rightDepositHi rightGas level
        let joint := stagePromiseAnd right.st left.promiseLocal right.promiseLocal level
        let callback ← stagePromiseThen p joint.st joint.promiseLocal callbackMethod
          callbackArgsCapacity callbackArguments callbackDepositLo callbackDepositHi callbackGas level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail
          { callback.st with pendingPromiseReturn := some callback.promiseLocal }
        return {
          lines := left.lines ++ right.lines ++ joint.lines ++ callback.lines ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.promiseResultRead capacity index) =>
        if view then throw "extract/unsupported: near view cannot read promise results"
        let index ← renderVal st index
        let status := "(call $pf_promise_result " ++ index ++ " (i64.const " ++
          toString promiseResultReg ++ "))"
        let lines := resetPromiseResult capacity level ++
          finishPromiseResult capacity status level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail st
        return { lines := lines ++ region.lines, st := region.st, terminal := region.terminal }
    | .ext (.transientBuffer64Begin capacity) =>
        let region ← emitRegion p outputPlan view echo level defaultSlot tail st
        return {
          lines := #[indent level ("(call $pf_buffer64_begin (i64.const " ++
            toString capacity ++ "))")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.transientBuffer64Set capacity index value) =>
        let i ← renderVal st index
        let v ← renderVal st value
        let region ← emitRegion p outputPlan view echo level defaultSlot tail st
        return {
          lines := #[indent level ("(call $pf_buffer64_set (i64.const " ++
            toString capacity ++ ") " ++ i ++ " " ++ v ++ ")")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.transientBuffer64Finish capacity) =>
        let region ← emitRegion p outputPlan view echo level defaultSlot tail st
        return {
          lines := #[indent level ("(call $pf_buffer64_finish (i64.const " ++
            toString capacity ++ "))")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .ext (.storageRead resultCapacity keyCapacity key) =>
        let staged ← stageStorageFrame st keyCapacity key level
        let status := "(call $pf_storage_read " ++ staged.length ++ " " ++ staged.pointer ++
          " (i64.const " ++ toString rawStorageReg ++ "))"
        let lines := staged.lines ++ resetStorageResult resultCapacity level ++
          finishStorageResult resultCapacity status (some rawStorageReg) level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return { lines := lines ++ region.lines, st := region.st, terminal := region.terminal }
    | .ext (.storageWrite resultCapacity keyCapacity valueCapacity key value) =>
        if view then throw "extract/unsupported: near view cannot write raw storage"
        let stagedKey ← stageStorageFrame st keyCapacity key level
        let stagedValue ← stageStorageFrame stagedKey.st valueCapacity value level
        let status := "(call $pf_storage_write " ++ stagedKey.length ++ " " ++
          stagedKey.pointer ++ " " ++ stagedValue.length ++ " " ++ stagedValue.pointer ++
          " (i64.const " ++ toString rawStorageReg ++ "))"
        let lines := stagedKey.lines ++ stagedValue.lines ++
          resetStorageResult resultCapacity level ++
          finishStorageResult resultCapacity status (some rawStorageReg) level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail stagedValue.st
        return { lines := lines ++ region.lines, st := region.st, terminal := region.terminal }
    | .ext (.storageRemove resultCapacity keyCapacity key) =>
        if view then throw "extract/unsupported: near view cannot remove raw storage"
        let staged ← stageStorageFrame st keyCapacity key level
        let status := "(call $pf_storage_remove " ++ staged.length ++ " " ++ staged.pointer ++
          " (i64.const " ++ toString rawStorageReg ++ "))"
        let lines := staged.lines ++ resetStorageResult resultCapacity level ++
          finishStorageResult resultCapacity status (some rawStorageReg) level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return { lines := lines ++ region.lines, st := region.st, terminal := region.terminal }
    | .ext (.storageHasKey resultCapacity keyCapacity key) =>
        let staged ← stageStorageFrame st keyCapacity key level
        let status := "(call $pf_storage_has_key " ++ staged.length ++ " " ++ staged.pointer ++ ")"
        let lines := staged.lines ++ resetStorageResult resultCapacity level ++
          finishStorageResult resultCapacity status none level
        let region ← emitRegion p outputPlan view echo level defaultSlot tail staged.st
        return { lines := lines ++ region.lines, st := region.st, terminal := region.terminal }
    | .returnU64 value =>
        unless view do
          throw "extract/unsupported: near v0 mutating region cannot return a value"
        let (values, skipped) := collectReturnU64s value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: near v0 instructions follow terminal operation"
        match outputPlan with
        | some plan =>
            return { lines := ← returnBorshInstr st plan values level, st, terminal := true }
        | none =>
            unless values.size == 1 do
              throw "extract/unsupported: near v0 view wants exactly one UInt64"
            let v ← renderVal st values[0]!
            return { lines := returnU64Instr v level, st, terminal := true }
    | _ => throw "extract/unsupported: near v0 op"

private def defaultSlotOf (p : Program ValKind OpExt) : String :=
  (p.slots[0]?).map (·.name) |>.getD "slot0"

private partial def countTemps (ops : Array (Op ValKind OpExt)) : Nat :=
  let rec walk : List (Op ValKind OpExt) → Nat
    | [] => 0
    | .checkedAddU64 .. :: rest | .checkedSubU64 .. :: rest | .checkedMulU64 .. :: rest
    | .checkedDivU64 .. :: rest | .checkedModU64 .. :: rest => 1 + walk rest
    | .ite _ _ _ thn els :: rest => walk thn.toList + walk els.toList + walk rest
    | _ :: rest => walk rest
  walk ops.toList

private partial def usesKind (kind : ValKind) : Op ValKind OpExt → Bool
  | .letLocal _ value | .setLocal _ value => valHas value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      valHas lhs || valHas rhs
  | .ite _ lhs rhs thn els =>
      valHas lhs || valHas rhs || thn.any (usesKind kind) || els.any (usesKind kind)
  | .storeField _ value | .okState value | .returnState value | .returnU64 value =>
      valHas value
  | .ext payload =>
      match payload with
      | .logUtf8 _ | .transientBuffer64Begin _ | .transientBuffer64Finish _ | .reserved => false
      | .logUtf8Bounded _ message => message.any valHas
      | .nep297StringData _ _ _ _ data => data.any valHas
      | .nep141FtMint owner amountLo amountHi =>
          owner.any valHas || valHas amountLo || valHas amountHi
      | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
          oldOwner.any valHas || newOwner.any valHas || valHas amountLo || valHas amountHi
      | .nep141FtBurn owner amountLo amountHi =>
          owner.any valHas || valHas amountLo || valHas amountHi
      | .nep141FtMintMemo _ owner amountLo amountHi memo
      | .nep141FtBurnMemo _ owner amountLo amountHi memo =>
          owner.any valHas || valHas amountLo || valHas amountHi || memo.any valHas
      | .nep141FtTransferMemo _ oldOwner newOwner amountLo amountHi memo =>
          oldOwner.any valHas || newOwner.any valHas || valHas amountLo || valHas amountHi ||
            memo.any valHas
      | .promiseFunctionCallDetached _ _ _ arguments depositLo depositHi gas =>
          arguments.any valHas || valHas depositLo || valHas depositHi || valHas gas
      | .promiseFunctionCallReturned _ _ _ arguments depositLo depositHi gas =>
          arguments.any valHas || valHas depositLo || valHas depositHi || valHas gas
      | .promiseTransferDetached _ amountLo amountHi
      | .promiseTransferReturned _ amountLo amountHi => valHas amountLo || valHas amountHi
      | .promiseFunctionCallThenReturned _ _ _ _ _ childArguments callbackArguments
          childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
          childArguments.any valHas || callbackArguments.any valHas ||
            valHas childDepositLo || valHas childDepositHi || valHas childGas ||
            valHas callbackDepositLo || valHas callbackDepositHi || valHas callbackGas
      | .promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _
          leftArguments rightArguments callbackArguments
          leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
          callbackDepositLo callbackDepositHi callbackGas =>
          leftArguments.any valHas || rightArguments.any valHas || callbackArguments.any valHas ||
            #[leftDepositLo, leftDepositHi, leftGas, rightDepositLo, rightDepositHi, rightGas,
              callbackDepositLo, callbackDepositHi, callbackGas].any valHas
      | .promiseResultRead _ index => valHas index
      | .transientBuffer64Set _ index value => valHas index || valHas value
      | .storageRead _ _ key | .storageRemove _ _ key | .storageHasKey _ _ key => key.any valHas
      | .storageWrite _ _ _ key value => key.any valHas || value.any valHas
  | _ => false
where
  valHas : Val ValKind → Bool
    | .ext k operands => k == kind || operands.any valHas
    | .select _ l r t f => valHas l || valHas r || valHas t || valHas f
    | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
        valHas l || valHas r
    | .field base _ | .bitNot base => valHas base
    | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
        valHas l || valHas r
    | _ => false

private partial def sourceLocalCount (ops : Array (Op ValKind OpExt)) : Nat :=
  ops.foldl (init := 0) fun count op =>
    match op with
    | .letLocal index _ | .joinLocal index | .setLocal index _ =>
        Nat.max count (index + 1)
    | .ite _ _ _ thn els =>
        Nat.max count (Nat.max (sourceLocalCount thn) (sourceLocalCount els))
    | .forBody _ body => Nat.max count (sourceLocalCount body)
    | _ => count

private def methodUses (kind : ValKind) (method : Method ValKind OpExt) : Bool :=
  method.ops.any (usesKind kind)

private def methodChainsPromise (method : Method ValKind OpExt) : Bool :=
  opsChainPromise method.ops

private def predecessorKinds : Array ValKind := #[
  .predecessor, .predecessorLen, .predecessorW1, .predecessorW2,
  .predecessorW3, .predecessorW4, .predecessorW5, .predecessorW6, .predecessorW7
]

private def currentAccountKinds : Array ValKind := #[
  .currentAccountId, .currentAccountIdLen, .currentAccountIdW1, .currentAccountIdW2,
  .currentAccountIdW3, .currentAccountIdW4, .currentAccountIdW5,
  .currentAccountIdW6, .currentAccountIdW7
]

private def attachedDepositKinds : Array ValKind := #[
  .attachedDeposit, .attachedDepositW0, .attachedDepositW1
]

private def accountBalanceKinds : Array ValKind := #[
  .accountBalance, .accountBalanceW0, .accountBalanceW1
]

private def methodUsesAny (kinds : Array ValKind) (method : Method ValKind OpExt) : Bool :=
  kinds.any (methodUses · method)

private def methodEntryPolicy (method : Method ValKind OpExt) : IR.EntryPolicy :=
  match IR.EntryPolicy.ofCanonical method.entryPolicy with
  | .ok policy => policy
  | .error _ => {}

private def methodPrivate (method : Method ValKind OpExt) : Bool :=
  (methodEntryPolicy method).isPrivate

private def methodMigrationFrom (method : Method ValKind OpExt) : Option UInt64 :=
  (methodEntryPolicy method).migrateFrom

/-- Explicit metadata supports donation-only entries. Existing deposit observation remains a
payable capability for source compatibility. `emit` validates the canonical policy first. -/
private def methodPayable (method : Method ValKind OpExt) : Bool :=
  (methodEntryPolicy method).payable || methodUsesAny attachedDepositKinds method

private def methodNeedsDepositGuard (method : Method ValKind OpExt) : Bool :=
  method.tupleArity.isNone && !methodPayable method

private def nonPayableMethods (p : Program ValKind OpExt) : Array (Method ValKind OpExt) :=
  (#[p.initializer] ++ p.entries).filter methodNeedsDepositGuard

private def privateMethods (p : Program ValKind OpExt) : Array (Method ValKind OpExt) :=
  (#[p.initializer] ++ p.entries).filter methodPrivate

private def programHasPrivate (p : Program ValKind OpExt) : Bool :=
  !(privateMethods p).isEmpty

private def nonPayableMessage (method : Method ValKind OpExt) : String :=
  "Method " ++ method.ixName ++ " doesn't accept deposit"

private def privateMessage (method : Method ValKind OpExt) : String :=
  "Method " ++ method.ixName ++ " is private"

private def lifecycleMessages (p : Program ValKind OpExt) : Array String :=
  let initial :=
    if p.entries.isEmpty then #[] else #[panicUninitialized, panicStateIncompatible]
  (#[p.initializer] ++ p.entries).foldl (init := initial) fun messages method =>
    let messages :=
      if methodPrivate method then messages.push (privateMessage method) else messages
    if methodNeedsDepositGuard method then messages.push (nonPayableMessage method) else messages

private def lifecycleLayout (p : Program ValKind OpExt) : Array (String × Nat × Nat) :=
  (lifecycleMessages p).foldl (init := #[]) fun layout message =>
    let next := match layout.back? with
      | some (_, off, len) => off + len
      | none => lifecycleDataBase
    layout.push (message, next, message.toUTF8.size)

private def nonPayableMessageOf (p : Program ValKind OpExt)
    (method : Method ValKind OpExt) : Except String (Nat × Nat) :=
  let message := nonPayableMessage method
  match (lifecycleLayout p).find? (fun item => item.1 == message) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near non-payable panic is missing from static layout"

private def privateMessageOf (p : Program ValKind OpExt)
    (method : Method ValKind OpExt) : Except String (Nat × Nat) :=
  let message := privateMessage method
  match (lifecycleLayout p).find? (fun item => item.1 == message) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near private panic is missing from static layout"

private def uninitializedMessageOf (p : Program ValKind OpExt) : Except String (Nat × Nat) :=
  match (lifecycleLayout p).find? (fun item => item.1 == panicUninitialized) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near uninitialized panic is missing from static layout"

private def incompatibleStateMessageOf (p : Program ValKind OpExt) : Except String (Nat × Nat) :=
  match (lifecycleLayout p).find? (fun item => item.1 == panicStateIncompatible) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near incompatible-state panic is missing from static layout"

private def lifecycleDataSection (p : Program ValKind OpExt) : Except String (Array String) := do
  let layout := lifecycleLayout p
  let total := match layout.back? with
    | some (_, off, len) => off + len - lifecycleDataBase
    | none => 0
  if maxLifecycleDataBytes < total then
    throw s!"extract/unsupported: near lifecycle data {total} exceeds {maxLifecycleDataBytes} bytes"
  return layout.map fun (message, off, _) =>
    "  (data (i32.const " ++ toString off ++ ") \"" ++ watBytes message ++ "\")"

private def depositGuard (p : Program ValKind OpExt) (method : Method ValKind OpExt)
    (level : Nat) : Except String (Array String) := do
  let (off, len) ← nonPayableMessageOf p method
  return #[
    indent level "(call $pf_attached_deposit (i64.const 24))",
    indent level "(if (i32.or (i64.ne (i64.load (i32.const 24)) (i64.const 0))",
    indent (level + 8) "(i64.ne (i64.load (i32.const 32)) (i64.const 0)))",
    indent (level + 2) "(then",
    indent (level + 4) ("(call $pf_panic_utf8 (i64.const " ++ toString len ++
      ") (i64.const " ++ toString off ++ "))"),
    indent (level + 2) "))"
  ]

private def stateEnvelopeGuard (p : Program ValKind OpExt) (expectedDigest : UInt64)
    (level : Nat) : Except String (Array String) := do
  let (missingOff, missingLen) ← uninitializedMessageOf p
  let (incompatibleOff, incompatibleLen) ← incompatibleStateMessageOf p
  let incompatiblePanic :=
    indent (level + 4) ("(call $pf_panic_utf8 (i64.const " ++
      toString incompatibleLen ++ ") (i64.const " ++ toString incompatibleOff ++ "))")
  return #[
    indent level ("(if (i64.eq (call $pf_storage_read (i64.const " ++
      toString stateKey.length ++ ") (i64.const " ++ toString stateKeyOff ++
      ") (i64.const " ++ toString stateMetadataReg ++ ")) (i64.const 0))"),
    indent (level + 2) "(then",
    indent (level + 4) ("(call $pf_panic_utf8 (i64.const " ++ toString missingLen ++
      ") (i64.const " ++ toString missingOff ++ "))"),
    indent (level + 2) "))",
    indent level ("(if (i64.ne (call $pf_register_len (i64.const " ++
      toString stateMetadataReg ++ ")) (i64.const " ++ toString stateMetadataLength ++ "))"),
    indent (level + 2) "(then",
    incompatiblePanic,
    indent (level + 2) "))",
    indent level ("(call $pf_read_register (i64.const " ++ toString stateMetadataReg ++
      ") (i64.const " ++ toString stateMetadataOff ++ "))"),
    indent level ("(if (i32.or (i64.ne (i64.load (i32.const " ++
      toString stateMetadataOff ++ ")) (i64.const " ++ toString stateMetadataMagic ++ "))"),
    indent (level + 8) ("(i64.ne (i64.load (i32.const " ++
      toString (stateMetadataOff + 8) ++ ")) (i64.const " ++
      toString expectedDigest ++ ")))"),
    indent (level + 2) "(then",
    incompatiblePanic,
    indent (level + 2) "))"
  ]

private def uninitializedGuard (p : Program ValKind OpExt)
    (level : Nat) : Except String (Array String) :=
  stateEnvelopeGuard p (IR.stateSchemaDigest p) level

private partial def valUsesArena : Val ValKind → Bool
  | .ext (.transientBuffer64Get _) _
  | .ext (.storageResultStatus _) _
  | .ext (.storageResultLength _) _
  | .ext (.storageResultFits _) _
  | .ext (.storageResultByte _) _
  | .ext (.promiseResultStatus _) _
  | .ext (.promiseResultLength _) _
  | .ext (.promiseResultFits _) _
  | .ext (.promiseResultByte _) _
  | .ext (.promiseResultBorshUInt64D _) _ => true
  | .ext _ operands => operands.any valUsesArena
  | .field base _ | .bitNot base => valUsesArena base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => valUsesArena lhs || valUsesArena rhs
  | .indexGet base _ index _ _ => valUsesArena base || valUsesArena index
  | .select _ lhs rhs thn els =>
      valUsesArena lhs || valUsesArena rhs || valUsesArena thn || valUsesArena els
  | _ => false

private partial def opUsesArena : Op ValKind OpExt → Bool
  | .ext (.transientBuffer64Begin _)
  | .ext (.transientBuffer64Set _ _ _)
  | .ext (.transientBuffer64Finish _)
  | .ext (.storageRead _ _ _)
  | .ext (.storageWrite _ _ _ _ _)
  | .ext (.storageRemove _ _ _)
  | .ext (.storageHasKey _ _ _) => true
  | .ext (.promiseFunctionCallDetached _ _ _ _ _ _ _) => true
  | .ext (.promiseFunctionCallReturned _ _ _ _ _ _ _) => true
  | .ext (.promiseTransferDetached _ _ _)
  | .ext (.promiseTransferReturned _ _ _) => true
  | .ext (.promiseFunctionCallThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _) => true
  | .ext (.promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => true
  | .ext (.promiseResultRead _ _) => true
  | .ext (.logUtf8Bounded _ _) => true
  | .ext (.nep297StringData _ _ _ _ _) => true
  | .ext (.nep141FtMint _ _ _) => true
  | .ext (.nep141FtTransfer _ _ _ _) => true
  | .ext (.nep141FtBurn _ _ _) => true
  | .ext (.nep141FtMintMemo _ _ _ _ _) => true
  | .ext (.nep141FtTransferMemo _ _ _ _ _ _) => true
  | .ext (.nep141FtBurnMemo _ _ _ _ _) => true
  | .ext (.logUtf8 _) | .ext .reserved => false
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      valUsesArena value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs
  | .indexSetLeaf _ lhs rhs _ _ | .indexSet _ lhs rhs _ _ =>
      valUsesArena lhs || valUsesArena rhs
  | .ite _ lhs rhs thn els =>
      valUsesArena lhs || valUsesArena rhs || thn.any opUsesArena || els.any opUsesArena
  | .forBody _ body => body.any opUsesArena
  | .joinLocal _ | .errorOverflow | .errorNamed _ => false

private def methodUsesArena (method : Method ValKind OpExt) : Bool :=
  !method.outputPolicy.isEmpty || method.ops.any opUsesArena

private def programUsesArena (p : Program ValKind OpExt) : Bool :=
  methodUsesArena p.initializer || p.entries.any methodUsesArena

private def clearAccountBuffer (off level : Nat) : Array String :=
  (List.range 8).toArray.map fun i =>
    indent level ("(i64.store (i32.const " ++ toString (off + i * 8) ++
      ") (i64.const 0))")

private def loadAccountId (hostCall lenLocal : String) (register off level : Nat)
    (wordLocal : Nat → String) : Array String :=
  #[
    indent level ("(call " ++ hostCall ++ " (i64.const " ++ toString register ++ "))"),
    indent level ("(local.set " ++ lenLocal ++ " (call $pf_register_len (i64.const " ++
      toString register ++ ")) )"),
    indent level ("(if (i64.gt_u (local.get " ++ lenLocal ++ ") (i64.const 64))"),
    indent (level + 2) "(then",
    indent (level + 4) ("(call $pf_panic_utf8 (i64.const 10) (i64.const " ++
      toString panicAccountIdOff ++ "))"),
    indent (level + 2) "))"
  ] ++ clearAccountBuffer off level ++ #[
    indent level ("(call $pf_read_register (i64.const " ++ toString register ++
      ") (i64.const " ++ toString off ++ "))")
  ] ++ (List.range 8).toArray.map fun i =>
    indent level ("(local.set " ++ wordLocal i ++ " (i64.load (i32.const " ++
      toString (off + i * 8) ++ ")))")

private def privateGuard (p : Program ValKind OpExt) (method : Method ValKind OpExt)
    (level : Nat) : Except String (Array String) := do
  let (off, len) ← privateMessageOf p method
  let comparisons :=
    ["(i64.eq (local.get $pf_self_len) (local.get $pf_pred_len))"] ++
      (List.range 8).map fun i =>
        "(i64.eq (local.get " ++ currentAccountWordLocal i ++ ") (local.get " ++
          predecessorWordLocal i ++ "))"
  let same := comparisons.foldr
    (fun comparison rest => "(i32.and " ++ comparison ++ " " ++ rest ++ ")")
    "(i32.const 1)"
  return (
    loadAccountId "$pf_current_account_id" "$pf_self_len" 3 currentAccountOff level
      currentAccountWordLocal ++
    loadAccountId "$pf_predecessor_account_id" "$pf_pred_len" 0 predecessorAccountOff level
      predecessorWordLocal ++ #[
      indent level ("(if (i32.eqz " ++ same ++ ")"),
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_panic_utf8 (i64.const " ++ toString len ++
        ") (i64.const " ++ toString off ++ "))"),
      indent (level + 2) "))"
    ])

private def loadHostPrelude (method : Method ValKind OpExt) (view : Bool) (level : Nat) :
    Except String (Array String) := do
  if view && methodUsesAny predecessorKinds method then
    throw s!"extract/unsupported: {method.ixName} view cannot read predecessor"
  if view && methodUsesAny attachedDepositKinds method then
    throw s!"extract/unsupported: {method.ixName} view cannot read attachedDeposit"
  let mut lines : Array String := #[]
  if methodUsesAny predecessorKinds method then
    lines := lines ++ loadAccountId "$pf_predecessor_account_id" "$pf_pred_len"
      0 predecessorAccountOff level predecessorWordLocal
  if methodUsesAny attachedDepositKinds method then
    lines := lines.push (indent level "(call $pf_attached_deposit (i64.const 24))")
    if methodUses .attachedDeposit method then
      lines := lines ++ #[
        indent level "(if (i64.ne (i64.load (i32.const 32)) (i64.const 0))",
        indent (level + 2) "(then",
        indent (level + 4) ("(call $pf_panic_utf8 (i64.const 8) (i64.const " ++
          toString panicOverflowOff ++ "))"),
        indent (level + 2) "))"
      ]
    lines := lines ++ #[
      indent level "(local.set $pf_dep (i64.load (i32.const 24)))",
      indent level "(local.set $pf_dep_hi (i64.load (i32.const 32)))"
    ]
  if methodUsesAny accountBalanceKinds method then
    lines := lines.push (indent level "(call $pf_account_balance (i64.const 40))")
    if methodUses .accountBalance method then
      lines := lines ++ #[
        indent level "(if (i64.ne (i64.load (i32.const 48)) (i64.const 0))",
        indent (level + 2) "(then",
        indent (level + 4) ("(call $pf_panic_utf8 (i64.const 8) (i64.const " ++
          toString panicOverflowOff ++ "))"),
        indent (level + 2) "))"
      ]
    lines := lines ++ #[
      indent level "(local.set $pf_bal (i64.load (i32.const 40)))",
      indent level "(local.set $pf_bal_hi (i64.load (i32.const 48)))"
    ]
  if methodUsesAny currentAccountKinds method then
    lines := lines ++ loadAccountId "$pf_current_account_id" "$pf_self_len"
      3 currentAccountOff level currentAccountWordLocal
  else if methodChainsPromise method then
    lines := lines ++ #[
      indent level "(call $pf_current_account_id (i64.const 3))",
      indent level "(local.set $pf_self_len (call $pf_register_len (i64.const 3)) )",
      indent level "(if (i64.gt_u (local.get $pf_self_len) (i64.const 64))",
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_panic_utf8 (i64.const 10) (i64.const " ++
        toString panicAccountIdOff ++ "))"),
      indent (level + 2) "))"
    ] ++ clearAccountBuffer currentAccountOff level ++ #[
      indent level ("(call $pf_read_register (i64.const 3) (i64.const " ++
        toString currentAccountOff ++ "))")
    ]
  return lines

private def inputPlanOf (method : Method ValKind OpExt) :
    Except String (Option Codec.BorshInputPlan) :=
  method.inputSchema.mapM Codec.inputPlan

private def panicInput (level : Nat) : String :=
  indent level ("(call $pf_panic_utf8 (i64.const 5) (i64.const " ++
    toString panicInputOff ++ "))")

private def loadArg (method : Method ValKind OpExt) (level : Nat) :
    Except String (Array String) := do
  if let some plan ← inputPlanOf method then
    unless method.paramCount == plan.localCount do
      throw s!"near/codec: {method.ixName} scalar frame does not match its Borsh input plan"
    let mut lines : Array String := #[
      indent level ("(call $pf_input (i64.const " ++ toString inputReg ++ "))"),
      indent level ("(local.set $pf_input_size (call $pf_register_len (i64.const " ++
        toString inputReg ++ ")) )"),
      indent level "(if (i64.lt_u (local.get $pf_input_size) (i64.const 4))",
      indent (level + 2) "(then",
      panicInput (level + 4),
      indent (level + 2) "))",
      indent level ("(if (i64.gt_u (local.get $pf_input_size) (i64.const " ++
        toString (4 + plan.capacity) ++ "))"),
      indent (level + 2) "(then",
      panicInput (level + 4),
      indent (level + 2) "))",
      indent level ("(call $pf_read_register (i64.const " ++ toString inputReg ++
        ") (i64.const " ++ toString boundedInputOff ++ "))"),
      indent level ("(local.set " ++ localOfArg 0 ++ " (i64.load32_u (i32.const " ++
        toString boundedInputOff ++ ")) )"),
      indent level ("(if (i64.gt_u (local.get " ++ localOfArg 0 ++ ") (i64.const " ++
        toString plan.capacity ++ "))"),
      indent (level + 2) "(then",
      panicInput (level + 4),
      indent (level + 2) "))",
      indent level ("(if (i64.ne (local.get $pf_input_size) (i64.add (i64.const 4) " ++
        "(local.get " ++ localOfArg 0 ++ ")))"),
      indent (level + 2) "(then",
      panicInput (level + 4),
      indent (level + 2) "))"
    ]
    if plan.validateUtf8 then
      lines := lines ++ #[
        indent level ("(if (i32.eqz (call $pf_utf8_valid (i32.const " ++
          toString (boundedInputOff + 4) ++ ") (i32.wrap_i64 (local.get " ++
          localOfArg 0 ++ "))))"),
        indent (level + 2) "(then",
        panicInput (level + 4),
        indent (level + 2) "))"
      ]
    for i in [0:plan.capacity] do
      lines := lines.push (indent level ("(local.set " ++ localOfArg (1 + i) ++
        " (if (result i64) (i64.lt_u (i64.const " ++ toString i ++ ") (local.get " ++
        localOfArg 0 ++ ")) (then (i64.load8_u (i32.const " ++
        toString (boundedInputOff + 4 + i) ++ "))) (else (i64.const 0))))"))
    return lines
  if method.paramCount == 0 then
    return #[
      indent level ("(call $pf_input (i64.const " ++ toString inputReg ++ "))"),
      indent level ("(if (i64.ne (call $pf_register_len (i64.const " ++
        toString inputReg ++ ")) (i64.const 0))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_panic_utf8 (i64.const 5) (i64.const " ++
        toString panicInputOff ++ "))"),
      indent (level + 2) "))"
    ]
  else if method.paramCount == 1 then
    return #[
      indent level ("(call $pf_input (i64.const " ++ toString inputReg ++ "))"),
      indent level ("(if (i64.ne (call $pf_register_len (i64.const " ++
        toString inputReg ++ ")) (i64.const 8))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_panic_utf8 (i64.const 5) (i64.const " ++
        toString panicInputOff ++ "))"),
      indent (level + 2) "))",
      indent level ("(call $pf_read_register (i64.const " ++ toString inputReg ++
        ") (i64.const 0))"),
      indent level ("(local.set " ++ localOfArg 0 ++ " (i64.load (i32.const 0)))")
    ]
  else
    return #[]

private def loadSlots (p : Program ValKind OpExt) (level : Nat) : Array String :=
  p.slots.foldl (init := #[]) fun acc slot =>
    let (off, len) := keyOf p slot.name
    acc ++ #[
      indent level ("(if (i64.eq (call $pf_storage_read (i64.const " ++ toString len ++
        ") (i64.const " ++ toString off ++ ") (i64.const " ++ toString storageReg ++
        ")) (i64.const 1))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(if (i64.ne (call $pf_register_len (i64.const " ++
        toString storageReg ++ ")) (i64.const 8)) (then unreachable))"),
      indent (level + 4) ("(call $pf_read_register (i64.const " ++ toString storageReg ++
        ") (i64.const 8))"),
      indent (level + 4) ("(local.set " ++ localOfSlot slot.name ++
        " (i64.load (i32.const 8)))"),
      indent (level + 2) ")",
      indent (level + 2) ("(else (local.set " ++ localOfSlot slot.name ++ " (i64.const 0))))")
    ]

private partial def supportsInitializerTerminal (ops : Array (Op ValKind OpExt)) : Bool :=
  ops.all fun op => match op with
    | .returnU64 _ => false
    | .ite _ _ _ thn els => supportsInitializerTerminal thn && supportsInitializerTerminal els
    | .forBody _ body => supportsInitializerTerminal body
    | _ => true

private def renderFn (p : Program ValKind OpExt)
    (method : Method ValKind OpExt) (initializer : Bool) : Except String (Array String) := do
  let inputPlan ← inputPlanOf method
  let outputPlan ← outputPlanOf method
  if inputPlan.isNone then
    unless method.paramCount ≤ 1 do
      throw s!"extract/unsupported: {method.ixName} wants at most one UInt64 parameter for near v0"
  if initializer then
    unless supportsInitializerTerminal method.ops do
      throw "extract/unsupported: near initializer must return state"
  let view := method.tupleArity.isSome
  let echo := method.echoDropped
  let isPrivate := methodPrivate method
  let migrateFrom := methodMigrationFrom method
  let writesStateEnvelope := initializer || migrateFrom.isSome
  if view && methodUses .promiseResultsCount method then
    throw "extract/unsupported: near view cannot count promise results"
  let st : EState := { paramCount := method.paramCount, initializer := writesStateEnvelope }
  let region ← emitRegion p outputPlan view echo 4 (defaultSlotOf p) method.ops.toList st
  unless region.terminal do
    throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
  let mut lines : Array String := #[]
  if method.echoDropped then
    lines := lines.push s!"  ;; v0 ABI: {method.ixName} value_returns 8-byte LE after store"
  lines := lines.push ("  (func (export \"" ++ method.ixName ++ "\")")
  for i in [0:method.paramCount] do
    lines := lines.push ("    (local " ++ localOfArg i ++ " i64)")
  if inputPlan.isSome then
    lines := lines.push "    (local $pf_input_size i64)"
  if outputPlan.isSome then
    lines := lines.push "    (local $pf_output_ptr i32)"
    lines := lines.push "    (local $pf_output_length i64)"
  if isPrivate || methodUsesAny predecessorKinds method then
    lines := lines.push "    (local $pf_pred_len i64)"
    for i in List.range 8 do
      lines := lines.push ("    (local " ++ predecessorWordLocal i ++ " i64)")
  if methodUsesAny attachedDepositKinds method then
    lines := lines.push "    (local $pf_dep i64)"
    lines := lines.push "    (local $pf_dep_hi i64)"
  if methodUsesAny accountBalanceKinds method then
    lines := lines.push "    (local $pf_bal i64)"
    lines := lines.push "    (local $pf_bal_hi i64)"
  if isPrivate || methodUsesAny currentAccountKinds method || methodChainsPromise method then
    lines := lines.push "    (local $pf_self_len i64)"
  if isPrivate || methodUsesAny currentAccountKinds method then
    for i in List.range 8 do
      lines := lines.push ("    (local " ++ currentAccountWordLocal i ++ " i64)")
  for slot in p.slots do
    lines := lines.push ("    (local " ++ localOfSlot slot.name ++ " i64)")
  for i in List.range (sourceLocalCount method.ops) do
    lines := lines.push ("    (local " ++ localOfSource i ++ " i64)")
  for i in List.range (Nat.max (countTemps method.ops) region.st.fresh) do
    lines := lines.push ("    (local " ++ localOfTemp i ++ " i64)")
  if isPrivate then
    lines := lines ++ (← privateGuard p method 4)
  if methodNeedsDepositGuard method then
    lines := lines ++ (← depositGuard p method 4)
  if methodUsesArena method then
    lines := lines.push "    (call $pf_arena_reset)"
  lines := lines ++ (← loadArg method 4)
  lines := lines ++ (← loadHostPrelude method view 4)
  if initializer then
    lines := lines ++ initializedGuard p 4
  else match migrateFrom with
    | some oldDigest => lines := lines ++ (← stateEnvelopeGuard p oldDigest 4)
    | none => lines := lines ++ (← uninitializedGuard p 4)
  if migrateFrom.isNone then
    lines := lines ++ loadSlots p 4
  lines := lines ++ region.lines
  lines := lines.push "  )"
  return lines

private def programUses (kind : ValKind) (p : IR.Program) : Bool :=
  methodUses kind p.initializer || p.entries.any (methodUses kind)

private def dataSection (p : Program ValKind OpExt) : Array String :=
  let keys := (keyLayout p).map fun (name, off, _) =>
    "  (data (i32.const " ++ toString off ++ ") \"" ++ name ++ "\")"
  let base := #[
    "  (data (i32.const " ++ toString panicOverflowOff ++ ") \"overflow\")",
    "  (data (i32.const " ++ toString panicDivOff ++ ") \"divide-by-zero\")",
    "  (data (i32.const " ++ toString panicInputOff ++ ") \"input\")",
    "  (data (i32.const " ++ toString stateKeyOff ++ ") \"" ++ stateKey ++ "\")",
    "  (data (i32.const " ++ toString panicInitializedOff ++ ") \"" ++
      panicInitialized ++ "\")"
  ]
  let account :=
    if programHasPrivate p || predecessorKinds.any (programUses · p) ||
        currentAccountKinds.any (programUses · p) then
      #["  (data (i32.const " ++ toString panicAccountIdOff ++ ") \"account-id\")"]
    else #[]
  keys ++ base ++ account

private def staticDataEnd (p : Program ValKind OpExt) : Nat :=
  let keyEnd := match (keyLayout p).back? with
    | some (_, off, len) => off + len
    | none => 0
  let logEnd := match (logLayout p).back? with
    | some (_, off, len) => off + len
    | none => 0
  let promiseEnd := match (promiseLayout p).back? with
    | some (_, off, len) => off + len
    | none => 0
  let lifecycleEnd := match (lifecycleLayout p).back? with
    | some (_, off, len) => off + len
    | none => 0
  let panicEnd := panicInitializedOff + panicInitialized.length
  Nat.max lifecycleEnd (Nat.max promiseEnd (Nat.max panicEnd (Nat.max keyEnd logEnd)))

private def arenaBase (p : Program ValKind OpExt) : Nat :=
  Memory.alignUp (staticDataEnd p) 8

/-- Generic upward bump arena plus bounded UInt64-buffer and raw-storage consumers. All addresses
remain in target-owned globals. Arithmetic is widened to i64 before memory32 page/range checks. -/
private def arenaHelpers (p : Program ValKind OpExt) : Array String :=
  let base := arenaBase p
  #[
    "  (global $pf_arena_cursor (mut i64) (i64.const " ++ toString base ++ "))",
    "  (global $pf_buffer64_ptr (mut i32) (i32.const 0))",
    "  (global $pf_buffer64_capacity (mut i64) (i64.const 0))",
    "  (global $pf_buffer64_active (mut i32) (i32.const 0))",
    "  (global $pf_storage_result_ptr (mut i32) (i32.const 0))",
    "  (global $pf_storage_result_capacity (mut i64) (i64.const 0))",
    "  (global $pf_storage_result_status (mut i64) (i64.const 0))",
    "  (global $pf_storage_result_length (mut i64) (i64.const 0))",
    "  (global $pf_storage_result_fits (mut i64) (i64.const 1))",
    "  (global $pf_storage_result_active (mut i32) (i32.const 0))",
    "  (global $pf_promise_result_ptr (mut i32) (i32.const 0))",
    "  (global $pf_promise_result_capacity (mut i64) (i64.const 0))",
    "  (global $pf_promise_result_status (mut i64) (i64.const 0))",
    "  (global $pf_promise_result_length (mut i64) (i64.const 0))",
    "  (global $pf_promise_result_fits (mut i64) (i64.const 1))",
    "  (global $pf_promise_result_active (mut i32) (i32.const 0))",
    "  (func $pf_arena_reset",
    "    (global.set $pf_arena_cursor (i64.const " ++ toString base ++ "))",
    "    (global.set $pf_buffer64_ptr (i32.const 0))",
    "    (global.set $pf_buffer64_capacity (i64.const 0))",
    "    (global.set $pf_buffer64_active (i32.const 0))",
    "    (global.set $pf_storage_result_ptr (i32.const 0))",
    "    (global.set $pf_storage_result_capacity (i64.const 0))",
    "    (global.set $pf_storage_result_status (i64.const 0))",
    "    (global.set $pf_storage_result_length (i64.const 0))",
    "    (global.set $pf_storage_result_fits (i64.const 1))",
    "    (global.set $pf_storage_result_active (i32.const 0))",
    "    (global.set $pf_promise_result_ptr (i32.const 0))",
    "    (global.set $pf_promise_result_capacity (i64.const 0))",
    "    (global.set $pf_promise_result_status (i64.const 0))",
    "    (global.set $pf_promise_result_length (i64.const 0))",
    "    (global.set $pf_promise_result_fits (i64.const 1))",
    "    (global.set $pf_promise_result_active (i32.const 0)))",
    "  (func $pf_arena_alloc (param $bytes i64) (param $alignment i64) (result i32)",
    "    (local $mask i64) (local $pointer i64) (local $finish i64)",
    "    (local $current_pages i64) (local $current_bytes i64)",
    "    (local $required_pages i64) (local $delta i64)",
    "    (if (i32.or (i64.eqz (local.get $bytes)) (i64.eqz (local.get $alignment)))",
    "      (then unreachable))",
    "    (local.set $mask (i64.sub (local.get $alignment) (i64.const 1)))",
    "    (if (i64.ne (i64.and (local.get $alignment) (local.get $mask)) (i64.const 0))",
    "      (then unreachable))",
    "    (if (i64.gt_u (local.get $alignment) (i64.const 4294967296))",
    "      (then unreachable))",
    "    (if (i64.gt_u (global.get $pf_arena_cursor)",
    "        (i64.sub (i64.const 4294967295) (local.get $mask)))",
    "      (then unreachable))",
    "    (local.set $pointer",
    "      (i64.and (i64.add (global.get $pf_arena_cursor) (local.get $mask))",
    "        (i64.xor (local.get $mask) (i64.const -1))))",
    "    (if (i64.gt_u (local.get $bytes)",
    "        (i64.sub (i64.const 4294967296) (local.get $pointer)))",
    "      (then unreachable))",
    "    (local.set $finish (i64.add (local.get $pointer) (local.get $bytes)))",
    "    (local.set $current_pages (i64.extend_i32_u (memory.size)))",
    "    (local.set $current_bytes (i64.shl (local.get $current_pages) (i64.const 16)))",
    "    (if (i64.gt_u (local.get $finish) (local.get $current_bytes))",
    "      (then",
    "        (local.set $required_pages",
    "          (i64.shr_u (i64.add (local.get $finish) (i64.const 65535)) (i64.const 16)))",
    "        (local.set $delta (i64.sub (local.get $required_pages) (local.get $current_pages)))",
    "        (if (i32.eq (memory.grow (i32.wrap_i64 (local.get $delta))) (i32.const -1))",
    "          (then unreachable))))",
    "    (global.set $pf_arena_cursor (local.get $finish))",
    "    (i32.wrap_i64 (local.get $pointer)))",
    "  (func $pf_buffer64_begin (param $capacity i64)",
    "    (local $i i64) (local $ptr i32)",
    "    (if (i32.or (i64.eqz (local.get $capacity))",
    "        (i64.gt_u (local.get $capacity) (i64.const 4096)))",
    "      (then unreachable))",
    "    (if (global.get $pf_buffer64_active) (then unreachable))",
    "    (local.set $ptr",
    "      (call $pf_arena_alloc (i64.shl (local.get $capacity) (i64.const 3)) (i64.const 8)))",
    "    (global.set $pf_buffer64_ptr (local.get $ptr))",
    "    (global.set $pf_buffer64_capacity (local.get $capacity))",
    "    (global.set $pf_buffer64_active (i32.const 1))",
    "    (loop $zero",
    "      (if (i64.lt_u (local.get $i) (local.get $capacity))",
    "        (then",
    "          (i64.store (i32.add (local.get $ptr)",
    "            (i32.wrap_i64 (i64.shl (local.get $i) (i64.const 3)))) (i64.const 0))",
    "          (local.set $i (i64.add (local.get $i) (i64.const 1)))",
    "          (br $zero)))))",
    "  (func $pf_buffer64_set (param $capacity i64) (param $index i64) (param $value i64)",
    "    (if (i32.eqz (global.get $pf_buffer64_active)) (then unreachable))",
    "    (if (i64.ne (local.get $capacity) (global.get $pf_buffer64_capacity))",
    "      (then unreachable))",
    "    (if (i64.ge_u (local.get $index) (local.get $capacity)) (then unreachable))",
    "    (i64.store (i32.add (global.get $pf_buffer64_ptr)",
    "      (i32.wrap_i64 (i64.shl (local.get $index) (i64.const 3)))) (local.get $value)))",
    "  (func $pf_buffer64_get (param $capacity i64) (param $index i64) (result i64)",
    "    (if (i32.eqz (global.get $pf_buffer64_active)) (then unreachable))",
    "    (if (i64.ne (local.get $capacity) (global.get $pf_buffer64_capacity))",
    "      (then unreachable))",
    "    (if (i64.ge_u (local.get $index) (local.get $capacity)) (then unreachable))",
    "    (i64.load (i32.add (global.get $pf_buffer64_ptr)",
    "      (i32.wrap_i64 (i64.shl (local.get $index) (i64.const 3))))))",
    "  (func $pf_buffer64_finish (param $capacity i64)",
    "    (if (i32.eqz (global.get $pf_buffer64_active)) (then unreachable))",
    "    (if (i64.ne (local.get $capacity) (global.get $pf_buffer64_capacity))",
    "      (then unreachable))",
    "    (global.set $pf_buffer64_ptr (i32.const 0))",
    "    (global.set $pf_buffer64_capacity (i64.const 0))",
    "    (global.set $pf_buffer64_active (i32.const 0)))",
    "  (func $pf_storage_result_check (param $capacity i64)",
    "    (if (i32.eqz (global.get $pf_storage_result_active)) (then unreachable))",
    "    (if (i64.ne (local.get $capacity) (global.get $pf_storage_result_capacity))",
    "      (then unreachable)))",
    "  (func $pf_storage_result_status (param $capacity i64) (result i64)",
    "    (call $pf_storage_result_check (local.get $capacity))",
    "    (global.get $pf_storage_result_status))",
    "  (func $pf_storage_result_length (param $capacity i64) (result i64)",
    "    (call $pf_storage_result_check (local.get $capacity))",
    "    (global.get $pf_storage_result_length))",
    "  (func $pf_storage_result_fits (param $capacity i64) (result i64)",
    "    (call $pf_storage_result_check (local.get $capacity))",
    "    (global.get $pf_storage_result_fits))",
    "  (func $pf_storage_result_byte (param $capacity i64) (param $index i64) (result i64)",
    "    (call $pf_storage_result_check (local.get $capacity))",
    "    (if (result i64)",
    "      (i32.and (i64.ne (global.get $pf_storage_result_fits) (i64.const 0))",
    "        (i64.lt_u (local.get $index) (global.get $pf_storage_result_length)))",
    "      (then (i64.load8_u (i32.add (global.get $pf_storage_result_ptr)",
    "        (i32.wrap_i64 (local.get $index)))))",
    "      (else (i64.const 0))))",
    "  (func $pf_promise_result_check (param $capacity i64)",
    "    (if (i32.eqz (global.get $pf_promise_result_active)) (then unreachable))",
    "    (if (i64.ne (local.get $capacity) (global.get $pf_promise_result_capacity))",
    "      (then unreachable)))",
    "  (func $pf_promise_result_status (param $capacity i64) (result i64)",
    "    (call $pf_promise_result_check (local.get $capacity))",
    "    (global.get $pf_promise_result_status))",
    "  (func $pf_promise_result_length (param $capacity i64) (result i64)",
    "    (call $pf_promise_result_check (local.get $capacity))",
    "    (global.get $pf_promise_result_length))",
    "  (func $pf_promise_result_fits (param $capacity i64) (result i64)",
    "    (call $pf_promise_result_check (local.get $capacity))",
    "    (global.get $pf_promise_result_fits))",
    "  (func $pf_promise_result_byte (param $capacity i64) (param $index i64) (result i64)",
    "    (call $pf_promise_result_check (local.get $capacity))",
    "    (if (result i64)",
    "      (i32.and (i64.eq (global.get $pf_promise_result_status) (i64.const 1))",
    "        (i32.and (i64.ne (global.get $pf_promise_result_fits) (i64.const 0))",
    "          (i64.lt_u (local.get $index) (global.get $pf_promise_result_length))))",
    "      (then (i64.load8_u (i32.add (global.get $pf_promise_result_ptr)",
    "        (i32.wrap_i64 (local.get $index)))))",
    "      (else (i64.const 0))))",
    ""
  ]

/-- Closed helpers used only by the NEP-141 event effect. The decimal routine keeps 39
little-endian base-10 digits, consumes source bits 127 down to 0, feeds each bit into digit zero,
updates digits 0 through 38, then emits digits 38 down to 0 (including one zero digit). -/
private def ftEventHelpers : Array String := #[
  "  (func $pf_json_escape_byte (param $byte i64) (param $ptr i32) (param $len i64) (result i64)",
  "    (local $nibble i64)",
  "    (if (i32.or (i64.eq (local.get $byte) (i64.const 34)) (i64.eq (local.get $byte) (i64.const 92)))",
  "      (then",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (local.get $byte))",
  "        (return (i64.add (local.get $len) (i64.const 2)))))",
  "    (if (i64.eq (local.get $byte) (i64.const 8))",
  "      (then (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (i64.const 98))",
  "        (return (i64.add (local.get $len) (i64.const 2)))))",
  "    (if (i64.eq (local.get $byte) (i64.const 9))",
  "      (then (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (i64.const 116))",
  "        (return (i64.add (local.get $len) (i64.const 2)))))",
  "    (if (i64.eq (local.get $byte) (i64.const 10))",
  "      (then (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (i64.const 110))",
  "        (return (i64.add (local.get $len) (i64.const 2)))))",
  "    (if (i64.eq (local.get $byte) (i64.const 12))",
  "      (then (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (i64.const 102))",
  "        (return (i64.add (local.get $len) (i64.const 2)))))",
  "    (if (i64.eq (local.get $byte) (i64.const 13))",
  "      (then (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (i64.const 114))",
  "        (return (i64.add (local.get $len) (i64.const 2)))))",
  "    (if (i64.lt_u (local.get $byte) (i64.const 32))",
  "      (then",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (i64.const 92))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 1)))) (i64.const 117))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 2)))) (i64.const 48))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 3)))) (i64.const 48))",
  "        (local.set $nibble (i64.shr_u (local.get $byte) (i64.const 4)))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 4))))",
  "          (if (result i64) (i64.lt_u (local.get $nibble) (i64.const 10))",
  "            (then (i64.add (local.get $nibble) (i64.const 48)))",
  "            (else (i64.add (local.get $nibble) (i64.const 87)))))",
  "        (local.set $nibble (i64.and (local.get $byte) (i64.const 15)))",
  "        (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (i64.add (local.get $len) (i64.const 5))))",
  "          (if (result i64) (i64.lt_u (local.get $nibble) (i64.const 10))",
  "            (then (i64.add (local.get $nibble) (i64.const 48)))",
  "            (else (i64.add (local.get $nibble) (i64.const 87)))))",
  "        (return (i64.add (local.get $len) (i64.const 6)))))",
  "    (i64.store8 (i32.add (local.get $ptr) (i32.wrap_i64 (local.get $len))) (local.get $byte))",
  "    (i64.add (local.get $len) (i64.const 1)))",
  "  (func $pf_u128_decimal (param $lo i64) (param $hi i64) (param $digits i32) (param $out i32) (result i64)",
  "    (local $bit i64) (local $i i64) (local $carry i64) (local $value i64)",
  "    (local $digit i64) (local $length i64) (local $started i32)",
  "    (local.set $i (i64.const 0))",
  "    (block $zero_done (loop $zero",
  "      (br_if $zero_done (i64.ge_u (local.get $i) (i64.const 39)))",
  "      (i64.store8 (i32.add (local.get $digits) (i32.wrap_i64 (local.get $i))) (i64.const 0))",
  "      (local.set $i (i64.add (local.get $i) (i64.const 1)))",
  "      (br $zero)))",
  "    (local.set $bit (i64.const 128))",
  "    (block $bits_done (loop $bits",
  "      (br_if $bits_done (i64.eqz (local.get $bit)))",
  "      (local.set $bit (i64.sub (local.get $bit) (i64.const 1)))",
  "      (local.set $carry",
  "        (if (result i64) (i64.ge_u (local.get $bit) (i64.const 64))",
  "          (then (i64.and (i64.shr_u (local.get $hi) (i64.sub (local.get $bit) (i64.const 64))) (i64.const 1)))",
  "          (else (i64.and (i64.shr_u (local.get $lo) (local.get $bit)) (i64.const 1)))))",
  "      (local.set $i (i64.const 0))",
  "      (block $digits_done (loop $digits_loop",
  "        (br_if $digits_done (i64.ge_u (local.get $i) (i64.const 39)))",
  "        (local.set $value (i64.add (i64.shl (i64.load8_u (i32.add (local.get $digits) (i32.wrap_i64 (local.get $i)))) (i64.const 1)) (local.get $carry)))",
  "        (i64.store8 (i32.add (local.get $digits) (i32.wrap_i64 (local.get $i))) (i64.rem_u (local.get $value) (i64.const 10)))",
  "        (local.set $carry (i64.div_u (local.get $value) (i64.const 10)))",
  "        (local.set $i (i64.add (local.get $i) (i64.const 1)))",
  "        (br $digits_loop)))",
  "      (br $bits)))",
  "    (local.set $i (i64.const 39))",
  "    (block $output_done (loop $output",
  "      (br_if $output_done (i64.eqz (local.get $i)))",
  "      (local.set $i (i64.sub (local.get $i) (i64.const 1)))",
  "      (local.set $digit (i64.load8_u (i32.add (local.get $digits) (i32.wrap_i64 (local.get $i)))))",
  "      (if (i32.or (i64.ne (local.get $digit) (i64.const 0)) (i32.or (local.get $started) (i64.eqz (local.get $i))))",
  "        (then",
  "          (i64.store8 (i32.add (local.get $out) (i32.wrap_i64 (local.get $length))) (i64.add (local.get $digit) (i64.const 48)))",
  "          (local.set $length (i64.add (local.get $length) (i64.const 1)))",
  "          (local.set $started (i32.const 1))))",
  "      (br $output)))",
  "    (local.get $length))",
  ""
]

private def methodUsesUtf8Codec (method : Method ValKind OpExt) : Bool :=
  (match method.inputSchema with
    | some (.boundedString _) => true
    | _ => false) ||
  (match method.outputSchema with
    | some (.boundedString _) => true
    | _ => false)

private def programUsesUtf8Codec (p : Program ValKind OpExt) : Bool :=
  methodUsesUtf8Codec p.initializer || p.entries.any methodUsesUtf8Codec

/-- Strict Unicode-scalar UTF-8 validation over one already bounded memory span. Explicit Borsh
lengths are always used; no NUL-terminated nearcore sentinel semantics enter this helper. -/
private def utf8Validator : Array String := #[
  "  (func $pf_utf8_valid (param $ptr i32) (param $len i32) (result i32)",
  "    (local $i i32) (local $b0 i32) (local $b1 i32) (local $b2 i32) (local $b3 i32)",
  "    (local $ok i32)",
  "    (block $invalid",
  "      (loop $scan",
  "        (if (i32.ge_u (local.get $i) (local.get $len))",
  "          (then (return (i32.const 1))))",
  "        (local.set $b0 (i32.load8_u (i32.add (local.get $ptr) (local.get $i))))",
  "        (if (i32.le_u (local.get $b0) (i32.const 127))",
  "          (then",
  "            (local.set $i (i32.add (local.get $i) (i32.const 1)))",
  "            (br $scan)))",
  "        (if (i32.and (i32.ge_u (local.get $b0) (i32.const 194))",
  "                     (i32.le_u (local.get $b0) (i32.const 223)))",
  "          (then",
  "            (br_if $invalid (i32.gt_u (i32.add (local.get $i) (i32.const 2)) (local.get $len)))",
  "            (local.set $b1 (i32.load8_u (i32.add (local.get $ptr) (i32.add (local.get $i) (i32.const 1)))))",
  "            (br_if $invalid (i32.eqz (i32.and (i32.ge_u (local.get $b1) (i32.const 128))",
  "                                                (i32.le_u (local.get $b1) (i32.const 191)))))",
  "            (local.set $i (i32.add (local.get $i) (i32.const 2)))",
  "            (br $scan)))",
  "        (if (i32.and (i32.ge_u (local.get $b0) (i32.const 224))",
  "                     (i32.le_u (local.get $b0) (i32.const 239)))",
  "          (then",
  "            (br_if $invalid (i32.gt_u (i32.add (local.get $i) (i32.const 3)) (local.get $len)))",
  "            (local.set $b1 (i32.load8_u (i32.add (local.get $ptr) (i32.add (local.get $i) (i32.const 1)))))",
  "            (local.set $b2 (i32.load8_u (i32.add (local.get $ptr) (i32.add (local.get $i) (i32.const 2)))))",
  "            (local.set $ok",
  "              (if (result i32) (i32.eq (local.get $b0) (i32.const 224))",
  "                (then (i32.and (i32.ge_u (local.get $b1) (i32.const 160)) (i32.le_u (local.get $b1) (i32.const 191))))",
  "                (else (if (result i32) (i32.eq (local.get $b0) (i32.const 237))",
  "                  (then (i32.and (i32.ge_u (local.get $b1) (i32.const 128)) (i32.le_u (local.get $b1) (i32.const 159))))",
  "                  (else (i32.and (i32.ge_u (local.get $b1) (i32.const 128)) (i32.le_u (local.get $b1) (i32.const 191))))))))",
  "            (br_if $invalid (i32.eqz (local.get $ok)))",
  "            (br_if $invalid (i32.eqz (i32.and (i32.ge_u (local.get $b2) (i32.const 128))",
  "                                                (i32.le_u (local.get $b2) (i32.const 191)))))",
  "            (local.set $i (i32.add (local.get $i) (i32.const 3)))",
  "            (br $scan)))",
  "        (if (i32.and (i32.ge_u (local.get $b0) (i32.const 240))",
  "                     (i32.le_u (local.get $b0) (i32.const 244)))",
  "          (then",
  "            (br_if $invalid (i32.gt_u (i32.add (local.get $i) (i32.const 4)) (local.get $len)))",
  "            (local.set $b1 (i32.load8_u (i32.add (local.get $ptr) (i32.add (local.get $i) (i32.const 1)))))",
  "            (local.set $b2 (i32.load8_u (i32.add (local.get $ptr) (i32.add (local.get $i) (i32.const 2)))))",
  "            (local.set $b3 (i32.load8_u (i32.add (local.get $ptr) (i32.add (local.get $i) (i32.const 3)))))",
  "            (local.set $ok",
  "              (if (result i32) (i32.eq (local.get $b0) (i32.const 240))",
  "                (then (i32.and (i32.ge_u (local.get $b1) (i32.const 144)) (i32.le_u (local.get $b1) (i32.const 191))))",
  "                (else (if (result i32) (i32.eq (local.get $b0) (i32.const 244))",
  "                  (then (i32.and (i32.ge_u (local.get $b1) (i32.const 128)) (i32.le_u (local.get $b1) (i32.const 143))))",
  "                  (else (i32.and (i32.ge_u (local.get $b1) (i32.const 128)) (i32.le_u (local.get $b1) (i32.const 191))))))))",
  "            (br_if $invalid (i32.eqz (local.get $ok)))",
  "            (br_if $invalid (i32.eqz (i32.and (i32.ge_u (local.get $b2) (i32.const 128)) (i32.le_u (local.get $b2) (i32.const 191)))))",
  "            (br_if $invalid (i32.eqz (i32.and (i32.ge_u (local.get $b3) (i32.const 128)) (i32.le_u (local.get $b3) (i32.const 191)))))",
  "            (local.set $i (i32.add (local.get $i) (i32.const 4)))",
  "            (br $scan)))",
  "        (br $invalid)))",
  "    (i32.const 0))"
]

def emit (p : IR.Program) : Except String String := do
  IR.validateEntryPolicies p
  let logData ← logDataSection p
  let promiseData ← promiseDataSection p
  let lifecycleData ← lifecycleDataSection p
  if programUsesArena p && Memory.pageBytes < arenaBase p then
    throw "extract/unsupported: near static data leaves no room in the initial Wasm page"
  let mut lines : Array String := #[]
  lines := lines.push s!";; {Host.headerTag}"
  lines := lines.push s!";; digest={IR.digestHex p}"
  for note in Host.headerNotes do
    lines := lines.push note
  lines := lines.push "(module"
  lines := lines.push "  (import \"env\" \"input\" (func $pf_input (param i64)))"
  lines := lines.push
    "  (import \"env\" \"register_len\" (func $pf_register_len (param i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"read_register\" (func $pf_read_register (param i64 i64)))"
  lines := lines.push
    "  (import \"env\" \"storage_read\" (func $pf_storage_read (param i64 i64 i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"storage_write\" (func $pf_storage_write (param i64 i64 i64 i64 i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"storage_remove\" (func $pf_storage_remove (param i64 i64 i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"storage_has_key\" (func $pf_storage_has_key (param i64 i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"value_return\" (func $pf_value_return (param i64 i64)))"
  lines := lines.push
    "  (import \"env\" \"panic_utf8\" (func $pf_panic_utf8 (param i64 i64)))"
  if !(logMessages p).isEmpty || programHasBoundedLog p then
    lines := lines.push
      "  (import \"env\" \"log_utf8\" (func $pf_log_utf8 (param i64 i64)))"
  if !(promiseLiterals p).isEmpty then
    lines := lines.push
      "  (import \"env\" \"promise_batch_create\" (func $pf_promise_batch_create (param i64 i64) (result i64)))"
  if programCallsPromiseFunction p then
    lines := lines.push
      "  (import \"env\" \"promise_batch_action_function_call\" (func $pf_promise_batch_action_function_call (param i64 i64 i64 i64 i64 i64 i64)))"
  if programTransfersPromise p then
    lines := lines.push
      "  (import \"env\" \"promise_batch_action_transfer\" (func $pf_promise_batch_action_transfer (param i64 i64)))"
  if programChainsPromise p then
    lines := lines.push
      "  (import \"env\" \"promise_batch_then\" (func $pf_promise_batch_then (param i64 i64 i64) (result i64)))"
  if programJoinsPromise p then
    lines := lines.push
      "  (import \"env\" \"promise_and\" (func $pf_promise_and (param i64 i64) (result i64)))"
  if programReturnsPromise p then
    lines := lines.push
      "  (import \"env\" \"promise_return\" (func $pf_promise_return (param i64)))"
  if programUses .promiseResultsCount p then
    lines := lines.push
      "  (import \"env\" \"promise_results_count\" (func $pf_promise_results_count (result i64)))"
  if programReadsPromiseResult p then
    lines := lines.push
      "  (import \"env\" \"promise_result\" (func $pf_promise_result (param i64 i64) (result i64)))"
  if programUses .blockIndex p then
    lines := lines.push
      "  (import \"env\" \"block_index\" (func $pf_block_index (result i64)))"
  if programUses .blockTimestamp p then
    lines := lines.push
      "  (import \"env\" \"block_timestamp\" (func $pf_block_timestamp (result i64)))"
  if programHasPrivate p || predecessorKinds.any (programUses · p) then
    lines := lines.push
      "  (import \"env\" \"predecessor_account_id\" (func $pf_predecessor_account_id (param i64)))"
  if attachedDepositKinds.any (programUses · p) || !(nonPayableMethods p).isEmpty then
    lines := lines.push
      "  (import \"env\" \"attached_deposit\" (func $pf_attached_deposit (param i64)))"
  if accountBalanceKinds.any (programUses · p) then
    lines := lines.push
      "  (import \"env\" \"account_balance\" (func $pf_account_balance (param i64)))"
  if programHasPrivate p || currentAccountKinds.any (programUses · p) || programChainsPromise p then
    lines := lines.push
      "  (import \"env\" \"current_account_id\" (func $pf_current_account_id (param i64)))"
  lines := lines.push "  (memory (export \"memory\") 1)"
  lines := lines ++ dataSection p
  lines := lines ++ logData
  lines := lines ++ promiseData
  lines := lines ++ lifecycleData
  if programUsesArena p then
    lines := lines ++ arenaHelpers p
  if programHasFtEvent p then
    lines := lines ++ ftEventHelpers
  if programUsesUtf8Codec p then
    lines := lines ++ utf8Validator
  lines := lines.push ""
  lines := lines ++ (← renderFn p p.initializer true)
  lines := lines.push ""
  for method in p.entries do
    lines := lines ++ (← renderFn p method false)
    lines := lines.push ""
  lines := lines.push ")"
  return String.intercalate "\n" lines.toList ++ "\n"

end ProofForge.Wasm.Near.Emit
