import ProofForge.Extract.IR
import ProofForge.Core.Target
import ProofForge.Wasm.IR
import ProofForge.Wasm.Near.Ops
import ProofForge.Wasm.Near.Host
import ProofForge.Wasm.Near.Codec

/-!
# NEAR target IR（薄封装）

NEAR Protocol 的 registration 实例化与家族 IR 的窄门面：程序形状、v0 子集检查
和 canonical 拼写都在家族共享的 `ProofForge.Wasm.IR` 里；本文件只钉 NEAR 的
方言类型（`Near.Ops`）、digest 域（`near-raw-u64|`）和 ext canonical 标签。
外来 svm/evm 叶子经家族约定拒绝（错误前缀 `near`）。
-/

namespace ProofForge.Wasm.Near.IR

abbrev CFG := Core.CFG.Graph Ops.ValKind Ops.OpExt
abbrev Method := Wasm.IR.Method Ops.ValKind Ops.OpExt
abbrev Program := Wasm.IR.Program Ops.ValKind Ops.OpExt

/-- NEAR-generated wrapper capabilities. This is target metadata, never an executable source Op. -/
structure EntryPolicy where
  isPrivate : Bool := false
  payable : Bool := false
  migrateFrom : Option UInt64 := none
  deriving BEq, Repr, Inhabited

/-- One spelling for digesting and emitter validation. Empty preserves historical methods. -/
def EntryPolicy.canonical (policy : EntryPolicy) : String :=
  match policy.migrateFrom with
  | some digest =>
      let capability := match policy.isPrivate, policy.payable with
        | false, false => "migrate-from"
        | true, false => "private,migrate-from"
        | false, true => "payable,migrate-from"
        | true, true => "private,payable,migrate-from"
      s!"near.entry.v2:{capability}:{digest.toNat}"
  | none =>
      match policy.isPrivate, policy.payable with
      | false, false => ""
      | true, false => "near.entry.v1:private"
      | false, true => "near.entry.v1:payable"
      | true, true => "near.entry.v1:private,payable"

/-- Parse only canonical target-owned policy values; malformed manually-built IR fails closed. -/
def EntryPolicy.ofCanonical : String → Except String EntryPolicy
  | "" => pure {}
  | "near.entry.v1:private" => pure { isPrivate := true }
  | "near.entry.v1:payable" => pure { payable := true }
  | "near.entry.v1:private,payable" => pure { isPrivate := true, payable := true }
  | policy => do
      let parts := policy.splitOn ":"
      if parts.length == 3 && parts[0]! == "near.entry.v2" &&
          parts[1]! == "private,migrate-from" then
        let some digest := parts[2]!.toNat?
          | throw s!"extract/unsupported: malformed near entry policy {policy}"
        unless digest ≤ 18446744073709551615 do
          throw s!"extract/unsupported: malformed near entry policy {policy}"
        let parsed : EntryPolicy := {
          isPrivate := true
          migrateFrom := some (UInt64.ofNat digest)
        }
        unless parsed.canonical == policy do
          throw s!"extract/unsupported: malformed near entry policy {policy}"
        return parsed
      throw s!"extract/unsupported: malformed near entry policy {policy}"

private partial def valUsesSourceState (paramCount : Nat) : Wasm.IR.Val Ops.ValKind → Bool
  | .arg index => paramCount ≤ index
  | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => valUsesSourceState paramCount base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valUsesSourceState paramCount lhs || valUsesSourceState paramCount rhs
  | .indexGet base _ index _ _ =>
      valUsesSourceState paramCount base || valUsesSourceState paramCount index
  | .select _ lhs rhs thn els =>
      valUsesSourceState paramCount lhs || valUsesSourceState paramCount rhs ||
        valUsesSourceState paramCount thn || valUsesSourceState paramCount els
  | .ext _ operands => operands.any (valUsesSourceState paramCount)

private partial def opUsesSourceState (paramCount : Nat) : Wasm.IR.Op Ops.ValKind Ops.OpExt → Bool
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      valUsesSourceState paramCount value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      valUsesSourceState paramCount lhs || valUsesSourceState paramCount rhs
  | .ite _ lhs rhs thn els =>
      valUsesSourceState paramCount lhs || valUsesSourceState paramCount rhs ||
        thn.any (opUsesSourceState paramCount) || els.any (opUsesSourceState paramCount)
  | .forBody _ body => body.any (opUsesSourceState paramCount)
  | .indexSetLeaf _ index value _ _ | .indexSet _ index value _ _ =>
      valUsesSourceState paramCount index || valUsesSourceState paramCount value
  | .ext payload =>
      (Ops.cfgDialect.values payload).any (valUsesSourceState paramCount)
  | .joinLocal _ | .errorOverflow | .errorNamed _ => false

def entryPolicyOf (method : Method) : Except String EntryPolicy := do
  let policy ← EntryPolicy.ofCanonical method.entryPolicy
  if method.tupleArity.isSome && policy.payable then
    throw s!"extract/unsupported: {method.ixName} view cannot be payable"
  if policy.migrateFrom.isSome then
    unless method.kind == .increment do
      throw s!"extract/unsupported: {method.ixName} migration must be a mutating entry"
    unless policy.isPrivate && !policy.payable do
      throw s!"extract/unsupported: {method.ixName} migration must be private and non-payable"
    unless method.paramCount == 0 do
      throw s!"extract/unsupported: {method.ixName} migration cannot accept public parameters"
    if method.ops.any (opUsesSourceState method.paramCount) then
      throw s!"extract/unsupported: {method.ixName} migration must read old state through explicit storage keys"
  return policy

/-- ProofForge-owned persistent-state schema identity. Method logic and the program name are
deliberately absent, so upgrades remain compatible exactly while ordered slot name/width/ABI stays
stable. FNV-1a-64 is pinned by `Core.IR.fnv1a64`; this is an engineering mismatch detector, not a
collision-resistant commitment. -/
def stateSchemaCanonical (p : Program) : String :=
  let slots := p.slots.map fun slot =>
    s!"{slot.name.toUTF8.size}:{slot.name}:{slot.width}:{slot.abi.toUTF8.size}:{slot.abi}"
  s!"near-state-schema-v1|{p.slots.size}|" ++ String.intercalate "/" slots.toList

def stateSchemaDigest (p : Program) : UInt64 :=
  Core.IR.fnv1a64 (stateSchemaCanonical p)

def stateSchemaDigestHex (p : Program) : String :=
  Core.IR.u64Hex (stateSchemaDigest p)

def validateEntryPolicies (program : Program) : Except String Unit := do
  let _ ← entryPolicyOf program.initializer
  let mut migrations := 0
  for method in program.entries do
    let policy ← entryPolicyOf method
    if let some oldDigest := policy.migrateFrom then
      migrations := migrations + 1
      if oldDigest == stateSchemaDigest program then
        throw s!"extract/unsupported: {method.ixName} migration source schema equals current schema"
  unless migrations ≤ 1 do
    throw "extract/unsupported: near supports at most one migration entry"

private def projectValExt : Extract.IR.ValKind → Except String Ops.ValKind
  | .near kind =>
      match kind with
      | .reserved => throw "extract/unsupported: near rejects reserved value"
      | k => pure k
  | .svm _ => throw "extract/unsupported: near rejects svm value"
  | .evm _ => throw "extract/unsupported: near rejects evm value"
  | .xrpl _ => throw "extract/unsupported: near rejects xrpl value"

private def projectOpExt
    (_projectVal : Extract.IR.Val → Except String Ops.Val) :
    Extract.IR.OpExt Extract.IR.Val → Except String (Ops.OpExt Ops.Val)
  | .near payload =>
      match payload with
      | .logUtf8 message => pure (.logUtf8 message)
      | .logUtf8Bounded capacity message =>
          return .logUtf8Bounded capacity (← message.mapM _projectVal)
      | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
          return .promiseFunctionCallDetached receiver method argsCapacity
            (← arguments.mapM _projectVal) (← _projectVal depositLo)
            (← _projectVal depositHi) (← _projectVal gas)
      | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
          return .promiseFunctionCallReturned receiver method argsCapacity
            (← arguments.mapM _projectVal) (← _projectVal depositLo)
            (← _projectVal depositHi) (← _projectVal gas)
      | .promiseTransferDetached receiver amountLo amountHi =>
          return .promiseTransferDetached receiver
            (← _projectVal amountLo) (← _projectVal amountHi)
      | .promiseTransferReturned receiver amountLo amountHi =>
          return .promiseTransferReturned receiver
            (← _projectVal amountLo) (← _projectVal amountHi)
      | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
          childArgsCapacity callbackArgsCapacity childArguments callbackArguments
          childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
          return .promiseFunctionCallThenReturned receiver childMethod callbackMethod
            childArgsCapacity callbackArgsCapacity (← childArguments.mapM _projectVal)
            (← callbackArguments.mapM _projectVal) (← _projectVal childDepositLo)
            (← _projectVal childDepositHi) (← _projectVal childGas)
            (← _projectVal callbackDepositLo) (← _projectVal callbackDepositHi)
            (← _projectVal callbackGas)
      | .promiseFunctionCallAndThenReturned
          leftReceiver leftMethod rightReceiver rightMethod callbackMethod
          leftArgsCapacity rightArgsCapacity callbackArgsCapacity
          leftArguments rightArguments callbackArguments
          leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
          callbackDepositLo callbackDepositHi callbackGas =>
          return .promiseFunctionCallAndThenReturned
            leftReceiver leftMethod rightReceiver rightMethod callbackMethod
            leftArgsCapacity rightArgsCapacity callbackArgsCapacity
            (← leftArguments.mapM _projectVal) (← rightArguments.mapM _projectVal)
            (← callbackArguments.mapM _projectVal)
            (← _projectVal leftDepositLo) (← _projectVal leftDepositHi) (← _projectVal leftGas)
            (← _projectVal rightDepositLo) (← _projectVal rightDepositHi) (← _projectVal rightGas)
            (← _projectVal callbackDepositLo) (← _projectVal callbackDepositHi)
            (← _projectVal callbackGas)
      | .promiseResultRead capacity index =>
          return .promiseResultRead capacity (← _projectVal index)
      | .transientBuffer64Begin capacity => pure (.transientBuffer64Begin capacity)
      | .transientBuffer64Set capacity index value =>
          return .transientBuffer64Set capacity (← _projectVal index) (← _projectVal value)
      | .transientBuffer64Finish capacity => pure (.transientBuffer64Finish capacity)
      | .storageRead resultCapacity keyCapacity key =>
          return .storageRead resultCapacity keyCapacity (← key.mapM _projectVal)
      | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
          return .storageWrite resultCapacity keyCapacity valueCapacity
            (← key.mapM _projectVal) (← value.mapM _projectVal)
      | .storageRemove resultCapacity keyCapacity key =>
          return .storageRemove resultCapacity keyCapacity (← key.mapM _projectVal)
      | .storageHasKey resultCapacity keyCapacity key =>
          return .storageHasKey resultCapacity keyCapacity (← key.mapM _projectVal)
      | .reserved => throw "extract/unsupported: near rejects reserved effect"
  | .svm _ => throw "extract/unsupported: near rejects svm effect"
  | .evm _ => throw "extract/unsupported: near rejects evm effect"
  | .xrpl _ => throw "extract/unsupported: near rejects xrpl effect"

/-- Static registration of the extractor-to-NEAR projection. Foreign svm/evm leaves
fail closed. NEAR host reads project through. -/
def extractRegistration :
    Core.Target.Registration Extract.IR.ValKind Extract.IR.OpExt Ops.ValKind Ops.OpExt where
  name := "NEAR"
  projectValExt := projectValExt
  projectOpExt := projectOpExt
  projectionError := fun method reason =>
    if reason.startsWith "extract/unsupported: near rejects" then
      s!"{reason} in {method}"
    else reason
  valArity := Ops.ValKind.arity
  opWellFormed := Ops.Op.wellFormed
  cfgDialect := Ops.cfgDialect

def projectExtractedOps (ops : Array Extract.IR.Op) : Except String (Array Ops.Op) :=
  Core.Target.projectOps extractRegistration ops

def extValCanon : Ops.ValKind → String
  | .blockIndex => "nblk"
  | .blockTimestamp => "nts"
  | .predecessor => "npred"
  | .predecessorLen => "nplen"
  | .predecessorW1 => "np1" | .predecessorW2 => "np2"
  | .predecessorW3 => "np3" | .predecessorW4 => "np4"
  | .predecessorW5 => "np5" | .predecessorW6 => "np6" | .predecessorW7 => "np7"
  | .attachedDeposit => "ndep"
  | .attachedDepositW0 => "ndep0" | .attachedDepositW1 => "ndep1"
  | .accountBalance => "nbal"
  | .accountBalanceW0 => "nbal0" | .accountBalanceW1 => "nbal1"
  | .currentAccountId => "nself"
  | .currentAccountIdLen => "nslen"
  | .currentAccountIdW1 => "ns1" | .currentAccountIdW2 => "ns2"
  | .currentAccountIdW3 => "ns3" | .currentAccountIdW4 => "ns4"
  | .currentAccountIdW5 => "ns5" | .currentAccountIdW6 => "ns6"
  | .currentAccountIdW7 => "ns7"
  | .transientBuffer64Get capacity => s!"ntb64.get.{capacity}"
  | .storageResultStatus capacity => s!"nstore.status.{capacity}"
  | .storageResultLength capacity => s!"nstore.length.{capacity}"
  | .storageResultFits capacity => s!"nstore.fits.{capacity}"
  | .storageResultByte capacity => s!"nstore.byte.{capacity}"
  | .promiseResultsCount => "npromise.results.count"
  | .promiseResultStatus capacity => s!"npromise.result.status.{capacity}"
  | .promiseResultLength capacity => s!"npromise.result.length.{capacity}"
  | .promiseResultFits capacity => s!"npromise.result.fits.{capacity}"
  | .promiseResultByte capacity => s!"npromise.result.byte.{capacity}"
  | .promiseResultBorshUInt64D capacity => s!"npromise.result.borsh.u64d.{capacity}"
  | .reserved => "wext"

private def canonValues (values : Array (Wasm.IR.Val Ops.ValKind)) : String :=
  String.intercalate "," (values.toList.map (Wasm.IR.valCanon extValCanon))

def extOpCanon : Ops.OpExt (Wasm.IR.Val Ops.ValKind) → String
  | .logUtf8 message => s!"nlog:{message.toUTF8.size}:{message}"
  | .logUtf8Bounded capacity message =>
      s!"nlog.bounded.{capacity}({canonValues message})"
  | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
      s!"npromise.detached:{receiver.toUTF8.size}:{receiver}:{method.toUTF8.size}:{method}." ++
        s!"{argsCapacity}({canonValues arguments};" ++
        s!"{Wasm.IR.valCanon extValCanon depositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon depositHi},{Wasm.IR.valCanon extValCanon gas})"
  | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
      s!"npromise.returned:{receiver.toUTF8.size}:{receiver}:{method.toUTF8.size}:{method}." ++
        s!"{argsCapacity}({canonValues arguments};" ++
        s!"{Wasm.IR.valCanon extValCanon depositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon depositHi},{Wasm.IR.valCanon extValCanon gas})"
  | .promiseTransferDetached receiver amountLo amountHi =>
      s!"npromise.transfer.detached:{receiver.toUTF8.size}:{receiver}(" ++
        s!"{Wasm.IR.valCanon extValCanon amountLo}," ++
        s!"{Wasm.IR.valCanon extValCanon amountHi})"
  | .promiseTransferReturned receiver amountLo amountHi =>
      s!"npromise.transfer.returned:{receiver.toUTF8.size}:{receiver}(" ++
        s!"{Wasm.IR.valCanon extValCanon amountLo}," ++
        s!"{Wasm.IR.valCanon extValCanon amountHi})"
  | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
      childArgsCapacity callbackArgsCapacity childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      s!"npromise.then.returned:{receiver.toUTF8.size}:{receiver}:" ++
        s!"{childMethod.toUTF8.size}:{childMethod}:{callbackMethod.toUTF8.size}:{callbackMethod}." ++
        s!"{childArgsCapacity}.{callbackArgsCapacity}(" ++
        s!"{canonValues childArguments};{canonValues callbackArguments};" ++
        s!"{Wasm.IR.valCanon extValCanon childDepositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon childDepositHi}," ++
        s!"{Wasm.IR.valCanon extValCanon childGas};" ++
        s!"{Wasm.IR.valCanon extValCanon callbackDepositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon callbackDepositHi}," ++
        s!"{Wasm.IR.valCanon extValCanon callbackGas})"
  | .promiseFunctionCallAndThenReturned
      leftReceiver leftMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      s!"npromise.and.then.returned:{leftReceiver.toUTF8.size}:{leftReceiver}:" ++
        s!"{leftMethod.toUTF8.size}:{leftMethod}:{rightReceiver.toUTF8.size}:{rightReceiver}:" ++
        s!"{rightMethod.toUTF8.size}:{rightMethod}:{callbackMethod.toUTF8.size}:{callbackMethod}." ++
        s!"{leftArgsCapacity}.{rightArgsCapacity}.{callbackArgsCapacity}(" ++
        s!"{canonValues leftArguments};{canonValues rightArguments};" ++
        s!"{canonValues callbackArguments};" ++
        s!"{Wasm.IR.valCanon extValCanon leftDepositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon leftDepositHi}," ++
        s!"{Wasm.IR.valCanon extValCanon leftGas};" ++
        s!"{Wasm.IR.valCanon extValCanon rightDepositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon rightDepositHi}," ++
        s!"{Wasm.IR.valCanon extValCanon rightGas};" ++
        s!"{Wasm.IR.valCanon extValCanon callbackDepositLo}," ++
        s!"{Wasm.IR.valCanon extValCanon callbackDepositHi}," ++
        s!"{Wasm.IR.valCanon extValCanon callbackGas})"
  | .promiseResultRead capacity index =>
      s!"npromise.result.read.{capacity}({Wasm.IR.valCanon extValCanon index})"
  | .transientBuffer64Begin capacity => s!"ntb64.begin.{capacity}"
  | .transientBuffer64Set capacity index value =>
      s!"ntb64.set.{capacity}({Wasm.IR.valCanon extValCanon index},{Wasm.IR.valCanon extValCanon value})"
  | .transientBuffer64Finish capacity => s!"ntb64.finish.{capacity}"
  | .storageRead resultCapacity keyCapacity key =>
      s!"nstore.read.{resultCapacity}.{keyCapacity}({canonValues key})"
  | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
      s!"nstore.write.{resultCapacity}.{keyCapacity}.{valueCapacity}" ++
        s!"({canonValues key};{canonValues value})"
  | .storageRemove resultCapacity keyCapacity key =>
      s!"nstore.remove.{resultCapacity}.{keyCapacity}({canonValues key})"
  | .storageHasKey resultCapacity keyCapacity key =>
      s!"nstore.has.{resultCapacity}.{keyCapacity}({canonValues key})"
  | .reserved => "wext"

def slotNames (p : Program) : Array String :=
  Wasm.IR.slotNames p

private def schemaIsScalar : Core.Codec.Schema → Bool
  | .scalar _ => true
  | _ => false

private partial def simplifyLiteralSelect : Ops.Val → Ops.Val
  | .select .eq (.lit lhs) (.lit rhs) thn els =>
      simplifyLiteralSelect (if lhs == rhs then thn else els)
  | value => value

private def rewritePayload
    (rewriteValue : Ops.Val → Except String Ops.Val) :
    Ops.OpExt Ops.Val → Except String (Ops.OpExt Ops.Val)
  | .logUtf8 message => pure (.logUtf8 message)
  | .logUtf8Bounded capacity message => do
      let rewritten ← message.mapM rewriteValue
      return .logUtf8Bounded capacity (rewritten.map simplifyLiteralSelect)
  | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
      return .promiseFunctionCallDetached receiver method argsCapacity
        (← arguments.mapM rewriteValue) (← rewriteValue depositLo)
        (← rewriteValue depositHi) (← rewriteValue gas)
  | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
      return .promiseFunctionCallReturned receiver method argsCapacity
        (← arguments.mapM rewriteValue) (← rewriteValue depositLo)
        (← rewriteValue depositHi) (← rewriteValue gas)
  | .promiseTransferDetached receiver amountLo amountHi =>
      return .promiseTransferDetached receiver
        (← rewriteValue amountLo) (← rewriteValue amountHi)
  | .promiseTransferReturned receiver amountLo amountHi =>
      return .promiseTransferReturned receiver
        (← rewriteValue amountLo) (← rewriteValue amountHi)
  | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
      childArgsCapacity callbackArgsCapacity childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      return .promiseFunctionCallThenReturned receiver childMethod callbackMethod
        childArgsCapacity callbackArgsCapacity (← childArguments.mapM rewriteValue)
        (← callbackArguments.mapM rewriteValue) (← rewriteValue childDepositLo)
        (← rewriteValue childDepositHi) (← rewriteValue childGas)
        (← rewriteValue callbackDepositLo) (← rewriteValue callbackDepositHi)
        (← rewriteValue callbackGas)
  | .promiseFunctionCallAndThenReturned
      leftReceiver leftMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      return .promiseFunctionCallAndThenReturned
        leftReceiver leftMethod rightReceiver rightMethod callbackMethod
        leftArgsCapacity rightArgsCapacity callbackArgsCapacity
        (← leftArguments.mapM rewriteValue) (← rightArguments.mapM rewriteValue)
        (← callbackArguments.mapM rewriteValue)
        (← rewriteValue leftDepositLo) (← rewriteValue leftDepositHi)
        (← rewriteValue leftGas) (← rewriteValue rightDepositLo)
        (← rewriteValue rightDepositHi) (← rewriteValue rightGas)
        (← rewriteValue callbackDepositLo) (← rewriteValue callbackDepositHi)
        (← rewriteValue callbackGas)
  | .promiseResultRead capacity index =>
      return .promiseResultRead capacity (← rewriteValue index)
  | .transientBuffer64Begin capacity => pure (.transientBuffer64Begin capacity)
  | .transientBuffer64Set capacity index value =>
      return .transientBuffer64Set capacity (← rewriteValue index) (← rewriteValue value)
  | .transientBuffer64Finish capacity => pure (.transientBuffer64Finish capacity)
  | .storageRead resultCapacity keyCapacity key =>
      return .storageRead resultCapacity keyCapacity (← key.mapM rewriteValue)
  | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
      return .storageWrite resultCapacity keyCapacity valueCapacity
        (← key.mapM rewriteValue) (← value.mapM rewriteValue)
  | .storageRemove resultCapacity keyCapacity key =>
      return .storageRemove resultCapacity keyCapacity (← key.mapM rewriteValue)
  | .storageHasKey resultCapacity keyCapacity key =>
      return .storageHasKey resultCapacity keyCapacity (← key.mapM rewriteValue)
  | .reserved => pure .reserved

private partial def rewriteInputRoot (method : Core.IR.Method Ops.ValKind Ops.OpExt)
    (plan : Codec.BorshInputPlan) : Ops.Val → Except String (Option Ops.Val)
  | .field (.arg 0) "length" => pure (some (.arg 0))
  | .field (.arg 0) name =>
      match plan.valueIndex? name with
      | some index => pure (some (.arg (1 + index)))
      | none => throw s!"near/codec: unsupported bounded input projection {name}"
  | .indexGet (.arg 0) name index length elementOffset => do
      unless name == "values" && (length == 0 || length == plan.capacity) && elementOffset == 0 do
        throw "near/codec: bounded index projection does not match its input plan"
      let rewrittenIndex ←
        Core.Target.rewriteValRoots (rewriteInputRoot method plan) index
      let mut selected : Ops.Val := .lit 0
      for i in [0:plan.capacity] do
        selected := .select .eq rewrittenIndex (.lit (UInt64.ofNat i))
          (.arg (1 + i)) selected
      pure (some selected)
  | .arg index =>
      if index == 0 then
        throw "near/codec: bounded input requires a scalar length or byte projection"
      else if method.kind != .init && index == method.paramCount then
        pure (some (.arg plan.localCount))
      else
        pure none
  | _ => pure none

private structure BoundInput where
  ixName : String
  schema : Core.Codec.Schema
  plan : Codec.BorshInputPlan

private def bindInput (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String (Core.IR.Method Ops.ValKind Ops.OpExt × Option BoundInput) := do
  if method.paramSchemas.isEmpty || method.paramSchemas.all schemaIsScalar then
    return (method, none)
  unless method.paramCount == 1 && method.paramSchemas.size == 1 do
    throw s!"near/codec: {method.ixName} supports exactly one bounded bytes/string parameter"
  let schema := method.paramSchemas[0]!
  let plan ← Codec.inputPlan schema
  let ops ← Core.Target.rewriteOpsValues (rewriteInputRoot method plan) rewritePayload method.ops
  let localCount := plan.localCount
  let scalarSchemas := Array.replicate localCount (.scalar .uint64)
  return ({ method with
    paramCount := localCount
    paramWidths := Array.replicate localCount 8
    paramTypes := Array.replicate localCount .uint64
    paramSchemas := scalarSchemas
    ops }, some { ixName := method.ixName, schema, plan })

private structure BoundOutput where
  ixName : String
  schema : Core.Codec.Schema
  plan : Codec.BorshOutputPlan

private structure BoundEntry where
  ixName : String
  policy : EntryPolicy

private def bindEntry (method : Extract.IR.Method) : Except String BoundEntry := do
  let privateAnnotations := method.annotations.filter (· == "near.private.v1")
  let payableAnnotations := method.annotations.filter (· == "near.payable.v1")
  let migrationAnnotations := method.annotations.filter (·.startsWith "near.migrate.v1:")
  unless privateAnnotations.size + payableAnnotations.size + migrationAnnotations.size ==
      method.annotations.size do
    throw s!"extract/unsupported: near cannot consume foreign target annotations on {method.ixName}"
  unless privateAnnotations.size ≤ 1 do
    throw s!"extract/unsupported: {method.ixName} has duplicate near private annotations"
  unless payableAnnotations.size ≤ 1 do
    throw s!"extract/unsupported: {method.ixName} has duplicate near payable annotations"
  unless migrationAnnotations.size ≤ 1 do
    throw s!"extract/unsupported: {method.ixName} has duplicate near migration annotations"
  let migrateFrom ← match migrationAnnotations[0]? with
    | none => pure none
    | some annotation => do
        let parts := annotation.splitOn ":"
        unless parts.length == 2 && parts[0]! == "near.migrate.v1" do
          throw s!"extract/unsupported: malformed near migration annotation on {method.ixName}"
        let some digest := parts[1]!.toNat?
          | throw s!"extract/unsupported: malformed near migration annotation on {method.ixName}"
        unless digest ≤ 18446744073709551615 do
          throw s!"extract/unsupported: malformed near migration annotation on {method.ixName}"
        pure (some (UInt64.ofNat digest))
  let policy : EntryPolicy := {
    isPrivate := !privateAnnotations.isEmpty
    payable := !payableAnnotations.isEmpty
    migrateFrom
  }
  if method.kind == .get && policy.payable then
    throw s!"extract/unsupported: {method.ixName} view cannot be payable"
  if policy.migrateFrom.isSome then
    unless method.kind == .increment do
      throw s!"extract/unsupported: {method.ixName} migration must be a mutating entry"
    unless policy.isPrivate do
      throw s!"extract/unsupported: {method.ixName} migration requires pf_near_private"
    if policy.payable then
      throw s!"extract/unsupported: {method.ixName} migration cannot be payable"
  return { ixName := method.ixName, policy }

private def bindOutput (method : Core.IR.Method Ops.ValKind Ops.OpExt) :
    Except String (Core.IR.Method Ops.ValKind Ops.OpExt × Option BoundOutput) := do
  match method.retSchema with
  | .boundedArray .. | .boundedBytes _ | .boundedString _ =>
      unless method.kind == .get do
        throw s!"near/codec: {method.ixName} bounded output currently requires a view"
      let schema := method.retSchema
      let plan ← Codec.outputPlan schema
      unless method.retCount == plan.sourceValueCount do
        throw s!"near/codec: {method.ixName} output frame does not match its Borsh plan"
      return ({ method with
        retWidths := #[8]
        retTypes := #[.uint64]
        retSchema := .scalar .uint64
        retCount := 1 }, some { ixName := method.ixName, schema, plan })
  | _ => return (method, none)

private def decorateMethod (entries : Array BoundEntry) (inputs : Array BoundInput)
    (outputs : Array BoundOutput) (method : Method) : Method :=
  let method := match entries.find? (·.ixName == method.ixName) with
  | some entry => { method with entryPolicy := entry.policy.canonical }
  | none => method
  let method := match inputs.find? (·.ixName == method.ixName) with
  | some input => { method with
      inputSchema := some input.schema
      inputPolicy := input.plan.canonical }
  | none => method
  match outputs.find? (·.ixName == method.ixName) with
  | some output => { method with
      outputSchema := some output.schema
      outputPolicy := output.plan.canonical
      tupleArity := some output.plan.sourceValueCount }
  | none => method

def fromExtracted (src : Extract.IR.Program) : Except String Program := do
  let entries ← src.methods.mapM bindEntry
  let projected ← Core.Target.projectProgram extractRegistration src
  let mut methods := #[]
  let mut inputs := #[]
  let mut outputs := #[]
  for method in projected.methods do
    let (inputBound, input?) ← bindInput method
    let (bound, output?) ← bindOutput inputBound
    methods := methods.push bound
    if let some input := input? then inputs := inputs.push input
    if let some output := output? then outputs := outputs.push output
  let program ← Wasm.IR.fromProjected { projected with methods }
  let program := {
    program with
    initializer := decorateMethod entries inputs outputs program.initializer
    entries := program.entries.map (decorateMethod entries inputs outputs)
  }
  validateEntryPolicies program
  return program

/-- Digest domain is chain-owned (`near-raw-u64|`), deliberately different from the
SVM / EVM / XRPL domains. -/
def digestHex (p : Program) : String :=
  Wasm.IR.digestHex Host.digestDomain extValCanon extOpCanon p

end ProofForge.Wasm.Near.IR
