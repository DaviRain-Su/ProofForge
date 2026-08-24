import ProofForge.Extract.IR
import ProofForge.Extract.LegacyIR

namespace ProofForge.Extract.IR

private def cmpOfLegacy : ProofForge.Ops.Cmp → Cmp
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

private def cmpToLegacy : Cmp → ProofForge.Ops.Cmp
  | .eq => .eq
  | .ne => .ne
  | .lt => .lt
  | .le => .le
  | .gt => .gt
  | .ge => .ge

/-- Lossless upgrade for callers that still own a legacy closed-union value. -/
partial def ofLegacyVal : ProofForge.Ops.Val → Val
  | .arg i => .arg i
  | .local i => .local i
  | .field base name => .field (ofLegacyVal base) name
  | .lit n => .lit n
  | .clockSlot => .ext (.svm .clockSlot) #[]
  | .clockEpoch => .ext (.svm .clockEpoch) #[]
  | .unixTime => .ext (.svm .unixTime) #[]
  | .slotsPerEpoch => .ext (.svm .slotsPerEpoch) #[]
  | .signerKey0 => .ext (.svm .signerKey0) #[]
  | .accLamports0 => .ext (.svm .accLamports0) #[]
  | .accOwner0 => .ext (.svm .accOwner0) #[]
  | .accDataLen0 => .ext (.svm .accDataLen0) #[]
  | .accN => .ext (.svm .accN) #[]
  | .isSigner0 => .ext (.svm .isSigner0) #[]
  | .isWritable0 => .ext (.svm .isWritable0) #[]
  | .isExecutable0 => .ext (.svm .isExecutable0) #[]
  | .accLamports1 => .ext (.svm .accLamports1) #[]
  | .accOwner1 => .ext (.svm .accOwner1) #[]
  | .accDataLen1 => .ext (.svm .accDataLen1) #[]
  | .isSigner1 => .ext (.svm .isSigner1) #[]
  | .isWritable1 => .ext (.svm .isWritable1) #[]
  | .isExecutable1 => .ext (.svm .isExecutable1) #[]
  | .findPda seed => .ext (.svm (.findPda seed)) #[]
  | .checkPda seed bump => .ext (.svm (.checkPda seed)) #[ofLegacyVal bump]
  | .rentExemption dataLen => .ext (.svm (.rentExemption dataLen)) #[]
  | .cpiReturn => .ext (.svm .cpiReturn) #[]
  | .sha256Lit seed => .ext (.svm (.sha256Lit seed)) #[]
  | .keccak256Lit seed => .ext (.svm (.keccak256Lit seed)) #[]
  | .accKeyWord acc word => .ext (.svm (.accKeyWord acc word)) #[]
  | .accOwnerWord acc word => .ext (.svm (.accOwnerWord acc word)) #[]
  | .accLamportsN acc => .ext (.svm (.accLamportsN acc)) #[]
  | .accDataLenN acc => .ext (.svm (.accDataLenN acc)) #[]
  | .isSignerN acc => .ext (.svm (.isSignerN acc)) #[]
  | .isWritableN acc => .ext (.svm (.isWritableN acc)) #[]
  | .isExecutableN acc => .ext (.svm (.isExecutableN acc)) #[]
  | .signerKeyN acc => .ext (.svm (.signerKeyN acc)) #[]
  | .ownerIsSelf acc => .ext (.svm (.ownerIsSelf acc)) #[]
  | .evmCaller => .ext (.evm .caller) #[]
  | .evmBlockNumber => .ext (.evm .blockNumber) #[]
  | .evmTimestamp => .ext (.evm .timestamp) #[]
  | .evmChainId => .ext (.evm .chainId) #[]
  | .evmSelf => .ext (.evm .self) #[]
  | .evmCallValue => .ext (.evm .callValue) #[]
  | .evmSelfBalance => .ext (.evm .selfBalance) #[]
  | .evmCallerW0 => .ext (.evm .callerW0) #[]
  | .evmCallerW1 => .ext (.evm .callerW1) #[]
  | .evmCallerW2 => .ext (.evm .callerW2) #[]
  | .evmSelfW0 => .ext (.evm .selfW0) #[]
  | .evmSelfW1 => .ext (.evm .selfW1) #[]
  | .evmSelfW2 => .ext (.evm .selfW2) #[]
  | .bitAnd lhs rhs => .bitAnd (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .bitOr lhs rhs => .bitOr (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .bitXor lhs rhs => .bitXor (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .bitNot value => .bitNot (ofLegacyVal value)
  | .shiftL lhs rhs => .shiftL (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .shiftR lhs rhs => .shiftR (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .indexGet base name idx len elemOff =>
      .indexGet (ofLegacyVal base) name (ofLegacyVal idx) len elemOff
  | .loopIx => .loopIx
  | .select cmp lhs rhs thn els =>
      .select (cmpOfLegacy cmp) (ofLegacyVal lhs) (ofLegacyVal rhs)
        (ofLegacyVal thn) (ofLegacyVal els)
  | .addU64 lhs rhs => .addU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .subU64 lhs rhs => .subU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .mulU64 lhs rhs => .mulU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .divU64 lhs rhs => .divU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .modU64 lhs rhs => .modU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .mapGetU64 base key => .ext (.evm .mapGetU64) #[ofLegacyVal base, ofLegacyVal key]
  | .mapGetAddr base w0 w1 w2 =>
      .ext (.evm .mapGetAddr)
        #[ofLegacyVal base, ofLegacyVal w0, ofLegacyVal w1, ofLegacyVal w2]
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      .ext (.evm .mapGetPair)
        #[ofLegacyVal base, ofLegacyVal o0, ofLegacyVal o1, ofLegacyVal o2,
          ofLegacyVal s0, ofLegacyVal s1, ofLegacyVal s2]

private def malformedValue : Except String α :=
  .error "extract/ir: malformed target value operands"

partial def toLegacyVal : Val → Except String ProofForge.Ops.Val
  | .arg i => pure (.arg i)
  | .local i => pure (.local i)
  | .field base name => return .field (← toLegacyVal base) name
  | .lit n => pure (.lit n)
  | .bitAnd lhs rhs => return .bitAnd (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .bitOr lhs rhs => return .bitOr (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .bitXor lhs rhs => return .bitXor (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .bitNot value => return .bitNot (← toLegacyVal value)
  | .shiftL lhs rhs => return .shiftL (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .shiftR lhs rhs => return .shiftR (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .indexGet base name idx len elemOff =>
      return .indexGet (← toLegacyVal base) name (← toLegacyVal idx) len elemOff
  | .loopIx => pure .loopIx
  | .select cmp lhs rhs thn els =>
      return .select (cmpToLegacy cmp) (← toLegacyVal lhs) (← toLegacyVal rhs)
        (← toLegacyVal thn) (← toLegacyVal els)
  | .addU64 lhs rhs => return .addU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .subU64 lhs rhs => return .subU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .mulU64 lhs rhs => return .mulU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .divU64 lhs rhs => return .divU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .modU64 lhs rhs => return .modU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .ext (.svm .clockSlot) #[] => pure .clockSlot
  | .ext (.svm .clockEpoch) #[] => pure .clockEpoch
  | .ext (.svm .unixTime) #[] => pure .unixTime
  | .ext (.svm .slotsPerEpoch) #[] => pure .slotsPerEpoch
  | .ext (.svm .signerKey0) #[] => pure .signerKey0
  | .ext (.svm .accLamports0) #[] => pure .accLamports0
  | .ext (.svm .accOwner0) #[] => pure .accOwner0
  | .ext (.svm .accDataLen0) #[] => pure .accDataLen0
  | .ext (.svm .accN) #[] => pure .accN
  | .ext (.svm .isSigner0) #[] => pure .isSigner0
  | .ext (.svm .isWritable0) #[] => pure .isWritable0
  | .ext (.svm .isExecutable0) #[] => pure .isExecutable0
  | .ext (.svm .accLamports1) #[] => pure .accLamports1
  | .ext (.svm .accOwner1) #[] => pure .accOwner1
  | .ext (.svm .accDataLen1) #[] => pure .accDataLen1
  | .ext (.svm .isSigner1) #[] => pure .isSigner1
  | .ext (.svm .isWritable1) #[] => pure .isWritable1
  | .ext (.svm .isExecutable1) #[] => pure .isExecutable1
  | .ext (.svm (.findPda seed)) #[] => pure (.findPda seed)
  | .ext (.svm (.checkPda seed)) #[bump] => return .checkPda seed (← toLegacyVal bump)
  | .ext (.svm (.rentExemption dataLen)) #[] => pure (.rentExemption dataLen)
  | .ext (.svm .cpiReturn) #[] => pure .cpiReturn
  | .ext (.svm (.sha256Lit seed)) #[] => pure (.sha256Lit seed)
  | .ext (.svm (.keccak256Lit seed)) #[] => pure (.keccak256Lit seed)
  | .ext (.svm (.accKeyWord acc word)) #[] => pure (.accKeyWord acc word)
  | .ext (.svm (.accOwnerWord acc word)) #[] => pure (.accOwnerWord acc word)
  | .ext (.svm (.accLamportsN acc)) #[] => pure (.accLamportsN acc)
  | .ext (.svm (.accDataLenN acc)) #[] => pure (.accDataLenN acc)
  | .ext (.svm (.isSignerN acc)) #[] => pure (.isSignerN acc)
  | .ext (.svm (.isWritableN acc)) #[] => pure (.isWritableN acc)
  | .ext (.svm (.isExecutableN acc)) #[] => pure (.isExecutableN acc)
  | .ext (.svm (.signerKeyN acc)) #[] => pure (.signerKeyN acc)
  | .ext (.svm (.ownerIsSelf acc)) #[] => pure (.ownerIsSelf acc)
  | .ext (.svm (.findPdaSeeds _)) #[] =>
      throw "extract/unsupported: legacy adapter cannot represent multi-seed PDA discovery"
  | .ext (.svm (.checkPdaSeeds _ _)) #[] =>
      throw "extract/unsupported: legacy adapter cannot represent multi-seed PDA checks"
  | .ext (.evm .caller) #[] => pure .evmCaller
  | .ext (.evm .blockNumber) #[] => pure .evmBlockNumber
  | .ext (.evm .timestamp) #[] => pure .evmTimestamp
  | .ext (.evm .chainId) #[] => pure .evmChainId
  | .ext (.evm .self) #[] => pure .evmSelf
  | .ext (.evm .callValue) #[] => pure .evmCallValue
  | .ext (.evm .selfBalance) #[] => pure .evmSelfBalance
  | .ext (.evm .callerW0) #[] => pure .evmCallerW0
  | .ext (.evm .callerW1) #[] => pure .evmCallerW1
  | .ext (.evm .callerW2) #[] => pure .evmCallerW2
  | .ext (.evm .selfW0) #[] => pure .evmSelfW0
  | .ext (.evm .selfW1) #[] => pure .evmSelfW1
  | .ext (.evm .selfW2) #[] => pure .evmSelfW2
  | .ext (.evm .mapGetU64) #[base, key] =>
      return .mapGetU64 (← toLegacyVal base) (← toLegacyVal key)
  | .ext (.evm .mapGetAddr) #[base, w0, w1, w2] =>
      return .mapGetAddr (← toLegacyVal base) (← toLegacyVal w0)
        (← toLegacyVal w1) (← toLegacyVal w2)
  | .ext (.evm .mapGetPair) #[base, o0, o1, o2, s0, s1, s2] =>
      return .mapGetPair (← toLegacyVal base) (← toLegacyVal o0) (← toLegacyVal o1)
        (← toLegacyVal o2) (← toLegacyVal s0) (← toLegacyVal s1) (← toLegacyVal s2)
  | .ext _ _ => malformedValue

private def metaOfLegacy (entry : ProofForge.Ops.CpiMeta) : Svm.Ops.CpiMeta :=
  { acc := entry.acc, signer := entry.signer, writable := entry.writable }

private def metaToLegacy (entry : Svm.Ops.CpiMeta) : ProofForge.Ops.CpiMeta :=
  { acc := entry.acc, signer := entry.signer, writable := entry.writable }

private def wordOfLegacy : ProofForge.Ops.CpiWord → Svm.Ops.CpiWord Val
  | .u8le n => .u8le (.lit n)
  | .u32le n => .u32le (.lit n)
  | .u64le value => .u64le (ofLegacyVal value)
  | .ascii value => .ascii value
  | .programId => .programId
  | .accKey i => .accKey i

private def wordToLegacy : Svm.Ops.CpiWord Val → Except String ProofForge.Ops.CpiWord
  | .u8le (.lit n) => pure (.u8le n)
  | .u8le _ => throw "extract/legacy: dynamic u8 CPI word"
  | .u16le _ => throw "extract/legacy: u16 CPI word"
  | .u32le (.lit n) => pure (.u32le n)
  | .u32le _ => throw "extract/legacy: dynamic u32 CPI word"
  | .u64le value => return .u64le (← toLegacyVal value)
  | .ascii value => pure (.ascii value)
  | .programId => pure .programId
  | .accKey i => pure (.accKey i)

partial def ofLegacyOp : ProofForge.Ops.Op → Op
  | .letLocal i value => .letLocal i (ofLegacyVal value)
  | .joinLocal i => .joinLocal i
  | .setLocal i value => .setLocal i (ofLegacyVal value)
  | .checkedAddU64 lhs rhs => .checkedAddU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .checkedSubU64 lhs rhs => .checkedSubU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .checkedMulU64 lhs rhs => .checkedMulU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .checkedDivU64 lhs rhs => .checkedDivU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .checkedModU64 lhs rhs => .checkedModU64 (ofLegacyVal lhs) (ofLegacyVal rhs)
  | .ite cmp lhs rhs thn els =>
      .ite (cmpOfLegacy cmp) (ofLegacyVal lhs) (ofLegacyVal rhs)
        (thn.map ofLegacyOp) (els.map ofLegacyOp)
  | .invoke programIx metas data seed bump =>
      .ext (.svm (.invoke programIx (metas.map metaOfLegacy) (data.map wordOfLegacy)
        (match seed with | some value => #[.ascii value] | none => #[])
        (bump.map ofLegacyVal)))
  | .evmDeposit amount => .ext (.evm (.deposit (ofLegacyVal amount)))
  | .evmSendEth w0 w1 w2 amount =>
      .ext (.evm (.sendEth (ofLegacyVal w0) (ofLegacyVal w1)
        (ofLegacyVal w2) (ofLegacyVal amount)))
  | .evmLog name amount => .ext (.evm (.log name (ofLegacyVal amount)))
  | .forAccum n addend resultLocal => .forAccum n (ofLegacyVal addend) resultLocal
  | .forBody n body => .forBody n (body.map ofLegacyOp)
  | .indexSet name idx value len elemOff =>
      .indexSet name (ofLegacyVal idx) (ofLegacyVal value) len elemOff
  | .mapGetU64 base key => .ext (.evm (.mapGetU64 (ofLegacyVal base) (ofLegacyVal key)))
  | .mapSetU64 base key value =>
      .ext (.evm (.mapSetU64 (ofLegacyVal base) (ofLegacyVal key) (ofLegacyVal value)))
  | .mapGetAddr base w0 w1 w2 =>
      .ext (.evm (.mapGetAddr (ofLegacyVal base) (ofLegacyVal w0)
        (ofLegacyVal w1) (ofLegacyVal w2)))
  | .mapSetAddr base w0 w1 w2 value =>
      .ext (.evm (.mapSetAddr (ofLegacyVal base) (ofLegacyVal w0)
        (ofLegacyVal w1) (ofLegacyVal w2) (ofLegacyVal value)))
  | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
      .ext (.evm (.mapGetPair (ofLegacyVal base) (ofLegacyVal o0) (ofLegacyVal o1)
        (ofLegacyVal o2) (ofLegacyVal s0) (ofLegacyVal s1) (ofLegacyVal s2)))
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      .ext (.evm (.mapSetPair (ofLegacyVal base) (ofLegacyVal o0) (ofLegacyVal o1)
        (ofLegacyVal o2) (ofLegacyVal s0) (ofLegacyVal s1) (ofLegacyVal s2)
        (ofLegacyVal value)))
  | .evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      .ext (.evm (.tokenTransfer (ofLegacyVal tw0) (ofLegacyVal tw1) (ofLegacyVal tw2)
        (ofLegacyVal dw0) (ofLegacyVal dw1) (ofLegacyVal dw2) (ofLegacyVal amount)))
  | .evmTokenBalanceOfSelf tw0 tw1 tw2 =>
      .ext (.evm (.tokenBalanceOfSelf (ofLegacyVal tw0) (ofLegacyVal tw1) (ofLegacyVal tw2)))
  | .storeField name value => .storeField name (ofLegacyVal value)
  | .okState value => .okState (ofLegacyVal value)
  | .errorOverflow => .errorOverflow
  | .errorNamed name => .errorNamed name
  | .returnU64 value => .returnU64 (ofLegacyVal value)
  | .returnState value => .returnState (ofLegacyVal value)

def ofLegacyOps (ops : Array ProofForge.Ops.Op) : Array Op := ops.map ofLegacyOp

partial def toLegacyOp : Op → Except String ProofForge.Ops.Op
  | .letLocal i value => return .letLocal i (← toLegacyVal value)
  | .joinLocal i => pure (.joinLocal i)
  | .setLocal i value => return .setLocal i (← toLegacyVal value)
  | .checkedAddU64 lhs rhs => return .checkedAddU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .checkedSubU64 lhs rhs => return .checkedSubU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .checkedMulU64 lhs rhs => return .checkedMulU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .checkedDivU64 lhs rhs => return .checkedDivU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .checkedModU64 lhs rhs => return .checkedModU64 (← toLegacyVal lhs) (← toLegacyVal rhs)
  | .ite cmp lhs rhs thn els =>
      return .ite (cmpToLegacy cmp) (← toLegacyVal lhs) (← toLegacyVal rhs)
        (← thn.mapM toLegacyOp) (← els.mapM toLegacyOp)
  | .forAccum n addend resultLocal =>
      return .forAccum n (← toLegacyVal addend) resultLocal
  | .forBody n body => return .forBody n (← body.mapM toLegacyOp)
  | .indexSetLeaf name _ _ _ leaf =>
      throw s!"extract/ir: unresolved vector leaf {name}.{leaf}"
  | .indexSet name idx value len elemOff =>
      return .indexSet name (← toLegacyVal idx) (← toLegacyVal value) len elemOff
  | .storeField name value => return .storeField name (← toLegacyVal value)
  | .okState value => return .okState (← toLegacyVal value)
  | .errorOverflow => pure .errorOverflow
  | .errorNamed name => pure (.errorNamed name)
  | .returnU64 value => return .returnU64 (← toLegacyVal value)
  | .returnState value => return .returnState (← toLegacyVal value)
  | .ext (.svm (.invoke programIx metas data seeds bump)) => do
      let seed ←
        match seeds.toList with
        | [] => pure none
        | [.ascii value] => pure (some value)
        | _ => throw "extract/unsupported: legacy adapter cannot represent multi-seed CPI"
      return .invoke programIx (metas.map metaToLegacy) (← data.mapM wordToLegacy)
        seed (← bump.mapM toLegacyVal)
  | .ext (.evm (.deposit amount)) => return .evmDeposit (← toLegacyVal amount)
  | .ext (.evm (.sendEth w0 w1 w2 amount)) =>
      return .evmSendEth (← toLegacyVal w0) (← toLegacyVal w1)
        (← toLegacyVal w2) (← toLegacyVal amount)
  | .ext (.evm (.log name amount)) => return .evmLog name (← toLegacyVal amount)
  | .ext (.evm (.mapGetU64 base key)) =>
      return .mapGetU64 (← toLegacyVal base) (← toLegacyVal key)
  | .ext (.evm (.mapSetU64 base key value)) =>
      return .mapSetU64 (← toLegacyVal base) (← toLegacyVal key) (← toLegacyVal value)
  | .ext (.evm (.mapGetAddr base w0 w1 w2)) =>
      return .mapGetAddr (← toLegacyVal base) (← toLegacyVal w0)
        (← toLegacyVal w1) (← toLegacyVal w2)
  | .ext (.evm (.mapSetAddr base w0 w1 w2 value)) =>
      return .mapSetAddr (← toLegacyVal base) (← toLegacyVal w0)
        (← toLegacyVal w1) (← toLegacyVal w2) (← toLegacyVal value)
  | .ext (.evm (.mapGetPair base o0 o1 o2 s0 s1 s2)) =>
      return .mapGetPair (← toLegacyVal base) (← toLegacyVal o0) (← toLegacyVal o1)
        (← toLegacyVal o2) (← toLegacyVal s0) (← toLegacyVal s1) (← toLegacyVal s2)
  | .ext (.evm (.mapSetPair base o0 o1 o2 s0 s1 s2 value)) =>
      return .mapSetPair (← toLegacyVal base) (← toLegacyVal o0) (← toLegacyVal o1)
        (← toLegacyVal o2) (← toLegacyVal s0) (← toLegacyVal s1) (← toLegacyVal s2)
        (← toLegacyVal value)
  | .ext (.evm (.tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount)) =>
      return .evmTokenTransfer (← toLegacyVal tw0) (← toLegacyVal tw1) (← toLegacyVal tw2)
        (← toLegacyVal dw0) (← toLegacyVal dw1) (← toLegacyVal dw2)
        (← toLegacyVal amount)
  | .ext (.evm (.tokenBalanceOfSelf tw0 tw1 tw2)) =>
      return .evmTokenBalanceOfSelf (← toLegacyVal tw0) (← toLegacyVal tw1)
        (← toLegacyVal tw2)

def toLegacyOps (ops : Array Op) : Except String (Array ProofForge.Ops.Op) :=
  ops.mapM toLegacyOp

private def slotOfLegacy (slot : Legacy.Slot) : Core.IR.Slot :=
  { name := slot.name, width := slot.width, abi := slot.abi }

private def slotToLegacy (slot : Core.IR.Slot) : Legacy.Slot :=
  { name := slot.name, width := slot.width, abi := slot.abi }

private def methodOfLegacy (schema : Core.Schema) (method : Legacy.Method) :
    Except String Method := do
  let ops := ofLegacyOps method.ops
  unless ops.all Op.wellFormed do
    throw s!"extract/ir: malformed target extension in {method.ixName}"
  let evaluation ←
    if schema.isEmpty then pure {}
    else Core.evaluate schema ops
  return {
    kind := method.kind
    name := method.name
    ixName := method.ixName
    paramCount := method.paramCount
    paramWidths := method.paramWidths
    retCount := method.retCount
    sketch := method.sketch
    ops
    evaluation
  }

/-- Upgrade the complete compatibility program at the extractor boundary. -/
def ofLegacyProgram (program : Legacy.Program) : Except String Program := do
  return {
    name := program.name
    slots := program.slots.map slotOfLegacy
    schema := program.schema
    methods := ← program.methods.mapM (methodOfLegacy program.schema)
  }

private def methodToLegacy (schema : Core.Schema) (method : Method) :
    Except String Legacy.Method := do
  let ops ← toLegacyOps method.ops
  let evaluation ←
    if schema.isEmpty then pure {}
    else Legacy.evaluate schema ops
  return {
    kind := method.kind
    name := method.name
    ixName := method.ixName
    paramCount := method.paramCount
    paramWidths := method.paramWidths
    retCount := method.retCount
    sketch := method.sketch
    ops
    evaluation
  }

/-- Downgrade only at a compatibility boundary; malformed target operands fail explicitly. -/
def toLegacyProgram (program : Program) : Except String Legacy.Program := do
  return {
    name := program.name
    slots := program.slots.map slotToLegacy
    schema := program.schema
    methods := ← program.methods.mapM (methodToLegacy program.schema)
  }

end ProofForge.Extract.IR
