import ProofForge.Extract.IR

namespace ProofForge.Extract.Ops

/-- Decoder-facing names over the extensible extraction dialect; no second Ops tree is created. -/
abbrev Cmp := IR.Cmp
abbrev Val := IR.Val
abbrev Op := IR.Op
abbrev CpiMeta := Svm.Ops.CpiMeta
abbrev CpiWord := Svm.Ops.CpiWord Val
abbrev PdaSeed := Svm.Ops.PdaSeed

private def svmLeaf (kind : Svm.Ops.ValKind) : Val :=
  .ext (.svm kind) #[]

private def evmLeaf (kind : Evm.Ops.ValKind) : Val :=
  .ext (.evm kind) #[]

private def xrplLeaf (kind : Wasm.Xrpl.Ops.ValKind) : Val :=
  .ext (.xrpl kind) #[]

@[match_pattern] def Val.clockSlot : Val := svmLeaf .clockSlot
@[match_pattern] def Val.clockEpoch : Val := svmLeaf .clockEpoch
@[match_pattern] def Val.unixTime : Val := svmLeaf .unixTime
@[match_pattern] def Val.slotsPerEpoch : Val := svmLeaf .slotsPerEpoch
@[match_pattern] def Val.signerKey0 : Val := svmLeaf .signerKey0
@[match_pattern] def Val.accLamports0 : Val := svmLeaf .accLamports0
@[match_pattern] def Val.accOwner0 : Val := svmLeaf .accOwner0
@[match_pattern] def Val.accDataLen0 : Val := svmLeaf .accDataLen0
@[match_pattern] def Val.accN : Val := svmLeaf .accN
@[match_pattern] def Val.isSigner0 : Val := svmLeaf .isSigner0
@[match_pattern] def Val.isWritable0 : Val := svmLeaf .isWritable0
@[match_pattern] def Val.isExecutable0 : Val := svmLeaf .isExecutable0
@[match_pattern] def Val.accLamports1 : Val := svmLeaf .accLamports1
@[match_pattern] def Val.accOwner1 : Val := svmLeaf .accOwner1
@[match_pattern] def Val.accDataLen1 : Val := svmLeaf .accDataLen1
@[match_pattern] def Val.isSigner1 : Val := svmLeaf .isSigner1
@[match_pattern] def Val.isWritable1 : Val := svmLeaf .isWritable1
@[match_pattern] def Val.isExecutable1 : Val := svmLeaf .isExecutable1
@[match_pattern] def Val.findPda (seed : String) : Val := svmLeaf (.findPda seed)
@[match_pattern] def Val.checkPda (seed : String) (bump : Val) : Val :=
  .ext (.svm (.checkPda seed)) #[bump]
@[match_pattern] def Val.rentExemption (dataLen : UInt64) : Val :=
  svmLeaf (.rentExemption dataLen)
@[match_pattern] def Val.cpiReturn : Val := svmLeaf .cpiReturn
@[match_pattern] def Val.sha256Lit (seed : String) : Val := svmLeaf (.sha256Lit seed)
@[match_pattern] def Val.keccak256Lit (seed : String) : Val := svmLeaf (.keccak256Lit seed)
@[match_pattern] def Val.byteSwap64 (word : Val) : Val :=
  .ext (.svm .byteSwap64) #[word]
@[match_pattern] def Val.accKeyWord (acc word : Nat) : Val := svmLeaf (.accKeyWord acc word)
@[match_pattern] def Val.accOwnerWord (acc word : Nat) : Val :=
  svmLeaf (.accOwnerWord acc word)
@[match_pattern] def Val.accDataWord (acc word : Nat) : Val :=
  svmLeaf (.accDataWord acc word)
@[match_pattern] def Val.accDataWordAt
    (acc baseWord strideWords capacity : Nat) (index : Val) : Val :=
  .ext (.svm (.component (.accountStorage
    (.readWordZeroBased acc baseWord strideWords capacity)))) #[index]
@[match_pattern] def Val.accDataWordAtOneBased
    (acc baseWord strideWords capacity : Nat) (index : Val) : Val :=
  .ext (.svm (.component (.accountStorage
    (.readWordOneBased acc baseWord strideWords capacity)))) #[index]
@[match_pattern] def Val.accDataRbTreeKey4Find
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : Val) : Val :=
  .ext (.svm (.component (.accountStorage (.key4FindOneBased
    acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity))))
      #[key0, key1, key2, key3]
@[match_pattern] def Val.accDataRbTreeOrderFind
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (price sequence : Val) : Val :=
  .ext (.svm (.component (.accountStorage (.fifoFindOneBased
    acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid))))
      #[price, sequence]
@[match_pattern] def Val.accDataRbTreeOrderCursor
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (hasCursor price sequence : Val) : Val :=
  .ext (.svm (.component (.accountStorage (.fifoCursorOneBased
    acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid))))
      #[hasCursor, price, sequence]
@[match_pattern] def Val.accDataParentPathValid
    (acc linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat)
    (index root bumpIndex : Val) : Val :=
  .ext (.svm (.component (.accountStorage (.parentPathValidOneBased
    acc linksBaseWord parentBaseWord strideWords capacity maxDepth)))) #[index, root, bumpIndex]
@[match_pattern] def Val.accDataRbTreeValid
    (acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (root size bumpIndex freeListHead : Val) : Val :=
  .ext (.svm (.component (.accountStorage (.fifoRbTreeValidOneBased
    acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid))))
      #[root, size, bumpIndex, freeListHead]
@[match_pattern] def Val.accDataRbTreeKey4Valid
    (acc linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (root size bumpIndex freeListHead : Val) : Val :=
  .ext (.svm (.component (.accountStorage (.key4RbTreeValidOneBased
    acc linksBaseWord parentBaseWord keyBaseWord strideWords capacity))))
      #[root, size, bumpIndex, freeListHead]
@[match_pattern] def Val.fifoCancelResult (query : Svm.FifoCancel.Query) : Val :=
  .ext (.svm (.component (.fifoCancel query))) #[]
@[match_pattern] def Val.accLamportsN (acc : Nat) : Val := svmLeaf (.accLamportsN acc)
@[match_pattern] def Val.accDataLenN (acc : Nat) : Val := svmLeaf (.accDataLenN acc)
@[match_pattern] def Val.isSignerN (acc : Nat) : Val := svmLeaf (.isSignerN acc)
@[match_pattern] def Val.isWritableN (acc : Nat) : Val := svmLeaf (.isWritableN acc)
@[match_pattern] def Val.isExecutableN (acc : Nat) : Val := svmLeaf (.isExecutableN acc)
@[match_pattern] def Val.signerKeyN (acc : Nat) : Val := svmLeaf (.signerKeyN acc)
@[match_pattern] def Val.ownerIsSelf (acc : Nat) : Val := svmLeaf (.ownerIsSelf acc)
@[match_pattern] def Val.findPdaSeeds (seeds : Array PdaSeed) : Val :=
  svmLeaf (.findPdaSeeds seeds)
@[match_pattern] def Val.checkPdaSeeds (account : Nat) (seeds : Array PdaSeed) : Val :=
  svmLeaf (.checkPdaSeeds account seeds)

@[match_pattern] def Val.evmCaller : Val := evmLeaf .caller
@[match_pattern] def Val.evmBlockNumber : Val := evmLeaf .blockNumber
@[match_pattern] def Val.evmTimestamp : Val := evmLeaf .timestamp
@[match_pattern] def Val.evmChainId : Val := evmLeaf .chainId
@[match_pattern] def Val.evmSelf : Val := evmLeaf .self
@[match_pattern] def Val.evmCallValue : Val := evmLeaf .callValue
@[match_pattern] def Val.evmSelfBalance : Val := evmLeaf .selfBalance
@[match_pattern] def Val.evmCallerW0 : Val := evmLeaf .callerW0
@[match_pattern] def Val.evmCallerW1 : Val := evmLeaf .callerW1
@[match_pattern] def Val.evmCallerW2 : Val := evmLeaf .callerW2
@[match_pattern] def Val.xrplCallerW0 : Val := xrplLeaf .callerW0
@[match_pattern] def Val.xrplCallerW1 : Val := xrplLeaf .callerW1
@[match_pattern] def Val.xrplCallerW2 : Val := xrplLeaf .callerW2
@[match_pattern] def Val.xrplSelfW0 : Val := xrplLeaf .selfW0
@[match_pattern] def Val.xrplSelfW1 : Val := xrplLeaf .selfW1
@[match_pattern] def Val.xrplSelfW2 : Val := xrplLeaf .selfW2
@[match_pattern] def Val.xrplLedgerSqn : Val := xrplLeaf .ledgerSqn
@[match_pattern] def Val.xrplParentTime : Val := xrplLeaf .parentTime
@[match_pattern] def Val.xrplParentHashW0 : Val := xrplLeaf .parentHashW0
@[match_pattern] def Val.xrplBaseFee : Val := xrplLeaf .baseFee
@[match_pattern] def Val.xrplSha512HalfLit (seed : String) : Val :=
  xrplLeaf (.sha512HalfLit seed)
@[match_pattern] def Val.xrplCallerBalanceDrops : Val := xrplLeaf .callerBalanceDrops
@[match_pattern] def Val.xrplCallerSequence : Val := xrplLeaf .callerSequence
@[match_pattern] def Val.xrplCallerFlags : Val := xrplLeaf .callerFlags
@[match_pattern] def Val.xrplCallerOwnerCount : Val := xrplLeaf .callerOwnerCount
@[match_pattern] def Val.xrplTxSequence : Val := xrplLeaf .txSequence
@[match_pattern] def Val.xrplTxFeeDrops : Val := xrplLeaf .txFeeDrops
@[match_pattern] def Val.xrplAccountLitW0 (hex : String) : Val := xrplLeaf (.accountLitW0 hex)
@[match_pattern] def Val.xrplAccountLitW1 (hex : String) : Val := xrplLeaf (.accountLitW1 hex)
@[match_pattern] def Val.xrplAccountLitW2 (hex : String) : Val := xrplLeaf (.accountLitW2 hex)
@[match_pattern] def Val.evmSelfW0 : Val := evmLeaf .selfW0
@[match_pattern] def Val.evmSelfW1 : Val := evmLeaf .selfW1
@[match_pattern] def Val.evmSelfW2 : Val := evmLeaf .selfW2
@[match_pattern] def Val.evmImmU64 : Val := evmLeaf .immU64
@[match_pattern] def Val.evmImmU64b : Val := evmLeaf .immU64b
@[match_pattern] def Val.evmImmW0 : Val := evmLeaf .immW0
@[match_pattern] def Val.evmImmW1 : Val := evmLeaf .immW1
@[match_pattern] def Val.evmImmW2 : Val := evmLeaf .immW2
@[match_pattern] def Val.evmImmX0 : Val := evmLeaf .immX0
@[match_pattern] def Val.evmImmX1 : Val := evmLeaf .immX1
@[match_pattern] def Val.evmImmX2 : Val := evmLeaf .immX2
@[match_pattern] def Val.mapGetU64 (base key : Val) : Val :=
  .ext (.evm (.component (.hashedMap .getU64))) #[base, key]
@[match_pattern] def Val.mapGetAddr (base w0 w1 w2 : Val) : Val :=
  .ext (.evm (.component (.hashedMap .getAddr))) #[base, w0, w1, w2]
@[match_pattern] def Val.mapGetPair (base o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.evm (.component (.hashedMap .getPair))) #[base, o0, o1, o2, s0, s1, s2]

@[match_pattern] def Op.invoke (programIx : Nat) (metas : Array CpiMeta)
    (data : Array CpiWord) (seeds : Array PdaSeed := #[]) (bump : Option Val := none) : Op :=
  .ext (.svm (.invoke programIx metas data seeds bump))
@[match_pattern] def Op.component (call : Svm.Component.Call Val) : Op :=
  .ext (.svm (.component call))
@[match_pattern] def Op.accDataWordSetAt
    (acc baseWord strideWords capacity : Nat) (index value : Val) : Op :=
  .ext (.svm (.component (.accountStorage
    (.writeWordZeroBased acc baseWord strideWords capacity index value))))
@[match_pattern] def Op.accDataWordSetAtOneBased
    (acc baseWord strideWords capacity : Nat) (index value : Val) : Op :=
  .ext (.svm (.component (.accountStorage
    (.writeWordOneBased acc baseWord strideWords capacity index value))))
@[match_pattern] def Op.accDataRbTreeKey4Insert
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : Val) : Op :=
  .ext (.svm (.component (.accountStorage (.rbMapInsertKey4OneBased acc rootWord linksBaseWord
    parentBaseWord keyBaseWord strideWords capacity key0 key1 key2 key3))))
@[match_pattern] def Op.accDataRbTreeTraderDeposit
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 quoteLots baseLots : Val) : Op :=
  .ext (.svm (.component (.accountStorage (.rbMapCheckedAddKey4OneBased acc rootWord linksBaseWord
    parentBaseWord keyBaseWord strideWords capacity key0 key1 key2 key3 quoteLots baseLots))))
@[match_pattern] def Op.accDataRbTreeKey4Remove
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : Val) : Op :=
  .ext (.svm (.component (.accountStorage (.rbMapRemoveKey4OneBased acc rootWord linksBaseWord
    parentBaseWord keyBaseWord strideWords capacity key0 key1 key2 key3))))
@[match_pattern] def Op.accDataRbTreeOrderInsert
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool)
    (price sequence traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp : Val) : Op :=
  .ext (.svm (.component (.accountStorage (.rbMapInsertFifoOneBased acc rootWord linksBaseWord
    parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid price sequence
    traderIndex numBaseLots lastValidSlot lastValidUnixTimestamp))))
@[match_pattern] def Op.accDataRbTreeOrderRemove
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool) (price sequence : Val) : Op :=
  .ext (.svm (.component (.accountStorage (.rbMapRemoveFifoOneBased acc rootWord linksBaseWord
    parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid price sequence))))
@[match_pattern] def Op.accDataRbTreeOrderSetWordOrRemove
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord valueBaseWord strideWords
      capacity : Nat) (bid : Bool) (price sequence index value : Val) : Op :=
  .ext (.svm (.component (.accountStorage (.rbMapSetWordOrRemoveFifoOneBased acc rootWord
    linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord valueBaseWord strideWords capacity bid
    price sequence index value))))
@[match_pattern] def Op.evmDeposit (amount : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.deposit amount))))
@[match_pattern] def Op.evmDeposit256 (a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.deposit256 a0 a1 a2 a3))))
@[match_pattern] def Op.evmSendEth (w0 w1 w2 amount : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.sendEth w0 w1 w2 amount))))
@[match_pattern] def Op.evmSendEth256 (w0 w1 w2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.sendEth256 w0 w1 w2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmLog (name : String) (amount : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.log name amount))))
@[match_pattern] def Op.evmLogTransfer256
    (f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmLogApproval256
    (o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmRevertInsufficient
    (h0 h1 h2 h3 w0 w1 w2 w3 : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3))))
@[match_pattern] def Op.evmRevertUnauthorized (w0 w1 w2 : Val) : Op :=
  .ext (.evm (.component (.nativeFx (.revertUnauthorized w0 w1 w2))))
@[match_pattern] def Op.evmRevertZeroAddress : Op :=
  .ext (.evm (.component (.nativeFx .revertZeroAddress)))
@[match_pattern] def Op.evmRevertPaused : Op :=
  .ext (.evm (.component (.nativeFx .revertPaused)))
@[match_pattern] def Op.evmRevertCapExceeded : Op :=
  .ext (.evm (.component (.nativeFx .revertCapExceeded)))
@[match_pattern] def Op.evmReceive : Op :=
  .ext (.evm (.component (.nativeFx .receive)))
@[match_pattern] def Op.evmStoreStaticU64 (field : String) (value : Val) : Op :=
  .ext (.evm (.component (.staticStorage (.storeU64 field value))))
@[match_pattern] def Op.mapGetU64 (base key : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.getU64 base key))))
@[match_pattern] def Op.mapSetU64 (base key value : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.setU64 base key value))))
@[match_pattern] def Op.mapGetAddr (base w0 w1 w2 : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.getAddr base w0 w1 w2))))
@[match_pattern] def Op.mapSetAddr (base w0 w1 w2 value : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.setAddr base w0 w1 w2 value))))
@[match_pattern] def Op.mapGetPair (base o0 o1 o2 s0 s1 s2 : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.getPair base o0 o1 o2 s0 s1 s2))))
@[match_pattern] def Op.mapSetPair (base o0 o1 o2 s0 s1 s2 value : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.setPair base o0 o1 o2 s0 s1 s2 value))))
@[match_pattern] def Op.mapSetAddr256 (base w0 w1 w2 v0 v1 v2 v3 : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.setAddr256 base w0 w1 w2 v0 v1 v2 v3))))
@[match_pattern] def Op.mapSetPair256 (base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 : Val) : Op :=
  .ext (.evm (.component (.hashedMap (.setPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3))))
@[match_pattern] def Op.evmTokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : Val) : Op :=
  .ext (.evm (.component (.closedCall (.transfer tw0 tw1 tw2 dw0 dw1 dw2 amount))))
@[match_pattern] def Op.evmTokenTransfer256
    (tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.transfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmTokenApprove256
    (tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.approve256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmTokenTransferFrom256
    (tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.transferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmTokenBalanceOfSelf (tw0 tw1 tw2 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.balanceOfSelf tw0 tw1 tw2))))
@[match_pattern] def Op.evmWethDeposit256
    (tw0 tw1 tw2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmWethWithdraw256
    (tw0 tw1 tw2 a0 a1 a2 a3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3))))
@[match_pattern] def Op.evmSwapExact2
    (rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3))))
@[match_pattern] def Op.evmSwapExact3
    (rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.swapExact3 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3))))
@[match_pattern] def Op.evmPermit
    (o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.permit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3))))
@[match_pattern] def Op.evmTokenPermit
    (t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : Val) : Op :=
  .ext (.evm (.component (.closedCall (.tokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3))))
@[match_pattern] def Op.evmComponent (call : Evm.Component.Call Val) : Op :=
  .ext (.evm (.component call))

private partial def walk (ops : Array Op) (predicate : Op → Bool) : Bool :=
  ops.any fun op =>
    predicate op ||
      match op with
      | .ite _ _ _ thn els => walk thn predicate || walk els predicate
      | .forBody _ body => walk body predicate
      | _ => false

def hasCheckedArith (ops : Array Op) : Bool :=
  walk ops fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. => true
    | _ => false

def hasForAccum (ops : Array Op) : Bool :=
  walk ops fun | .forAccum .. => true | _ => false

def hasIndexSet (ops : Array Op) : Bool :=
  walk ops fun | .indexSetLeaf .. | .indexSet .. => true | _ => false

def hasStoreField (ops : Array Op) : Bool :=
  walk ops fun | .storeField .. => true | _ => false

def hasInvoke (ops : Array Op) : Bool :=
  walk ops fun | .invoke .. => true | _ => false

partial def isLangLeaf : Val → Bool
  | .local _ | .loopIx | .select .. | .bitAnd .. | .bitOr .. | .bitXor ..
  | .bitNot .. | .shiftL .. | .shiftR .. | .indexGet .. => true
  | .field base _ => isLangLeaf base
  | .ext _ operands => operands.any isLangLeaf
  | _ => false

private partial def hasSelectVal : Val → Bool
  | .select .. => true
  | .field base _ | .bitNot base => hasSelectVal base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      hasSelectVal lhs || hasSelectVal rhs
  | .indexGet base _ index _ _ => hasSelectVal base || hasSelectVal index
  | .ext _ operands => operands.any hasSelectVal
  | _ => false

private partial def isBitVal : Val → Bool
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. => true
  | .field base _ => isBitVal base
  | .select _ lhs rhs thn els =>
      isBitVal lhs || isBitVal rhs || isBitVal thn || isBitVal els
  | .ext _ operands => operands.any isBitVal
  | _ => false

private def opValuesAny (predicate : Val → Bool) : Op → Bool
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      predicate value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
  | .indexSetLeaf _ lhs rhs _ _ | .indexSet _ lhs rhs _ _ => predicate lhs || predicate rhs
  | .invoke _ _ data _ bump =>
      data.any (fun word => word.value?.any predicate) || bump.any predicate
  | .ext (.svm (.component call)) => call.anyValue predicate
  | .ext (.xrpl _) => false
  | .evmComponent call => call.anyValue predicate
  | .joinLocal _ | .forBody _ _ | .errorOverflow | .errorNamed _ => false

private partial def isEvmContext : Val → Bool
  | .ext (.evm kind) operands =>
      (match kind with
       | .callValue256 _ | .selfBalance256 _ | .gasLeft256 _ | .baseFee256 _
       | .prevRandao256 _ | .gasLimit256 _ | .domainSep256 _ | .component _ => false
       | _ => true) || operands.any isEvmContext
  | .field base _ | .bitNot base => isEvmContext base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      isEvmContext lhs || isEvmContext rhs
  | .indexGet base _ index _ _ => isEvmContext base || isEvmContext index
  | .select _ lhs rhs thn els =>
      isEvmContext lhs || isEvmContext rhs || isEvmContext thn || isEvmContext els
  | .ext _ operands => operands.any isEvmContext
  | _ => false

def hasEvmLeaf (ops : Array Op) : Bool :=
  walk ops (opValuesAny isEvmContext)

private partial def isXrplLeaf : Val → Bool
  | .ext (.xrpl _) _ => true
  | .field base _ | .bitNot base => isXrplLeaf base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      isXrplLeaf lhs || isXrplLeaf rhs
  | .select _ lhs rhs thn els =>
      isXrplLeaf lhs || isXrplLeaf rhs || isXrplLeaf thn || isXrplLeaf els
  | .ext _ operands => operands.any isXrplLeaf
  | _ => false

def hasXrplLeaf (ops : Array Op) : Bool :=
  walk ops (opValuesAny isXrplLeaf)

def hasLangOp (ops : Array Op) : Bool :=
  walk ops fun op =>
    match op with
    | .forAccum .. | .forBody .. | .indexSetLeaf .. | .indexSet .. | .errorNamed _ => true
    | _ => opValuesAny (fun value => isLangLeaf value || isBitVal value || hasSelectVal value) op

def hasEvmEffect (ops : Array Op) : Bool :=
  hasEvmLeaf ops || walk ops fun
    | .evmComponent .. => true
    | _ => false

end ProofForge.Extract.Ops
