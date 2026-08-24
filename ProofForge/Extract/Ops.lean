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
@[match_pattern] def Val.accKeyWord (acc word : Nat) : Val := svmLeaf (.accKeyWord acc word)
@[match_pattern] def Val.accOwnerWord (acc word : Nat) : Val :=
  svmLeaf (.accOwnerWord acc word)
@[match_pattern] def Val.accLamportsN (acc : Nat) : Val := svmLeaf (.accLamportsN acc)
@[match_pattern] def Val.accDataLenN (acc : Nat) : Val := svmLeaf (.accDataLenN acc)
@[match_pattern] def Val.isSignerN (acc : Nat) : Val := svmLeaf (.isSignerN acc)
@[match_pattern] def Val.isWritableN (acc : Nat) : Val := svmLeaf (.isWritableN acc)
@[match_pattern] def Val.isExecutableN (acc : Nat) : Val := svmLeaf (.isExecutableN acc)
@[match_pattern] def Val.signerKeyN (acc : Nat) : Val := svmLeaf (.signerKeyN acc)
@[match_pattern] def Val.ownerIsSelf (acc : Nat) : Val := svmLeaf (.ownerIsSelf acc)
@[match_pattern] def Val.findPdaSeeds (seeds : Array PdaSeed) : Val :=
  svmLeaf (.findPdaSeeds seeds)

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
@[match_pattern] def Val.evmSelfW0 : Val := evmLeaf .selfW0
@[match_pattern] def Val.evmSelfW1 : Val := evmLeaf .selfW1
@[match_pattern] def Val.evmSelfW2 : Val := evmLeaf .selfW2
@[match_pattern] def Val.mapGetU64 (base key : Val) : Val :=
  .ext (.evm .mapGetU64) #[base, key]
@[match_pattern] def Val.mapGetAddr (base w0 w1 w2 : Val) : Val :=
  .ext (.evm .mapGetAddr) #[base, w0, w1, w2]
@[match_pattern] def Val.mapGetPair (base o0 o1 o2 s0 s1 s2 : Val) : Val :=
  .ext (.evm .mapGetPair) #[base, o0, o1, o2, s0, s1, s2]

@[match_pattern] def Op.invoke (programIx : Nat) (metas : Array CpiMeta)
    (data : Array CpiWord) (seeds : Array PdaSeed := #[]) (bump : Option Val := none) : Op :=
  .ext (.svm (.invoke programIx metas data seeds bump))
@[match_pattern] def Op.evmDeposit (amount : Val) : Op :=
  .ext (.evm (.deposit amount))
@[match_pattern] def Op.evmSendEth (w0 w1 w2 amount : Val) : Op :=
  .ext (.evm (.sendEth w0 w1 w2 amount))
@[match_pattern] def Op.evmLog (name : String) (amount : Val) : Op :=
  .ext (.evm (.log name amount))
@[match_pattern] def Op.mapGetU64 (base key : Val) : Op :=
  .ext (.evm (.mapGetU64 base key))
@[match_pattern] def Op.mapSetU64 (base key value : Val) : Op :=
  .ext (.evm (.mapSetU64 base key value))
@[match_pattern] def Op.mapGetAddr (base w0 w1 w2 : Val) : Op :=
  .ext (.evm (.mapGetAddr base w0 w1 w2))
@[match_pattern] def Op.mapSetAddr (base w0 w1 w2 value : Val) : Op :=
  .ext (.evm (.mapSetAddr base w0 w1 w2 value))
@[match_pattern] def Op.mapGetPair (base o0 o1 o2 s0 s1 s2 : Val) : Op :=
  .ext (.evm (.mapGetPair base o0 o1 o2 s0 s1 s2))
@[match_pattern] def Op.mapSetPair (base o0 o1 o2 s0 s1 s2 value : Val) : Op :=
  .ext (.evm (.mapSetPair base o0 o1 o2 s0 s1 s2 value))
@[match_pattern] def Op.evmTokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : Val) : Op :=
  .ext (.evm (.tokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount))
@[match_pattern] def Op.evmTokenBalanceOfSelf (tw0 tw1 tw2 : Val) : Op :=
  .ext (.evm (.tokenBalanceOfSelf tw0 tw1 tw2))

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
      data.any (fun | .u64le value => predicate value | _ => false) || bump.any predicate
  | .evmDeposit value | .evmLog _ value => predicate value
  | .evmSendEth w0 w1 w2 amount => #[w0, w1, w2, amount].any predicate
  | .mapGetU64 base key => #[base, key].any predicate
  | .mapSetU64 base key value => #[base, key, value].any predicate
  | .mapGetAddr base w0 w1 w2 => #[base, w0, w1, w2].any predicate
  | .mapSetAddr base w0 w1 w2 value => #[base, w0, w1, w2, value].any predicate
  | .mapGetPair base o0 o1 o2 s0 s1 s2 => #[base, o0, o1, o2, s0, s1, s2].any predicate
  | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
      #[base, o0, o1, o2, s0, s1, s2, value].any predicate
  | .evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, amount].any predicate
  | .evmTokenBalanceOfSelf tw0 tw1 tw2 => #[tw0, tw1, tw2].any predicate
  | .joinLocal _ | .forBody _ _ | .errorOverflow | .errorNamed _ => false

private partial def isEvmContext : Val → Bool
  | .ext (.evm kind) operands =>
      (match kind with
       | .mapGetU64 | .mapGetAddr | .mapGetPair => false
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

def hasLangOp (ops : Array Op) : Bool :=
  walk ops fun op =>
    match op with
    | .forAccum .. | .forBody .. | .indexSetLeaf .. | .indexSet .. | .errorNamed _ => true
    | _ => opValuesAny (fun value => isLangLeaf value || isBitVal value || hasSelectVal value) op

def hasEvmEffect (ops : Array Op) : Bool :=
  hasEvmLeaf ops || walk ops fun
    | .evmDeposit .. | .evmSendEth .. | .evmLog ..
    | .mapGetU64 .. | .mapSetU64 .. | .mapGetAddr .. | .mapSetAddr ..
    | .mapGetPair .. | .mapSetPair ..
    | .evmTokenTransfer .. | .evmTokenBalanceOfSelf .. => true
    | _ => false

end ProofForge.Extract.Ops
