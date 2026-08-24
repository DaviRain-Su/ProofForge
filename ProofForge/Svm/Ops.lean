import ProofForge.Core.Ops

namespace ProofForge.Svm.Ops

/-- Agave's currently enforced transaction account-lock limit. -/
def maxTxAccountLocks : Nat := 64

def accInRange (acc : Nat) : Bool :=
  acc < maxTxAccountLocks

/-- CPI indices address the external-account region after the state account at physical index 0. -/
def cpiAccInRange (acc : Nat) : Bool :=
  acc + 1 < maxTxAccountLocks

/-- SVM-only source value intrinsics. Recursive operands live in `Core.Ops.Val.ext`. -/
inductive ValKind where
  | clockSlot
  | clockEpoch
  | unixTime
  | slotsPerEpoch
  | signerKey0
  | accLamports0
  | accOwner0
  | accDataLen0
  | accN
  | isSigner0
  | isWritable0
  | isExecutable0
  | accLamports1
  | accOwner1
  | accDataLen1
  | isSigner1
  | isWritable1
  | isExecutable1
  | findPda (seed : String)
  | checkPda (seed : String)
  | rentExemption (dataLen : UInt64)
  | cpiReturn
  | sha256Lit (seed : String)
  | keccak256Lit (seed : String)
  | accKeyWord (acc word : Nat)
  | accOwnerWord (acc word : Nat)
  | accLamportsN (acc : Nat)
  | accDataLenN (acc : Nat)
  | isSignerN (acc : Nat)
  | isWritableN (acc : Nat)
  | isExecutableN (acc : Nat)
  | signerKeyN (acc : Nat)
  | ownerIsSelf (acc : Nat)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .checkPda _ => 1
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- Account index relative to the CPI account region; physical account 0 is reserved for state. -/
structure CpiMeta where
  acc : Nat
  signer : Bool := false
  writable : Bool := false
  deriving BEq, Repr, Inhabited

inductive CpiWord (V : Type) where
  | u8le (n : UInt64)
  | u32le (n : UInt64)
  | u64le (value : V)
  | ascii (value : String)
  | programId
  | accKey (i : Nat)
  deriving BEq, Repr, Inhabited

/-- SVM-only source effects. -/
inductive OpExt (V : Type) where
  | invoke (programIx : Nat) (metas : Array CpiMeta) (data : Array (CpiWord V))
      (seed : Option String := none) (bump : Option V := none)
  deriving BEq, Repr, Inhabited

abbrev Op := ProofForge.Core.Ops.Op ValKind OpExt

private def leaf (kind : ValKind) : Val := .ext kind #[]

def clockSlot : Val := leaf .clockSlot
def clockEpoch : Val := leaf .clockEpoch
def unixTime : Val := leaf .unixTime
def slotsPerEpoch : Val := leaf .slotsPerEpoch
def signerKey0 : Val := leaf .signerKey0
def accLamports0 : Val := leaf .accLamports0
def accOwner0 : Val := leaf .accOwner0
def accDataLen0 : Val := leaf .accDataLen0
def accN : Val := leaf .accN
def isSigner0 : Val := leaf .isSigner0
def isWritable0 : Val := leaf .isWritable0
def isExecutable0 : Val := leaf .isExecutable0
def accLamports1 : Val := leaf .accLamports1
def accOwner1 : Val := leaf .accOwner1
def accDataLen1 : Val := leaf .accDataLen1
def isSigner1 : Val := leaf .isSigner1
def isWritable1 : Val := leaf .isWritable1
def isExecutable1 : Val := leaf .isExecutable1
def findPda (seed : String) : Val := leaf (.findPda seed)
def checkPda (seed : String) (bump : Val) : Val := .ext (.checkPda seed) #[bump]
def rentExemption (dataLen : UInt64) : Val := leaf (.rentExemption dataLen)
def cpiReturn : Val := leaf .cpiReturn
def sha256Lit (seed : String) : Val := leaf (.sha256Lit seed)
def keccak256Lit (seed : String) : Val := leaf (.keccak256Lit seed)
def accKeyWord (acc word : Nat) : Val := leaf (.accKeyWord acc word)
def accOwnerWord (acc word : Nat) : Val := leaf (.accOwnerWord acc word)
def accLamportsN (acc : Nat) : Val := leaf (.accLamportsN acc)
def accDataLenN (acc : Nat) : Val := leaf (.accDataLenN acc)
def isSignerN (acc : Nat) : Val := leaf (.isSignerN acc)
def isWritableN (acc : Nat) : Val := leaf (.isWritableN acc)
def isExecutableN (acc : Nat) : Val := leaf (.isExecutableN acc)
def signerKeyN (acc : Nat) : Val := leaf (.signerKeyN acc)
def ownerIsSelf (acc : Nat) : Val := leaf (.ownerIsSelf acc)

def CpiWord.wellFormed (word : CpiWord Val) : Bool :=
  match word with
  | .u64le value => value.wellFormed ValKind.arity
  | .accKey acc => cpiAccInRange acc
  | _ => true

def OpExt.wellFormed : OpExt Val → Bool
  | .invoke programIx metas data _ bump =>
      cpiAccInRange programIx && metas.all (cpiAccInRange ·.acc) &&
        data.all CpiWord.wellFormed &&
        match bump with
        | some value => value.wellFormed ValKind.arity
        | none => true

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

private partial def walkOps (ops : Array Op) (predicate : Op → Bool) : Bool :=
  ops.any fun op =>
    predicate op ||
      match op with
      | .ite _ _ _ thn els => walkOps thn predicate || walkOps els predicate
      | .forBody _ body => walkOps body predicate
      | _ => false

partial def valNeedsWalk : Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => valNeedsWalk base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => valNeedsWalk lhs || valNeedsWalk rhs
  | .indexGet base _ idx _ _ => valNeedsWalk base || valNeedsWalk idx
  | .select _ lhs rhs thn els =>
      valNeedsWalk lhs || valNeedsWalk rhs || valNeedsWalk thn || valNeedsWalk els
  | .ext kind operands =>
      (match kind with
       | .accLamports1 | .accOwner1 | .accDataLen1
       | .isSigner1 | .isWritable1 | .isExecutable1 => true
       | .accKeyWord acc _ | .accOwnerWord acc _
       | .accLamportsN acc | .accDataLenN acc
       | .isSignerN acc | .isWritableN acc | .isExecutableN acc
       | .signerKeyN acc | .ownerIsSelf acc => acc ≥ 1
       | _ => false) || operands.any valNeedsWalk

partial def valMinAccounts : Val → Nat
  | .arg _ | .local _ | .lit _ | .loopIx => 0
  | .field base _ | .bitNot base => valMinAccounts base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => Nat.max (valMinAccounts lhs) (valMinAccounts rhs)
  | .indexGet base _ idx _ _ => Nat.max (valMinAccounts base) (valMinAccounts idx)
  | .select _ lhs rhs thn els =>
      Nat.max (Nat.max (valMinAccounts lhs) (valMinAccounts rhs))
        (Nat.max (valMinAccounts thn) (valMinAccounts els))
  | .ext kind operands =>
      let here :=
        match kind with
        | .accLamports1 | .accOwner1 | .accDataLen1
        | .isSigner1 | .isWritable1 | .isExecutable1 => 2
        | .accKeyWord acc _ | .accOwnerWord acc _
        | .accLamportsN acc | .accDataLenN acc
        | .isSignerN acc | .isWritableN acc | .isExecutableN acc
        | .signerKeyN acc | .ownerIsSelf acc => acc + 1
        | _ => 0
      operands.foldl (init := here) fun current operand =>
        Nat.max current (valMinAccounts operand)

partial def valHasSelect : Val → Bool
  | .select .. => true
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => valHasSelect base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs => valHasSelect lhs || valHasSelect rhs
  | .indexGet base _ idx _ _ => valHasSelect base || valHasSelect idx
  | .ext _ operands => operands.any valHasSelect

partial def isLangVal : Val → Bool
  | .local _ | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot ..
  | .shiftL .. | .shiftR .. | .indexGet .. | .loopIx | .select .. => true
  | .field base _ => isLangVal base
  | _ => false

private def CpiWord.needsWalk : CpiWord Val → Bool
  | .u64le value => valNeedsWalk value
  | _ => false

private def CpiWord.minAccounts : CpiWord Val → Nat
  | .u64le value => valMinAccounts value
  | _ => 0

private def CpiWord.hasSelect : CpiWord Val → Bool
  | .u64le value => valHasSelect value
  | _ => false

private def OpExt.needsWalk : OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.any CpiWord.needsWalk || bump.any valNeedsWalk

private def OpExt.minAccounts : OpExt Val → Nat
  | .invoke _ _ data _ bump =>
      let fromData := data.foldl (init := 0) fun current word =>
        Nat.max current word.minAccounts
      Nat.max fromData (bump.map valMinAccounts |>.getD 0)

private def OpExt.hasSelect : OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.any CpiWord.hasSelect || bump.any valHasSelect

def hasInvoke (ops : Array Op) : Bool :=
  walkOps ops fun | .ext (.invoke ..) => true | _ => false

def hasStoreField (ops : Array Op) : Bool :=
  walkOps ops fun | .storeField .. => true | _ => false

def hasIndexSet (ops : Array Op) : Bool :=
  walkOps ops fun | .indexSet .. => true | _ => false

def hasCheckedArith (ops : Array Op) : Bool :=
  walkOps ops fun
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. => true
    | _ => false

def hasForAccum (ops : Array Op) : Bool :=
  walkOps ops fun | .forAccum .. => true | _ => false

def hasSelect (ops : Array Op) : Bool :=
  walkOps ops fun
    | .letLocal _ value | .setLocal _ value | .forAccum _ value _
    | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
        valHasSelect value
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
    | .indexSet _ lhs rhs _ _ => valHasSelect lhs || valHasSelect rhs
    | .ext payload => payload.hasSelect
    | _ => false

def hasAcc1 (ops : Array Op) : Bool :=
  walkOps ops fun
    | .letLocal _ value | .setLocal _ value | .forAccum _ value _
    | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
        valNeedsWalk value
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
    | .indexSet _ lhs rhs _ _ => valNeedsWalk lhs || valNeedsWalk rhs
    | .ext payload => payload.needsWalk
    | _ => false

private def opMinAccounts : Op → Nat
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      valMinAccounts value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
  | .indexSet _ lhs rhs _ _ => Nat.max (valMinAccounts lhs) (valMinAccounts rhs)
  | .ext payload => payload.minAccounts
  | _ => 0

partial def opsMinAccounts (ops : Array Op) : Nat :=
  ops.foldl (init := 0) fun result op =>
    let result := Nat.max result (opMinAccounts op)
    match op with
    | .ite _ _ _ thn els => Nat.max result (Nat.max (opsMinAccounts thn) (opsMinAccounts els))
    | .forBody _ body => Nat.max result (opsMinAccounts body)
    | _ => result

end ProofForge.Svm.Ops
