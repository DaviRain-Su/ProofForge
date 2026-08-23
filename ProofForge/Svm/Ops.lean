import ProofForge.Core.Ops

namespace ProofForge.Svm.Ops

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
  | _ => true

def OpExt.wellFormed : OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.all CpiWord.wellFormed &&
        match bump with
        | some value => value.wellFormed ValKind.arity
        | none => true

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Svm.Ops
