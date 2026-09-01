import ProofForge.Core.Ops
import ProofForge.Svm.Component
import ProofForge.Svm.Cpi.TokenTlv
import ProofForge.Svm.Memo
import ProofForge.Svm.Seed

namespace ProofForge.Svm.Ops

/-- Agave's currently enforced transaction account-lock limit. -/
def maxTxAccountLocks : Nat := 64

def accInRange (acc : Nat) : Bool :=
  acc < maxTxAccountLocks

/-- CPI indices address the external-account region after the state account at physical index 0. -/
def cpiAccInRange (acc : Nat) : Bool :=
  acc + 1 < maxTxAccountLocks

/-- The final byte of a statically selected u64 word must fit in a u64 `data_len`. -/
def dataWordInRange (word : Nat) : Bool :=
  word < 2305843009213693951

/-- The largest statically reachable indexed word must leave room for its final eight bytes. -/
def indexedDataWordsInRange (baseWord strideWords capacity : Nat) : Bool :=
  capacity > 0 && strideWords > 0 && dataWordInRange strideWords &&
    dataWordInRange (baseWord + strideWords * (capacity - 1))

/-- A parent-path reader touches the links and parent/color words of fixed-stride slots and has a
compile-time loop bound. Keeping the bound at most 64 prevents an intrinsic from becoming an
unbounded account scan. -/
def parentPathWordsInRange
    (linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat) : Bool :=
  (AccountStorage.Query.parentPathValidOneBased
    0 linksBaseWord parentBaseWord strideWords capacity maxDepth).wellFormed maxTxAccountLocks

/-- A complete account-resident red-black tree scan uses one fixed 4096-bit stack bitmap. The
selected words cover Sokoban's links, parent/color, order-price, and order-sequence fields. -/
def rbTreeWordsInRange
    (linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat) : Bool :=
  (AccountStorage.Query.fifoRbTreeValidOneBased
    0 linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity false).wellFormed
      maxTxAccountLocks

/-- A four-word-key complete tree scan uses a fixed 8321-bit bitmap and a fixed 64-entry
traversal stack. The key words are consecutive and compared in original byte order. -/
def rbTreeKey4WordsInRange
    (linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat) : Bool :=
  (AccountStorage.Query.key4RbTreeValidOneBased
    0 linksBaseWord parentBaseWord keyBaseWord strideWords capacity).wellFormed maxTxAccountLocks

/-- Static non-bump bytes in one PDA signer group. -/
inductive PdaSeed where
  | ascii (value : String)
  | stateKey
  | accKey (i : Nat)
  /-- Fixed byte slice of an external account's data, used directly as one PDA seed. -/
  | accData (i offset length : Nat)
  deriving BEq, Repr, Inhabited

/-- SVM-only source value intrinsics. Recursive operands live in `Core.Ops.Val.ext`. -/
inductive ValKind where
  | clockSlot
  | clockEpoch
  | unixTime
  | slotsPerEpoch
  | byteSwap64
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
  | accDataWord (acc word : Nat)
  | component (query : Component.Query)
  | accLamportsN (acc : Nat)
  | accDataLenN (acc : Nat)
  | isSignerN (acc : Nat)
  | isWritableN (acc : Nat)
  | isExecutableN (acc : Nat)
  | signerKeyN (acc : Nat)
  | ownerIsSelf (acc : Nat)
  | findPdaSeeds (seeds : Array PdaSeed)
  | checkPdaSeeds (account : Nat) (seeds : Array PdaSeed)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .checkPda _ => 1
  | .byteSwap64 => 1
  | .component query => query.arity
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- Account index relative to the CPI account region; physical account 0 is reserved for state. -/
structure CpiMeta where
  acc : Nat
  signer : Bool := false
  writable : Bool := false
  expectedDataLen : Option Nat := none
  /-- Typed account-data policy (e.g. the bounded Token-2022 TLV cursor); mutually exclusive
  with `expectedDataLen`. -/
  accountData : Option Cpi.TokenTlv.Policy := none
  deriving BEq, Repr, Inhabited

def CpiMeta.wellFormed (entry : CpiMeta) : Bool :=
  cpiAccInRange entry.acc && entry.expectedDataLen.all (· ≤ 18446744073709551615) &&
    !(entry.expectedDataLen.isSome && entry.accountData.isSome) &&
    entry.accountData.all (fun policy =>
      match Cpi.TokenTlv.planFor policy with
      | .ok plan => plan.wellFormed
      | .error _ => false)

inductive CpiWord (V : Type) where
  | u8le (value : V)
  | u16le (value : V)
  | u32le (value : V)
  | u64le (value : V)
  /-- One-byte data prefix that also declares the matching signed raw self-entry. -/
  | selfEntry (tag : UInt64) (authoritySeed : String)
  | ascii (value : String)
  | programId
  | accKey (i : Nat)
  deriving BEq, Repr, Inhabited

def CpiWord.map (f : α → β) : CpiWord α → CpiWord β
  | .u8le value => .u8le (f value)
  | .u16le value => .u16le (f value)
  | .u32le value => .u32le (f value)
  | .u64le value => .u64le (f value)
  | .selfEntry tag authoritySeed => .selfEntry tag authoritySeed
  | .ascii value => .ascii value
  | .programId => .programId
  | .accKey i => .accKey i

def CpiWord.value? : CpiWord V → Option V
  | .u8le value | .u16le value | .u32le value | .u64le value => some value
  | .selfEntry _ _ | .ascii _ | .programId | .accKey _ => none

structure RawSelfEntry where
  tag : UInt64
  authoritySeed : String
  deriving BEq, Repr, Inhabited

def CpiWord.rawSelfEntry? : CpiWord V → Option RawSelfEntry
  | .selfEntry tag authoritySeed => some { tag, authoritySeed }
  | _ => none

/-- SVM-only source effects. -/
inductive OpExt (V : Type) where
  | invoke (programIx : Nat) (metas : Array CpiMeta) (data : Array (CpiWord V))
      (seeds : Array PdaSeed := #[]) (bump : Option V := none)
  | component (call : Component.Call V)
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
def byteSwap64 (word : Val) : Val := .ext .byteSwap64 #[word]
def accKeyWord (acc word : Nat) : Val := leaf (.accKeyWord acc word)
def accOwnerWord (acc word : Nat) : Val := leaf (.accOwnerWord acc word)
def accDataWord (acc word : Nat) : Val := leaf (.accDataWord acc word)
def accDataWordAt (acc baseWord strideWords capacity : Nat) (index : Val) : Val :=
  .ext (.component (.accountStorage
    (.readWordZeroBased acc baseWord strideWords capacity))) #[index]
def accDataWordAtOneBased (acc baseWord strideWords capacity : Nat) (index : Val) : Val :=
  .ext (.component (.accountStorage
    (.readWordOneBased acc baseWord strideWords capacity))) #[index]
/-- Read one header field of the runtime-selected remaining account `base + index`. The compile-time
window `[base, base + capacity)` bounds the index; availability and geometry are checked at
runtime by the target. -/
def viewHeader (base capacity : Nat) (field : AccountView.Header) (index : Val) : Val :=
  .ext (.component (.accountView (.header { base, capacity } field))) #[index]
def viewLamports (base capacity : Nat) (index : Val) : Val :=
  viewHeader base capacity .lamports index
def viewDataLen (base capacity : Nat) (index : Val) : Val :=
  viewHeader base capacity .dataLen index
def viewIsSigner (base capacity : Nat) (index : Val) : Val :=
  viewHeader base capacity .isSigner index
def viewIsWritable (base capacity : Nat) (index : Val) : Val :=
  viewHeader base capacity .isWritable index
def viewKeyWord (base capacity word : Nat) (index : Val) : Val :=
  viewHeader base capacity (.key word) index
def viewOwnerIsSelf (base capacity : Nat) (index : Val) : Val :=
  .ext (.component (.accountView (.ownerIsSelf { base, capacity }))) #[index]
def viewDataWord (base capacity word : Nat) (index : Val) : Val :=
  .ext (.component (.accountView (.dataWord { base, capacity } word))) #[index]
def accDataRbTreeKey4Find
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : Val) : Val :=
  .ext (.component (.accountStorage (.key4FindOneBased
    acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity)))
      #[key0, key1, key2, key3]
def accDataRbTreeOrderFind
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (price sequence : Val) : Val :=
  .ext (.component (.accountStorage (.fifoFindOneBased
    acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid)))
      #[price, sequence]
def accDataRbTreeOrderCursor
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (hasCursor price sequence : Val) : Val :=
  .ext (.component (.accountStorage (.fifoCursorOneBased
    acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid)))
      #[hasCursor, price, sequence]
def accDataParentPathValid
    (acc linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat)
    (index root bumpIndex : Val) : Val :=
  .ext (.component (.accountStorage (.parentPathValidOneBased
    acc linksBaseWord parentBaseWord strideWords capacity maxDepth))) #[index, root, bumpIndex]
def accDataRbTreeValid
    (acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (root size bumpIndex freeListHead : Val) : Val :=
  .ext (.component (.accountStorage (.fifoRbTreeValidOneBased
    acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity bid)))
      #[root, size, bumpIndex, freeListHead]
def accDataRbTreeKey4Valid
    (acc linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (root size bumpIndex freeListHead : Val) : Val :=
  .ext (.component (.accountStorage (.key4RbTreeValidOneBased
    acc linksBaseWord parentBaseWord keyBaseWord strideWords capacity)))
      #[root, size, bumpIndex, freeListHead]
def fifoCancelResult (query : FifoCancel.Query) : Val :=
  .ext (.component (.fifoCancel query)) #[]
def accLamportsN (acc : Nat) : Val := leaf (.accLamportsN acc)
def accDataLenN (acc : Nat) : Val := leaf (.accDataLenN acc)
def isSignerN (acc : Nat) : Val := leaf (.isSignerN acc)
def isWritableN (acc : Nat) : Val := leaf (.isWritableN acc)
def isExecutableN (acc : Nat) : Val := leaf (.isExecutableN acc)
def signerKeyN (acc : Nat) : Val := leaf (.signerKeyN acc)
def ownerIsSelf (acc : Nat) : Val := leaf (.ownerIsSelf acc)
def findPdaSeeds (seeds : Array PdaSeed) : Val := leaf (.findPdaSeeds seeds)
def checkPdaSeeds (account : Nat) (seeds : Array PdaSeed) : Val :=
  leaf (.checkPdaSeeds account seeds)

private def asciiSeedWellFormed (value : String) : Bool :=
  ProofForge.Svm.Seed.Ascii.wellFormed value

def CpiWord.wellFormed (word : CpiWord Val) : Bool :=
  match word with
  | .u8le value | .u16le value | .u32le value | .u64le value =>
      value.wellFormed ValKind.arity
  | .selfEntry tag authoritySeed =>
      tag.toNat < 256 && asciiSeedWellFormed authoritySeed
  | .accKey acc => cpiAccInRange acc
  | _ => true

def PdaSeed.wellFormed : PdaSeed → Bool
  | .ascii value => asciiSeedWellFormed value
  | .stateKey => true
  | .accKey acc => cpiAccInRange acc
  | .accData acc offset length =>
      cpiAccInRange acc && 0 < length && length ≤ 32 &&
        offset ≤ 18446744073709551615 - length

/-- Solana permits at most 16 seeds of at most 32 bytes each. The emitter appends the bump, so
the statically declared non-bump group is nonempty and contains at most 15 seeds. -/
def PdaSeed.groupWellFormed (seeds : Array PdaSeed) : Bool :=
  !seeds.isEmpty && seeds.size ≤ 15 && seeds.all PdaSeed.wellFormed

private partial def staticPayloadsWellFormed : Val → Bool
  | .field base _ | .bitNot base => staticPayloadsWellFormed base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      staticPayloadsWellFormed lhs && staticPayloadsWellFormed rhs
  | .indexGet base _ idx _ _ =>
      staticPayloadsWellFormed base && staticPayloadsWellFormed idx
  | .select _ lhs rhs thn els =>
      staticPayloadsWellFormed lhs && staticPayloadsWellFormed rhs &&
        staticPayloadsWellFormed thn && staticPayloadsWellFormed els
  | .ext (.findPda seed) operands | .ext (.checkPda seed) operands =>
      asciiSeedWellFormed seed && operands.all staticPayloadsWellFormed
  | .ext (.findPdaSeeds seeds) operands =>
      PdaSeed.groupWellFormed seeds && operands.all staticPayloadsWellFormed
  | .ext (.checkPdaSeeds account seeds) operands =>
      cpiAccInRange account && PdaSeed.groupWellFormed seeds &&
        operands.all staticPayloadsWellFormed
  | .ext (.accDataWord acc word) operands =>
      accInRange acc && dataWordInRange word && operands.all staticPayloadsWellFormed
  | .ext (.component query) operands =>
      query.wellFormed maxTxAccountLocks && operands.all staticPayloadsWellFormed
  | .ext _ operands => operands.all staticPayloadsWellFormed
  | _ => true

private def rawSelfInvokeWellFormed (metas : Array CpiMeta) (data : Array (CpiWord Val))
    (seeds : Array PdaSeed) (bump : Option Val) : Bool :=
  let entries := data.filterMap CpiWord.rawSelfEntry?
  if entries.isEmpty then true
  else
    match data[0]?, entries[0]?, metas.toList, seeds.toList, bump with
    | some (CpiWord.selfEntry tag authoritySeed), some entry,
        [authorityMeta], [.ascii signerSeed], some _ =>
        entries.size == 1 && entry.tag == tag && entry.authoritySeed == authoritySeed &&
          signerSeed == authoritySeed && authorityMeta.signer && !authorityMeta.writable
    | _, _, _, _, _ => false

/-- Seed-derived System instructions carry a bincode `u64` byte length immediately before their
ASCII seed. Validate only the four closed account geometries owned by the SDK; `.ascii` remains a
generic CPI data word for other programs. -/
private def systemAsciiSeedWellFormed
    (programIx : Nat) (metas : Array CpiMeta) (data : Array (CpiWord Val)) : Bool :=
  let derivedMetas : Array CpiMeta :=
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
  let createMetas : Array CpiMeta :=
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
  let transferMetas : Array CpiMeta := derivedMetas.push
    { acc := 2, signer := false, writable := true }
  let validLength (length : Val) (seed : String) : Bool :=
    match length with
    | .lit encoded => encoded.toNat == seed.length && asciiSeedWellFormed seed
    | _ => false
  match data with
  | #[.u32le (.lit tag), .accKey 0, .u64le length, .ascii seed, .u64le _, .programId] =>
      if tag == 9 && programIx == 2 && metas == derivedMetas then validLength length seed else true
  | #[.u32le (.lit tag), .accKey 0, .u64le length, .ascii seed, .u64le _, .u64le _,
      .programId] =>
      if tag == 3 && programIx == 2 && metas == createMetas then validLength length seed else true
  | #[.u32le (.lit tag), .accKey 0, .u64le length, .ascii seed, .programId] =>
      if tag == 10 && programIx == 2 && metas == derivedMetas then validLength length seed else true
  | #[.u32le (.lit tag), .u64le _, .u64le length, .ascii seed, .programId] =>
      if tag == 11 && programIx == 3 && metas == transferMetas then validLength length seed else true
  | _ => true

/-- Validate the statically bounded payload only for the fixed Memo SDK account geometry. The gate
accepts either the historical seven-bit ASCII policy or the UTF-8 byte budget (`svm-sdk-006`).
Other `.ascii` CPI words remain generic instruction data. -/
private def memoPayloadWellFormed
    (programIx : Nat) (metas : Array CpiMeta) (data : Array (CpiWord Val)) : Bool :=
  let memoMetas : Array CpiMeta :=
    #[{ acc := 0, signer := true, writable := false }]
  match data with
  | #[.ascii value] =>
      if programIx == 1 && metas == memoMetas then
        ProofForge.Svm.Memo.Ascii.wellFormed value ||
          ProofForge.Svm.Memo.Utf8.wellFormed value
      else true
  | _ => true

def OpExt.wellFormed : OpExt Val → Bool
  | .invoke programIx metas data seeds bump =>
      cpiAccInRange programIx && metas.all CpiMeta.wellFormed &&
        data.all CpiWord.wellFormed &&
        systemAsciiSeedWellFormed programIx metas data &&
        memoPayloadWellFormed programIx metas data &&
        rawSelfInvokeWellFormed metas data seeds bump &&
        ((seeds.isEmpty && bump.isNone) ||
          (PdaSeed.groupWellFormed seeds && bump.isSome)) &&
        bump.all fun value =>
          value.wellFormed ValKind.arity && staticPayloadsWellFormed value
  | .component call =>
      call.wellFormed (fun value =>
        value.wellFormed ValKind.arity && staticPayloadsWellFormed value) maxTxAccountLocks

private partial def opStaticPayloadsWellFormed : Op → Bool
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      staticPayloadsWellFormed value
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs
  | .indexSetLeaf _ lhs rhs _ _ | .indexSet _ lhs rhs _ _ =>
      staticPayloadsWellFormed lhs && staticPayloadsWellFormed rhs
  | .ite _ lhs rhs thn els =>
      staticPayloadsWellFormed lhs && staticPayloadsWellFormed rhs &&
        thn.all opStaticPayloadsWellFormed && els.all opStaticPayloadsWellFormed
  | .forBody _ body => body.all opStaticPayloadsWellFormed
  | .ext payload =>
      match payload with
      | .invoke _ _ data _ bump =>
          data.all (fun word => word.value?.all staticPayloadsWellFormed) &&
            bump.all staticPayloadsWellFormed
      | .component call => call.allValues staticPayloadsWellFormed
  | .errorTyped frame => frame.values.all staticPayloadsWellFormed
  | .joinLocal _ | .errorOverflow | .errorNamed _ => true

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op &&
    opStaticPayloadsWellFormed op

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
       | .accKeyWord acc _ | .accOwnerWord acc _ | .accDataWord acc _
       | .accLamportsN acc | .accDataLenN acc
       | .isSignerN acc | .isWritableN acc | .isExecutableN acc
       | .signerKeyN acc | .ownerIsSelf acc => acc ≥ 1
       | .findPdaSeeds seeds =>
           seeds.any fun | .stateKey | .accKey _ | .accData .. => true | _ => false
       | .component query => query.needsWalk
       | .checkPdaSeeds _ _ => true
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
        | .accKeyWord acc _ | .accOwnerWord acc _ | .accDataWord acc _
        | .accLamportsN acc | .accDataLenN acc
        | .isSignerN acc | .isWritableN acc | .isExecutableN acc
        | .signerKeyN acc | .ownerIsSelf acc => acc + 1
        | .component query => query.minAccounts valMinAccounts operands
        | .findPdaSeeds seeds => seeds.foldl (init := 0) fun current seed =>
            match seed with
            | .accKey acc | .accData acc .. => Nat.max current (acc + 2)
            | _ => current
        | .checkPdaSeeds account seeds =>
            seeds.foldl (init := account + 2) fun current seed =>
              match seed with
              | .accKey acc | .accData acc .. => Nat.max current (acc + 2)
              | _ => current
        | _ => 0
      match kind with
      | .component _ => here
      | _ => operands.foldl (init := here) fun current operand =>
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

private partial def valHasAccountView : Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ => valHasAccountView base
  | .ext (.component (.accountView _)) _ => true
  | .ext _ operands => operands.any valHasAccountView
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valHasAccountView lhs || valHasAccountView rhs
  | .bitNot v => valHasAccountView v
  | .indexGet base _ idx _ _ => valHasAccountView base || valHasAccountView idx
  | .select _ lhs rhs thn els =>
      valHasAccountView lhs || valHasAccountView rhs ||
        valHasAccountView thn || valHasAccountView els

/-- True when any value or component call in `ops` selects an account through a bounded
remaining-account view. Variable remaining accounts change where instruction data and the program
id live, so the emitter must switch to the runtime account-count walk. -/
partial def hasAccountView (ops : Array Op) : Bool :=
  walkOps ops fun op =>
    match op with
    | .letLocal _ v | .setLocal _ v | .forAccum _ v _
    | .storeField _ v | .okState v | .returnU64 v | .returnState v => valHasAccountView v
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs | .ite _ lhs rhs _ _
    | .indexSetLeaf _ lhs rhs _ _ | .indexSet _ lhs rhs _ _ =>
        valHasAccountView lhs || valHasAccountView rhs
    | .ext payload =>
        match payload with
        | .component call => call.values.any valHasAccountView
        | .invoke _ _ data _ bump =>
            data.any (fun word => word.value?.any valHasAccountView) ||
              bump.any valHasAccountView
    | .errorTyped frame => frame.values.any valHasAccountView
    | .joinLocal _ | .errorOverflow | .errorNamed _ => false
    | .forBody _ body => hasAccountView body

partial def isLangVal : Val → Bool
  | .local _ | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot ..
  | .shiftL .. | .shiftR .. | .indexGet .. | .loopIx | .select .. => true
  | .field base _ => isLangVal base
  | _ => false

private def CpiWord.needsWalk : CpiWord Val → Bool
  | word => word.value?.any valNeedsWalk

private def CpiWord.minAccounts : CpiWord Val → Nat
  | word => word.value?.map valMinAccounts |>.getD 0

private def CpiWord.hasSelect : CpiWord Val → Bool
  | word => word.value?.any valHasSelect

private def OpExt.needsWalk : OpExt Val → Bool
  | .invoke _ _ data seeds bump =>
      data.any CpiWord.needsWalk ||
        seeds.any (fun | .stateKey | .accKey _ | .accData .. => true | _ => false) ||
        bump.any valNeedsWalk
  | .component .. => true

private def OpExt.minAccounts : OpExt Val → Nat
  | .invoke _ _ data seeds bump =>
      let fromData := data.foldl (init := 0) fun current word =>
        Nat.max current word.minAccounts
      let fromSeeds := seeds.foldl (init := 0) fun current seed =>
        match seed with
        | .accKey acc | .accData acc .. => Nat.max current (acc + 2)
        | _ => current
      Nat.max (Nat.max fromData fromSeeds) (bump.map valMinAccounts |>.getD 0)
  | .component call => call.minAccounts valMinAccounts

private def OpExt.hasSelect : OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.any CpiWord.hasSelect || bump.any valHasSelect
  | .component call => call.anyValue valHasSelect

def hasInvoke (ops : Array Op) : Bool :=
  walkOps ops fun
    | .ext (.invoke ..) => true
    | .ext (.component call) => call.usesCpi
    | _ => false

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
