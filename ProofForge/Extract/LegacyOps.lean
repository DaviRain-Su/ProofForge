/-! Legacy closed union retained at the extraction compatibility boundary. -/
namespace ProofForge.Ops

inductive Cmp where
  | eq | ne | lt | le | gt | ge
  deriving BEq, Repr, Inhabited, DecidableEq

/-- 可 load 的值。SVM 叶是 `clock*` / `acc*` / PDA / hash；EVM 叶是 `evm*`。 -/
inductive Val where
  | arg (i : Nat)
  /-- Lexically scoped pure `UInt64` let binding, numbered by nesting depth. -/
  | local (i : Nat)
  | field (base : Val) (name : String)
  | lit (n : UInt64)
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
  | checkPda (seed : String) (bump : Val)
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
  | evmCaller
  | evmBlockNumber
  | evmTimestamp
  | evmChainId
  | evmSelf
  | evmCallValue
  | evmSelfBalance
  | evmCallerW0 | evmCallerW1 | evmCallerW2
  | evmSelfW0 | evmSelfW1 | evmSelfW2
  | bitAnd (lhs rhs : Val)
  | bitOr (lhs rhs : Val)
  | bitXor (lhs rhs : Val)
  | bitNot (v : Val)
  | shiftL (lhs rhs : Val)
  | shiftR (lhs rhs : Val)
  | indexGet (base : Val) (name : String) (idx : Val) (len : Nat) (elemOff : Nat := 0)
  | loopIx
  /-- Pure conditional value. Unlike `Op.ite`, both arms produce a value and no state effects. -/
  | select (cmp : Cmp) (lhs rhs thn els : Val)
  | addU64 (lhs rhs : Val)
  | subU64 (lhs rhs : Val)
  | mulU64 (lhs rhs : Val)
  | divU64 (lhs rhs : Val)
  | modU64 (lhs rhs : Val)
  | mapGetU64 (base key : Val)
  | mapGetAddr (base w0 w1 w2 : Val)
  | mapGetPair (base o0 o1 o2 s0 s1 s2 : Val)
  deriving BEq, Repr, Inhabited

/-- 内层 AccountMeta：外层账户下标 + 旗。编译期钉死。 -/
structure CpiMeta where
  acc : Nat
  signer : Bool := false
  writable : Bool := false
  deriving BEq, Repr, Inhabited

/-- 内层 instruction data 的一段。 -/
inductive CpiWord where
  | u8le (n : UInt64)
  | u32le (n : UInt64)
  | u64le (v : Val)
  | ascii (s : String)
  | programId
  | accKey (i : Nat)
  deriving BEq, Repr, Inhabited

inductive Op where
  | letLocal (i : Nat) (value : Val)
  /-- Declare a scalar slot before control flow whose successful paths assign it. -/
  | joinLocal (i : Nat)
  /-- Assign a previously declared join slot without introducing branch-local scope. -/
  | setLocal (i : Nat) (value : Val)
  | checkedAddU64 (lhs rhs : Val)
  | checkedSubU64 (lhs rhs : Val)
  | checkedMulU64 (lhs rhs : Val)
  | checkedDivU64 (lhs rhs : Val)
  | checkedModU64 (lhs rhs : Val)
  | ite (cmp : Cmp) (lhs rhs : Val) (thn els : Array Op)
  | invoke (programIx : Nat) (metas : Array CpiMeta) (data : Array CpiWord)
      (seed : Option String := none) (bump : Option Val := none)
  | evmDeposit (amount : Val)
  | evmSendEth (w0 w1 w2 amount : Val)
  | evmLog (name : String) (amount : Val)
  | forAccum (n : Nat) (addend : Val)
  /-- 有界 `for i in [:n]`，体里可用 `loopIx`。体里 `exit` 的 op 提前结束；否则落到循环后。 -/
  | forBody (n : Nat) (body : Array Op)
  | indexSet (name : String) (idx value : Val) (len : Nat) (elemOff : Nat := 0)
  | mapGetU64 (base key : Val)
  | mapSetU64 (base key value : Val)
  | mapGetAddr (base w0 w1 w2 : Val)
  | mapSetAddr (base w0 w1 w2 value : Val)
  | mapGetPair (base o0 o1 o2 s0 s1 s2 : Val)
  | mapSetPair (base o0 o1 o2 s0 s1 s2 value : Val)
  | evmTokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : Val)
  | evmTokenBalanceOfSelf (tw0 tw1 tw2 : Val)
  /-- 写一个已摊平的账户叶。mutate 槽 diff 一次可发多条。 -/
  | storeField (name : String) (value : Val)
  | okState (value : Val)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Val)
  | returnState (value : Val)
  deriving BEq, Repr, Inhabited

/-- `system.transfer` 特化。 -/
def systemTransfer (amount : Val) : Op :=
  .invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    #[.u32le 2, .u64le amount]

/-- CPI 到外层账户 1；空 metas、空 data。 -/
def invokeAcc1 : Op :=
  .invoke 1 #[] #[]

def systemCreate (lamports space : Val) : Op :=
  .invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    #[.u32le 0, .u64le lamports, .u64le space, .programId]

def createPda (lamports : Val) : Op :=
  .invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    #[.u32le 0, .u64le lamports, .u64le (.lit 16), .programId]
    (some "vault") (some (.findPda "vault"))

def systemAssign : Op :=
  .invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 1, .programId]

def systemAllocate (space : Val) : Op :=
  .invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 8, .u64le space]

def systemAllocateWithSeed (space : Val) : Op :=
  .invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 9, .accKey 0, .u64le (.lit 5), .ascii "vault", .u64le space, .programId]

def systemCreateWithSeed (lamports space : Val) : Op :=
  .invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    #[.u32le 3, .accKey 0, .u64le (.lit 5), .ascii "vault", .u64le lamports, .u64le space, .programId]

def systemAssignWithSeed : Op :=
  .invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 10, .accKey 0, .u64le (.lit 5), .ascii "vault", .programId]

def systemTransferWithSeed (lamports : Val) : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false },
      { acc := 2, signer := false, writable := true }]
    #[.u32le 11, .u64le lamports, .u64le (.lit 5), .ascii "vault", .programId]

def tokenInitMint : Op :=
  .invoke 2
    #[{ acc := 1, signer := false, writable := true }]
    #[.u8le 20, .u8le 6, .accKey 0, .u8le 0]

def tokenSyncNative : Op :=
  .invoke 2
    #[{ acc := 1, signer := false, writable := true }]
    #[.u8le 17]

def tokenTransferChecked (amount : Val) (decimals : UInt64) : Op :=
  .invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 12, .u64le amount, .u8le decimals]

def tokenMintToChecked (amount : Val) (decimals : UInt64) : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 14, .u64le amount, .u8le decimals]

def tokenBurnChecked (amount : Val) (decimals : UInt64) : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 15, .u64le amount, .u8le decimals]

def tokenInitAccount : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false }]
    #[.u8le 18, .accKey 0]

def tokenCloseAccount : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 9]

def tokenApproveChecked (amount : Val) (decimals : UInt64) : Op :=
  .invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 13, .u64le amount, .u8le decimals]

def tokenFreezeAccount : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 10]

def tokenThawAccount : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 11]

def tokenSetAccountAuthority : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 6, .u8le 2, .u8le 1, .accKey 2]
    none none

def tokenApprove (amount : Val) : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 4, .u64le amount]
    none none

def tokenInitMultisig : Op :=
  .invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false }]
    #[.u8le 19, .u8le 2]
    none none

def systemAdvanceNonce : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 4]
    none none

def tokenSetMintAuthority : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 6, .u8le 0, .u8le 1, .accKey 2]

def tokenRevoke : Op :=
  .invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 5]

def tokenAccountSize : Op :=
  .invoke 2
    #[{ acc := 1, signer := false, writable := false }]
    #[.u8le 21]

def memoWrite : Op :=
  .invoke 1
    #[{ acc := 0, signer := true, writable := false }]
    #[.ascii "ok"]

def ataCreateIdempotent : Op :=
  .invoke 6
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false },
      { acc := 4, signer := false, writable := false },
      { acc := 5, signer := false, writable := false }]
    #[.u8le 1]

private def walk (fuel : Nat) (ops : Array Op) (p : Op → Bool) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun op =>
      p op ||
        match op with
        | .ite _ _ _ t f => walk fuel' t p || walk fuel' f p
        | .forBody _ body => walk fuel' body p
        | _ => false

def hasInvoke (ops : Array Op) : Bool :=
  walk 16 ops (fun | .invoke .. => true | _ => false)

/-- 读账户 ≥1 header 的叶子；要 walk，但不等于 CPI。 -/
def valNeedsWalk : Val → Bool
  | .accLamports1 | .accOwner1 | .accDataLen1
  | .isSigner1 | .isWritable1 | .isExecutable1 => true
  | .accKeyWord acc _ | .accOwnerWord acc _ => acc ≥ 1
  | .accLamportsN acc | .accDataLenN acc
  | .isSignerN acc | .isWritableN acc | .isExecutableN acc
  | .signerKeyN acc | .ownerIsSelf acc => acc ≥ 1
  | .checkPda _ b => valNeedsWalk b
  | .field b _ => valNeedsWalk b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      valNeedsWalk l || valNeedsWalk r
  | .bitNot v => valNeedsWalk v
  | .indexGet b _ i _ => valNeedsWalk b || valNeedsWalk i
  | .select _ l r t f =>
      valNeedsWalk l || valNeedsWalk r || valNeedsWalk t || valNeedsWalk f
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
      valNeedsWalk l || valNeedsWalk r
  | .mapGetU64 b k => valNeedsWalk b || valNeedsWalk k
  | .mapGetAddr b a0 a1 a2 =>
      valNeedsWalk b || valNeedsWalk a0 || valNeedsWalk a1 || valNeedsWalk a2
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      valNeedsWalk b || valNeedsWalk a0 || valNeedsWalk a1 || valNeedsWalk a2 ||
        valNeedsWalk c0 || valNeedsWalk c1 || valNeedsWalk c2
  | _ => false

/-- 兼容旧名：账户 1+ 就要 walk。 -/
def valNeedsAcc1 : Val → Bool := valNeedsWalk

/-- 这个叶子要求的最小外层账户数。 -/
def valMinAccounts : Val → Nat
  | .accLamports1 | .accOwner1 | .accDataLen1
  | .isSigner1 | .isWritable1 | .isExecutable1 => 2
  | .accKeyWord acc _ | .accOwnerWord acc _ => acc + 1
  | .accLamportsN acc | .accDataLenN acc
  | .isSignerN acc | .isWritableN acc | .isExecutableN acc
  | .signerKeyN acc | .ownerIsSelf acc => acc + 1
  | .checkPda _ b => valMinAccounts b
  | .field b _ => valMinAccounts b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
  | .mapGetU64 l r => Nat.max (valMinAccounts l) (valMinAccounts r)
  | .bitNot v => valMinAccounts v
  | .indexGet b _ i _ => Nat.max (valMinAccounts b) (valMinAccounts i)
  | .select _ l r t f =>
      Nat.max (Nat.max (valMinAccounts l) (valMinAccounts r))
        (Nat.max (valMinAccounts t) (valMinAccounts f))
  | .mapGetAddr a b c d =>
      Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
        (Nat.max (valMinAccounts c) (valMinAccounts d))
  | .mapGetPair a b c d e f g =>
      Nat.max
        (Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
          (Nat.max (valMinAccounts c) (valMinAccounts d)))
        (Nat.max (Nat.max (valMinAccounts e) (valMinAccounts f)) (valMinAccounts g))
  | _ => 0

def hasAcc1 (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .letLocal _ v => valNeedsAcc1 v
    | .joinLocal _ => false
    | .setLocal _ v => valNeedsAcc1 v
    | .checkedAddU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedSubU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedMulU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedDivU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedModU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .ite _ l r _ _ => valNeedsAcc1 l || valNeedsAcc1 r
    | .invoke _ _ data _ bump =>
        data.any (fun | .u64le v => valNeedsAcc1 v | _ => false) ||
          (match bump with | some v => valNeedsAcc1 v | none => false)
    | .evmDeposit v => valNeedsAcc1 v
    | .evmSendEth a b c d =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c || valNeedsAcc1 d
    | .evmLog _ v => valNeedsAcc1 v
    | .forAccum _ v => valNeedsAcc1 v
    | .forBody _ _ => false
    | .indexSet _ i v _ _ => valNeedsAcc1 i || valNeedsAcc1 v
    | .mapGetU64 a b => valNeedsAcc1 a || valNeedsAcc1 b
    | .mapSetU64 a b c => valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c
    | .mapGetAddr a b c d =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c || valNeedsAcc1 d
    | .mapSetAddr a b c d e =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c ||
          valNeedsAcc1 d || valNeedsAcc1 e
    | .mapGetPair a b c d e f g =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c || valNeedsAcc1 d ||
          valNeedsAcc1 e || valNeedsAcc1 f || valNeedsAcc1 g
    | .mapSetPair a b c d e f g h =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c || valNeedsAcc1 d ||
          valNeedsAcc1 e || valNeedsAcc1 f || valNeedsAcc1 g || valNeedsAcc1 h
    | .evmTokenTransfer a b c d e f g =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c || valNeedsAcc1 d ||
          valNeedsAcc1 e || valNeedsAcc1 f || valNeedsAcc1 g
    | .evmTokenBalanceOfSelf a b c =>
        valNeedsAcc1 a || valNeedsAcc1 b || valNeedsAcc1 c
    | .okState v | .returnU64 v | .returnState v | .storeField _ v => valNeedsAcc1 v
    | .errorOverflow | .errorNamed _ => false

def hasEvmDeposit (ops : Array Op) : Bool :=
  walk 16 ops (fun | .evmDeposit _ => true | _ => false)

def hasEvmSendEth (ops : Array Op) : Bool :=
  walk 16 ops (fun | .evmSendEth .. => true | _ => false)

def hasEvmLog (ops : Array Op) : Bool :=
  walk 16 ops (fun | .evmLog .. => true | _ => false)

private def maxValAccounts (l r : Val) : Nat :=
  Nat.max (valMinAccounts l) (valMinAccounts r)

def opMinAccounts : Op → Nat
  | .letLocal _ v => valMinAccounts v
  | .joinLocal _ => 0
  | .setLocal _ v => valMinAccounts v
  | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
  | .checkedDivU64 l r | .checkedModU64 l r | .ite _ l r _ _ => maxValAccounts l r
  | .invoke _ _ data _ bump =>
      let fromData :=
        data.foldl (init := 0) fun a w =>
          match w with
          | .u64le v => Nat.max a (valMinAccounts v)
          | _ => a
      let fromBump := match bump with | some v => valMinAccounts v | none => 0
      Nat.max fromData fromBump
  | .okState v | .returnU64 v | .returnState v | .storeField _ v => valMinAccounts v
  | .errorOverflow | .errorNamed _ => 0
  | .evmDeposit v | .evmLog _ v | .forAccum _ v => valMinAccounts v
  | .forBody _ _ => 0
  | .evmSendEth a b c d =>
      Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
        (Nat.max (valMinAccounts c) (valMinAccounts d))
  | .indexSet _ i v _ _ => Nat.max (valMinAccounts i) (valMinAccounts v)
  | .mapGetU64 a b => Nat.max (valMinAccounts a) (valMinAccounts b)
  | .mapSetU64 a b c =>
      Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b)) (valMinAccounts c)
  | .mapGetAddr a b c d =>
      Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
        (Nat.max (valMinAccounts c) (valMinAccounts d))
  | .mapSetAddr a b c d e =>
      Nat.max
        (Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
          (Nat.max (valMinAccounts c) (valMinAccounts d)))
        (valMinAccounts e)
  | .mapGetPair a b c d e f g =>
      Nat.max
        (Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
          (Nat.max (valMinAccounts c) (valMinAccounts d)))
        (Nat.max (Nat.max (valMinAccounts e) (valMinAccounts f)) (valMinAccounts g))
  | .mapSetPair a b c d e f g h =>
      Nat.max
        (Nat.max
          (Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
            (Nat.max (valMinAccounts c) (valMinAccounts d)))
          (Nat.max (Nat.max (valMinAccounts e) (valMinAccounts f)) (valMinAccounts g)))
        (valMinAccounts h)
  | .evmTokenTransfer a b c d e f g =>
      Nat.max
        (Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b))
          (Nat.max (valMinAccounts c) (valMinAccounts d)))
        (Nat.max (Nat.max (valMinAccounts e) (valMinAccounts f)) (valMinAccounts g))
  | .evmTokenBalanceOfSelf a b c =>
      Nat.max (Nat.max (valMinAccounts a) (valMinAccounts b)) (valMinAccounts c)

def opsMinAccounts (ops : Array Op) : Nat :=
  let rec go (fuel : Nat) (ops : Array Op) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      ops.foldl (init := acc) fun a op =>
        let here := Nat.max a (opMinAccounts op)
        match op with
        | .ite _ _ _ t f => Nat.max (go fuel' t here) (go fuel' f here)
        | .forBody _ body => go fuel' body here
        | _ => here
  go 16 ops 0

def hasSystemTransfer (ops : Array Op) : Bool :=
  hasInvoke ops

def hasCheckedAdd (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedAddU64 .. => true | _ => false)

def hasCheckedSub (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedSubU64 .. => true | _ => false)

def hasCheckedMul (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedMulU64 .. => true | _ => false)

def hasCheckedDiv (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedDivU64 .. => true | _ => false)

def hasCheckedMod (ops : Array Op) : Bool :=
  walk 16 ops (fun | .checkedModU64 .. => true | _ => false)

def hasCheckedArith (ops : Array Op) : Bool :=
  hasCheckedAdd ops || hasCheckedSub ops ||
    hasCheckedMul ops || hasCheckedDiv ops || hasCheckedMod ops

def isBitVal : Val → Bool
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. => true
  | .field b _ => isBitVal b
  | .select _ l r t f => isBitVal l || isBitVal r || isBitVal t || isBitVal f
  | _ => false

def isLangVal : Val → Bool
  | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR ..
  | .local _ | .indexGet .. | .loopIx | .select .. => true
  | .field b _ => isLangVal b
  | _ => false

def isLangLeaf : Val → Bool
  | .local _ => true
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      isLangLeaf l || isLangLeaf r
  | .bitNot v => isLangLeaf v
  | .indexGet b _ i _ => isLangLeaf b || isLangLeaf i
  | .loopIx => true
  | .select _ l r t f =>
      isLangLeaf l || isLangLeaf r || isLangLeaf t || isLangLeaf f
  | .field b _ => isLangLeaf b
  | _ => false

def hasSelectVal : Val → Bool
  | .select .. => true
  | .field b _ | .bitNot b | .checkPda _ b => hasSelectVal b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
  | .mapGetU64 l r => hasSelectVal l || hasSelectVal r
  | .indexGet b _ i _ => hasSelectVal b || hasSelectVal i
  | .mapGetAddr a b c d =>
      hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d
  | .mapGetPair a b c d e f g =>
      hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d ||
        hasSelectVal e || hasSelectVal f || hasSelectVal g
  | _ => false

def isEvmLeaf : Val → Bool
  | .evmCaller | .evmBlockNumber | .evmTimestamp | .evmChainId
  | .evmSelf | .evmCallValue | .evmSelfBalance
  | .evmCallerW0 | .evmCallerW1 | .evmCallerW2
  | .evmSelfW0 | .evmSelfW1 | .evmSelfW2 => true
  | .field b _ => isEvmLeaf b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      isEvmLeaf l || isEvmLeaf r
  | .bitNot v => isEvmLeaf v
  | .indexGet b _ i _ => isEvmLeaf b || isEvmLeaf i
  | .select _ l r t f =>
      isEvmLeaf l || isEvmLeaf r || isEvmLeaf t || isEvmLeaf f
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
  | .mapGetU64 l r => isEvmLeaf l || isEvmLeaf r
  | .mapGetAddr a b c d =>
      isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d
  | .mapGetPair a b c d e f g =>
      isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d ||
        isEvmLeaf e || isEvmLeaf f || isEvmLeaf g
  | _ => false

private def cpiWordEvm : CpiWord → Bool
  | .u64le v => isEvmLeaf v
  | _ => false

def hasEvmLeaf (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .letLocal _ v => isEvmLeaf v
    | .joinLocal _ => false
    | .setLocal _ v => isEvmLeaf v
    | .checkedAddU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedSubU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedMulU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedDivU64 l r => isEvmLeaf l || isEvmLeaf r
    | .checkedModU64 l r => isEvmLeaf l || isEvmLeaf r
    | .ite _ l r _ _ => isEvmLeaf l || isEvmLeaf r
    | .invoke _ _ data _ bump =>
        data.any cpiWordEvm ||
          (match bump with | some v => isEvmLeaf v | none => false)
    | .evmDeposit v => isEvmLeaf v
    | .evmSendEth a b c d =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d
    | .evmLog _ v => isEvmLeaf v
    | .forAccum _ v => isEvmLeaf v
    | .forBody _ _ => false
    | .indexSet _ i v _ _ => isEvmLeaf i || isEvmLeaf v
    | .mapGetU64 a b => isEvmLeaf a || isEvmLeaf b
    | .mapSetU64 a b c => isEvmLeaf a || isEvmLeaf b || isEvmLeaf c
    | .mapGetAddr a b c d =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d
    | .mapSetAddr a b c d e =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d || isEvmLeaf e
    | .mapGetPair a b c d e f g =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d ||
          isEvmLeaf e || isEvmLeaf f || isEvmLeaf g
    | .mapSetPair a b c d e f g h =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d ||
          isEvmLeaf e || isEvmLeaf f || isEvmLeaf g || isEvmLeaf h
    | .evmTokenTransfer a b c d e f g =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c || isEvmLeaf d ||
          isEvmLeaf e || isEvmLeaf f || isEvmLeaf g
    | .evmTokenBalanceOfSelf a b c =>
        isEvmLeaf a || isEvmLeaf b || isEvmLeaf c
    | .okState v => isEvmLeaf v
    | .returnU64 v => isEvmLeaf v
    | .returnState v => isEvmLeaf v
    | .storeField _ v => isEvmLeaf v
    | .errorOverflow | .errorNamed _ => false

private def cpiWordLang : CpiWord → Bool
  | .u64le v => isLangLeaf v
  | _ => false

def hasLangLeaf (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .letLocal _ v => isLangLeaf v
    | .joinLocal _ => false
    | .setLocal _ v => isLangLeaf v
    | .checkedAddU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedSubU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedMulU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedDivU64 l r => isLangLeaf l || isLangLeaf r
    | .checkedModU64 l r => isLangLeaf l || isLangLeaf r
    | .ite _ l r _ _ => isLangLeaf l || isLangLeaf r
    | .invoke _ _ data _ bump =>
        data.any cpiWordLang ||
          (match bump with | some v => isLangLeaf v | none => false)
    | .evmDeposit v => isLangLeaf v
    | .evmSendEth a b c d =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d
    | .evmLog _ v => isLangLeaf v
    | .forAccum _ v => isLangLeaf v
    | .forBody _ _ => false
    | .indexSet _ i v _ _ => isLangLeaf i || isLangLeaf v
    | .mapGetU64 a b => isLangLeaf a || isLangLeaf b
    | .mapSetU64 a b c => isLangLeaf a || isLangLeaf b || isLangLeaf c
    | .mapGetAddr a b c d =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d
    | .mapSetAddr a b c d e =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d || isLangLeaf e
    | .mapGetPair a b c d e f g =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d ||
          isLangLeaf e || isLangLeaf f || isLangLeaf g
    | .mapSetPair a b c d e f g h =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d ||
          isLangLeaf e || isLangLeaf f || isLangLeaf g || isLangLeaf h
    | .evmTokenTransfer a b c d e f g =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c || isLangLeaf d ||
          isLangLeaf e || isLangLeaf f || isLangLeaf g
    | .evmTokenBalanceOfSelf a b c =>
        isLangLeaf a || isLangLeaf b || isLangLeaf c
    | .okState v => isLangLeaf v
    | .returnU64 v => isLangLeaf v
    | .returnState v => isLangLeaf v
    | .storeField _ v => isLangLeaf v
    | .errorOverflow | .errorNamed _ => false

def hasSelect (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .letLocal _ v => hasSelectVal v
    | .joinLocal _ => false
    | .setLocal _ v => hasSelectVal v
    | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
    | .checkedDivU64 l r | .checkedModU64 l r | .ite _ l r _ _ =>
        hasSelectVal l || hasSelectVal r
    | .invoke _ _ data _ bump =>
        (data.any fun | .u64le v => hasSelectVal v | _ => false) ||
          (match bump with | some v => hasSelectVal v | none => false)
    | .evmDeposit v | .evmLog _ v | .forAccum _ v => hasSelectVal v
    | .forBody _ _ => false
    | .evmSendEth a b c d =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d
    | .indexSet _ i v _ _ | .mapGetU64 i v => hasSelectVal i || hasSelectVal v
    | .mapSetU64 a b c => hasSelectVal a || hasSelectVal b || hasSelectVal c
    | .mapGetAddr a b c d =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d
    | .mapSetAddr a b c d e =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d || hasSelectVal e
    | .mapGetPair a b c d e f g =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d ||
          hasSelectVal e || hasSelectVal f || hasSelectVal g
    | .mapSetPair a b c d e f g h =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d ||
          hasSelectVal e || hasSelectVal f || hasSelectVal g || hasSelectVal h
    | .evmTokenTransfer a b c d e f g =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c || hasSelectVal d ||
          hasSelectVal e || hasSelectVal f || hasSelectVal g
    | .evmTokenBalanceOfSelf a b c =>
        hasSelectVal a || hasSelectVal b || hasSelectVal c
    | .okState v | .returnU64 v | .returnState v | .storeField _ v => hasSelectVal v
    | .errorOverflow | .errorNamed _ => false

def hasForAccum (ops : Array Op) : Bool :=
  walk 16 ops (fun | .forAccum .. => true | _ => false)

def hasForBody (ops : Array Op) : Bool :=
  walk 16 ops (fun | .forBody .. => true | _ => false)

def hasIndexSet (ops : Array Op) : Bool :=
  walk 16 ops (fun | .indexSet .. => true | _ => false)

def hasStoreField (ops : Array Op) : Bool :=
  walk 16 ops (fun | .storeField .. => true | _ => false)

def hasErrorNamed (ops : Array Op) : Bool :=
  walk 16 ops (fun | .errorNamed _ => true | _ => false)

def hasMapOp (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .mapGetU64 .. | .mapSetU64 .. | .mapGetAddr .. | .mapSetAddr ..
    | .mapGetPair .. | .mapSetPair .. => true
    | _ => false

def hasTokenOp (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .evmTokenTransfer .. | .evmTokenBalanceOfSelf .. => true
    | _ => false

/-- SVM 还不能发的语言叶：位运算、命名错误。for / index 不算。 -/
def hasSvmRejectedLang (ops : Array Op) : Bool :=
  hasErrorNamed ops ||
    walk 16 ops (fun
      | .letLocal _ v => isBitVal v
      | .joinLocal _ => false
      | .setLocal _ v => isBitVal v
      | .returnU64 v | .okState v | .returnState v | .storeField _ v => isBitVal v
      | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
      | .checkedDivU64 l r | .checkedModU64 l r | .ite _ l r _ _ =>
          isBitVal l || isBitVal r
      | .invoke _ _ data _ bump =>
          (data.any fun | .u64le v => isBitVal v | _ => false) ||
            (match bump with | some v => isBitVal v | none => false)
      | _ => false)

def hasLangOp (ops : Array Op) : Bool :=
  hasForAccum ops || hasForBody ops || hasIndexSet ops || hasSelect ops ||
    hasSvmRejectedLang ops

def hasEvmEffect (ops : Array Op) : Bool :=
  hasEvmDeposit ops || hasEvmSendEth ops || hasEvmLog ops || hasEvmLeaf ops ||
    hasMapOp ops || hasTokenOp ops

end ProofForge.Ops
