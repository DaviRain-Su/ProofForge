namespace SolanaLean.Ops

/-- 可 load 的值。`clockSlot` / `signerKey0` / `acc*` 是运行时叶子，不是账户槽。 -/
inductive Val where
  | arg (i : Nat)
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
  deriving BEq, Repr, Inhabited

inductive Cmp where
  | eq | ne | lt | le | gt | ge
  deriving BEq, Repr, Inhabited, DecidableEq

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
  | checkedAddU64 (lhs rhs : Val)
  | checkedSubU64 (lhs rhs : Val)
  | checkedMulU64 (lhs rhs : Val)
  | checkedDivU64 (lhs rhs : Val)
  | checkedModU64 (lhs rhs : Val)
  | ite (cmp : Cmp) (lhs rhs : Val) (thn els : Array Op)
  | invoke (programIx : Nat) (metas : Array CpiMeta) (data : Array CpiWord)
      (seed : Option String := none) (bump : Option Val := none)
  | okState (value : Val)
  | errorOverflow
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
  | _ => 0

def hasAcc1 (ops : Array Op) : Bool :=
  walk 16 ops fun
    | .checkedAddU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedSubU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedMulU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedDivU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .checkedModU64 l r => valNeedsAcc1 l || valNeedsAcc1 r
    | .ite _ l r _ _ => valNeedsAcc1 l || valNeedsAcc1 r
    | .invoke _ _ data _ bump =>
        data.any (fun | .u64le v => valNeedsAcc1 v | _ => false) ||
          (match bump with | some v => valNeedsAcc1 v | none => false)
    | .okState v | .returnU64 v | .returnState v => valNeedsAcc1 v
    | .errorOverflow => false

private def maxValAccounts (l r : Val) : Nat :=
  Nat.max (valMinAccounts l) (valMinAccounts r)

def opMinAccounts : Op → Nat
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
  | .okState v | .returnU64 v | .returnState v => valMinAccounts v
  | .errorOverflow => 0

def opsMinAccounts (ops : Array Op) : Nat :=
  let rec go (fuel : Nat) (ops : Array Op) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      ops.foldl (init := acc) fun a op =>
        let here := Nat.max a (opMinAccounts op)
        match op with
        | .ite _ _ _ t f => Nat.max (go fuel' t here) (go fuel' f here)
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

end SolanaLean.Ops
