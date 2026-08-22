namespace SolanaLean.Ops

/-- 可 load 的值。`clockSlot` / `signerKey0` / `acc*` 是运行时叶子，不是账户槽。 -/
inductive Val where
  | arg (i : Nat)
  | field (base : Val) (name : String)
  | lit (n : UInt64)
  | clockSlot
  | signerKey0
  | accLamports0
  | accOwner0
  | accDataLen0
  | accN
  | isSigner0
  | isWritable0
  | isExecutable0
  | findPda (seed : String)
  | rentExemption (dataLen : UInt64)
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

def systemAssign : Op :=
  .invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 1, .programId]

def systemAllocate (space : Val) : Op :=
  .invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 8, .u64le space]

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
