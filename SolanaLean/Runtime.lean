namespace SolanaLean.Runtime

/--
当前 slot。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.slot`（偏移 0）。这是物理 slot，不是逻辑 block。

宿主侧是不可约 stub：定理把它当未指定的 `UInt64`，不要unfold成 0。
`unixTime` / 其余 Clock 字段本剖面 fail closed。
-/
@[irreducible] def clockSlot : UInt64 := 0

/--
当前 epoch。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.epoch`（偏移 16）。宿主侧是不可约 stub。
`unixTime` / `epoch_start_timestamp` 本剖面 fail closed。
-/
@[irreducible] def clockEpoch : UInt64 := 0

/--
`dataLen` 字节账户的 rent-exempt 下限。
抽出后发射 `sol_get_rent_sysvar`，读 `lamports_per_byte`，再乘 `128 + dataLen`。
`dataLen` 必须在抽出时是常量。宿主侧是不可约 stub。
`exemption_threshold` 当浮点用仍 fail closed。
-/
@[irreducible] def rentExemption (dataLen : UInt64) : UInt64 :=
  let _ := dataLen
  0

/--
当前 `EpochSchedule.slots_per_epoch`。抽出后发射
`sol_get_epoch_schedule_sysvar`，读偏移 0。宿主侧是不可约 stub。
`warmup` / `first_normal_*` 本剖面 fail closed。
-/
@[irreducible] def slotsPerEpoch : UInt64 := 0

/--
账户 0 公钥的第一个小端 `u64`（`ACC0_KEY+0`）。
用到这个叶子的入口会检查 `is_signer`。

这是指定账户的 key，不是 `tx.origin`，也不是 fee payer。
完整 32 字节以后再开。
-/
@[irreducible] def signerKey0 : UInt64 := 0

/-- 内层 AccountMeta。编译期钉死下标和旗。 -/
structure CpiMeta where
  acc : UInt64
  signer : Bool := false
  writable : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- 内层 instruction data 的一段。长度和布局编译期钉死。 -/
inductive CpiWord where
  | u8le (n : UInt64)
  | u32le (n : UInt64)
  | u64le (v : UInt64)
  | ascii (s : String)
  | programId
  | accKey (i : UInt64)
  deriving Repr, Inhabited

/--
编译期钉死的 CPI。抽出器认这个名字，发射 `sol_invoke_signed_c`。
`programIx`、metas、data 布局必须在抽出时已知。
宿主侧是不可约 stub，返回 0，不要当链上结果用。
运行时拼 program id / remaining accounts / 变长 data 仍 fail closed。
-/
@[irreducible] def invoke (programIx : UInt64) (metas : Array CpiMeta) (data : Array CpiWord) :
    UInt64 :=
  let _ := programIx
  let _ := metas
  let _ := data
  0

/--
一组 signer seeds：一条 ASCII 种子 + 一个 bump。
抽出器认这个名字，发射带 `SolSignerSeeds` 的 `sol_invoke_signed_c`。
宿主侧是不可约 stub，返回 0。多组 seeds / 运行时拼种子 fail closed。
-/
@[irreducible] def invokeSigned (programIx : UInt64) (metas : Array CpiMeta)
    (data : Array CpiWord) (seed : String) (bump : UInt64) : UInt64 :=
  let _ := programIx
  let _ := metas
  let _ := data
  let _ := seed
  let _ := bump
  0

/-- `system.transfer`：普通包装，不是抽出特例。 -/
def systemTransfer (lamports : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    #[.u32le 2, .u64le lamports]

/-- CPI 到外层账户 1；空 metas、空 data。普通包装。 -/
def invokeAcc1 : UInt64 :=
  invoke 1 #[] #[]

/--
`system.createAccount`：payer / 新账户 / System。
owner 钉死为当前 program id。space 编译期常量。
-/
def systemCreate (lamports space : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    -- bincode：u32 tag 0，无 pad；52 字节。
    #[.u32le 0, .u64le lamports, .u64le space, .programId]

/--
`system.assign`：把账户 0 的 owner 改成当前 program id。
外层：账户 0 s+w、System。
-/
def systemAssign : UInt64 :=
  invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 1, .programId]

/--
`system.allocate`：给账户 0 开 `space` 字节。space 编译期常量。
外层：账户 0 s+w、System。
-/
def systemAllocate (space : UInt64) : UInt64 :=
  invoke 1
    #[{ acc := 0, signer := true, writable := true }]
    #[.u32le 8, .u64le space]

/--
Token `TransferChecked`：普通包装。decimals 编译期常量。
外层 0 必须是 authority（prelude 强制 acc0 signer）。
内层账户按官方顺序：source / mint / dest / authority。
-/
def tokenTransferChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    -- packed：u8 tag 12 || u64le amount || u8 decimals。
    #[.u8le 12, .u64le amount, .u8le decimals]

/--
Token `MintToChecked`：普通包装。decimals 编译期常量。
外层 0 是 mint authority。内层：mint w / dest w / authority。
-/
def tokenMintToChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 14, .u64le amount, .u8le decimals]

/--
Token `BurnChecked`：普通包装。decimals 编译期常量。
外层 0 是 token owner。内层：source w / mint w / authority。
-/
def tokenBurnChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 15, .u64le amount, .u8le decimals]

/--
Token `InitializeAccount3`：普通包装。owner = 外层账户 0 公钥。
外层 0 是 owner。内层：account w / mint r。
-/
def tokenInitAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false }]
    #[.u8le 18, .accKey 0]

/--
Token `CloseAccount`：普通包装。
外层 0 是 owner。内层：source w / dest w / owner s。
-/
def tokenCloseAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 9]

/--
Token `ApproveChecked`：普通包装。decimals 编译期常量。
外层 0 是 owner。内层：source w / mint r / delegate r / owner s。
-/
def tokenApproveChecked (amount : UInt64) (decimals : UInt64) : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 13, .u64le amount, .u8le decimals]

/--
Token `FreezeAccount`：普通包装。
外层 0 是 mint freeze authority。内层：account w / mint r / authority s。
-/
def tokenFreezeAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 10]

/--
Token `ThawAccount`：普通包装。账户表与 Freeze 相同。
-/
def tokenThawAccount : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 11]

/--
Token `SetAuthority`：普通包装。本切片钉死 `MintTokens`，
新 authority = 外层账户 2 公钥。
外层 0 是当前 mint authority。内层：mint w / current authority s。
-/
def tokenSetMintAuthority : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 6, .u8le 0, .u8le 1, .accKey 2]

/--
Token `Revoke`：普通包装。清掉 source 的 delegate。
外层 0 是 owner。内层：source w / owner s。
-/
def tokenRevoke : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 5]

/--
Memo 写一条 UTF-8 字面量。本切片钉死 `"ok"`。
外层 0 是 signer；callee 是外层账户 1。
-/
def memoWrite : UInt64 :=
  invoke 1
    #[{ acc := 0, signer := true, writable := false }]
    #[.ascii "ok"]

/--
ATA `CreateIdempotent`：普通包装。
外层 0 是 payer（prelude 强制 acc0 signer+writable）。
内层按官方顺序：payer / ata / wallet / mint / System / Token。
callee 是外层账户 6。
-/
def ataCreateIdempotent : UInt64 :=
  invoke 6
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false },
      { acc := 4, signer := false, writable := false },
      { acc := 5, signer := false, writable := false }]
    #[.u8le 1]

/--
找当前 program id 下、一条 ASCII 种子的 canonical bump。
抽出器认这个名字，发射 `sol_try_find_program_address`。
宿主侧是不可约 stub，返回 0，不要当链上 bump 用。
完整 32B key / 多种子 / 指定 program id 本剖面 fail closed。
-/
@[irreducible] def findPda (seed : String) : UInt64 :=
  let _ := seed
  0

/--
当前 program id + 一条 ASCII 种子 + bump 是否是合法 PDA。
抽出后发射 `sol_create_program_address`。成功 0，失败 1。
宿主侧是不可约 stub，返回 0。完整 32B 地址本剖面 fail closed。
-/
@[irreducible] def checkPda (seed : String) (bump : UInt64) : UInt64 :=
  let _ := seed
  let _ := bump
  0

/--
给当前 program 下、种子 `"vault"` 的 PDA 开 16 字节。
PDA 用 `findPda` 的 bump 签字。space 本切片钉死。
-/
def createPda (lamports : UInt64) : UInt64 :=
  invokeSigned 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := true, writable := true }]
    #[.u32le 0, .u64le lamports, .u64le 16, .programId]
    "vault" (findPda "vault")

/-- 账户 0 的 lamports。只读；改余额走 `systemTransfer`。 -/
@[irreducible] def accLamports0 : UInt64 := 0

/-- 账户 0 owner 的第一个小端 `u64`。不是完整 32B。 -/
@[irreducible] def accOwner0 : UInt64 := 0

/-- 账户 0 `data_len`。只读。 -/
@[irreducible] def accDataLen0 : UInt64 := 0

/-- `NUM_ACCOUNTS`。只读；不开放 remaining accounts。 -/
@[irreducible] def accN : UInt64 := 0

/-- 账户 0 `is_signer`，0 或 1。不因此强制入口签名。 -/
@[irreducible] def isSigner0 : UInt64 := 0

/-- 账户 0 `is_writable`，0 或 1。 -/
@[irreducible] def isWritable0 : UInt64 := 0

/-- 账户 0 `is_executable`，0 或 1。 -/
@[irreducible] def isExecutable0 : UInt64 := 0

end SolanaLean.Runtime
