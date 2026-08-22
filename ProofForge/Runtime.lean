namespace ProofForge.Runtime

/--
当前 slot。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.slot`（偏移 0）。这是物理 slot，不是逻辑 block。

宿主侧是不可约 stub：定理把它当未指定的 `UInt64`，不要unfold成 0。
其余 Clock 字段本剖面 fail closed。
-/
@[irreducible] def clockSlot : UInt64 := 0

/--
当前 epoch。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.epoch`（偏移 16）。宿主侧是不可约 stub。
`epoch_start_timestamp` 本剖面 fail closed。
-/
@[irreducible] def clockEpoch : UInt64 := 0

/--
当前 unix 时间戳。抽出后发射 `sol_get_clock_sysvar`，读
`Clock.unix_timestamp`（偏移 32）为无符号 `u64`。
宿主侧是不可约 stub。有符号语义本剖面不建模。
-/
@[irreducible] def unixTime : UInt64 := 0

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
`system.allocateWithSeed`：给 `create_with_seed(acc0, "vault", program)` 开 `space` 字节。
种子本切片钉死。owner = 当前 program id。
外层：base s+w、派生账户 w、System。
-/
def systemAllocateWithSeed (space : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    -- bincode：u32 tag 9 || base32 || u64le len || seed || space || owner32。
    #[.u32le 9, .accKey 0, .u64le 5, .ascii "vault", .u64le space, .programId]

/--
`system.createAccountWithSeed`：给 `create_with_seed(acc0, "vault", program)` 转 `lamports` 并开 `space` 字节。
种子本切片钉死。owner = 当前 program id。付款人兼 base。
外层：funder=base s+w、派生账户 w、System。
-/
def systemCreateWithSeed (lamports space : UInt64) : UInt64 :=
  invoke 2
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, signer := false, writable := true }]
    -- bincode：u32 tag 3 || base32 || u64le len || seed || lamports || space || owner32。
    #[.u32le 3, .accKey 0, .u64le 5, .ascii "vault", .u64le lamports, .u64le space, .programId]

/--
`system.assignWithSeed`：把 `create_with_seed(acc0, "vault", program)` 的 owner 改成当前 program。
种子本切片钉死。
外层：base s+w、派生账户 w、System。
-/
def systemAssignWithSeed : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    -- bincode：u32 tag 10 || base32 || u64le len || seed || owner32。
    #[.u32le 10, .accKey 0, .u64le 5, .ascii "vault", .programId]

/--
`system.transferWithSeed`：从 `create_with_seed(acc0, "vault", program)` 转 `lamports` 到账户 2。
种子本切片钉死。from_owner = 当前 program id。
外层：base s+w、派生付款 w、收款 w、System。
-/
def systemTransferWithSeed (lamports : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false },
      { acc := 2, signer := false, writable := true }]
    -- bincode：u32 tag 11 || lamports || u64le len || seed || from_owner32。
    #[.u32le 11, .u64le lamports, .u64le 5, .ascii "vault", .programId]

/--
Token `InitializeMint2`：decimals 钉死 6，mint authority = acc0，freeze = None。
外层：authority s+w、mint w、Token。
-/
def tokenInitMint : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true }]
    -- packed：u8 tag 20 || u8 decimals || mint_authority32 || COption None。
    #[.u8le 20, .u8le 6, .accKey 0, .u8le 0]

/--
Token `SyncNative`：把 native token 账户的 amount 同步成底层 lamports。
外层：owner s+w、native 账户 w、Token。
-/
def tokenSyncNative : UInt64 :=
  invoke 2
    #[{ acc := 1, signer := false, writable := true }]
    #[.u8le 17]

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
Token `SetAuthority`：`AccountOwner`。新 owner = 外层账户 2。
外层 0 是当前 owner。内层：account w / current owner s。
-/
def tokenSetAccountAuthority : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 6, .u8le 2, .u8le 1, .accKey 2]

/--
Token 未检查 `Approve`（tag 4）。decimals 不进 data。
外层 0 是 owner。内层：source w / delegate r / owner s。
-/
def tokenApprove (amount : UInt64) : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u8le 4, .u64le amount]

/--
Token `InitializeMultisig2`（tag 19，不吃 Rent sysvar）。
本切片钉死 m=2，两个 signer = acc2 / acc3。
内层：multisig w / signer0 r / signer1 r。callee 是外层账户 4。
-/
def tokenInitMultisig : UInt64 :=
  invoke 4
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 3, signer := false, writable := false }]
    #[.u8le 19, .u8le 2]

/--
System `AdvanceNonceAccount`（tag 4）。
外层 0 是 nonce authority。内层：nonce w / recent blockhashes r / authority s。
callee 是外层账户 3（System）。
-/
def systemAdvanceNonce : UInt64 :=
  invoke 3
    #[{ acc := 1, signer := false, writable := true },
      { acc := 2, signer := false, writable := false },
      { acc := 0, signer := true, writable := false }]
    #[.u32le 4]

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
最近一次 CPI 的 8 字节返回。抽出后发射 `sol_get_return_data`。
宿主侧是不可约 stub。无 CPI / 长度不是 8 链上 Custom(1)。
完整 program id / 变长缓冲本剖面 fail closed。
-/
@[irreducible] def cpiReturn : UInt64 := 0

/--
Token `GetAccountDataSize`：普通包装。
外层 1 是 mint，callee 是外层账户 2。返回值走 `cpiReturn`。
-/
def tokenAccountSize : UInt64 :=
  let _ := invoke 2
    #[{ acc := 1, signer := false, writable := false }]
    #[.u8le 21]
  cpiReturn

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

/-- 账户 1 的 lamports。只读。 -/
@[irreducible] def accLamports1 : UInt64 := 0

/-- 账户 1 owner 的第一个小端 `u64`。不是完整 32B。 -/
@[irreducible] def accOwner1 : UInt64 := 0

/-- 账户 1 `data_len`。只读。 -/
@[irreducible] def accDataLen1 : UInt64 := 0

/-- 账户 1 `is_signer`，0 或 1。不因此强制入口签名。 -/
@[irreducible] def isSigner1 : UInt64 := 0

/-- 账户 1 `is_writable`，0 或 1。 -/
@[irreducible] def isWritable1 : UInt64 := 0

/-- 账户 1 `is_executable`，0 或 1。 -/
@[irreducible] def isExecutable1 : UInt64 := 0

/--
编译期 ASCII 字面量的 SHA-256。抽出器认这个名字，发射 `sol_sha256`。
返回 32 字节 digest 的第一个小端 `u64`。宿主侧是不可约 stub，返回 0。
完整 32B / 多切片 / 运行时缓冲 / blake3 / poseidon 本剖面 fail closed。
-/
@[irreducible] def sha256Lit (seed : String) : UInt64 :=
  let _ := seed
  0

/--
编译期 ASCII 字面量的 Keccak-256（Ethereum，不是 FIPS SHA3-256）。
抽出器认这个名字，发射 `sol_keccak256`。
返回 32 字节 digest 的第一个小端 `u64`。宿主侧是不可约 stub，返回 0。
完整 32B / 多切片 / 运行时缓冲 / blake3 / poseidon 本剖面 fail closed。
-/
@[irreducible] def keccak256Lit (seed : String) : UInt64 :=
  let _ := seed
  0

/--
账户 `acc` 公钥的第 `word` 个小端 `u64`（`word` 0..=3）。
`acc` / `word` 必须在抽出时是常量。`acc ≥ 1` 走 walk，不强制入口签名。
这不是 `signerKey0`：读 key 字不检查 `is_signer`。
账户 2+ / 运行时下标本剖面 fail closed。
-/
@[irreducible] def accKeyWord (acc word : UInt64) : UInt64 :=
  let _ := acc
  let _ := word
  0

/--
账户 `acc` owner 的第 `word` 个小端 `u64`（`word` 0..=3）。
`acc` / `word` 必须在抽出时是常量。`acc ≥ 1` 走 walk。
账户 2+ / 运行时下标本剖面 fail closed。
-/
@[irreducible] def accOwnerWord (acc word : UInt64) : UInt64 :=
  let _ := acc
  let _ := word
  0

/--
账户 `acc` 的 lamports。`acc` 必须在抽出时是常量，且 `acc ≤ 3`。
`acc ≥ 1` 走 walk。旧名 `accLamports0` / `accLamports1` 仍独立。
-/
@[irreducible] def accLamports (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `data_len`。`acc ≤ 3`，抽出时常量。 -/
@[irreducible] def accDataLen (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `is_signer`，0 或 1。不因此强制入口签名。 -/
@[irreducible] def isSigner (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `is_writable`，0 或 1。 -/
@[irreducible] def isWritable (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/-- 账户 `acc` 的 `is_executable`，0 或 1。 -/
@[irreducible] def isExecutable (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/--
账户 `acc` 公钥的第一个小端 `u64`。用到这个叶子的入口会检查该账户 `is_signer`。
`acc ≤ 3`。这不是 `tx.origin`。旧名 `signerKey0` 仍独立。
-/
@[irreducible] def signerKey (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/--
账户 `acc` 的 owner 是否是当前 program id。
抽出后比 32B。相等返回 0，不等返回 1。`acc ≤ 3`。
-/
@[irreducible] def ownerIsSelf (acc : UInt64) : UInt64 :=
  let _ := acc
  0

/--
`CALLER` 的低 8 字节：`and(caller(), 0xffffffffffffffff)`。
这是 20 字节地址的末 8 字节，不是完整 address，也不是 `tx.origin`。
SVM 发射器碰到这个叶子 fail closed。
-/
@[irreducible] def evmCaller : UInt64 := 0

/--
`NUMBER`，超出 `UInt64` 则 revert。这是 EVM block number，不是 Solana slot。
`clockSlot` 继续只表示 `Clock.slot`。
-/
@[irreducible] def evmBlockNumber : UInt64 := 0

@[irreducible] def evmTimestamp : UInt64 := 0
@[irreducible] def evmChainId : UInt64 := 0
/-- `ADDRESS` 低 8 字节。完整 20B 用 `evmSelfW*`。 -/
@[irreducible] def evmSelf : UInt64 := 0
@[irreducible] def evmCallValue : UInt64 := 0
@[irreducible] def evmSelfBalance : UInt64 := 0

/-- `CALLER` 20 字节拆成三叶：w0、w1 各 8 字节，w2 低 4 字节。小端装地址字节 0..19。 -/
@[irreducible] def evmCallerW0 : UInt64 := 0
@[irreducible] def evmCallerW1 : UInt64 := 0
@[irreducible] def evmCallerW2 : UInt64 := 0
@[irreducible] def evmSelfW0 : UInt64 := 0
@[irreducible] def evmSelfW1 : UInt64 := 0
@[irreducible] def evmSelfW2 : UInt64 := 0

/-- `eq(callvalue(), amt)`。入口因此 payable。宿主返回 amt。 -/
@[irreducible] def evmDeposit (amt : UInt64) : UInt64 := amt

/-- value CALL 到 20B 地址。失败应 revert。重入不进参考语义。宿主返回 amt。 -/
@[irreducible] def evmSendEth (w0 w1 w2 amt : UInt64) : UInt64 :=
  let _ := w0; let _ := w1; let _ := w2; amt

/-- LOG1 `Tipped(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogTipped (amt : UInt64) : UInt64 := amt

/-- LOG1 `Incremented(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogIncremented (amt : UInt64) : UInt64 := amt

/-- LOG1 `Transfer(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogTransfer (amt : UInt64) : UInt64 := amt

/-- LOG1 `Approval(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogApproval (amt : UInt64) : UInt64 := amt

/-- hashed `Map` 读 payload。缺席是 0。宿主返回 0。 -/
@[irreducible] def evmMapGetU64 (_base _key : UInt64) : UInt64 := 0

/-- hashed `Map` 写 payload，occ=1。宿主返回 val。 -/
@[irreducible] def evmMapSetU64 (_base _key val : UInt64) : UInt64 := val

/-- hashed `Map Addr20` 读。缺席是 0。 -/
@[irreducible] def evmMapGetAddr (_base w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0; let _ := w1; let _ := w2; 0

/-- hashed `Map Addr20` 写。 -/
@[irreducible] def evmMapSetAddr (_base w0 w1 w2 val : UInt64) : UInt64 :=
  let _ := w0; let _ := w1; let _ := w2; val

/-- pair-key hashed Map 读：owner 三叶 + spender 三叶。缺席是 0。 -/
@[irreducible] def evmMapGetPair
    (_base o0 o1 o2 s0 s1 s2 : UInt64) : UInt64 :=
  let _ := o0; let _ := o1; let _ := o2
  let _ := s0; let _ := s1; let _ := s2
  0

/-- pair-key hashed Map 写。 -/
@[irreducible] def evmMapSetPair
    (_base o0 o1 o2 s0 s1 s2 val : UInt64) : UInt64 :=
  let _ := o0; let _ := o1; let _ := o2
  let _ := s0; let _ := s1; let _ := s2
  val

/-- 封闭 ERC-20 `transfer`。callee 20B；失败 / 假返回 revert。宿主返回 amt。 -/
@[irreducible] def evmTokenTransfer
    (tw0 tw1 tw2 dw0 dw1 dw2 amt : UInt64) : UInt64 :=
  let _ := tw0; let _ := tw1; let _ := tw2
  let _ := dw0; let _ := dw1; let _ := dw2
  amt

/-- 封闭 ERC-20 `balanceOf(address(this))`。超 UInt64 应 revert。宿主返回 0。 -/
@[irreducible] def evmTokenBalanceOfSelf (tw0 tw1 tw2 : UInt64) : UInt64 :=
  let _ := tw0; let _ := tw1; let _ := tw2; 0

end ProofForge.Runtime
