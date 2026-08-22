namespace SolanaLean.Runtime

/--
当前 slot。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.slot`（偏移 0）。这是物理 slot，不是逻辑 block。

宿主侧是不可约 stub：定理把它当未指定的 `UInt64`，不要unfold成 0。
`unixTime` / 其余 Clock 字段本剖面 fail closed。
-/
@[irreducible] def clockSlot : UInt64 := 0

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
  | u32le (n : UInt64)
  | u64le (v : UInt64)
  | ascii (s : String)
  | programId
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
找当前 program id 下、一条 ASCII 种子的 canonical bump。
抽出器认这个名字，发射 `sol_try_find_program_address`。
宿主侧是不可约 stub，返回 0，不要当链上 bump 用。
完整 32B key / 多种子 / 指定 program id 本剖面 fail closed。
-/
@[irreducible] def findPda (seed : String) : UInt64 :=
  let _ := seed
  0

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
