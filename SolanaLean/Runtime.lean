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

/--
封闭 `system.transfer`。抽出器认这个名字，发射固定三账户 CPI：
payer / recipient / System Program，内层 `u32le(2) || u64le(lamports)`，
`sol_invoke_signed_c`，无 signer seeds。

宿主侧是不可约 stub，返回传入的 `lamports`，不要当链上余额用。
这是编译期钉死的 `invoke` 特化。运行时拼 program id / remaining accounts 仍 fail closed。
-/
@[irreducible] def systemTransfer (lamports : UInt64) : UInt64 := lamports

/--
编译期钉死的 `invoke`：CPI 到外层账户 1，空 metas、空 data。
program id 来自账户 1 的 key，不是写死 System。
-/
@[irreducible] def invokeAcc1 : UInt64 := 0

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
