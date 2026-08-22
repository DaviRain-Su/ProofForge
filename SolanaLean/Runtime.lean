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
通用 CPI / 动态 program id / remaining accounts 本剖面 fail closed。
-/
@[irreducible] def systemTransfer (lamports : UInt64) : UInt64 := lamports

end SolanaLean.Runtime
