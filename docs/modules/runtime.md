# SolanaLean.Runtime

## Purpose

普通 Lean 名，抽出后变成 syscall / AccountInfo 读。不是新 DSL。

## Surface

- `clockSlot : UInt64` — 链上 `sol_get_clock_sysvar` → `Clock.slot`（物理 slot）。宿主 `@[irreducible]` stub，值是 0，不要 unfold。
- `signerKey0 : UInt64` — 链上 `ACC0_KEY+0` 第一个小端 u64。用到该叶子的入口检查 `is_signer`。不是 `tx.origin`。
- `invoke programIx metas data` — 编译期钉死的 CPI。抽出认这个名字。
- `systemTransfer` / `invokeAcc1` — 普通 Lean 包装，展开成同一条 `invoke`。
- `accLamports0` / `accOwner0` / `accDataLen0` / `accN` — 账户 0 只读 header。
- `isSigner0` / `isWritable0` / `isExecutable0` — 账户 0 旗，0 或 1；不强制入口签名。

`unixTime`、完整 32B key、独立 caller 账户、运行时拼的 CPI（动态 program id / remaining accounts）fail closed。编译期钉死的 `invoke` 已开。

## Tests

`Examples/Clock.lean` + `runtime-tests/solana/tests/clock.rs`：两次 `warp_to_slot`、`stamp` 写回、`key0` 缺 signer → `Custom(1)`。
`Examples/Info.lean` + `runtime-tests/solana/tests/info.rs`：余额 / owner 首 u64 / data_len / NUM_ACCOUNTS / 三旗；只读不改账户数据。
