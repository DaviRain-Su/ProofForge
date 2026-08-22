# SolanaLean.Runtime

## Purpose

普通 Lean 名，抽出后变成 syscall / AccountInfo 读。不是新 DSL。

## Surface

- `clockSlot : UInt64` — 链上 `sol_get_clock_sysvar` → `Clock.slot`（物理 slot）。宿主 `@[irreducible]` stub，值是 0，不要 unfold。
- `clockEpoch : UInt64` — 同一条 syscall → `Clock.epoch`（偏移 16）。宿主 stub。
- `slotsPerEpoch : UInt64` — 链上 `sol_get_epoch_schedule_sysvar` → 首 u64。宿主 stub。
- `rentExemption n` — 链上 `sol_get_rent_sysvar` → `lamports_per_byte * (128 + n)`。`n` 抽出时必须是常量。宿主 stub。
- `signerKey0 : UInt64` — 链上 `ACC0_KEY+0` 第一个小端 u64。用到该叶子的入口检查 `is_signer`。不是 `tx.origin`。
- `invoke programIx metas data` — 编译期钉死的 CPI。抽出认这个名字。
- `invokeSigned programIx metas data seed bump` — 同一条发射器，一组 signer seeds。
- `systemTransfer` / `invokeAcc1` / `systemCreate` / `createPda` / `systemAssign` / `systemAllocate` / `systemAllocateWithSeed` / `tokenTransferChecked` / `tokenMintToChecked` / `tokenBurnChecked` / `tokenInitAccount` / `tokenCloseAccount` / `tokenApproveChecked` / `tokenFreezeAccount` / `tokenThawAccount` / `tokenSetMintAuthority` / `tokenRevoke` / `tokenAccountSize` / `memoWrite` / `ataCreateIdempotent` — 普通 Lean 包装，展开成同一条 `invoke` / `invokeSigned`。
- `accLamports0` / `accOwner0` / `accDataLen0` / `accN` — 账户 0 只读 header。
- `isSigner0` / `isWritable0` / `isExecutable0` — 账户 0 旗，0 或 1；不强制入口签名。
- `findPda seed` — 当前 program id + 一条 ASCII 种子；链上 `sol_try_find_program_address`，返回 bump。
- `checkPda seed bump` — 同一组种子 + bump；链上 `sol_create_program_address`，成功 0 / 失败 1。完整 32B 地址 fail closed。
- `cpiReturn` — 最近一次 CPI 的 8 字节返回；`sol_get_return_data`。长度不是 8 → Custom(1)。
- `tokenAccountSize` — Token GetAccountDataSize；返回值走 `cpiReturn`。

`unixTime`、完整 32B key、独立 caller 账户、运行时拼的 CPI（动态 program id / remaining accounts）fail closed。编译期钉死的 `invoke` 已开。

## Tests

`Examples/Clock.lean` + `runtime-tests/solana/tests/clock.rs`：两次 `warp_to_slot` 读 slot / epoch、`stamp` 写回、`key0` 缺 signer → `Custom(1)`。
`Examples/Info.lean` + `runtime-tests/solana/tests/info.rs`：余额 / owner 首 u64 / data_len / NUM_ACCOUNTS / 三旗；只读不改账户数据。
`Examples/Pda.lean` + `runtime-tests/solana/tests/pda.rs`：`findPda "vault"` 的 bump 与宿主 `find_program_address` 一致；`checkPda` 对 canonical bump 返回 0，对 bump 0 返回 1。
`Examples/Signed.lean` + `runtime-tests/solana/tests/signed.rs`：canonical bump 签字成功；bump 0 失败。
`Examples/SysAlloc.lean` + `runtime-tests/solana/tests/sys_alloc.rs`：allocate 把空 System 账户扩到 16 字节；assign 把 owner 改成当前 program；缺 signer → `Custom(1)`。
`Examples/TokenAcc.lean` + `runtime-tests/solana/tests/token_acc.rs`：InitializeAccount3 写 owner/mint；CloseAccount 把 0 余额账户 lamports 退回 dest；缺 signer → `Custom(1)`。
`Examples/Memo.lean` + `runtime-tests/solana/tests/memo.rs`：CPI 进官方 Memo v3，写字面量 `"ok"`；缺 signer → `Custom(1)`。
`Examples/CreatePda.lean` + `runtime-tests/solana/tests/create_pda.rs`：给 `"vault"` PDA 开 16 字节；bump 0 失败。
`Examples/TokenApprove.lean` + `runtime-tests/solana/tests/token_approve.rs`：ApproveChecked 写 delegate + delegated_amount；缺 signer → `Custom(1)`。
`Examples/TokenFreeze.lean` + `runtime-tests/solana/tests/token_freeze.rs`：Freeze 把 state 写成 Frozen；Thaw 写回 Initialized；缺 signer → `Custom(1)`。
`Examples/TokenAuth.lean` + `runtime-tests/solana/tests/token_auth.rs`：SetAuthority 把 mint_authority 改成 acc2；Revoke 清掉 delegate；缺 signer → `Custom(1)`。
`Examples/Epoch.lean` + `runtime-tests/solana/tests/epoch.rs`：默认 `slots_per_epoch` 432000；改 schedule 后再读一次。
`Examples/TokenSize.lean` + `runtime-tests/solana/tests/token_size.rs`：GetAccountDataSize 返回 165；缺 signer → `Custom(1)`。
`Examples/SysSeed.lean` + `runtime-tests/solana/tests/sys_seed.rs`：AllocateWithSeed 给 `create_with_seed(acc0, "vault", program)` 开 16 字节；缺 signer → `Custom(1)`。
