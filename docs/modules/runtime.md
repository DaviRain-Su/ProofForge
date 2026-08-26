# Target runtimes

## Purpose

普通 Lean 名，抽出后变成 syscall / AccountInfo 读 / EVM opcode。不是新 DSL。

宿主 stub 按链分目录：

| 模块 | 拥有 |
|---|---|
| `ProofForge.Svm.Runtime` | sysvar、AccountInfo、CPI、PDA、hash syscall |
| `ProofForge.Evm.Runtime` | 环境 opcode、Addr20、LOG、hashed Map、封闭 ERC-20 |

根层不再提供混合 façade。合约必须按 target 明确 `open ProofForge.Svm.Runtime` 或
`open ProofForge.Evm.Runtime`，抽出器也只识别对应的具名 runtime。

## Surface

- `clockSlot : UInt64` — 链上 `sol_get_clock_sysvar` → `Clock.slot`（物理 slot）。宿主 `@[irreducible]` stub，值是 0，不要 unfold。
- `clockEpoch : UInt64` — 同一条 syscall → `Clock.epoch`（偏移 16）。宿主 stub。
- `unixTime : UInt64` — 同一条 syscall → `Clock.unix_timestamp`@32，按无符号 u64。
- `slotsPerEpoch : UInt64` — 链上 `sol_get_epoch_schedule_sysvar` → 首 u64。宿主 stub。
- `rentExemption n` — 链上 `sol_get_rent_sysvar` → `lamports_per_byte * (128 + n)`。`n` 抽出时必须是常量。宿主 stub。
- `signerKey0 : UInt64` — 链上 `ACC0_KEY+0` 第一个小端 u64。用到该叶子的入口检查 `is_signer`。不是 `tx.origin`。
- `systemTransfer lamports` — 封闭 `system.transfer`。三账户 payer/recipient/System，`sol_invoke_signed_c`，无 signer seeds。
- EVM 叶（SVM 发射器一律拒）：`evmTimestamp` / `evmChainId` / `evmSelf` / `evmCallValue` / `evmSelfBalance` / `evmCaller`（低 8B）/ `evmBlockNumber` / `structure Addr20`（w0/w1/w2，w2 仅低 4 字节）/ `evmCaller20` / `evmSelf20` / `structure UInt256`（w0 最低）/ `evmAdd256` / `evmSub256` / `evmMul256`。ABI 上 `Addr20` 是一个 `address`，`UInt256` 是一个 `uint256`。默认算术仍是 `UInt64`。
- `evmDeposit amt` — `eq(callvalue(), amt)`，入口变 payable。
- `evmSendEth dst amt` — `dst : Addr20`，组装 20B 后 value `CALL`，失败 revert。重入不进参考语义。
- `evmLogTipped amt` — LOG1 topic = keccak(`Tipped(uint64)`)。
- `evmMapGetU64` / `evmMapSetU64` — hashed `Map UInt64 UInt64`：`keccak256(key || base)` → occ + payload。
- `evmMapGetAddr` / `evmMapSetAddr` — hashed `Map Addr20 UInt64`：`keccak256(w0||w1||w2||base)`。key 是 `Addr20`。
- `evmTokenTransfer token dest amt` — 封闭 ERC-20 `transfer`；callee / dest 都是 `Addr20`；返回 0 或 32 非零。
- `evmTokenBalanceOfSelf token` — `STATICCALL balanceOf(address(this))`，超 UInt64 revert。

`unixTime` 已支持。32B key / owner 可通过四个 `UInt64` word 读取；把它们当作一个
native 32-byte value、以及运行时动态拼装 CPI 仍 fail closed。不把 SVM 名译成 EVM opcode。
- `invoke programIx metas data` — 编译期钉死的 CPI。抽出认这个名字。
- `CpiMeta.expectedDataLen` — 可选的精确账户 data 长度；目标发射器在 CPI 前检查，错长以
  `Custom(1)` 退出。未设置时不改变既有 recipe / digest。
- `invokeSigned programIx metas data seed bump` — 同一条发射器，一组 signer seeds。
- `invokeSignedSeeds programIx metas data seeds bump` — 一组编译期定形的异构 signer seeds；支持 ASCII、state key 和静态 account key，运行时只提供 bump。
- 首个 CPI word `.selfEntry tag seed` — 声明唯一 raw self-entry；只接受 canonical seed PDA 的 readonly signer，认证后把完整 payload 作为一个 `sol_log_data` field 发布。
- `let _ := invoke...` — 被忽略的 CPI 结果按效应顺序保留；无论普通或 signed、单条或多条，后续 state writes 都不能被抽取器吞掉。
- init 中的静态 CPI 在账户初始化写回前执行；非 CPI init effect fail closed，不再静默省略。
- `systemTransfer` / `invokeAcc1` / `systemCreate` / `createPda` / `systemAssign` / `systemAllocate` / `systemAllocateWithSeed` / `systemCreateWithSeed` / `systemAssignWithSeed` / `systemTransferWithSeed` / `systemAdvanceNonce` / `tokenInitMint` / `tokenSyncNative` / `tokenTransferChecked` / `token2022TransferChecked` / `tokenTransferCheckedIx` / `tokenTransferCheckedSignedIx` / `tokenMintToChecked` / `tokenBurnChecked` / `tokenInitAccount` / `tokenCloseAccount` / `tokenApproveChecked` / `tokenApprove` / `tokenFreezeAccount` / `tokenThawAccount` / `tokenSetMintAuthority` / `tokenSetAccountAuthority` / `tokenRevoke` / `tokenInitMultisig` / `tokenAccountSize` / `memoWrite` / `ataCreateIdempotent` — 普通 Lean 包装，按 Runtime 命名空间统一展开成同一组 `invoke` / `invokeSigned` / `invokeSignedSeeds` 原语，不维护 recipe 名白名单。Token-2022 包装只接收 82B mint / 165B token account。
- `accLamports0` / `accOwner0` / `accDataLen0` / `accN` — 账户 0 只读 header。
- `isSigner0` / `isWritable0` / `isExecutable0` — 账户 0 旗，0 或 1；不强制入口签名。
- `accLamports1` / `accOwner1` / `accDataLen1` / `isSigner1` / `isWritable1` / `isExecutable1` — 账户 1 只读 header。读到这些叶子就 walk，不强制 acc0 signer。
- `findPda seed` — 当前 program id + 一条 ASCII 种子；链上 `sol_try_find_program_address`，返回 bump。
- `findPdaSeeds seeds` — 当前 program id + 编译期定形的异构 seed 列表；返回 canonical bump。
- `checkPdaSeeds account seeds` — 推导 canonical PDA 并比较目标账户完整 32-byte key；相等 0，否则 1。
- `sha256Lit seed` — 编译期 ASCII 字面量；链上 `sol_sha256`，返回 digest 第一个小端 u64。完整 32B / 多切片 / blake3 fail closed。
- `keccak256Lit seed` — 同形；链上 `sol_keccak256`（Ethereum Keccak，不是 FIPS SHA3-256）。blake3 / poseidon 仍 FC。
- `accKeyWord acc word` / `accOwnerWord acc word` — 账户 `acc < IR.maxTxAccountLocks` 的 32B key / owner 第 `word`∈{0..=3} 个小端 u64。抽出时必须是常量。`acc≥1` 走 walk，不强制入口签名。不是 `signerKey0`。
- `accDataWord acc word` — 账户 data 第 `word` 个小端 u64；账户和 word 均为编译期常量。发射器在形成 data pointer 前检查 `data_len ≥ 8*(word+1)`，短账户 `Custom(1)`。
- `accDataWordAt acc base stride capacity index` — `acc/base/stride/capacity` 编译期固定，零基 `index` 可运行时选择；发射器先检查 `index < capacity`，再检查计算出的 word 位于 `data_len` 内。只做账户内 zero-copy u64 读取，不分配或复制动态数组。
- `accLamports` / `accDataLen` / `isSigner` / `isWritable` / `isExecutable` `acc` — 账户 `acc < IR.maxTxAccountLocks`（官方当前 64）header。旧名 `accLamports0` 等仍独立。
- `signerKey acc` — 该账户 key 首 u64；入口强制该账户 `is_signer`。旧名 `signerKey0` 仍独立。
- `ownerIsSelf acc` — owner 32B 是否等于当前 program id；相等 0 / 不等 1。
- `checkPda seed bump` — 旧的一条 ASCII 种子接口；链上只检查 bump 能否导出合法 PDA，成功 0 / 失败 1，不接收也不比较目标账户。需要完整 32B account-key 相等时使用 `checkPdaSeeds`。
- `cpiReturn` — 最近一次 CPI 的 8 字节返回；`sol_get_return_data`。长度不是 8 → Custom(1)。
- `tokenAccountSize` — Token GetAccountDataSize；返回值走 `cpiReturn`。

把完整 32B key 当作单一值、运行时拼的 CPI（动态 program id / remaining accounts）
fail closed。常量 `acc < 64` 的账户 header 和四个 key / owner word 已开；编译期钉死的
`invoke`、`unixTime` 和 `Bool` 字段也已开。


## Tests

`Examples/Clock.lean` + `runtime-tests/solana/tests/clock.rs`：两次 `warp_to_slot` 读 slot / epoch、`stamp` 写回、`key0` 缺 signer → `Custom(1)`。
`Examples/Info.lean` + `runtime-tests/solana/tests/info.rs`：余额 / owner 首 u64 / data_len / NUM_ACCOUNTS / 三旗；只读不改账户数据。
`Examples/Peer.lean` + `runtime-tests/solana/tests/peer.rs`：账户 1 的 lamports / owner 首 u64 / data_len / 三旗；缺第二账户 → `Custom(1)`。
`Examples/Hash.lean` + `runtime-tests/solana/tests/hash.rs`：`sha256Lit "vault"` / `"ok"` / `""` 的首 u64 与宿主 `sha2` 一致。
`Examples/Keccak.lean` + `runtime-tests/solana/tests/keccak.rs`：`keccak256Lit "vault"` / `"ok"` / `""` 的首 u64 与宿主 `sha3::Keccak256` 一致。
`Examples/Keys.lean` + `runtime-tests/solana/tests/keys.rs`：账户 0/1 的 key / owner 按字读与宿主 `Pubkey` 一致；读 key 字不强制 signer；缺第二账户 → `Custom(1)`。
`Examples/Trio.lean` + `runtime-tests/solana/tests/trio.rs`：账户 2 header / key 字；`signerKey 1` 缺签名 Custom(1)；`ownerIsSelf 0` = 0、异 owner = 1。
`Examples/Gate.lean` + `runtime-tests/solana/tests/gate.rs`：Bool 字段 1 字节；`unixTime` 跟 `clock.unix_timestamp`。
`Examples/Nonce.lean` + `runtime-tests/solana/tests/nonce.rs`：AdvanceNonceAccount 缺 signer → `Custom(1)`。
`Examples/TokenOwner.lean` + `runtime-tests/solana/tests/token_owner.rs`：SetAuthority AccountOwner 改 owner；Approve 写 delegate。
`Examples/TokenMs.lean` + `runtime-tests/solana/tests/token_ms.rs`：InitializeMultisig2 m=2 n=2；未使用的 payer 不要求 signer。
`Examples/Pda.lean` + `runtime-tests/solana/tests/pda.rs`：`findPda "vault"` 的 bump 与宿主 `find_program_address` 一致；`checkPda` 对 canonical bump 返回 0，对 bump 0 返回 1。
`Examples/Signed.lean` + `runtime-tests/solana/tests/signed.rs`：canonical bump 签字成功；bump 0 失败。
`Examples/SysAlloc.lean` + `runtime-tests/solana/tests/sys_alloc.rs`：allocate 把空 System 账户扩到 16 字节；assign 把 owner 改成当前 program；缺 signer → `Custom(1)`。
`Examples/TokenAcc.lean` + `runtime-tests/solana/tests/token_acc.rs`：InitializeAccount3 写 owner/mint 且不要求 owner signer；CloseAccount 把 0 余额账户 lamports 退回 dest，并要求 owner signer。
`Examples/Memo.lean` + `runtime-tests/solana/tests/memo.rs`：CPI 进官方 Memo v3，写字面量 `"ok"`；缺 signer → `Custom(1)`。
`Examples/CreatePda.lean` + `runtime-tests/solana/tests/create_pda.rs`：给 `"vault"` PDA 开 16 字节；bump 0 失败。
`Examples/TokenApprove.lean` + `runtime-tests/solana/tests/token_approve.rs`：ApproveChecked 写 delegate + delegated_amount；缺 signer → `Custom(1)`。
`Examples/TokenFreeze.lean` + `runtime-tests/solana/tests/token_freeze.rs`：Freeze 把 state 写成 Frozen；Thaw 写回 Initialized；缺 signer → `Custom(1)`。
`Examples/TokenAuth.lean` + `runtime-tests/solana/tests/token_auth.rs`：SetAuthority 把 mint_authority 改成 acc2；Revoke 清掉 delegate；缺 signer → `Custom(1)`。
`Examples/Epoch.lean` + `runtime-tests/solana/tests/epoch.rs`：默认 `slots_per_epoch` 432000；改 schedule 后再读一次。
`Examples/TokenSize.lean` + `runtime-tests/solana/tests/token_size.rs`：GetAccountDataSize 返回 165；未使用的 dummy 不要求 signer。
`Examples/SysSeed.lean` + `runtime-tests/solana/tests/sys_seed.rs`：AllocateWithSeed 开 16 字节；CreateAccountWithSeed 转 lamports；AssignWithSeed 改 owner；缺 signer → `Custom(1)`。
`Examples/SysXfer.lean` + `runtime-tests/solana/tests/sys_xfer.rs`：TransferWithSeed 从 `create_with_seed(acc0, "vault", program)` 转 lamports；缺 signer → `Custom(1)`。
`Examples/TokenMint2.lean` + `runtime-tests/solana/tests/token_mint2.rs`：InitializeMint2 写 decimals=6、authority=acc0；authority 不要求 signer。
`Examples/TokenNative.lean` + `runtime-tests/solana/tests/token_native.rs`：SyncNative 把 native 账户 amount 同步成多余 lamports；owner 不要求 signer。
`Examples/Token2022.lean` + `runtime-tests/solana/tests/token_2022.rs`：Token-2022 base-layout TransferChecked 精确转账；缺 signer、transfer-fee mint、enabled transfer-hook mint 均原子失败。
`Examples/Nested.lean` + `runtime-tests/solana/tests/nested.rs`：嵌套 projection 更新只写目标叶。
`Examples/Book.lean` + `runtime-tests/solana/tests/book.rs`：有界循环与运行时 Vector 下标写在链上执行。
`Examples/Lang.lean` + `runtime-tests/solana/tests/lang.rs`：位运算、mod-64 移位及 state-carrying fold 的链上语义。
`Examples/Tree.lean` + `runtime-tests/solana/tests/tree.rs`：红黑树插入布局，以及 black-leaf 删除 fixup、free-list 回收和精确地址复用。
`Examples/Seat.lean` + `runtime-tests/solana/tests/seat.rs`：PDA bump view、canonical seat PDA 创建、base/quote Token vault 初始化，以及 signer/writable 原子失败。
`Examples/SelfLog.lean` + `runtime-tests/solana/tests/self_log.rs`：当前 program id 的 signed self-CPI，canonical `"log"` PDA raw 入口、packed Borsh integer words、续段状态写回，以及 signer/writable/tag/key 失败矩阵。
`Projects/Phoenix.lean` + `runtime-tests/solana/tests/phoenix.rs`：认证状态账户上的 ask/bid 生命周期、双向撮合、费用/seat 结算、classic SPL Token 双 vault deposit/withdraw、未注册 take-only 双 Token 腿、严格 slot/time TIF、三种 self-trade、官方形状的 authenticated AuditLogHeader/event self-CPI，以及 vault/mint/Token program/self program/log PDA/writable/signer/owner 原子失败；跨四档逐样本 refinement 仍由 host/IR 门覆盖。
`Projects/PhoenixV1Profile.lean` + `runtime-tests/solana/tests/phoenix_v1_profile.rs`：Phoenix canonical owner/discriminant、12 个 capacity tuple/exact length、固定 scalar/allocator header，以及编译期固定 base/stride/capacity 的 bid root/直接 child zero-copy 读取；最小 profile 84,944 B；短 header `Custom(1)`。
