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

协议入口和持久容器分两层：`Svm.EntryAdapter` 负责 target-owned wire decode、physical
account contract 与 raw/generated dispatch；`Svm.AccountStorage` 负责 fixed-capacity
account-resident map/queue/allocator/tree routine。source 语义组合两层后进入普通 CFG，
不为每个 Phoenix/Map/queue 功能增加顶层 Ops 或主 Emit case。

## Surface

- `clockSlot : UInt64` — 链上 `sol_get_clock_sysvar` → `Clock.slot`（物理 slot）。宿主 `@[irreducible]` stub，值是 0，不要 unfold。
- `clockEpoch : UInt64` — 同一条 syscall → `Clock.epoch`（偏移 16）。宿主 stub。
- `unixTime : UInt64` — 同一条 syscall → `Clock.unix_timestamp`@32，按无符号 u64。
- `slotsPerEpoch : UInt64` — 链上 `sol_get_epoch_schedule_sysvar` → 首 u64。宿主 stub。
- `rentExemption n` — 链上 `sol_get_rent_sysvar` → `lamports_per_byte * (128 + n)`。`n` 抽出时必须是常量。宿主 stub。
- `signerKey0 : UInt64` — 链上 `ACC0_KEY+0` 第一个小端 u64。用到该叶子的入口检查 `is_signer`。不是 `tx.origin`。
- `systemTransfer lamports` — 封闭 `system.transfer`。三账户 payer/recipient/System，`sol_invoke_signed_c`，无 signer seeds。
- EVM 叶（SVM 发射器一律拒）：`evmTimestamp` / `evmChainId` / `evmSelf` / `evmCallValue` / `evmSelfBalance` / `evmCaller`（低 8B）/ `evmBlockNumber` / Addr20 三叶 `evmCallerW0..W2`、`evmSelfW0..W2`（w2 仅低 4 字节）。
- `evmDeposit amt` — `eq(callvalue(), amt)`，入口变 payable。
- `evmSendEth w0 w1 w2 amt` — 组装 20B 后 value `CALL`，失败 revert。重入不进参考语义。
- `evmLogTipped amt` — LOG1 topic = keccak(`Tipped(uint64)`)。
- `evmMapGetU64` / `evmMapSetU64` — hashed `Map UInt64 UInt64`：`keccak256(key || base)` → occ + payload。
- `evmMapGetAddr` / `evmMapSetAddr` — hashed `Map Addr20 UInt64`：`keccak256(w0||w1||w2||base)`。
- `evmTokenTransfer` — 封闭 ERC-20 `transfer`；返回 0 或 32 非零。
- `evmTokenBalanceOfSelf` — `STATICCALL balanceOf(address(this))`，超 UInt64 revert。

`unixTime` 已支持。32B key / owner 可通过四个 `UInt64` word 读取；把它们当作一个
native 32-byte value、以及运行时动态拼装 CPI 仍 fail closed。不把 SVM 名译成 EVM opcode。
- `invoke programIx metas data` — 编译期钉死的 CPI。抽出认这个名字。
- `CpiMeta.expectedDataLen` — 可选的精确账户 data 长度；目标发射器在 CPI 前检查，错长以
  `Custom(1)` 退出。未设置时不改变既有 recipe / digest。
- `invokeSigned programIx metas data seed bump` — 同一条发射器，一组 signer seeds。
- `invokeSignedSeeds programIx metas data seeds bump` — 一组编译期定形的异构 signer seeds；支持 ASCII、state key 和静态 account key，运行时只提供 bump。
- 首个 CPI word `.selfEntry tag seed` — 声明唯一 raw self-entry；只接受 canonical seed PDA 的 readonly signer，认证后把完整 payload 作为一个 `sol_log_data` field 发布。
- `@[pf_svm_raw tag accountCount programAccount]` — 声明 target-owned packed 外部入口；tag
  是首个 u8，后续参数按 source 的 u8/u16/u32/u64 width 精确小端解码。adapter 静态消费
  account prefix，要求指定 physical account executable 且 key 等于当前 program id，然后把
  参数零扩展到普通 scalar locals。raw method 不得访问 managed `State`；协议持久数据必须走
  explicit `AccountStorage`。该 annotation 不产生 Op，raw instruction 不进入 generated IDL。
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
- `accDataWordSetAt acc base stride capacity index value` — 同一固定形状的账户内 u64
  写入 effect；只接受外部账户，要求 writable 且 owner 等于当前 program，并在 store 前
  检查账户数、`index < capacity` 和最终 `data_len`。连续 ignored writes 保持源码顺序；
  guarded `Except` success branch 也保留完整 effect sequence，不会被最终 state projection
  消除。失败以 `Custom(1)` 退出并由 SVM 回滚整条 instruction。它不返回或持久化
  pointer，也不把 transient heap 当账户 allocator。
- 该写入在 target 内部通过 `Svm.AccountStorage.Call` lowering：`Region/Field` 固定
  account/base/stride/capacity，显式记录 zero/one-based indexing，并统一提供 value
  traversal、geometry validation、canonical digest 与 read/write effect。主 SVM IR/emitter
  只看一个 generic storage bridge；allocator/tree/map/queue 的 bounded routine 应继续进入
  这一层，而不是增加新的顶层 store emitter。它是 account-resident zero-copy backend，
  不是 Rust transient heap 或普通 `HashMap`。
- `accDataParentPathValid acc linksBase parentBase stride capacity maxDepth index root bump` —
  static shape + 最多 64 步的账户内 parent walk；运行时 index/root/bump 先过 1-based
  envelope，每步验证 color、parent 和 parent→child reciprocity，root 外 cycle 到界返回 0。
  只用常量 memory；不是 whole-tree 或 free-list membership proof。target 内部表示为
  `AccountStorage.Query.parentPathValid`：query 自己携带 static fields、arity、read effects、
  geometry 与 canonicalization，主 value emitter 只做 generic query dispatch。
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
`Examples/RawEntry.lean` + `runtime-tests/solana/tests/raw_entry.rs`：同一 ELF 的 generated/raw
dispatch；`07 || u8 || u64` exact decode、bounded trailing account、program account authentication，
以及 wrong tag/length、missing signer、wrong/non-executable program fail-closed matrix。
`Projects/Phoenix.lean` + `runtime-tests/solana/tests/phoenix.rs`：认证状态账户上的 ask/bid 生命周期、双向撮合、费用/seat 结算、classic SPL Token 双 vault deposit/withdraw、未注册 take-only 双 Token 腿、严格 slot/time TIF、三种 self-trade、官方形状的 authenticated AuditLogHeader/event self-CPI，以及 vault/mint/Token program/self program/log PDA/writable/signer/owner 原子失败；跨四档逐样本 refinement 仍由 host/IR 门覆盖。
`Projects/PhoenixV1Profile.lean` + `runtime-tests/solana/tests/phoenix_v1_profile.rs`：Phoenix canonical owner/discriminant、12 个 capacity tuple/exact length、固定 scalar/allocator header，以及编译期固定 base/stride/capacity 的 bid root/child、32-edge parent path 和完整 bid/ask/trader tree/free-list partition；order tree 使用固定 4096-bit bitmap，trader tree 使用固定 8321-bit bitmap + 64-entry stack 并按原始 32-byte Pubkey 排序；bounded write surface 在 owner/writable/capacity/length 门后原位写 topology，五个 registration entry 再按 Sokoban exact 144-byte node layout 原子发布前五个 distinct trader，第三次覆盖 LL/LR/RR/RL rotation 和两个 no-fix 分支，第四次覆盖任意 canonical 三节点地址布局的 red-uncle recolor，第五次覆盖 black-parent 无修复和 black-uncle LL/LR/RL/RR rotation，失败不留下 detached node 或部分更新；最小 profile 84,944 B；短 header `Custom(1)`。
