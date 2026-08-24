# Backlog

补全依据：[analysis/authority.md](analysis/authority.md)。
缺口阶段：[analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)。

## 已做

- S0–S5：普通 Lean Counter 竖切到 Mollusk
- 多字段 UInt64；从 `init` 返回 structure 收字段；Pair `.so` / Mollusk 4/4
- Loader 偏移按 `dataLen` 算
- `@[pf_entry]` + `#pf_build`；按名 disc；Counter 同程序 decrement
- 任意 `ite`；checked mul/div/mod；`=` `≠` 比较；Counter scale/divide/modulo/nonzero
- `IR.digestHex`（FNV-1a 64）；`#pf_build` 抽出与 fixture 必须同一 digest
- 带类型字段表：`UInt8/16/32/64` + `Option UInt64` 双叶；Flag / Maybe Mollusk
- disc / layout marker 本机 SHA-256，不再挂名表
- 定长 `Vector UInt64 n` 展开成连续槽；Window Mollusk；不定长 Array fail closed
- 无 payload 枚举作 tag；Phase Mollusk；带 payload 仍 fail closed。Bool 已在 L4-034 开成 1 字节 u8-le
- 多个 init；`init` paramCount 按 λ 算；Pair `initBoth` / `getRight`
- `Option UInt64` match 读 payload；Maybe.getValue Mollusk
- 单字段用户 inductive 作 tag+payload；Choice Mollusk
- `clockSlot` + 账户 0 `signerKey0`；Clock Mollusk
- 封闭 `system.transfer`；三账户虚地址 walk + `sol_invoke_signed_c`；Transfer Mollusk
- 编译期钉死的 `invoke`；`systemTransfer` / `invokeAcc1` 共用发射器；Ping Mollusk
- 账户 0 AccountInfo 只读叶子（lamports / owner 首 u64 / data_len / NUM_ACCOUNTS / 三旗）；Info Mollusk
- 表层通用 `invoke`；`systemTransfer` / `invokeAcc1` 是普通包装；Call Mollusk
- `findPda` 一条 ASCII 种子 + 当前 program id；返回 bump；Pda Mollusk
- `invokeSigned` 一组 ASCII 种子 + bump；Signed Mollusk（错 bump 失败）
- `systemCreate` 普通包装；owner = 当前 program id；Create Mollusk
- `tokenTransferChecked` 普通包装；Token `TransferChecked`；TokenXfer Mollusk
- `ataCreateIdempotent` 普通包装；ATA CreateIdempotent；Ata Mollusk
- `rentExemption` 叶子；`sol_get_rent_sysvar` × `(128+n)`；Rent Mollusk
- `tokenMintToChecked` / `tokenBurnChecked`；TokenMint Mollusk
- `systemAssign` / `systemAllocate`；SysAlloc Mollusk
- `tokenInitAccount` / `tokenCloseAccount`；TokenAcc Mollusk
- `memoWrite`；Memo Mollusk
- `createPda`；CreatePda Mollusk
- `checkPda`；Pda Mollusk 验证 bump
- `tokenApproveChecked` / `tokenFreezeAccount` / `tokenThawAccount`；TokenApprove / TokenFreeze Mollusk
- `clockEpoch`；Clock Mollusk 两次 warp 跨 epoch
- `tokenSetMintAuthority` / `tokenRevoke`；TokenAuth Mollusk
- `slotsPerEpoch`；Epoch Mollusk 改 schedule
- `tokenAccountSize` / `cpiReturn`；TokenSize Mollusk 返回 165
- `systemAllocateWithSeed`；SysSeed Mollusk
- `systemCreateWithSeed`；SysSeed Mollusk 转 lamports
- `systemAssignWithSeed`；SysSeed Mollusk 改 owner
- `systemTransferWithSeed`；SysXfer Mollusk
- `tokenInitMint`；TokenMint2 Mollusk
- `tokenSyncNative`；TokenNative Mollusk
- 账户 1 只读叶子；Peer Mollusk
- `sha256Lit`；Hash Mollusk
- 32B key / owner 按字读；Keys Mollusk
- `keccak256Lit`；Keccak Mollusk
- 账户下标叶子收口；Trio Mollusk
- Bool / `unixTime` / nonce prelude / SetAuthority owner / Approve / Multisig2；Gate / Nonce / TokenOwner / TokenMs Mollusk
- Core control/schema 与 `Svm.Ops/IR/Runtime`、`Evm.Ops/IR/Runtime` 分层；Extract.IR 是唯一 typed target-extension 组合点
- 嵌套 structure / `Vector Nested n` 摊平；Nested / Tree Mollusk
- Phoenix bounded N=4 双边书、四 seat registry、逐 seat 结算、TIF、费用和 typed event batch
- SVM 47 个 registry program 各有 runtime test 文件；EVM 12 个 registry program 全进 Anvil 总入口
- 审查修复：分支 fallthrough、state owner/marker、常量求值、Option identity、窄叶、Nat.sub、移位、EVM init、未知 CPI、solc 诊断

## 当前状态

- `lake build Tests` 当前 181 jobs；65 个 imported test modules 含 723 个 `#guard`。
- SVM registry 47 个程序 / 47 个 Mollusk integration 文件；这表示每个程序有门，不表示每个入口都已有链上矩阵。
- EVM registry 12 个程序；Counter / Pair / Flag / Maybe / Context / TipJar / Lang / Vault / Ownable / Token / Window / Phase 的 Anvil 总门 12/12。
- Phoenix Mollusk 已覆盖 ask/bid 挂单、reduce、双向撮合、费用收取、withdraw/evict、严格 slot/time TIF、三种 self-trade 及签名/owner 原子失败；跨四档逐样本 refinement 仍由 host/IR 门承担。
- `l5-003` 抽取已完成，Seat 的 CPI runtime 成功路径与双 vault 尚未完成。
- `l5-004` Token-2022 classic-compatible program-id 切片尚未开始。
- `l5-005` 已完成；任务状态已同步为 done。

## 按优先级继续

### P0：现有语义的链上闭环

1. Seat Mollusk：`openSeat` / `openBase` CPI 成功路径及权限负例。
2. Phoenix 双 vault Token CPI adapter，把 deposit/withdraw/未注册 take-only 的占位结算接到真实账户。
3. `AuditLogHeader` + Borsh wire event + `Log` self-CPI recorder。

### P1：通用后端边界

1. 显式 basic-block CFG、local CSE 和共享 block；先缩小 Phoenix，不在合约或 emitter 加特判。
2. Solanalib control-flow / instruction correspondence；当前只覆盖 bounded checked arithmetic + static store。
3. 新 target 的注册边界；现在新增 target 仍需在 `Extract.IR` 增加 typed extension case 和 conversion。

### P2：扩大产品面

1. `l5-004` Token-2022 指令 0–24 的 program-id 切片；hook / fee mint 在 TLV / remaining accounts 之前继续 fail closed。
2. Phoenix 动态 trader/order 红黑树、删除 fixup 和非固定 N；当前 Phoenix 仍是 bounded N=4 有序投影。
3. 固定长度 32-byte / u128 / Borsh protocol types；当前 Pubkey 和 client id 使用 `UInt64` limbs。
4. GitHub CI：串行 Lake、SVM Mollusk、EVM Anvil。

## 明确保持 fail closed

- 搬 PF 前端 / `HandlerIR.mk` 私有构造、新 DSL、无约束 Lean、FFI→asm。
- `.so` / loader / 全 SVM refinement 与公网部署声明。
- 运行时 program id、变长 data、运行时 remaining accounts；编译期钉死的 CPI 已开。
- Token-2022 transfer hook / fee / TLV extension，直到对应账户模型落地。
- feature-gated blake3 / poseidon / curve25519 / alt_bn128 / `sol_get_sysvar`。
- 把完整 32B key 当作现有 8B return-data ABI 的单一返回值。

历史 SDK 清单和阶段分析保留作设计记录，不再当当前 backlog：
[sdk-surface.md](analysis/sdk-surface.md)、[gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)、
[remaining-surface.md](analysis/remaining-surface.md)。
