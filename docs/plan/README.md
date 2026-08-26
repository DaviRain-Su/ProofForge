# 交付计划

分析：[analysis/v0-slice.md](analysis/v0-slice.md) · [analysis/authority.md](analysis/authority.md) · [analysis/gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)

任务：

| ID | 状态 | 内容 |
|---|---|---|
| [skel-001](tasks/skel-001.md) | done | Lake 骨架 + Counter 参考语义 |
| [prof-001](tasks/prof-001.md) | done | Profile 传递闭包 |
| [extr-001](tasks/extr-001.md) | done | Expr 抽出 |
| [lowr-001](tasks/lowr-001.md) | done | 本仓 Counter sBPF 发射（对齐 PF StateCell） |
| [asmb-001](tasks/asmb-001.md) | done | sbpf + Mollusk 4/4 |

| [gen-001](tasks/gen-001.md) | done | Expr → checkedAdd 操作序列 |
| [gen-002](tasks/gen-002.md) | done | 按 Op 选择 handler 体 |
| [gen-003](tasks/gen-003.md) | done | 按 Val 生成 load |
| [gen-004](tasks/gen-004.md) | done | 单账户 UInt64 表达式编译器 + decrement |
| [fld-001](tasks/fld-001.md) | done | 多字段 UInt64 布局 + Pair |
| [fld-002](tasks/fld-002.md) | done | 从 structure 收字段 + Pair .so |
| [l1-001](tasks/l1-001.md) | done | 属性入口 + 按名 disc + 多 mutate |
| [l1-002](tasks/l1-002.md) | done | 任意 ite + checked mul/div/mod |
| [l1-003](tasks/l1-003.md) | done | Program 内容寻址 digest |
| [l2-001](tasks/l2-001.md) | done | 带类型字段表 + Option 双叶 |
| [l2-002](tasks/l2-002.md) | done | 定长 Vector UInt64 n |
| [l2-003](tasks/l2-003.md) | done | 本机算出 disc 与 layout marker |
| [l2-004](tasks/l2-004.md) | done | 无 payload 枚举作 tag |
| [l3-001](tasks/l3-001.md) | done | init 写全字段 + view 任意叶子 |
| [l3-002](tasks/l3-002.md) | done | Option match 读 payload |
| [l3-003](tasks/l3-003.md) | done | 单字段用户 inductive 作 tag+payload |
| [l4-001](tasks/l4-001.md) | done | clock.slot + account-0 signer key |
| [l4-002](tasks/l4-002.md) | done | 封闭 system.transfer |
| [evm-001](tasks/evm-001.md) | done | Evm.IR + keccak selector |
| [evm-002](tasks/evm-002.md) | done | Ops → Yul |
| [evm-003](tasks/evm-003.md) | done | `#pf_evm_build` + locked solc |
| [evm-004](tasks/evm-004.md) | done | Anvil ctor / increment / get / overflow |
| [evm-005](tasks/evm-005.md) | done | Pair 多 slot + Anvil |
| [evm-006](tasks/evm-006.md) | done | 窄槽 + Option 双叶 |
| [evm-007](tasks/evm-007.md) | done | Darwin / Linux 共用 Anvil 入口 |
| [evm-008](tasks/evm-008.md) | done | 独立 EVM runtime 叶子 |
| [e-rt-001](tasks/e-rt-001.md) | done | 环境 + value + Addr20 + ETH + event |
| [e-lang-001](tasks/e-lang-001.md) | done | 位运算 / for / 下标 / ABI / tuple / 命名 revert |
| [e-asset-001](tasks/e-asset-001.md) | done | hashed Map + 封闭 ERC-20 |
| [e-own-001](tasks/e-own-001.md) | done | Ownable + 通用 event + allowance |
| [e-tok-001](tasks/e-tok-001.md) | done | 封闭 ERC-20 形：余额 + 真额度扣减 |
| [l4-003](tasks/l4-003.md) | done | 编译期钉死的 invoke 原语 |
| [l4-004](tasks/l4-004.md) | done | 账户 0 AccountInfo 只读叶子 |
| [l4-005](tasks/l4-005.md) | done | 表层通用 invoke |
| [l4-006](tasks/l4-006.md) | done | findPda 返回 bump |
| [l4-007](tasks/l4-007.md) | done | invokeSigned 一组种子 |
| [l4-008](tasks/l4-008.md) | done | System createAccount |
| [l4-009](tasks/l4-009.md) | done | Token TransferChecked |
| [l4-010](tasks/l4-010.md) | done | ATA CreateIdempotent |
| [l4-011](tasks/l4-011.md) | done | rentExemption |
| [l4-012](tasks/l4-012.md) | done | Token mint / burn |
| [l4-013](tasks/l4-013.md) | done | System assign / allocate |
| [l4-014](tasks/l4-014.md) | done | Token init / close |
| [l4-015](tasks/l4-015.md) | done | Memo write |
| [l4-016](tasks/l4-016.md) | done | createPda |
| [l4-017](tasks/l4-017.md) | done | checkPda |
| [l4-018](tasks/l4-018.md) | done | Token approve / freeze / thaw |
| [l4-019](tasks/l4-019.md) | done | clockEpoch |
| [l4-020](tasks/l4-020.md) | done | Token SetAuthority / Revoke |
| [l4-021](tasks/l4-021.md) | done | slotsPerEpoch |
| [l4-022](tasks/l4-022.md) | done | tokenAccountSize / cpiReturn |
| [l4-023](tasks/l4-023.md) | done | systemAllocateWithSeed |
| [l4-024](tasks/l4-024.md) | done | systemCreateWithSeed |
| [l4-025](tasks/l4-025.md) | done | systemAssignWithSeed |
| [l4-026](tasks/l4-026.md) | done | systemTransferWithSeed |
| [l4-027](tasks/l4-027.md) | done | tokenInitMint |
| [l4-028](tasks/l4-028.md) | done | tokenSyncNative |
| [l4-029](tasks/l4-029.md) | done | 账户 1 只读叶子 |
| [l4-030](tasks/l4-030.md) | done | sha256Lit / sol_sha256 |
| [l4-031](tasks/l4-031.md) | done | 32B key / owner 按字读 |
| [l4-032](tasks/l4-032.md) | done | keccak256Lit / sol_keccak256 |
| [l4-033](tasks/l4-033.md) | done | 账户下标叶子收口 |
| [l4-034](tasks/l4-034.md) | done | 关着的格子一次开完 |
| [l5-001](tasks/l5-001.md) | done | 有界 for 改状态（`fillFirst` 抽出 `forBody`） |
| [l5-002](tasks/l5-002.md) | done | Phoenix bounded N=4 ask lifecycle：挂单 / IOC / self-trade / 结算 |
| [l5-003](tasks/l5-003.md) | done | 席位 PDA + base/quote vault 初始化 + Mollusk 权限门 |
| [l5-004](tasks/l5-004.md) | done | Token-2022 program id 切片 |
| [l5-005](tasks/l5-005.md) | done | 嵌套 structure / Vector element 摊平 + Mollusk |
| [l5-006](tasks/l5-006.md) | done | Sokoban 节点 + allocator/free-list + 完整左右旋 |
| [l5-007](tasks/l5-007.md) | done | Phoenix bounded N=4 bid lifecycle + sell IOC |
| [l5-008](tasks/l5-008.md) | done | Phoenix-v1 canonical owner/header/profile/length gate |
| [l5-009](tasks/l5-009.md) | done | Phoenix-v1 account-resident scalar/allocator-size gate；无 heap/Map |
| [l5-010](tasks/l5-010.md) | done | Phoenix-v1 Sokoban root/bump/free-list header envelope |
| [l5-011](tasks/l5-011.md) | done | Phoenix-v1 bounded account-resident bid-root slot read |
| [l5-012](tasks/l5-012.md) | done | Phoenix-v1 constant-memory bid-root child reciprocity/order gate |
| [l5-013](tasks/l5-013.md) | done | Phoenix-v1 verifier Surfpool Loader-v3 transaction deployment |
| [l5-014](tasks/l5-014.md) | done | Phoenix-v1 bounded parent-path reciprocity/cycle gate |
| [l5-015](tasks/l5-015.md) | done | Phoenix-v1 fixed-memory whole bid tree + allocator partition |
| [l5-016](tasks/l5-016.md) | done | Phoenix-v1 complete ask tree + ascending FIFO ordering |
| [l5-017](tasks/l5-017.md) | done | Phoenix-v1 complete trader tree + 32-byte Pubkey ordering |
| [l5-018](tasks/l5-018.md) | done | Phoenix-v1 bounded account-resident topology-word writes |
| [l5-019](tasks/l5-019.md) | done | Phoenix-v1 exact first trader registration |
| [l5-020](tasks/l5-020.md) | done | Phoenix-v1 exact second trader registration |
| [l5-021](tasks/l5-021.md) | done | Phoenix-v1 exact third trader registration + full insertion fixups |
| [l5-022](tasks/l5-022.md) | done | Phoenix-v1 exact fourth trader registration + red-uncle recolor |
| [l5-023](tasks/l5-023.md) | done | Phoenix-v1 exact fifth trader registration + black-uncle rotations |
| [l5-024](tasks/l5-024.md) | done | Phoenix-v1 general bounded trader insertion |
| [l5-025](tasks/l5-025.md) | done | Phoenix-v1 general bounded trader removal |
| [l5-026](tasks/l5-026.md) | done | Phoenix-v1 fixed-capacity bid/ask insertion |
| [l5-027](tasks/l5-027.md) | done | Phoenix-v1 fixed-capacity bid/ask removal |
| [l5-028](tasks/l5-028.md) | done | Phoenix-v1 fixed-capacity trader get-or-register deposit |
| [l5-029](tasks/l5-029.md) | done | SVM account-resident storage backend boundary + word-store migration |
| [l6-001](tasks/l6-001.md) | done | Solana 官方形状的 bounded transient bump heap 模型 |


积压：[backlog.md](backlog.md)
历史 SDK 表面盘点：[analysis/sdk-surface.md](analysis/sdk-surface.md)
