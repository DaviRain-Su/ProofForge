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
- SVM 异构 PDA seeds（ASCII/state key/account key）、完整 canonical key 校验和可续接 ignored CPI；Phoenix classic SPL Token 双 vault 全链路
- SVM packed u8/u16/u32/u64 CPI words 与 canonical PDA 签名 raw self-entry；SelfLog 覆盖 self-CPI、续段写回和认证失败矩阵
- Phoenix 官方形状 `AuditLogHeader` / Borsh event 通过 `"log"` PDA signed self-CPI 发布真实 `Program data`
- SVM 50 个 registry program 各有 runtime test 文件；EVM 12 个 registry program 全进 Anvil 总入口
- 审查修复：分支 fallthrough、state owner/marker、常量求值、Option identity、窄叶、Nat.sub、移位、EVM init、未知 CPI、solc 诊断
- GitHub CI 串行执行 Lake guards、50 个 SVM 构建 + Mollusk，以及 12 个 EVM 构建 + Anvil
- Core 显式 basic-block CFG 第一阶段：block arguments、显式 branch/checked/exit、完整 checker、local CSE、线性共享 block；Phoenix 全方法已通过 lowering/validation
- SVM/EVM emitter 已消费 target-owned Core CFG：SVM 用全局 block layout + 迭代 long-jump relay，EVM 用 Yul `pf_pc` dispatcher；当时 Phoenix 汇编由 4,109,725 B 降至 2,748,784 B（加入 trader topology 后当前为 3,314,430 B），全部 49 个 Mollusk 文件与 12 个 Anvil 程序通过
- Solanalib CFG correspondence：Counter add/sub/mul/div/mod 的 Core operands / physical slot / success-overflow edge 必须一致；typed guards、multiply zero-path jump、`r10-24` scratch handoff、static store 由上游 small-step semantics 执行。普通 eq/ne/lt/le/gt/ge branch 保留 cmp/operands/then/else identity，exact decoded pair theorem 证明 edge selection 与内存不变
- 通用 target registration：`Core.Target.Registration` 统一递归投影公共 Val/Op/Program，并携带 extension callbacks、arity、op well-formedness 和 CFG dialect；SVM/EVM conversion 已移回各自 IR，`Extract.IR` 不再含后端 projection case。Core-only 合成第三 target 证明新增公共语言后端无需修改抽取 IR，并继续 fail closed 拒绝 foreign extension
- Token-2022 classic-compatible `TransferChecked`：通用 `CpiMeta.expectedDataLen` 在 CPI 前约束 base Mint=82B / Account=165B；真实 base transfer 成功，transfer-fee / enabled transfer-hook mint 原子拒绝；Runtime CPI wrapper 改为按命名空间统一展开，不再维护 recipe 名白名单
- 独立 Tree N=4 删除切片：successor transplant、全部可达 delete-fixup、free-list 回收和精确地址复用；24 种插入顺序 × 4 个删除 key 的宿主不变量门，以及 black-leaf fixup/reuse Mollusk 链上门
- Phoenix trader tree 持久化 N=4 topology：root/left/right/parent/color、bounded 插入/删除修复和 exact address reuse；deposit 沿 links 查找并复用 parent，evict 先 detach 再回收。抽取器只增加 target-neutral 的 continuation/conditional-state/vector-write lowering，没有 Tree/Phoenix 名字或 emitter 特判
- Phoenix ask/bid order tree 持久化 N=4 topology：payload 地址稳定，撮合按中序 best/successor 遍历，fill/expiry/reduce/cancel detach，满书驱逐后 exact address reuse。通用抽取器增加 scalar let zeta-reduction 和 qualified nested-vector schema path；两个 target emitter、IR 与 Phoenix ABI 无需特判或改动

## 当前状态

- `lake build Tests` 当前 196 jobs；71 个 imported test modules 含 928 个 `#guard` / `#guard_msgs`。
- SVM registry 50 个程序 / 50 个 Mollusk integration 文件；这表示每个程序有门，不表示每个入口都已有链上矩阵。全量 `pf build` 与 Mollusk 230/230 当前通过。
- EVM registry 12 个程序；Counter / Pair / Flag / Maybe / Context / TipJar / Lang / Vault / Ownable / Token / Window / Phase 的 Anvil 总门 12/12。
- Phoenix Mollusk 8/8：ask/bid 挂单、reduce、双向撮合、费用收取、真实 base/quote deposit/withdraw、trader topology 删除后的 surviving root、ask/bid order topology 与满书 exact address reuse、未注册 take-only 双 Token 腿、严格 slot/time TIF、三种 self-trade、认证 audit `Program data`，及 vault/mint/Token program/self program/log PDA/writable/signer/owner 原子失败；跨四档逐样本 refinement 仍由 host/IR 门承担。
- `postAskFunds → detached → insertAskOrder` 的 aggregate `baseLocked` / `baseFree` stores 已恢复：`flattenLeaves` 先 reduce constructor projection，再给闭包了 bounded tree walk 的 scalar 字段足够 decoder fuel。IR 门钉住 `postAsk` 的 `baseLocked`/`baseFree` 和 `postBid` 的 `quoteLocked`/`quoteFree`。
- P4 通用压缩 / Loader-v3 部署资格：Core `shareBlocks` 从相邻比较升级为全图 fingerprint 分桶 + 精确结构相等，已知 redirect 先归一化；collision 不会错误共享。Phoenix CFG 6,128 → 5,151 blocks；实测 `pf build --target svm Phoenix`：digest `7a969da7b60ead4`，assembly 10,642,331 bytes，ELF 3,429,336 bytes，IDL 19,626 bytes，比上一 checkpoint 再减 244,637 / 75,440 bytes。Assembler 按 Agave 4.0 Loader-v3 `ProgramData` 10 MiB、metadata 45 B，强制 ELF ≤ 10,485,715 B；当前 headroom 7,056,379 B。Surfpool 1.5.0 offline smoke 禁用 instant direct-state 路径，以 3,389 个 Loader write transactions + deploy + authority transfer 完成本地部署；confirmed signature、Program/ProgramData layout 与完整 ELF bytes 全部核对。本轮 `lake build Tests`、全 49 个 SVM `pf build`、Mollusk 198/198（含 Phoenix 8/8 与 Tree 2/2）及 Anvil 12/12 全绿；不作公网部署声明。
- P5 第一段 profile gate 已完成：通用 `accDataWord acc word` 对编译期固定账户/word 做 `data_len` 边界检查；独立 `PhoenixV1Profile` verifier 验证官方 program owner、MarketHeader discriminant、12 个官方 `(bids, asks, seats)` tuple 与 exact account length，最小 profile 返回 84,944 B。它不读取 market body，也不宣称完整 Phoenix-v1 兼容。产物 ELF 26,064 B；12 个 tuple 全部进入 profile Mollusk 3/3，全量 Mollusk 201/201 与 Anvil 12/12 通过。
- P5 第二段静态 body metadata gate 已完成：官方 Sokoban tree 是账户内固定 `[Node; N]` 与 bump/free-list allocator，不是 Rust heap Map。本切片只按四档 compiled profile 读取固定 sequence、bids/asks/traders allocator `size` word，并检查 count ≤ capacity；不开放 runtime offset、节点遍历/写入或 remaining accounts。`PhoenixV1Profile` digest `39d77b7c712ba581`，ELF 80,576 B；12 个 profile 的 scalar/count 与三类超限失败进入同一 Mollusk 3/3。
- P5 第三段 allocator header envelope 已完成：按四档固定 word 验证三棵树的 root/padding、1-based bump/free-list cursor、size/root/capacity 关系；checkpoint digest `3322a44e27b16f42`，ELF 156,200 B。
- P5 第四段 bounded root slot 已完成：通用 `accDataWordAt` 只允许运行时 slot，account/base/stride/capacity 均编译期固定，并做 slot + 最终 data-length 双边界。bid root index=2 的 links/parent/color/price 直接从账户读取；无 heap/Map/节点复制。当前 digest `b2519600b8cfe99f`，assembly 878,132 B，ELF 282,536 B；profile Mollusk 4/4。
- P5 第五段 constant-memory root neighborhood 已完成：四档 profile 原位读取 bid root 与两个直接 child，验证 bid side tag、child→parent reciprocity、color、index envelope 及局部 price/sequence ordering；不分配节点容器，也不声明全树验证。当前 digest `7952977f008911a8`，assembly 2,171,011 B，ELF 716,344 B；profile Mollusk 4/4。
- P5 第六段本地部署门已完成：Surfpool smoke 参数化为 Phoenix / PhoenixV1Profile 两个显式目标；P5 verifier 的 716,344 B ELF 经 708 个 Loader write + deploy + authority transactions 落入 exact 716,389-byte ProgramData，confirmed signature 与完整 bytes 已核对。默认 Phoenix 3,389-write 路径也重跑通过；不用 `solana-test-validator`，不声明公网部署。
- P5 第七段 bounded parent path 已完成：通用 `accDataParentPathValid` 以静态
  base/stride/capacity/max-depth 逐步读取账户内 parent path，验证 color、index envelope、
  parent→child reciprocity，并在 32 edge 内要求到 root；root 外 reciprocal cycle 有界返回 0。
  当前 digest `381c728318e7fe26`，assembly 2,509,900 B，ELF 821,576 B；无 heap/Map；
  Surfpool 1.5.0 以 812 个 Loader write transactions 部署并核对 exact ProgramData。
- P5 第八段 whole bid tree + allocator partition 已完成：通用 `accDataRbTreeValid` 以
  iterative parent-pointer traversal 和固定 4096-bit stack bitmap 原位验证 root/color、
  reciprocity、red rule、equal black height、strict Phoenix FIFO ordering、reachable live count，
  再验证 free-list 无 cycle/duplicate/live overlap 且精确覆盖全部 pre-bump slot；无 heap、
  Map、node copy 或 persistent pointer。4095-node / 4096-capacity perfect tree 在 Mollusk 中
  消耗 852,066 CU。当前 digest `53d37673dbf95305`，assembly 2,876,110 B，ELF 936,264 B；
  Surfpool 1.5.0 以 926 个 Loader write transactions 部署并核对 exact 936,309-byte
  ProgramData。
- P5 第九段 whole ask tree 已完成：四档 ask allocator 复用同一 fixed-memory validator，
  额外强制 ask side tag=0 与 `(price, stored sequence)` strict ascending FIFO；4095-node /
  4096-capacity perfect ask tree 消耗 852,060 CU。当前 digest `1356885e6582aab2`，assembly
  3,242,689 B，ELF 1,050,952 B；Surfpool 1.5.0 以 1,039 个 Loader write transactions
  部署并核对 exact 1,050,997-byte ProgramData。
- P5 第十段 whole registered-trader tree 已完成：十二个官方 profile 选择固定
  base/18-word stride/capacity，通用 `accDataRbTreeKey4Valid` 直接扫描账户内节点，以固定
  8321-bit bitmap + 64-entry stack 验证完整 RB invariants、child-parent reciprocity、
  Rust `[u8;32]` byte-lexicographic Pubkey strict ordering 和 exact live/free partition；不复制
  node，不使用 heap/Map 或持久 pointer。最大 8321-capacity allocator 的 8191 live + 130
  free slots 消耗 1,344,959 / 1,400,000 CU。当前 digest `6d8e6cbb2d5dd163`，assembly
  3,703,126 B，ELF 1,194,760 B；Surfpool 1.5.0 以 1,181 个 Loader write transactions
  部署并核对 exact 1,194,805-byte ProgramData。
- P5 第十一段 bounded account-resident write 基础已完成：通用 `accDataWordSetAt` 把
  account/base/stride/capacity 固定在编译期，只让运行时选择 slot 和 u64 value；只写外部
  writable、current-program-owned account，并在 store 前检查 account count、capacity 和
  最终 data length。它是有序 target effect / CFG CSE barrier，不返回或持久化 pointer。
  `writeTraderTopology128` 连续原位写最小 profile 的 links 与 parent/color；readonly、错误
  owner、slot 128 和“第一字可写、第二字越界”的短账户均 `Custom(1)` 且原子回滚。
  当前 digest `f77c4fc2ca622dc9`，assembly 3,709,362 B，ELF 1,196,400 B，IDL 3,386 B；
  Surfpool 1.5.0 以 1,183 个 Loader write transactions 完成本地部署并核对 exact
  1,196,445-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 210/210 和
  Anvil 12/12 全绿。
- P5 第十二段 exact first trader registration 已完成：按 Sokoban 0.3.0 的真实
  16-byte registers + 32-byte Pubkey + 96-byte TraderState 节点布局，把 canonical fresh
  128-seat allocator 从 root/size=0、bump/free=1 原子变成 slot 1 黑根、root/size=1、
  bump/free=2。完整 144-byte slot 均覆盖，guarded `Except` 分支内 21 个 ignored effects
  不再被最终 state projection 吞掉；成功后 complete trader validator 返回 1，不暴露
  detached node。nonempty/profile 错误、readonly 和 wrong owner 均原子失败。当前 digest
  `e6a7a4e2393cc64f`，assembly 3,759,660 B，ELF 1,209,400 B，IDL 3,721 B；Surfpool 1.5.0
  以 1,196 个 Loader write transactions 部署并核对 exact 1,209,445-byte ProgramData。
- P5 第十三段 exact second trader registration 已完成：canonical one-root 128-seat tree
  经 bump path 分配 address 2，完整覆盖第二个 144-byte slot，以 parent=1/color=Red 挂到
  黑根 left 或 right，不发生 rotation。四个 little-endian limb 各自 byte-swap 后逐 limb
  比较，精确复现 Rust `[u8;32]` Pubkey ordering；测试 key 刻意让该顺序与 u64 数值序相反。
  duplicate/malformed、readonly/wrong owner 均原子失败，左右结果都通过 complete tree/
  allocator validator。当前 digest `f741f2eaffde779e`，assembly 3,888,574 B，ELF
  1,248,584 B，IDL 4,058 B；Surfpool 1.5.0 以 1,234 个 Loader write transactions
  部署并核对 exact 1,248,629-byte ProgramData。本轮 194-job Lean、50 个 SVM build、
  Mollusk 212/212 和 Anvil 12/12 全绿。
- P5 第十四段 exact third trader registration 已完成：canonical two-node 128-seat tree 经
  bump path 分配 address 3，完整覆盖第三个 144-byte slot，并按 Sokoban 0.3.0 精确产生
  LL/LR/RR/RL rotation/recolor 与两个 no-fix topology。通用 `svmByteSwap64` 在宿主侧保持
  纯语义，SVM 侧直接发射 `be64`，不引入 heap allocation；external-account write 只要出现
  但任一 operand 无法解码，抽取就 fail closed，不再静默丢 effect。六种结果逐字节匹配并
  通过 complete trader tree/allocator validator；duplicate/malformed/readonly/wrong owner
  均原子失败。当前 digest `d9b9ee673526ff9f`，assembly 3,949,948 B，ELF 1,261,744 B，
  IDL 4,392 B；Surfpool 1.5.0 以 1,247 个 Loader write transactions 部署并核对 exact
  1,261,789-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 214/214 和
  Anvil 12/12 全绿。
- P5 第十五段 exact fourth trader registration 已完成：任意 canonical three-node trader
  tree 必为 black root + two red leaves；本切片从六种 address assignments bump-alloc
  address 4，覆盖四个 key intervals，把新节点挂到 selected red parent，并按 Sokoban
  red-uncle path 把两个 existing leaves recolor black，root 地址不变。slot 4 的 18 words
  全部覆盖，三个既有 TraderState 逐字节保留，成功路径精确 23 个 account writes；三种
  duplicate、malformed、readonly/wrong owner 均原子失败。fixed-memory tree/parent-path
  intrinsic 现在保存 walked ABI 的 `r7` instruction-data base，traversal 不再破坏后续参数
  读取。当前 digest `a2c228178be89985`，assembly 4,078,543 B，ELF 1,300,352 B，
  IDL 4,727 B；Surfpool 1.5.0 以 1,285 个 Loader write transactions 部署并核对 exact
  1,300,397-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 216/216 和
  Anvil 12/12 全绿。
- P5 第十六段 exact fifth trader registration 已完成：canonical four-node tree 经 bump
  path 分配 address 5，完整覆盖第五个 144-byte slot。若 parent 为 black，只填 missing
  child；若 parent 是唯一 red address-4 leaf，则按 Sokoban black/null-uncle 路径执行
  LL/LR/RL/RR local rotation/recolor，并保持最上层 black root 地址不变。八种逐字节结果
  覆盖全部六种既有 address layout、四种 rotation 和两侧 black-parent insertion；四个
  existing TraderState 保留，结果都通过 complete tree/allocator validator。四个
  duplicate、malformed、readonly/wrong owner 均原子失败。持久状态仍只使用 one-based
  slot index 与 `0` sentinel，不引入 heap/Map、节点副本或 persistent pointer。当前 digest
  `9140326aef66cbdc`，assembly 4,378,054 B，ELF 1,399,096 B，IDL 5,061 B；Surfpool 1.5.0
  以 1,383 个 Loader write transactions 部署并核对 exact 1,399,141-byte ProgramData。
  本轮 194-job Lean、50 个 SVM build、Mollusk 218/218 和 Anvil 12/12 全绿。
- P5 第十七段 general bounded trader insertion 已完成：通用
  `accDataRbTreeKey4Insert` 以编译期固定 geometry 在账户原位执行 bounded search、
  bump/free-list allocation 与完整 RB insert fixup，不再继续增加第六/第七次特例。
  `lib-sokoban = 0.3.0` differential test 用 128-key permutation 填满全部 seat，并在每次
  插入后精确比较完整 18,464 bytes；官方 delete 产生的 free head 也能逐字节复用。
  duplicate/full/malformed/readonly/wrong owner 全部在 store 前原子失败。IDL 现在从
  instruction effect 推导 external writable meta。持久状态仍只有 one-based index 与
  `0` sentinel，不使用 heap/Map 或 persistent pointer。当前 digest `ea2110304454c9e6`，
  assembly 4,413,033 B，ELF 1,410,648 B，IDL 5,499 B；Surfpool 1.5.0 以 1,394 个
  Loader write transactions 部署并核对 exact 1,410,693-byte ProgramData。本轮
  194-job Lean、50 个 SVM build、Mollusk 220/220 和 Anvil 12/12 全绿。
- P5 第十八段 general bounded trader removal 已完成：通用
  `accDataRbTreeKey4Remove` 在完整 tree/free-list preflight 与 key lookup 后，按 Sokoban
  0.3.0 原位执行 predecessor transplant、bounded delete-fixup 和 free-list push。128-key
  tree 以独立 permutation 逐个删空，每一步完整 18,464 bytes 与官方实现一致；随后 16 次
  insertion 也精确复用同一 LIFO free-list。持久状态仍只有 one-based index / `0` sentinel，
  不使用 heap/Map、detached node 或 persistent pointer。当前 digest `74f755a74720a766`，
  assembly 4,456,725 B，ELF 1,424,912 B，IDL 5,842 B；Surfpool 1.5.0 以 1,409 个 Loader
  write transactions 部署并核对 exact 1,424,957-byte ProgramData。本轮 194-job Lean、
  50 个 SVM build、Mollusk 222/222 和 Anvil 12/12 全绿。
- P5 第十九段 fixed-capacity bid/ask insertion 已完成：通用
  `accDataRbTreeOrderInsert` 以官方连续 8-word / 64-byte order slot 原位保存 2-word
  `FIFOOrderId` 与 4-word `FIFORestingOrder`，按 bid descending / ask ascending comparator
  和 encoded sequence side tag 执行 bounded search、bump/free-list allocation 与完整 RB
  fixup。两个 512-node books 各自填满，每一步完整 32,800 bytes 都与 `lib-sokoban 0.3.0`
  一致；满树 duplicate 只替换 value，满树新 key 与 malformed/readonly/wrong owner 均原子
  失败。持久状态仍只有 one-based index / `0` sentinel，不使用 heap/Map、detached node 或
  persistent pointer。当前 digest `2a24252f935ac912`，assembly 4,528,527 B，ELF
  1,448,496 B，IDL 6,647 B；Surfpool 1.5.0 以 1,432 个 Loader write transactions 部署并
  核对 exact 1,448,541-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk
  225/225 和 Anvil 12/12 全绿。
- P5 第二十段 fixed-capacity bid/ask removal 已完成：通用
  `accDataRbTreeOrderRemove` 在完整 tree/free-list preflight、encoded sequence side tag 与
  key lookup 后，按 Sokoban 0.3.0 原位执行 predecessor transplant、bounded delete-fixup
  和 free-list push。两个满载 512-node books 各自按独立 permutation 逐个删空，每一步
  完整 32,800 bytes 都与官方实现一致；随后各 16 次 insertion 也精确复用同一 LIFO
  free-list。missing/malformed/readonly/wrong owner 全部在 store 前原子失败。持久状态仍
  只有 one-based index / `0` sentinel，不使用 heap/Map、detached node 或 persistent
  pointer。当前 digest `8290f8143ffc2374`，assembly 4,616,716 B，ELF 1,477,344 B，IDL
  7,210 B；Surfpool 1.5.0 以 1,460 个 Loader write transactions 部署并核对 exact
  1,477,389-byte ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 228/228 和
  Anvil 12/12 全绿。
- P5 第二十一段 fixed-capacity trader deposit 已完成：通用
  `accDataRbTreeTraderDeposit` 按官方 18-word node / 12-word `TraderState` 布局，在完整
  tree/free-list preflight 后执行 Pubkey get-or-register。已有 trader 的 quote/base free
  lots 在两个 checked-add 均成功后才一起写回；新 trader 的完整 slot 先清零再初始化，
  满树 existing-key 仍成功而 absent-key 返回 full。128 个 trader 在每个 allocator size
  重复 deposit，每一步完整 18,464 bytes 均与 `lib-sokoban 0.3.0` 一致；两类 overflow、
  malformed/readonly/wrong owner 全部原子失败。持久状态只有 one-based index / `0`
  sentinel，不使用 heap/Map、detached node 或 persistent pointer。当前 digest
  `e9966de4a1795a47`，assembly 4,652,382 B，ELF 1,489,088 B，IDL 7,613 B；Surfpool
  1.5.0 以 1,472 个 Loader write transactions 部署并核对 exact 1,489,133-byte
  ProgramData。本轮 194-job Lean、50 个 SVM build、Mollusk 230/230 和 Anvil 12/12 全绿。
- P5 第二十二段 account-resident storage backend boundary 已完成：新增 target-owned
  `Svm.AccountStorage`，以编译期固定 `Region/Field`、显式 zero/one-based indexing、generic
  value traversal/canonicalization 与 transitive `EffectSummary` 承载 persistent container
  routine。`accDataWordSetAt` 已从顶层 SVM Ops/IR 和主 emitter 的 bespoke case 迁入单一
  `.accountStorage` bridge；主 emitter 只注入 value loader、owner check 与 walked-account
  frame，IDL writable meta 由 storage effect 推导。source spelling、digest
  `e9966de4a1795a47`、ELF 1,489,088 B 与 IDL 7,613 B 均保持不变。该层不引入 heap
  allocation、runtime capacity、Map、detached node 或 persistent pointer。本轮 196-job
  Lean、50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿；Surfpool 1.5.0 以 1,472 个
  Loader write transactions 部署并核对 exact 1,489,133-byte ProgramData。下一步先迁移
  bounded parent-path，再收拢 RB search/allocator/rotation/transplant/fixup。
- P5 第二十三段 bounded account-storage query bridge 已完成：
  `accDataParentPathValid` 迁入 `AccountStorage.Query.parentPathValid`；两个 fixed-stride
  `Field` 统一声明 one-based region、read-only effects、三参数 arity、geometry/depth bound、
  account walk 与 canonical spelling。SVM `ValKind`、generic extraction traversal、IR digest
  与主 `loadVal` 都只保留单一 `.accountStorage query` bridge，原 138 行 parent-path emitter
  已移入 storage backend。source 名称与 digest `e9966de4a1795a47` 保持；assembly
  4,652,144 B、ELF 1,489,088 B、IDL 7,613 B 均不变。路径仍只保存当前 one-based index、
  depth 和 account-derived transient pointer，不使用 heap/Map、visited collection、node copy
  或 persistent pointer。本轮 196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil
  12/12 全绿；Surfpool 1.5.0 以 1,472 个 Loader write transactions 部署并核对 exact
  1,489,133-byte ProgramData。下一步迁移 complete RB validator 的共同 envelope 与内部例程。
- P5 第二十四段 FIFO RB-tree account-storage query 已完成：bid/ask 共用的 complete
  `accDataRbTreeValid` 已迁入 `AccountStorage.Query.fifoRbTreeValid`；links、parent/color、
  price、sequence 四个 fixed-stride `Field` 统一声明 one-based region、read-only effects、
  四参数 arity、4096-slot capacity bound 与 canonical spelling。原 449 行完整 tree/free-list
  validator 已从主 emitter 移入 storage backend，order insert/remove preflight 也组合调用
  同一 Query routine；`ValKind`、generic extractor、IR canonicalization 与主 `loadVal` 不再有
  FIFO validator 特判。实现继续只用 fixed 4096-bit frame bitmap、one-based index 和 `0`
  sentinel，不使用 heap/Map、node copy、runtime geometry 或 persistent pointer。digest
  `e9966de4a1795a47`、assembly 4,652,144 B、ELF 1,489,088 B 与 IDL 7,613 B 保持不变；
  196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿，Surfpool 1.5.0
  以 1,472 个 Loader write transactions 部署并核对 exact 1,489,133-byte ProgramData。
  下一步迁移 four-word Pubkey validator 并抽取共同 topology/allocator layout。
- P5 第二十五段 Pubkey RB-tree account-storage query 已完成：four-word
  `accDataRbTreeKey4Valid` 已迁入 `AccountStorage.Query.key4RbTreeValid`；FIFO 与 Pubkey
  layout 共用编译期固定的 `RbTree` links/parent-color topology 和 64-edge traversal bound，
  Pubkey query 另声明连续四字 key region 与 8321-slot capacity bound。trader insert/remove/
  deposit preflight 组合调用同一个 Query routine，顶层 `ValKind`、主 `loadVal` 和 IR
  canonicalization 不再有 Pubkey validator 特判。完整 tree/free-list 验证仍只使用 fixed
  8321-bit frame bitmap、64-entry stack、one-based index 与 `0` sentinel，不引入 heap/Map、
  runtime geometry、node copy 或 persistent pointer。source digest `e9966de4a1795a47`、
  assembly 4,652,144 B、ELF 1,489,088 B 与 IDL 7,613 B 保持不变；196-job Lean、50 个
  SVM build、Mollusk 230/230、Anvil 12/12 全绿，Surfpool 1.5.0 以 1,472 个 Loader write
  transactions 部署并核对 exact 1,489,133-byte ProgramData。下一步把 bounded search、
  allocator acquire/release、rotation/transplant/fixup 迁为 storage mutation routines。
- P5 第二十六段 bounded account-storage map mutation vocabulary 已完成：原 five 个
  trader/order bespoke mutation constructors 已从顶层 `Svm.OpExt`、`Svm.IR.Op` 和主 emitter
  dispatch 删除，收敛为 `AccountStorage.Call` 的 `rbMapInsert`、`rbMapRemove` 与
  `rbMapCheckedAdd`。`RbMap` descriptor 统一拥有编译期固定 account/header/topology/key/value
  geometry、capacity、one-based indexing、writable/current-owner access 与 duplicate policy；
  extraction、CFG、signer/account inference、IDL writable inference 和 canonicalization 只遍历
  generic values/effects。现有原位 assembly 由 storage mutation backend adapter 复用，source
  digest `e9966de4a1795a47`、assembly 4,652,144 B、ELF 1,489,088 B 与 IDL 7,613 B 均不变。
  持久状态仍不使用 heap/Map、runtime geometry、node copy、detached node 或 persistent
  pointer。196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿；Surfpool
  1.5.0 以 1,472 个 Loader write transactions 部署并核对 exact 1,489,133-byte
  ProgramData。下一步把 search/allocator/rotation/transplant/fixup assembly 实体迁入 backend。
- P5 第二十七段 bounded account-storage field extractor 已完成：runtime-indexed
  `accDataWordAt` 已从独立 SVM `ValKind` 和主 `loadVal` case 迁入
  `AccountStorage.Query.readWord`。统一 `Field` descriptor 携带编译期固定 account/base/stride/
  capacity 与 zero/one-based indexing；one-based 模式拒绝 `0` sentinel 后再归一化，供后续
  map lookup 返回 index 直接组合。query 自己拥有 arity、read-only effects、account inference
  与 `dwi`/`dwi1` canonical spelling，source helper 和 wire ABI 不变。实现只在 index 与最终
  data length 检查后形成调用期 transient pointer，不分配 heap/Map、不复制 node、不开放
  runtime geometry 或 persistent pointer。source digest `e9966de4a1795a47` 保持，迁移前后
  4,652,144-byte assembly 逐字节相同；ELF 1,489,088 B、IDL 7,613 B 不变。196-job Lean、
  50 个 SVM build、Mollusk 230/230、Anvil 12/12 全绿；Surfpool 1.5.0 以 1,472 个 Loader
  write transactions 部署并核对 exact 1,489,133-byte ProgramData。下一步增加 bounded
  Key4/FIFO map-find query，再组合 field read/write/remove 实现 ReduceOrder。
- P5 第二十八段 bounded account-storage RB map find 已完成：`Query.fifoFind` 与
  `Query.key4Find` 复用同一个 storage-owned `emitRbFind`，按编译期固定 root/links/key/
  stride/capacity 在 account bytes 中直接搜索，返回 one-based node index 或 `0`。Key4 用
  `be64` 保持 `[u8;32]` byte ordering；FIFO ask 升序、bid 降序。每个 dereference 都检查
  `1..capacity`，统一 64-level bound 拒绝 cycle/过深输入；account 0 与 walked external
  account 都先做覆盖 root/links/key 的 data-length gate。validator/find/mutable map 现在共用
  `FifoRbTree.oneBased` / `Key4RbTree.oneBased` layout constructors；query 自己拥有 arity、
  read-only effects、account inference 与 `rbof`/`rb4f` canonical spelling，主 `loadVal` 没有
  新 case。实现只保留 scalar index/depth 和调用期 transient pointer，不分配 heap/Map、
  bitmap，不复制 node，不开放 runtime geometry。isolated Key4/FIFO programs 经 `sbpf build`
  产出 3,720 B / 3,480 B ELF；196-job Lean、50 个 SVM build、Mollusk 230/230、Anvil
  12/12 与 Surfpool smoke 全绿。下一步接 Runtime/source intrinsic，再组合
  find/read/write/remove 实现 ReduceOrder。
- P6 第一段 bounded transient heap 模型已完成：按官方 entrypoint allocator 固定
  `0x300000000`、默认 32 KiB / 最大 256 KiB、首 word bump、向下对齐、OOM 与 no-op
  deallocation。它不开放 raw pointer，也不替代账户内 Phoenix/Sokoban allocator。
- `l5-003` 与 Phoenix 双 vault adapter 已完成：Seat 初始化和 Phoenix 同一入口的 canonical PDA 校验、classic SPL Token CPI 成功/失败路径都进 Mollusk。
- `l5-004` Token-2022 classic-compatible program-id 切片已完成；TLV extension 语义仍保持 fail closed。
- `l5-005` 已完成；任务状态已同步为 done。
- P3 横向回归：`lake build Tests`、全 49 个 SVM `pf build`、Mollusk 194/194（含 Phoenix 8/8 与 Tree 2/2）、Anvil 12/12。lowering 修复没有改 Tree digest。

## Phoenix / Solana P0–P5 路线

| 阶段 | 状态 | 依赖 | 验收门 |
|---|---|---|---|
| P0 抽取收口 | 已有 | 通用 Extract state-loop/helper sequencing；SVM CFG/local 布局 | `postAsk` 值树预算、单方法发射、PhoenixSpec、可复现 assembly/ELF/IDL/digest；continuation 不得静默丢 aggregate scalar stores。已知 `postAskFunds` 缺口已关；值树 90,604 / 24,840 是缺口关闭前的探针，本 lowering 后未重测 |
| P1 bounded 产品语义 | 已有 | P0；固定 N=4 账户布局 | ask/bid/trader 三棵持久化树的 N=4 host/IR 门、24 种 topology、双向 IOC、TIF/self-trade/fee/事件与 exact address reuse 全绿 |
| P2 链上认证矩阵 | 已有 | 可组装 Phoenix ELF；classic SPL Token 与 signed self-CPI | Phoenix Mollusk lifecycle/CPI/authenticated audit 矩阵 8/8；跨四档逐样本 chain refinement 补齐前不得宣称 host↔chain 完整 refinement |
| P3 横向回归 | 已有 | P0/P2 产物稳定 | `lake build Tests`、全 SVM `pf build`、SVM Mollusk 194/194、EVM Anvil 12/12 全绿；无 Phoenix 特判。跨四档 host↔chain refinement 仍未宣称；P4 部署资格见下一行 |
| P4 产物资格/压缩 | 已有（本地 Surfpool Loader-v3 transaction；公网未声明） | P0 的稳定 CFG 和可测基线 | 通用 OOB fallthrough + 全图 keyed shared-block；Phoenix assembly 10,642,331 B / ELF 3,429,336 B，digest 不变。ELF 通过 10,485,715 B size gate，并经 Surfpool 1.5.0 的 3,389 write + deploy + authority transactions 落入 exact ProgramData；全 49 SVM + Mollusk 198/198 + Anvil 12/12 回归通过。更深 value-tree CSE 为后续优化 |
| P5 动态 Phoenix-v1 | 部分：profile + complete tree/free-list validation + bounded trader/order insertion/removal + account-storage boundary + 本地部署门已有 | 固定/固定-stride有界 account region、parent walk、fixed bitmap/stack、effect-safe guarded stores | canonical profile/allocator envelope/三树 invariants 已进 Lean/Mollusk；trader allocator 与 bid/ask books 均可按 Sokoban 0.3.0 填满并逐个删空；word-store、parent path、FIFO/Pubkey RB validators 与共同 topology 已迁入 generic account-storage bridge，mutation routines 待迁移；matching/placement ABI、remaining accounts 和完整 Phoenix-v1 指令兼容仍 fail closed |
| P6 SDK memory/protocol surface | 进行中：官方形状 transient heap 模型已有 | P5 的 account-resident 边界；后续需要 effect-safe lowering | 默认 32 KiB / 显式 32–256 KiB frame、OOM/no-op free 已建模；后续只开放 bounded scratch/container API，禁止持久 heap pointer。再分片补 32-byte/u128/Borsh、remaining accounts 和 Token-2022 extension semantics |

P0–P4 不把 Phoenix 名字或字段偏移加入 Extract/IR/emitter。P5 verifier 已能按账户原始
32 bytes 比较 Pubkey，但通用 SDK 的固定长度 32-byte / u128 / Borsh protocol types 仍需
后续设计；现有 contract source 的 Pubkey 与 client id 仍以 `UInt64` limbs 表达。P5 profile
gate 不是把运行时变长账户偷偷放进现有 bounded model，也不是 P0 的验收条件。

Solana Rust 允许 `Vec`/`Box` 等调用期 allocation，但默认 allocator 是有界 bump heap，
不是通用进程 heap；`dealloc` 不回收，pointer 不能跨 invocation 或写入 account。普通
`HashMap` 也不作为 SVM SDK 的默认能力。ProofForge 后续 transient container lowering 必须
携带静态/运行时容量门和显式 OOM，不得把它用于 P5 持久树的全量复制。

## 明确保持 fail closed

- 搬 PF 前端 / `HandlerIR.mk` 私有构造、新 DSL、无约束 Lean、FFI→asm。
- 全 SVM `.so` / loader refinement 与公网部署声明；当前只宣称 Phoenix 本地 Surfpool transaction smoke。
- 运行时 program id、运行时选择的 data offset / 变长 body、运行时 remaining accounts；编译期固定 offset 的 bounds-checked data word 与编译期钉死的 CPI 已开。
- Token-2022 transfer hook / fee / TLV extension 语义，直到对应账户模型落地；当前 base-layout
  wrapper 用精确 data length 在 CPI 前拒绝全部 extension-bearing mint/account。
- feature-gated blake3 / poseidon / curve25519 / alt_bn128 / `sol_get_sysvar`。
- 把完整 32B key 当作现有 8B return-data ABI 的单一返回值。

历史 SDK 清单和阶段分析保留作设计记录，不再当当前 backlog：
[sdk-surface.md](analysis/sdk-surface.md)、[gap-vs-proofforge.md](analysis/gap-vs-proofforge.md)、
[remaining-surface.md](analysis/remaining-surface.md)。
