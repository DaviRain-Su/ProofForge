# Runtime / SDK 并行开发执行图

> 基线：R1-010、SVM-SDK-1/2 和 EVM-SDK-1/2 已集成到本地 `main`；远端同步由 coordinator
> 单独执行。本文只拆 ownership、依赖和验收，不改变
> [Runtime / SDK 双目标路线图](runtime-sdk-roadmap.md) 的能力边界。

## 1. 为什么按模块拆，而不是按文件数量拆

并行开发的目标是让每个 agent 拥有一个可以独立验证的纵向模块，而不是让多个 agent
同时修改 `Extract.lean`、target IR 和主 emitter。共享 schema/control 只保留一个 owner；
SVM 与 EVM 的物理 binding、SDK facade 和 fixture 才适合并行。

```diagram
                              ┌─────────────────────────────┐
                              │ Coordinator / integration   │
                              │ Shared schema · Extract · CI│
                              └──────────────┬──────────────┘
                                             │ stable contracts
                ┌────────────────────────────┼────────────────────────────┐
                ▼                            ▼                            ▼
┌──────────────────────────┐  ┌──────────────────────────┐  ┌──────────────────────────┐
│ SVM Runtime              │  │ SVM SDK                  │  │ EVM Runtime              │
│ account/CPI/TLV binding  │  │ storage/scratch facades  │  │ ABI/storage/effects      │
└─────────────┬────────────┘  └─────────────┬────────────┘  └─────────────┬────────────┘
              │                             │                             │
              └─────────────────────────────┼─────────────────────────────┘
                                            ▼
                              ┌──────────────────────────┐
                              │ EVM SDK + conformance    │
                              │ policies/assets/examples │
                              └──────────────────────────┘
```

三条硬规则：

1. agent 只拥有下表列出的 write set；发现必须越界时停止并报告 integration hook，不自行扩
   shared Ops/Extract/Emit。
2. worker 不修改 `docs/plan/**`、顶层 import、registry 或总 CI；它返回测试证据，由
   coordinator 在集成 commit 一次更新。
3. Queue/Map/Allocator/Phoenix instruction 都不能成为新 opcode。只有新的 VM effect 才能扩
   target Ops/Component/Emit，并且必须先给出为什么现有 component 无法组合的证据。

## 2. 写入锁和集成所有权

下面文件是高冲突 source of truth。任意时刻只允许 coordinator，或被明确授予当前
`shared-lock` 的一个 agent 修改：

- `ProofForge/Core/**`、`ProofForge/Profile.lean`、`ProofForge/Extract.lean`、
  `ProofForge/Extract/**`；
- `ProofForge.lean`、`Examples.lean`、`Tests.lean`；
- `ProofForge/Svm/Registry.lean`、`ProofForge/Evm/Registry.lean`；
- `.github/**`、`scripts/check_ownership.py`、`docs/plan/**`。

Coordinator（当前线程）固定负责：

- **PF-COORD-1 / R1-009 + R1-010**：shared `BoundedVec` source contract，以及 SVM canonical
  bounded Borsh / EVM canonical bounded ABI 两套独立 target binding 与证据；
- **PF-COORD-2**：审查并集成各 worker 的 target-local commits，统一处理顶层 imports、
  registries、capability matrix、digest 和 CI；
- **PF-COORD-3**：每一 wave 的全 Lean、全 SVM build/Mollusk、全 EVM build/Anvil 和
  ownership/reproducibility 门。CI 中三类门独立并行，完整 Lean aggregate 只运行一次；
  见 CI-001。

`shared-lock` 不允许被“顺手”复制：如果 SVM Runtime agent 正在修改 Extract，其他 agent
只能做 target-local plan/component/test，不能同时提交另一份 Extract patch。

## 3. 可直接交给其他 agent 的工作包

### Wave A — 现在即可并行，不占 shared-lock

| 包 | Owner | 允许写入 | 交付 | 禁止项 | 局部门 |
|---|---|---|---|---|---|
| **SVM-SDK-1 persistent facade** | worker | 新建 `ProofForge/Svm/Sdk/Storage.lean`、`ProofForge/Svm/Sdk/Queue.lean`；新建两个非 Phoenix example/test 文件 | 用现有 `AccountStorage.Source` 组合 POD Field、fixed-capacity Vec/Queue、ordered Map/RBMap/one-based allocator handle；两个独立小例子消费 facade | 不改 Runtime/Ops/IR/Emit/Extract；不复制 account offset 到操作调用；不使用 heap pointer/Array/Map 作持久状态 | 新 test module 单独 `lake env lean`；两个 example 的 focused `pf build --target svm` 和 Mollusk fixture |
| **EVM-SDK-1 access policy（已集成）** | worker + coordinator | `ProofForge/Evm/Sdk/Access.lean`、两个独立 example/test/runtime fixture；coordinator 接 umbrella/registry/Extract generic fix | fixed single-pending Address、`requireOwner`/`requireRunning`/two-step ownership；显式 state writes，旧 nominee 不残留 | 未增加 Runtime/Ops/IR/Emit case；未伪造 reentrancy error 或 roles map | dedicated Lean、solc + Anvil stale-nominee matrix；见 R5-001 |
| **QA-1 artifact manifest** | worker | 新建 `scripts/check_artifact_manifest.py`、`Tests/ArtifactManifestSpec.lean` 或独立 fixture 目录 | 从现有 build manifest 检查 digest、target、artifact size 与注册程序集合的一致性；输出 deterministic 诊断 | 不改 build 产物、registry、CI workflow 或计划文档；不执行部署 | script 自测、当前 SVM/EVM manifest 检查、`git diff --check` |

Wave A worker 的 example/test 暂不加入 `Examples.lean` / `Tests.lean` / registry；coordinator
集成时统一接线，以避免三个分支都修改聚合文件。

### Wave B — PF-COORD-1 合入后并行

| 包 | Owner | 允许写入 | 交付 | 禁止项 | 局部门 |
|---|---|---|---|---|---|
| **EVM-RT-1 bounded ABI（已集成）** | coordinator | `Evm.Codec` plan + `Evm.Codec.Emit` interpreter；dedicated example/test/Anvil fixture | shared `.boundedArray` 已绑定 canonical ABI dynamic array/tail：offset、length、padding、capacity、exact tail 全部 fail closed；固定 local word frame | 未复用 Borsh、修改 Core/Extract、开放无界 bytes/array 或增加 array opcode | 253-job Lean、18-contract solc、Anvil 18/18 malformed matrix；见 R1-010 |
| **SVM-RT-1 account view（已集成）** | worker + coordinator | `Svm.AccountView` component/source/emitter + bounded runtime account-count walk；dedicated example/test/Mollusk fixture | compile-time window、runtime-safe index、统一 account-count/OOB/duplicate/signer/writable/owner/data-length gate | 未做 runtime-selected geometry、写 view、persistent pointer 或 Token/Phoenix policy | 260-job Lean、AccountView sBPF、Mollusk 11/11；见 R2-001 |
| **EVM-SDK-2 static storage declarations（已集成）** | worker + coordinator | `Evm.Sdk.Storage.Static` compile-time descriptors；两个独立 examples/tests/Anvil fixtures；coordinator 接 umbrella/registry | scalar/record/fixed-array cursor 与 typed handles；布局对象只在抽取期存在，ordinary typed State access 继续走现有 Extract→EVM IR | 未改 hashed-map namespace；未做 runtime slot allocator、handle `sload` recipe 或新 Component/Emit case | descriptor/extracted-layout conformance + two contracts + solc/Anvil raw-slot matrix；见 R5-002 |
| **EVM-SDK-3 bounded roles（已集成）** | worker + coordinator | `Evm.Sdk.Roles.Set2` + 两个 existing static-layout consumers/tests/Anvil matrices | capacity-2 membership/grant/revoke slot 纯决策；权限/terminal/literal State write 保持 application-owned | 未做 Vector/hashed role map/runtime allocator/隐藏 write；indexed Address return 继续 fail closed | extraction slot/entry gate + two contracts zero/duplicate/full/revoke/authorization Anvil matrix；见 R5-003 |
| **EVM-SDK-4 Pausable policy（已集成）** | coordinator | `Evm.Sdk.Pausable` + Access compatibility delegates + TwoStepCounter/Credits/tests | canonical u8 flags、fail-closed predicates、replacement transitions；权限/事件/literal State write 保持 application-owned | 未增加 pause Ops/IR/Emit recipe 或 hidden slot；typed events 后置；reentrancy 继续等待 effect sequencing | narrow-scalar generic inline gate + focused extraction + 两份 Yul/ABI/bin identity + existing Anvil pause matrices；见 R5-004 |

Wave B 的上述组件包已经集成，`shared-lock` 保持释放。下一 wave 的 worker 必须保持
target-local；需要顶层 schema 接线时，把最小 hook 和预期 IR 写进交付说明，由 coordinator
集成。

### Wave C — Runtime contracts 稳定后并行

| 包 | 依赖 | 交付边界 |
|---|---|---|
| **SVM-RT-2a instruction layout（已集成）** | SVM-RT-1 | typed bounded scratch bank + instruction/metas/data/infos/signer-tail plan；1,024-byte OOM、alignment、duplicate region 在 emission 前 fail closed；见 R2-002 |
| **SVM-RT-2b instruction effects（已集成）** | SVM-RT-2a | bounded return data、multi-seed PDA/CPI meta/signer seeds；复用同一 scratch plan，未知 shape fail closed；见 R2-003 |
| **SVM-RT-3 Token-2022 TLV（envelope 已集成）** | SVM-RT-1/2 | allocation-free scalar cursor/bitmap 与 closed end/padding specialization 已落地；transfer-fee、hook/account requirements 继续按语义分片，未知 extension 不走 classic 82/165-byte path；见 R2-004 |
| **SVM-RT-4 invocation telemetry（已集成）** | generic Component bridge | remaining compute、stack height、compute diagnostic、fixed five-word hexadecimal logger；exact official syscall symbols，scalar-only 且 allocation-free；不新增 top-level Ops/IR/main Emit；见 R2-006 |
| **SVM-RT-5 sysvar component boundary（已集成）** | generic Component bridge | Clock/EpochSchedule/compile-time Rent 统一走 target-owned Query/interpreter；production source 不再生成 top-level value recipe，legacy Golden 委托同一实现，产物 byte-exact；见 R2-007 |
| **SVM-RT-6 complete unsigned sysvar views（已集成）** | SVM-RT-5 | Clock leader schedule + complete EpochSchedule unsigned/Bool fields；exact native 40-byte C layout，不误用 33-byte packed/POD layout；signed timestamps 继续 fail closed；见 R2-008 |
| **SVM-RT-7 checked lamport mutation（已集成）** | static Account handles + generic Component bridge | `Account.Handle.transferLamports` 绑定 target-owned checked debit/credit；static Loader-v3 walk 解析 backward duplicate alias，same-canonical、readonly、foreign source、insufficient 与 overflow 均在双 store 前 fail closed；foreign destination 与 validated zero no-op 可用；不走 System CPI、不暴露 pointer/runtime index；见 R2-009 |
| **SVM-RT-8 checked account-data resize（已集成）** | static Account handles + generic Component bridge | `Account.Handle.resizeData` 绑定 target-owned zero-initializing resize；Component capability 让 alias-aware walk 固定 invocation-entry length，managed-state alias、readonly、foreign owner、10 MiB ceiling 与 +10,240 growth 在 payload/length 写入前 fail closed；不走 System Allocate、不暴露 pointer/runtime geometry、不冒充 heap realloc；见 R2-010 |
| **SVM-SDK-2 transient（已集成）** | SVM-RT-2 | 直接复用 Heap/Scratch 的 invocation-local bounded buffer/fixed Vec/byte writer/signed-CPI codec composition；显式 capacity/alignment/frame/OOM，不复制 allocator/plan/lifetime，不能持久化 pointer；见 R3-003 |
| **SVM-SDK-3 PDA/System foundation（已集成）** | SVM-RT-2 | static ASCII PDA bump/check/signed-create 与 fixed-account System transfer/create；example 只见 SDK 名称，`pf_inline` 通用展开，不增加名字特判或 CPI recipe；见 R3-004 |
| **SVM-SDK-4 System core（已集成）** | SVM-SDK-3 | non-seeded assign/allocate/advanceNonce 直接组合既有 Runtime；SysAlloc/Nonce 只见 SDK 名称，canonical 产物不变；见 R3-005 |
| **SVM-SDK-5 classic Token（已集成）** | SVM-SDK-4 | CPI-relative handle、role-typed checked/unchecked transfer layout 与 fixed classic facade；Phoenix concrete layouts 仍在 Examples，十二个非 Phoenix consumer 与 Phoenix/PhoenixV1Profile 产物保持不变；见 R3-006 |
| **SVM-SDK-6 fixed ATA/Memo（已集成）** | SVM-SDK-5 | caller-selected Token program 的 fixed CreateIdempotent 与诚实名 fixed Memo facade；Ata/Memo canonical 产物不变；见 R3-007 |
| **SVM-SDK-7 seeded System（已集成）** | SVM-SDK-6 | generic compile-time ASCII seed 的 allocate/create/assign/transfer；自动 bincode length、closed geometry verifier gate、`ledger` 非特判证据；不新增 CPI recipe；见 R3-008 |
| **SVM-SDK-8 bounded static Memo（已集成）** | SVM-SDK-7 | ≤512-byte compile-time ASCII payload；共享 policy 只约束 exact Memo geometry，非 ASCII/超长 fail closed；不增加动态 String/Vec、Memo opcode 或 emitter case；见 R3-009 |
| **SVM-SDK-9 general remainder（ATA + Token state + close slices 已集成）** | SVM-SDK-8、SVM-RT-3 | role-typed static ATA 已组合 generic invoke；canonical program ids 与 exact SPL base views 已组合 account leaves；fixed-handle resize 已由 R2-010 收口，close/refund 已由 R3-025 组合既有 resize/lamport effects；继续分模块处理 rent top-up/owner reassignment、runtime-selected/UTF-8 Memo 与 Token-2022 typed extension facade；未知 extension/runtime account geometry 继续 fail closed；见 R3-010/011/025 |
| **SVM-SDK-10 source-visible transient Vector64（已集成）** | SVM-SDK-2、R2-005 | 一个 active handle 的 fixed-capacity u64 heap vector；begin/push/set/clear/finish/length/get、explicit full/OOB/state/OOM，复用 BatchRecorder 的 shared bump emitter；两个 consumer + Mollusk；不持久化 pointer、不增加 top-level Ops/IR/main Emit；见 R3-012 |
| **SVM-SDK-11 source-visible transient bytes（已集成）** | SVM-SDK-10 | 一个 byte handle 可与一个 Vector64 同时 active；checked push/set/get/length/clear/finish + fixed `appendLe64`，显式 OOM/full/OOB/state/range，仍复用 shared bump allocator；不持久化 pointer、不伪造 realloc/free、不增加 top-level Ops/IR/main Emit；见 R3-013 |
| **SVM-SDK-12 shared transient lifecycle（已集成）** | SVM-SDK-10/11 | Vector64/Bytes 共同的 allocation、metadata、active/capacity gate、clear/finish 由一个 target-owned interpreter 发射；concrete emitters 只拥有 element 语义，assembly byte-exact；见 R3-015 |
| **SVM-SDK-13 bounded log-data（已集成）** | SVM-SDK-11/12 | active byte prefix 通过 syscall-adjacent `[addr,len]` descriptor 发布为一个 `sol_log_data` field；不复制 payload、不暴露 pointer，Mollusk 钉 exact payload + scalar return；见 R3-016 |
| **SVM-SDK-14 transient Vector64 pop（已集成）** | SVM-SDK-10/12 | checked LIFO pop 原位缩短 active prefix 并返回旧尾元素；empty=`0x1202`，不分配、不清 payload、不伪造 reclaim/realloc，继续只扩 target component；见 R3-017 |
| **SVM-SDK-15 transient Bytes pop（已集成）** | SVM-SDK-11/12 | checked LIFO byte pop 原位缩短 active prefix 并返回旧尾 byte；empty=`0x1212`，不分配、不清 payload、不伪造 reclaim/realloc，继续只扩 target component；见 R3-018 |
| **SVM-SDK-16 shared transient truncate（已集成）** | SVM-SDK-10/11/12 | Vector64/Bytes 共用 Rust `Vec::truncate` 的 checked lifecycle transition；只缩短 active prefix，`>= current`（含 `UInt64.max`）no-op，不清 payload、不分配/reclaim/realloc、不新增 top-level Ops/IR/main Emit；见 R3-019 |
| **SVM-SDK-17 rent-exempt create（已集成）** | R3-004/008、R3-014 | regular/ASCII-seeded/PDA CreateAccount 组合 compile-time space + current Rent minimum；自定义 Rent Mollusk 核对 exact lamports/space/owner，不开放 runtime geometry/resize/close，不新增 Runtime/IR/Emit；见 R3-020 |
| **SVM-SDK-18 same-kind transient slots（已集成）** | SVM-SDK-10/11/12 | Vector64/Bytes 各有两个编译期 slot，共用 handle-word contract、32-byte metadata-bank stride 与 official-shaped bump heap；四 handle 可同时 active，生命周期/OOM 按 slot 隔离；不新增 Runtime leaf、top-level Ops/IR/main Emit 或 persistent pointer；见 R3-021 |
| **SVM-SDK-19 fixed-width transient records（已集成）** | SVM-SDK-10/12/18 | `Record64` 从 `(limbs, records)` 派生 Vector64 geometry，提供 `append1..4` whole-record preflight、aligned count/access/truncate/drop/clear；两个非 Phoenix consumer + Mollusk；不暴露 raw word push、pointer/realloc/reclaim，不新增 Runtime/Ops/IR/Component/main Emit；见 R3-022 |
| **SVM-SDK-20 first-class Pubkey values（已集成）** | R3-011 Pubkey/Program | `Account.Handle.key`/`.owner` 把完整 32-byte key/owner 投影为一等 compiler-erased `Pubkey`，`notEquals` 与收口后的 `sameKey`/`ownerIsKeyOf` 全部复用同一 `Pubkey.equals`；projection 写法钉住 matcher 边界；独立 `PubkeyGate` consumer + Mollusk 24/24；不新增 Runtime/Ops/IR/Component/main Emit，不分配，不含 word magic；见 R3-023 |
| **SVM-SDK-21 whole-value SDK record boundary（已集成）** | R1 static schema/Borsh、R3-023 | representation-free `@[pf_boundary]` 让 compiler-owned finite SDK datatype 复用 generic schema/projection/fixed result frame；`Pubkey` exact 32-byte Borsh input/return 由 RawEntry round-trip 与 Keys account projection 两个 consumer 验证；recursive/polymorphic/over-budget shape fail closed；不新增 type-specific Runtime/Ops/IR/Component/main Emit、allocation 或 pointer；见 R3-024 |
| **SVM-SDK-22 fixed-account close/refund（已集成）** | R2-009/010 checked effects、static Account handles | `Account.Handle.closeTo` 以一次 pre-effect balance snapshot 顺序组合 resize-to-zero 与 full-balance transfer；foreign-owned writable destination 可接收退款，post-resize overflow/alias failure 由 instruction rollback 原子恢复；不新增 Runtime/Ops/IR/Component/Emit、System CPI、pointer 或 heap；见 R3-025 |
| **SVM-SDK-23 persistent bounded BitSet（已集成）** | Core bounded BitSet、R3-001 typed account storage | shared bounds/word/mask/update policy 分别绑定 SVM fixed account words 与既有 EVM static slots；SVM bit capacity 自动派生 exact one-based word geometry，O(1) selected-word contains/insert/remove/toggle；FeatureBits/ClaimBits 两 consumer + Mollusk + Surfpool；不新增 Runtime/Ops/IR/Component/Emit、allocator、pointer、runtime length 或 scan；见 R3-026 |
| **SVM-SDK-24 persistent bounded enumerable Set（已集成）** | Core bounded Set position laws、R3-001 typed account storage/RBMap | shared position+1/count/move policy 分别绑定 SVM account RBMap 与既有 EVM static/hashed storage；SVM 从 account/base/capacity 派生完整 compact layout，支持 explicit initialize、value zero、bounded valueAt 与 validated swap-remove；MemberDirectory/UniqueRoster 两 consumer + Mollusk + Surfpool；不新增 Runtime/Ops/IR/Component/Emit、allocator/pointer/runtime geometry；见 R3-027 |
| **SVM-SDK-25 fixed-account version header（已集成）** | R3-001 typed account storage | 两个 adjacent typed Field 固定 nonzero discriminator/version；inspect 区分 fresh/ready/foreign/unsupported/malformed，init version-first/discriminator-last，Transition 只表示一个 static edge；VersionedLedger/VersionedMigrator + Mollusk + Surfpool；不新增 Runtime/Ops/IR/Component/Emit、allocator/pointer/runtime geometry；见 R3-028 |
| **SVM-SDK-26 typed transient wide vectors（已集成）** | SVM-SDK-19 fixed-width records、R1-023 wide result frame | `Vector128`/`Vector256` 以 fixed 2-/4-word `Record64` 组合 existing two-slot Vector64 effects；whole-value push/set 在首个 write 前完整 preflight，drop/truncate 保持 element alignment；两个 consumer + Mollusk 钉 full 16-/32-byte return；不新增 Runtime/Ops/IR/Component/Emit、allocator/pointer；见 R3-029 |
| **EVM-RT-ENV address balance（已集成）** | R4-008 Environment Component | `Address.balance : UInt256` 使用完整三-limb address 与单次 BALANCE observation；numeric 四-limb cache，不新增 top-level Ops/IR/main Emit；见 R4-011 |
| **EVM-RT-ENV transaction context（已集成）** | R4-008 Environment Component | `Context.origin : Address` 与 `gasPrice : UInt256` 使用单次 ORIGIN/GASPRICE observation + cached limb projection；不新增 top-level Ops/IR/main Emit，origin 不作为 access-control 推荐；见 R4-012 |
| **EVM-RT-ENV call selector（已集成）** | R4-008 Environment Component、shared FixedBytes | `Context.selector : Bytes4` 单次读取 calldata word 0 并按 source byte order 投影；不开放 arbitrary msg.data/pointer，不新增 top-level Ops/IR/main Emit；见 R4-013 |
| **EVM-RT-ENV calldata length（已集成）** | R4-008 Environment Component | `Context.calldataSize : UInt64` 观察 exact `CALLDATASIZE`；不开放 raw calldata/pointer/unchecked read，不新增 top-level Ops/IR/main Emit；见 R4-014 |
| **EVM-RT-ENV Cancun blob context（已集成）** | R4-008 Environment Component | full-width `blobBaseFee` + source-order `blobHash(index)`，各只观察一次 opcode；不开放 blob payload/allocation，不新增 top-level Ops/IR/main Emit；见 R4-015 |
| **EVM-RT-2a call result（已集成并由 R5-012 收紧）** | EVM-RT-1 | closed CALL/STATICCALL success + exact-word；ERC-20 只接受 exact canonical `1` 或 post-call code-backed empty，success-only empty 同样要求 code；≤32 copied bytes；显式 source result 不被 effect carrier 覆盖；见 R4-001/R5-012 |
| **EVM-RT-2b/c/d effects（已集成）** | EVM-RT-2a | typed LOG0..4/custom error/payable 与 fixed ecrecover contract；exact returndata 防 stale memory，不开放其他 precompile/delegatecall/create/arbitrary callee；见 R4-002/003/004 |
| **EVM-SDK-5 bounded payments（已集成）** | EVM-SDK-1/2/3/4、EVM-RT-2 | `Evm.Sdk.Payments` 收口 Ether/ERC20/WETH/fixed-router facade；Vault/TipJar/Ownable 不再直连 lower Source boundary，产物不变；见 R5-005 |
| **EVM-SDK-6a fungible debit（已集成）** | EVM-SDK-5 | explicit `AddressMap256` handle 的 balanceOf/canDebit/debit/insufficient；Token/Credits 独立复用且产物不变；见 R5-006 |
| **EVM-SDK-6b checked credit/transfer（已集成）** | EVM-SDK-6a | checked additive credit、cap-minus-supply mint gate、same-address-safe direct/delegated transfer；Token/Vault 两个 consumer，明确 overflow/alias/event/allowance ordering；见 R5-007 |
| **EVM-SDK-6c allowance core（已集成）** | EVM-SDK-6b | explicit pair-map handle 的 approve/checked increase/decrease/spend policy；Token/Ownable 两个 consumer，permit owner 与 event ordering 留在 application；见 R5-008 |
| **EVM-SDK-6d Reentrancy（已集成）** | EVM-RT-2e、EVM-SDK-2/5 | explicit UInt64 handle、nonzero sentinel、ordered enter/leave；GuardedPayout/EvmOrderedStorage 两 consumer + hostile callback；不新增 Runtime/IR/Emit recipe；见 R5-009 |
| **EVM-SDK runtime-code observation（已集成）** | R4-010 Address codeSize | `Address.hasCode` 纯组合 existing EXTCODESIZE query + UInt64 compare；不冒充 EOA/authentication/call-success，不自动改 closed CALL，不新增 Runtime/IR/Emit；见 R5-011 |
| **EVM-SDK safe closed-call result（已集成）** | EVM-RT-2a、R5-011 | `Evm.CallResult` 唯一 interpreter + `Sdk.Effect.thenTrue` canonical Bool composition；false/2/EOA-empty fail closed，code-backed no-return compatible；exact-32 比 OZ ≥32 更严格，revert bubbling 仍未开放；见 R5-012 |
| **EVM-SDK-7 bounded ERC-721（已集成）** | EVM-SDK-6c/6d | 四个 compile-time hashed-map handles 上的 192-bit-key owner/approval/operator/balance core；Collectible/Badge 两 consumer；不可编码 id 在截断前拒绝；standard Address views/events/receiver callback 继续 fail closed；见 R5-013 |
| **EVM-SDK-8 bounded ERC-1155（已集成）** | EVM-SDK-6c/6d、EVM-SDK-7 | 192-bit-key single-id UInt256 balance/operator/checked movement core；MultiToken/CraftToken 两 consumer；view/auth/write 先 gate 再截断，不开放 batch/receiver/metadata/standard event；见 R5-014 |
| **EVM-SDK-9 persistent StorageBitmap（已集成）** | Core bounded BitSet、EVM-SDK-2 | compile-time bit capacity 绑定 ordinary fixed `Vector UInt64 wordCount` state；O(1) checked read/set/clear/toggle，不新增 Runtime/Ops/IR/Emit；EvmFeatureFlags/EvmClaimBitmap 两 consumer；bulk iteration/enumeration 继续 fail closed；见 R5-015 |
| **EVM-SDK-10 persistent StorageRing（已集成）** | Core bounded Queue、EVM-SDK-2/5 | compile-time UInt64 payload/head/live static geometry；O(1) checked push/pop/peek/get/clear、modulo wraparound、malformed metadata fail closed；EvmRingMailbox/EvmRingHistory 两 consumer；不新增 Runtime/Ops/IR/Emit；见 R5-016 |
| **EVM-SDK-11 persistent StorageEnumerableSet（已集成）** | Core bounded Set、EVM-SDK-2/10、generic effect sequencing | compile-time fixed UInt64 vector + live count + key→position+1 map；O(1) insert/contains/valueAt/swap-remove，key zero 与 malformed backing fail-closed；EvmAllowlist/EvmIdRegistry 两 consumer；generic mutable-query snapshot 保证 effect/State write 共享 pre-state，不新增 set-specific Runtime/Ops/IR/Emit；见 R5-017 |
| **EVM-SDK-12 persistent StorageCheckpoints（已集成）** | EVM-SDK-2/5、fixed-vector extraction | adjacent static UInt64 keys/values vectors + live count；capacity 1..4、strict persisted order、monotonic append、same-latest overwrite、latest/first-≥ lower-bound；Book/Trace 两 consumer + Anvil corruption；不新增 Runtime/Ops/IR/Component/Emit/allocator；见 R5-018 |
| **EVM-SDK-13 persistent StorageEnumerableMap（已集成）** | EVM-SDK-11、typed hashed maps、generic effect sequencing | fixed UInt64 keys/count/position+1 index + disjoint key→value namespace；O(1) insert/update/lookup/index/swap-remove，key/value zero、dual-map clear 与 moved-key position repair；ConfigMap/ScoreMap 两 consumer + Anvil corruption；不新增 Runtime/Ops/IR/Component/Emit/allocator/scan；见 R5-019 |
| **Shared/EVM-SDK SafeCast（已集成）** | Core wide values、ordinary inline control、generic fixed-scalar `Except` bind | shared UInt128/UInt256→UInt8/UInt16/UInt32/UInt64 checked narrowing，caller-owned typed error；UInt8/16/32 路径 gate upper limbs 与 exact low-word limits；owner-gated UInt8 consumer widen result 以保留 full auth sentinel；ordinary normalization 不变；不新增 target Runtime/Ops/IR/CFG/Component/Emit/allocation；见 R5-020..023 |
| **Shared static wide result frames（已集成）** | `@[pf_boundary]`、Core Value、SVM CFG | UInt128/UInt256 constructor 复用 generic fixed frame；component effect 后保留 2/4 leaves，SVM successful exit 与 `retCount` 不一致时 fail closed；不新增 wide-specific Runtime/Ops/IR/Component/Emit；见 R1-023 |
| **Shared bounded/saturating/logarithmic/root UInt64 Math（已集成）** | ordinary UInt64 scalar control/arithmetic + bounded local-frame loops | `Core.Math.UInt64` 提供 min/max、overflow-safe floor average、caller-typed checked ceilDiv、explicit saturating add/sub/mul、floor log2/log10/log256 与 floor sqrt；BatchSizer/EvmPriceBand 分别绑定 SVM/EVM policy；structural guard 钉住 saturation preflight、log ladders、5-step root seed + 6-step Newton frame，并拒绝 additive-loop 误识别和 target extension effect；见 R1-024..027 |

## 4. Worker 统一交付合同

每个 code agent 从最新 `origin/main` 建自己的 reviewable 分支/commit，不直接合并或 force-push
`main`。完成时只需要返回：

1. commit SHA 和准确 write set；
2. source API、lowering path、资源上界和 fail-closed 边界；
3. 运行过的命令及通过数量；
4. 需要 coordinator 完成的最小 integration hook；
5. 已知未完成项，不得用 placeholder、magic selector/offset 或测试 special case 掩盖。

Coordinator 集成顺序固定为：检查 write set → review target contract → 接 shared hook/顶层 import
→ focused test → 双目标全回归 → 更新计划证据 → 一个稳定切片一个 commit。不同 worker 的
commit 不直接互相 cherry-pick；都以 `origin/main` 的已集成状态为下一基线。

## 5. Agent prompt 最小模板

```text
在 ProofForge 仓库实现工作包 <ID>。从最新 origin/main 开始，严格遵守
docs/plan/parallel-workstreams.md 的 write set；不要修改 shared-lock、docs/plan、registry、
顶层 imports 或 CI。目标是 <交付>，资源/fail-closed 边界是 <边界>。复用现有 Component/Source
模式，不新增协议 opcode 或主 emitter recipe。添加 dedicated tests 并运行表中局部门。
完成后给出 commit SHA、文件列表、验证结果和 coordinator 所需的最小 integration hook；
不要 push/merge main。
```

这套拆法允许 target-local Runtime 和两个 SDK 方向真正并行，同时把最容易发生语义漂移的
shared schema/Extract/registry 留在单一集成路径。
