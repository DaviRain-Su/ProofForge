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
  ownership/reproducibility 门。

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
| **SVM-SDK-2 transient（已集成）** | SVM-RT-2 | 直接复用 Heap/Scratch 的 invocation-local bounded buffer/fixed Vec/byte writer/signed-CPI codec composition；显式 capacity/alignment/frame/OOM，不复制 allocator/plan/lifetime，不能持久化 pointer；见 R3-003 |
| **SVM-SDK-3 PDA/System foundation（已集成）** | SVM-RT-2 | static ASCII PDA bump/check/signed-create 与 fixed-account System transfer/create；example 只见 SDK 名称，`pf_inline` 通用展开，不增加名字特判或 CPI recipe；见 R3-004 |
| **SVM-SDK-4 System core（已集成）** | SVM-SDK-3 | non-seeded assign/allocate/advanceNonce 直接组合既有 Runtime；SysAlloc/Nonce 只见 SDK 名称，canonical 产物不变；见 R3-005 |
| **SVM-SDK-5 seeded System/Token remainder** | SVM-SDK-4、SVM-RT-3 | 分模块收口 seeded System 与 classic Token/Token-2022 typed facade；逐条复用既有 Runtime/typed TLV contract，每类至少两个非 Phoenix consumer；未知 extension/account geometry 继续 fail closed |
| **EVM-RT-2a call result（已集成）** | EVM-RT-1 | closed CALL/STATICCALL success + bounded empty/nonzero/exact-word policy；≤32 copied bytes；见 R4-001 |
| **EVM-RT-2b/c/d effects（已集成）** | EVM-RT-2a | typed LOG0..4/custom error/payable 与 fixed ecrecover contract；exact returndata 防 stale memory，不开放其他 precompile/delegatecall/create/arbitrary callee；见 R4-002/003/004 |
| **EVM-SDK-5 assets** | EVM-SDK-1/2/3/4、EVM-RT-2 | reusable fungible、ERC-721、bounded ERC-1155 core；每个组件至少两个 consumer |

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
