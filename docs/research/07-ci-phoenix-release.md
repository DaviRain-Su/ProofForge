# CI 耗时 · Phoenix 拆分 · CLI/SDK 发版调研

> 日期：2026-09-02 · 性质：调研结论（不含代码改动承诺）  
> 证据基线：CI run [`33615137771`](https://github.com/DaviRain-Su/ProofForge/actions/runs/33615137771) 逐步耗时；近期成功 run 墙钟约 **50–53 min**。  
> 相关已有方案：[productization.md](../plan/productization.md)、[ci-001](../plan/tasks/ci-001.md)、[prod-004](../plan/tasks/prod-004.md)、[phoenix.md](../modules/phoenix.md)。

## 0. 一句话结论

反馈慢的根因不是「某一条脚本慢」，而是 **每次 commit 无差别跑满四条轨道**，其中 **SVM 被 Phoenix（编译+Mollusk+Surfpool×2）拖到 ~60min**，**NEAR 仍重复整仓 `lake build Tests`（~46min）**，而 **网站 workflow 已有的 path filter 没有用到主 CI**。  
Phoenix 应先从默认 PR CI 分流，再拆独立项目。  
CLI/SDK 产品化（prod-001…004）代码面已齐，**缺的是首次 `v*` Release**，不是再造一套工具链。

---

## 1. 当前 CI 画像

### 1.1 触发面

| Workflow | 触发 | Path filter |
|---|---|---|
| `ci.yml` | 任意 `push`→`main`、任意 `pull_request` | **无** |
| `website.yml` | `website/**` 变更 | **有** |
| `release.yml` | `v*` tag | n/a |

因此：改 `docs/`、单测一个 NEAR sandbox、改 Phoenix 撮合，都会拉起 Lean + SVM + EVM + NEAR 全套。

### 1.2 实测逐步耗时（run 33615137771）

| Lane | 墙钟量级 | 主要步骤 |
|---|---|---|
| **Lean** | ~46 min | `lake build` + `lake build Tests` **2578s**（含 PhoenixSpec / PhoenixV1ProfileSpec） |
| **SVM** | ~60 min ★最慢 | Mollusk **1582s**；Phoenix Surfpool **375s**；PhoenixV1Profile Surfpool **669s**；`pf build` 全部 SVM **596s**；`lake build Examples` **277s** |
| **EVM** | ~13 min | `pf build` EVM **388s**；Examples **259s**；Anvil **79s**；XRPL 可忽略 |
| **NEAR** | ~59 min | **再次** `lake build`+Tests **2767s**；`pf build` near **425s**；~35 个 sandbox 串行合计 ~11 min |
| 聚合 `test` | 等最慢 lane | `needs: [lean,svm,evm,near]` + `if: always()` |

成功 run 墙钟约 **50–53 min**（由 SVM/NEAR 封顶）。大量 PR 在迭代中被 `concurrency: cancel-in-progress` 取消——取消本身合理，但每次推送仍会重新冷启动最重步骤。

### 1.3 已修过、仍漏掉的点

[ci-001](../plan/tasks/ci-001.md) 已把 **SVM/EVM 的重复 `lake build Tests` 抽到 Lean lane**。  
**NEAR lane 没有吃到这次修复**，仍独立编译整套 Tests（含 Phoenix），等于把最贵的 Lean 门又跑一遍。

缓存只覆盖 toolchain / `.lake/packages` / Mollusk `target`，**不覆盖 `.lake/build` olean**，所以每次 job 基本是冷 elaborator。

---

## 2. 如何降低 CI 耗时（按优先级）

### P0 — 快赢（改 workflow 即可，风险低）

1. **Path / 变更检测分流**（对标 `website.yml`）  
   - `docs/**`、`website/**`、纯 markdown → 跳过 runtime lanes，或只跑轻量 lint。  
   - `ProofForge/Wasm/Near/**` + `runtime-tests/near/**` → 只跑 Lean guards + NEAR。  
   - `ProofForge/Evm/**` + `runtime-tests/evm/**` → Lean + EVM。  
   - `ProofForge/Svm/**` / `Examples/Svm/**`（非 Phoenix）→ Lean + SVM（轻量子集）。  
   - `main` 合入 / nightly / `workflow_dispatch` → 全量。  
   - 实现可选：`dorny/paths-filter` 或 `paths:` + 多 workflow。

2. **NEAR 对齐 ci-001**  
   - NEAR job **禁止**再跑完整 `lake build Tests`；只 `lake build Examples`（或 Wasm/Near 相关）+ `pf build --target near` + sandbox。  
   - 预期：NEAR 从 ~59 min → ~15–20 min 量级，全仓墙钟立刻被 SVM 单独封顶。

3. **默认 PR 不部署 Phoenix Surfpool**  
   - 主 CI 保留 Counter / RawEntry 级 Loader-v3 smoke（或完全放到 nightly）。  
   - Phoenix / PhoenixV1Profile Surfpool → `ci-phoenix.yml`（nightly + label `phoenix` + `workflow_dispatch`）。  
   - 预期：SVM 少掉 ~17 min（375+669s）。

### P1 — 中等收益

4. **Phoenix 退出默认 Lean Tests / Mollusk 默认矩阵**  
   - `Tests.lean` 聚合拆成 `Tests`（快）与 `TestsPhoenix`（重）。  
   - Mollusk：默认 `cargo test` 排除 `phoenix*`；Phoenix crate/feature 或独立 job。  
   - Lean lane 有望从 ~46 min 明显下降（PhoenixSpec+V1 约 3.3k LOC Lean 证明）。

5. **增量 / 烟雾 lane**  
   - PR 默认：`pf build` 只构建变更涉及的 Registry 程序 + 一组 smoke（Counter、Token、一个 Wasm）。  
   - 全 Registry（67 SVM / 40 EVM / …）留给 `main` 与 nightly。

6. **并行化 NEAR sandbox**  
   - 35 个串行 script → `strategy.matrix` 或 xargs 并行（注意 sandbox 端口冲突，需隔离）。  
   - 墙钟可再砍数分钟。

### P2 — 结构性

7. **缓存 `.lake/build` olean**（按 `lean-toolchain` + manifest + 源 hash 分键；注意 dirty 风险，建议 restore-keys 谨慎）。  
8. **拆 XRPL 出 EVM job**（当前 XRPL 便宜，优先级低；主要为失败归因清晰）。  
9. **Mollusk `--test-threads=1` 评估**：若可按文件分 job 并行，比单进程串行更划算。

### 预期数量级（粗算）

| 动作组合 | 典型 PR 反馈墙钟 |
|---|---|
| 现状 | ~50–60 min |
| P0（path + NEAR 去重 + Phoenix Surfpool 分流） | ~25–35 min（SVM Mollusk 仍重） |
| P0+P1（再去掉默认 Phoenix Lean/Mollusk） | ~15–25 min |
| + 增量 build | 小改动可到 **个位数～15 min** |

---

## 3. Phoenix 单独摘出

### 3.1 为什么现在就该动

| 资产 | 体量（约） |
|---|---|
| `Examples/Svm/Phoenix.lean` | 3155 LOC |
| `Examples/Svm/PhoenixV1Profile.lean` | 2616 LOC |
| `Examples/Svm/PhoenixV1Layout.lean` | 288 LOC |
| `Tests/PhoenixSpec.lean` + `PhoenixV1ProfileSpec.lean` | ~3367 LOC |
| `runtime-tests/solana/tests/phoenix*.rs` | ~7463 LOC |
| **合计** | **~17k LOC**，且贯穿 Lean / 全量 SVM build / Mollusk / Surfpool |

所有权规则已明确：**Phoenix 名字/offset/撮合不得进入 `ProofForge/Svm`**（见 svm-work-plan）。它是 **应用层消费者**，不是编译器/SDK 核心——继续放在默认 CI 等于用应用回归绑架工具链反馈。

### 3.2 建议两阶段，不要一步拆仓

```
阶段 A（同仓分流，立刻降本）
  Examples/Svm/Phoenix* + Tests/Phoenix* + phoenix*.rs
  → 保留在 monorepo
  → 移出默认 ci.yml；新建 ci-phoenix.yml（nightly / label / dispatch）
  → Registry 仍可登记，但「build all」默认列表可排除或打标 heavy

阶段 B（独立项目，SDK 发版稳定后）
  新仓 proof-forge-phoenix（或 Ellipsis 风格应用仓）
  lakefile: require ProofForgeSvmSdk from git @ "vX.Y.Z"
  合约只 import ProofForge.Attr + ProofForge.Svm.Sdk
  自有 Mollusk / Surfpool / digest pin
  ProofForge 主仓保留 1–2 个非 Phoenix consumer 证明同一 SDK 能力
```

阶段 B 依赖产品化已具备的能力：`pf build --module`、Lake `*Sdk` 包、`require … @ tag`。  
**不要**在 SDK tag 未稳时强行拆仓，否则两边会跟 main 漂移。

### 3.3 拆仓验收（阶段 B）

1. 干净机器：`pf` Release 二进制 + `require … @ vX.Y.Z` → 构建 Phoenix 出 `.so`。  
2. 主仓 CI 不再出现 Phoenix Surfpool / PhoenixSpec。  
3. 主仓仍有 ≥2 个非 Phoenix 程序覆盖 Phoenix 用过的 SDK 叶子（ownership 惯例）。  
4. Phoenix 仓 CI 失败不红 ProofForge 工具链 PR。

---

## 4. CLI / SDK 要不要正式发版本？

### 4.1 答案：要，而且路径已经铺好

[productization.md](../plan/productization.md) 定义的三角色与行业惯例一致：

| 角色 | ProofForge | 行业对标 |
|---|---|---|
| CLI | `pf` 二进制（linux/mac） | `forge` / `anchor` / `near` CLI |
| SDK | `ProofForgeSvmSdk` / `ProofForgeEvmSdk` Lake lib | `forge-std` / `@coral-xyz/anchor` / `near-sdk` |
| 模板 | `pf init` + `templates/*-counter` | `forge init` / `anchor init` |

prod-001…004 **必做项已勾选**；`.github/workflows/release.yml` 已能按 `v*` 产出 CLI + checksums + Lake require 说明 + capability 摘要。

### 4.2 真正缺口

| 项 | 状态 |
|---|---|
| Lake libs 拆分 / import 守卫 | 已有 |
| `pf init` / 模板 | 已有 |
| `pf --version` pin | 已有 |
| Release workflow | 已有 |
| **公开 `v*` GitHub Release** | **未见**（`lakefile` 仍 `version := v!"0.0.1"`） |
| 干净机器「装 CLI → require tag → 模板 build」人工复核 | prod-004 仍标建议人工复核 |

### 4.3 发版建议

1. **立刻切 `v0.1.0`（或 `v0.0.1`）试发**，走通 Release 流水线；能力清单用 fail-closed 措辞（已有 `release-capability-summary.md`）。  
2. **CLI 与 SDK 同版本号**（productization 已定原则），避免「CLI 抽了 SDK 不懂的 effect」。  
3. Semver 实务：  
   - `0.x`：允许 breaking（IR/digest/SDK 面变更在 notes 写明）。  
   - SDK 面新增叶子 → minor；破坏 import/行为 → major（或 0.x 的 minor 当 breaking）。  
4. 后续可选：NEAR/XRPL SDK facade + 模板（productization 已 defer）。  
5. **不要**为发版再拆多个 git 仓；先单仓多 lib + tag（文档已写明）。Phoenix 独立仓是应用层事，不是 SDK 分发前提。

### 4.4 工具齐全清单（对标「智能合约开发全家桶」）

| 能力 | 现状 | 下一步 |
|---|---|---|
| 写合约（SDK） | SVM/EVM 可用；Wasm facade 进行中 | 钉 tag |
| 初始化工程 | `pf init` | 文档/网站 Quickstart 指向 Release |
| 编译 | `pf build --module` / `pf.toml` | Release 二进制安装说明 |
| 本地验证 | Mollusk / Anvil / near-sandbox / XRPL | 保持；PR 默认减负 |
| 部署 | Surfpool / `pf deploy`（XRPL 等） | 与发版 notes 对齐支持面 |
| 版本钉 | `pf --version` + lean-toolchain | 首次 tag |
| 应用级大程序 | Phoenix 在 monorepo | 分流 → 独立仓 |

---

## 5. 建议执行顺序（给主仓）

1. **本周工程**：path-filter + NEAR 去掉重复 `lake build Tests` + Phoenix Surfpool/重测试移出默认 PR CI。  
2. **同周产品**：打 `v0.1.0`，验证「干净机器模板 build」。  
3. **随后**：`Tests` / Mollusk 拆出 Phoenix 重集；增量 `pf build`。  
4. **SDK tag 稳定后**：Phoenix 迁独立仓，主仓只保留轻量 consumer。

---

## 6. 非目标（本调研明确不主张）

- 为了加速而削弱 ownership / fail-closed 语义。  
- 把 Phoenix 政策或撮合逻辑塞进 SDK。  
- 一上来拆 `proof-forge-sdk` 独立仓（发版不需要）。  
- 用「只跑 SVM」取代多 target 合入门——`main`/nightly 仍应全绿。


## 7. P0 / P1 落地状态（2026-09-02，合并 #15）

| 项 | 状态 |
|---|---|
| Path filter 四轨分流 | ✅ main 已有；保持 |
| NEAR 去掉重复 `lake build Tests` | ✅ |
| Phoenix Lean specs 退出默认 Tests | ✅（#15：`PhoenixTests`） |
| Phoenix Mollusk 独立 crate + lane | ✅（#15：`runtime-tests/phoenix`） |
| Phoenix Surfpool 退出默认 SVM | ✅（专属 `phoenix` job） |
| 聚合 `test` needs phoenix | ✅（修 #15 空 result 竞态） |
| Phoenix Surfpool（非 V1） | ✅ 留在 PR `phoenix` lane |
| PhoenixV1 Surfpool | ✅ 挪到 `ci-phoenix.yml` nightly（PR 上 45m 仍超时） |
| 本地 `scripts/ci_local.sh` | ✅（V1 Surfpool 需 `PHOENIX_V1_SURFPOOL=1`） |
| 首次 `v*` Release / Phoenix 独立仓 | 后续 |
