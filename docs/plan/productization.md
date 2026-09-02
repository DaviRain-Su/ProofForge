# 产品化拆分：CLI · SDK · 模板 · Release

> 更新：2026-09-01。本文是 **ProofForge 走向可安装开发工具** 的权威拆分方案。
> 它不替代 [runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) 的能力排期；
> 它回答「用户项目如何只依赖 SDK、如何初始化、如何发布制品」。
> 执行任务见 [prod-001](tasks/prod-001.md) … [prod-004](tasks/prod-004.md)。

## 1. 结论

ProofForge 作为正规合约开发工具，对外应暴露 **三样东西**，而不是一个耦合 monorepo：

| 制品 | 用户拿到什么 | 用户怎么用 |
|---|---|---|
| **CLI `pf`** | 预编译可执行文件（或 `lake exe pf`） | `pf init` / `pf build` / `pf deploy` |
| **Target SDK** | 可单独 `import` 的 Lean 库 | 合约源码只依赖 SDK + Attr |
| **项目模板** | `pf init --target svm\|evm|…` 生成的 Lake 工程 | 模板已 `require` SDK，可直接写 `@[pf_entry]` |

当前仓库把编译器、Emit、Registry fixture、Examples 回归、以及合约面 SDK **捆成同一个 `lean_lib ProofForge`**。
结果是：

1. 合约侧常见 `import ProofForge`（约 147 个 Examples），一次性拖进 Emit / Assemble / Registry / 全 target。
2. CLI 写死 `Examples.<Name>` 模块路径，外部工程无法作为一等公民构建。
3. 没有 `init` / 模板 / 版本化 release，克隆整仓是唯一上手路径。

**下一步不是继续堆 Runtime 叶子，而是先把产品边界切开。**

## 2. 当前耦合诊断

```diagram
今天（单包）

┌─────────────────────────────────────────────────────────┐
│ lean_lib ProofForge  (= ProofForge.lean 伞模块)          │
│  Attr · Profile · Extract · Core                         │
│  Svm.{Runtime,Sdk,IR,Emit,Assemble,Registry}             │
│  Evm.{Runtime,Sdk,IR,Emit,Assemble,Registry}             │
│  Wasm.{Near,Xrpl}.{…}                                    │
└───────────────┬───────────────────────────┬──────────────┘
                │ import ProofForge         │ root Cli
                ▼                           ▼
         Examples / 用户合约              lean_exe pf
```

| 症状 | 证据 | 产品后果 |
|---|---|---|
| 伞模块过重 | `ProofForge.lean` 同时 import 各 target 的 `*.Emit` / `Assemble` / `Registry` | 合约 elaborator 加载编译器后端 |
| SDK 已有语义边界，无包边界 | `ProofForge.Evm.Sdk` / `Svm.Sdk` 文档要求应用只 import 它们；Lake 仍只有一个 lib | 「能单独写 import」≠「能单独依赖」 |
| SDK 仍穿透到 Runtime/Source | `Evm.Sdk.Base` → `Runtime` / `*.Source`；`Svm.Sdk.Account` → `Runtime` | 合理（`pf_inline` 擦除需要），但必须 **止于 Source/Runtime，不到 Emit** |
| CLI 命名空间写死 | `Cli.lean`：`Lean.Name.str \`Examples name` | 外部包 `MyProtocol.Vault` 无法 `pf build` |
| Registry = 仓内回归表 | `Svm.Registry` / `Evm.Registry` 钉 Examples digest | 用户项目不该进入这条表，也不该被强制对照 |
| 无模板 / 无 release | 无 `templates/`、无 `pf init`、无 versioned SDK tag 工作流 | 无法产品化分发 |

语义 ownership（R0 anti-leak）已经正确：**应用不 import Emit；target 不 import Examples**。
缺的是 **分发 ownership**：哪些 Lake 包可安装、CLI 如何发现用户模块、tag 如何切。

## 3. 目标产品形状

```diagram
用户机器

  pf (CLI binary)                    Lake require (git tag / path)
        │                                    │
        │ build/deploy                       ▼
        │                          ┌─────────────────────┐
        │                          │ proof-forge-sdk-svm │  或 sdk-evm / …
        │                          │  Attr + Svm.Sdk     │
        │                          │  (+ Runtime/Source  │
        │                          │   供 inline 擦除)   │
        │                          └──────────┬──────────┘
        │                                     │ import ProofForge.Svm.Sdk
        ▼                                     ▼
  读取用户 Lake 包 ────── elaborator ──► 抽出 IR ──► target Emit/Assemble
  (模块路径可配置)                         ▲
                                           │ 仅 CLI/compiler 包持有
                                    ┌──────┴──────┐
                                    │ pf-compiler │  Extract/IR/Emit/…
                                    └─────────────┘
```

### 3.1 包切分（Lake libs，同仓可先切）

保持 **一个 git monorepo**，先切 `lean_lib` 边界；不必一上来拆多个 git 仓。

| Lake 目标 | roots / 内容 | 谁依赖它 |
|---|---|---|
| `ProofForgeAttr` | `ProofForge.Attr` | 所有 SDK、compiler |
| `ProofForgeCore` | `ProofForge.Core.*`、`Profile`、共享 Value/Math/SafeCast | SDK + compiler |
| `ProofForgeSvmSdk` | `ProofForge.Svm.Sdk` (+ 其擦除所需 Runtime/Source/AccountStorage **不含 Emit**) | SVM 用户工程、Examples.Svm |
| `ProofForgeEvmSdk` | `ProofForge.Evm.Sdk` (+ Runtime/Source **不含 Emit**) | EVM 用户工程、Examples.Evm |
| `ProofForgeWasmSdk`（可选后续） | Near/Xrpl 合约面 facade | WASM 用户工程 |
| `ProofForgeCompiler` | Extract、各 target IR/Emit/Assemble/Component.Emit、Cli | 仅 `pf` 与仓内 Tests |
| `Examples` / `Tests` | 回归 | CI；**不是**发布 SDK 的一部分 |

伞模块 `ProofForge.lean` 降级为 **开发者便利聚合**（compiler workspace 用），
**禁止**出现在用户模板与 SDK 文档的推荐 import 里。

验收门（prod-001/002）：

- 用户模板 `lakefile` 只 `require` / 依赖对应 `*Sdk` lib。
- `import ProofForge.Svm.Sdk` 的传递闭包 **不含** `ProofForge.Svm.Emit`、`Assemble`、`Registry`。
- 对 EVM /（以后）WASM SDK 同样成立。
- CI 增加 import-graph / 路径守卫（扩展 `scripts/check_ownership.py`）。

### 3.2 合约推荐 import

```lean
-- SVM 程序
import ProofForge.Attr
import ProofForge.Svm.Sdk

-- EVM 合约
import ProofForge.Attr
import ProofForge.Evm.Sdk
```

已有好例子：`Examples/Evm/Vault.lean` → `import ProofForge.Evm.Sdk`；
`Examples/Svm/VersionedLedger.lean` → Attr + `Svm.Sdk.Versioned`。
坏例子：`Examples/Counter.lean` → `import ProofForge`（应迁走）。

### 3.3 CLI 去 `Examples` 硬编码

`pf build` 必须从用户工程解析模块名：

1. **显式参数**：`pf build --target svm MyProtocol.Counter`
2. **项目清单**：工程根 `pf.toml`（或 `lakefile` 约定）列出 `[[program]] name / module / target`
3. **仓内回归**：本仓 CI 仍可用 Registry + `Examples.*`；那是 compiler 测试夹具，不是产品 API

`pf` 负责：配置 Lake search path → `importModules` 用户模块 → Extract → target Emit/Assemble。
Digest 对照只在「声明了 golden」时启用；用户默认工程不做 fixture pin。

### 3.4 初始化模板

```text
pf init my-vault --target evm
pf init my-program --target svm
# 后续：--target near | xrpl
```

生成（见仓内 `templates/` 骨架）：

```text
my-program/
  lakefile.lean          -- require ProofForgeSvmSdk（path 或 git tag）
  lean-toolchain         -- 与发布钉死同一 toolchain
  pf.toml                -- target + program 模块列表
  MyProgram.lean         -- 最小 @[pf_entry] 合约，只 import SDK
  README.md
```

模板约束：

- 只依赖对应 target SDK，不依赖 Examples / Tests / Emit。
- 自带一个可 `pf build` 的最小程序（Counter 级别）。
- SVM / EVM 模板分离；不要一个「全能」模板塞两个物理模型。
- WASM 家族模板等 SDK facade 稳定后再加。

### 3.5 Release 发布（产品化后半段）

| 通道 | 内容 | 机制 |
|---|---|---|
| GitHub Release | `pf` 二进制（linux/mac）、校验和、changelog | CI 按 tag 构建 `lake build pf` 并上传 |
| Lake 依赖 | `ProofForgeSvmSdk` / `ProofForgeEvmSdk` 源码包 | 同仓 tag `vX.Y.Z`；用户 `require … from git @ "vX.Y.Z"` |
| 工具链钉 | `lean-toolchain`、sbpf、solc、wat2wasm 版本 | Release notes 与 `pf --version` 打印同一组 pin |
| 能力清单 | 本版本 fail-closed ceiling（摘自 capability matrix） | `docs` 或 `pf.toml` schema 的 `capabilities` 段 |

发布原则：

- **SDK tag 与 CLI tag 同版本号**，避免「CLI 0.4 抽了 SDK 0.3 不懂的 effect」。
- Examples / Tests / research **不进** SDK 包 root。
- 先做「单仓多 lib + tag」，再评估是否拆 `proof-forge-sdk` 独立仓（有独立 semver 需求时再拆）。

## 4. 分阶段交付

| 阶段 | 目标 | 不做 |
|---|---|---|
| **P0 · 表面冻结**（[prod-001](tasks/prod-001.md)） | 文档规定推荐 import；CI 禁止 Examples 新增 `import ProofForge` 伞模块；扩展 anti-leak 检查 SDK→Emit | 尚不改 Lake 包图 |
| **P1 · Lake 包拆分**（[prod-002](tasks/prod-002.md)） | 落地 `*Sdk` / `Compiler` libs；伞模块仅 compiler workspace；传递闭包测试 | 不改链上语义 / digest |
| **P2 · init + 模板**（[prod-003](tasks/prod-003.md)） | `pf init`；`templates/svm-counter`、`templates/evm-counter` 可在隔离目录 `pf build` | 不上应用商店式注册表 |
| **P3 · Release**（[prod-004](tasks/prod-004.md)） | tag 发布 CLI 二进制 + SDK require 说明；`pf --version`；能力清单 | 不承诺多仓拆分 |

每阶段 Definition of Done：

1. 边界可用一句话描述，且有 CI 守卫。
2. 本仓全 target 回归不红（SVM/EVM；WASM 按现有 lane）。
3. 用户路径（模板或文档）不再要求克隆后 `import ProofForge` 伞模块。
4. 不把 Phoenix / 协议名或 Examples 路径泄漏进 SDK 包。

## 5. 与现有路线图的关系

| 已有文档 | 关系 |
|---|---|
| [runtime-sdk-roadmap.md](runtime-sdk-roadmap.md) | 继续定义 **能力** 谁拥有、ceiling 是什么 |
| [capability-matrix.md](capability-matrix.md) | Release 能力清单的数据源 |
| [svm-work-plan.md](svm-work-plan.md) | SVM 能力/形式化主线；产品化与之 **并行**，不抢 Runtime 切片的 write set |
| R0 ownership / `check_ownership.py` | 产品化 P0/P1 **扩展**同一 ownership 思想到「可安装包」 |

并行规则：产品化改 `lakefile`、Cli、templates、docs、ownership script；
**默认不改** target Emit interpreter 与 IR digest。若 P1 为断 Emit 依赖必须挪文件，保持 byte-identical 产物。

## 6. 非目标

- 新合约语法或新包管理器（继续 Lake + 普通 Lean）。
- 把 SDK 做成隐藏状态写入的「框架」；仍是显式 effect / 显式 State。
- 统一 SVM account bytes 与 EVM storage 的物理模型。
- 一上来拆多个 git 仓库或 npm 风格 registry。
- 用模板替换仓内 Examples（Examples 仍是 compiler 回归与能力证明）。

## 7. 本 PR 跟踪清单（#11 · `cursor/productization-split-4d63`）

本产品化切片 **全部在同一 PR / 同一分支完成**，按 P0→P3 顺序推进；每完成一阶段更新本表勾选与任务卡状态。

### 已落地（文档骨架）

- [x] 权威方案本文
- [x] 任务卡 [prod-001](tasks/prod-001.md) … [prod-004](tasks/prod-004.md)
- [x] `templates/svm-counter`、`templates/evm-counter` 目标工程骨架（`pf init` 后可 `lake build`）
- [x] `docs/INDEX.md` / `docs/plan/README.md` 入口链接

### 待做 · P0（prod-001）— SDK 导入表面

- [x] README / 快速开始：合约示例改为 `ProofForge.Svm.Sdk` / `Evm.Sdk`（+ Attr）
- [x] 扩展 `scripts/check_ownership.py`（或并列脚本）
  - [x] Examples **新增**文件禁止 `import ProofForge` 伞模块（存量白名单，只减不增）
  - [x] `ProofForge/{Svm,Evm}/Sdk/**` 禁止 import 同 target `Emit` / `Assemble` / `Registry`
- [x] CI 接入守卫；故意违规用例证明会红
- [ ] （可选）存量 Examples 分批从伞 import 迁到 SDK import，不阻塞 P0 合入门

### 待做 · P1（prod-002）— Lake 包拆分 + CLI 去硬编码

- [x] `lakefile.lean` 增加 `ProofForgeSvmSdk` / `ProofForgeEvmSdk` / compiler lib `ProofForge`（+ `ProofForgeCore`）
- [x] 伞模块 `ProofForge.lean` 降级为 compiler workspace 便利聚合；用户模板禁止引用
- [x] CI：断言 `import ProofForge.Svm.Sdk` / `Evm.Sdk` 传递闭包不含 Emit（`scripts/check_sdk_import_closure.py`）
- [x] CLI：去掉写死的 `Examples.<Name>`；支持 `--module` 与工程根 `pf.toml`
- [x] 仓内回归仍可用 Registry + `Examples.*`（compiler 夹具，不是产品 API）
- [x] 全量 SVM/EVM/XRPL/NEAR 回归绿且 Registry digest 不变（本地：70 `.so` / 44 `.bin` / 23 + 38 `.wasm`，各 target `check_artifact_manifest` ok；**CI run [`33531419129`](https://github.com/DaviRain-Su/ProofForge/actions/runs/33531419129) Lean/SVM/EVM/NEAR 全绿 @ `c6a96454`**）
  - 另已验证：`Examples.Counter` digest 钉；`pf init`→`lake build`→`pf build` 出 `.so`/`.bin`
  - `lean_lib Examples` 使用 `globs := #[.one, .submodules]`，保证 Registry 中未写入 `Examples.lean` 伞的模块（如 `NearQueue`/`NearIterable`/`NearPromise*`/`NearMigration`）也会被 `lake build Examples` 产出 olean

### 待做 · P2（prod-003）— `pf init` + 可构建模板

- [x] CLI 子命令：`pf init <name> --target svm|evm`
- [x] 以 `templates/svm-counter`、`templates/evm-counter` 为源生成工程
- [x] 生成物：`lakefile.lean`、`lean-toolchain`、`pf.toml`、最小合约、`README.md`
- [x] 模板 path-`require` monorepo；合约只 import 对应 `*Sdk`（git tag 钉死见 P3）
- [x] 验收：`pf init` → `lake build` 绿；`lake exe pf -- build` 产出 `.so`/`.bin`（本机已装 `sbpf`/`solc` 钉）
- [x] 验收：绝对路径临时目录 `pf init /tmp/…`（require 指向本 checkout）→ `lake build` → assemble `.so`
- [ ] （后续）near / xrpl 模板等 WASM SDK facade 稳定后再加

### 待做 · P3（prod-004）— Release 打包

- [x] GitHub Release workflow：`pf` 二进制（linux/mac）+ checksums + changelog（`.github/workflows/release.yml`）
- [x] 同 tag `vX.Y.Z` 供 Lake `require … @ "vX.Y.Z"`（Release notes 说明）
- [x] `pf --version` 打印 CLI / Lean / sbpf / solc / wat2wasm 等 pin
- [x] Release notes 附 fail-closed capability 摘要（`docs/plan/release-capability-summary.md`）
- [x] 验收：干净目录用独立 `pf` 二进制 + `require … from git @ <commit>`（等同 tag 机制）构建模板并产出 `.so`（首次公开 `v*` Release 仍建议人工复核）
- [ ] 首次公开 tag：按 [release-001](tasks/release-001.md) 切 `v0.0.1`（**不要**在未过烟测前 push tag）

### 明确不在本 PR

- 新合约语法 / 新包管理器
- 拆独立 git 仓或 npm 式 registry
- 改链上语义、IR digest、Runtime interpreter（除非 P1 搬家且 byte-identical）
- 用模板替换仓内 Examples
- 统一 SVM / EVM 物理存储模型

## 8. 建议的立即执行顺序

1. 在本 PR 落地 **P0（prod-001）**：推荐 import + CI 守卫。
2. **P1（prod-002）** 拆 Lake lib + CLI 模块发现。
3. **P2（prod-003）** `pf init` 使模板可隔离构建。
4. **P3（prod-004）** tag / 二进制 release。
5. 每阶段推送到本分支并更新本节勾选；全部勾完再转 ready / 合并。

**2026-09-01：** prod-001…004 必做项已勾选；CI [`33531419129`](https://github.com/DaviRain-Su/ProofForge/actions/runs/33531419129) 全 lane 绿（`c6a96454`）。剩余未勾仅为明确 defer（Examples 伞迁移、near/xrpl 模板、首次 tag 人工复核）。
