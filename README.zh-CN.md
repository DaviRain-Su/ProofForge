# ProofForge

[English](README.md) · [简体中文](README.zh-CN.md)

[![Lean 4](https://img.shields.io/badge/Lean-4.31.0-blueviolet)](https://lean-lang.org)
[![Solana](https://img.shields.io/badge/target-Solana%20sBPF-14F195)](https://solana.com)
[![EVM](https://img.shields.io/badge/target-EVM%20Yul-627EEA)](https://ethereum.org)
[![CI](https://github.com/DaviRain-Su/ProofForge/actions/workflows/ci.yml/badge.svg)](https://github.com/DaviRain-Su/ProofForge/actions/workflows/ci.yml)
[![Website](https://img.shields.io/badge/website-GitHub%20Pages-0A0A0A)](https://davirain-su.github.io/ProofForge/)

**ProofForge** 是面向 **Solana** 与 **EVM** 智能合约的 [Lean 4](https://lean-lang.org) 编译剖面。普通 `def` 写合约，普通 `theorem` 证合约，同一主语抽出到链上字节。

它**不是**一门新合约语言。没有 `program … where`。用 `@[pf_entry]` 标记可调用入口。CLI 是 `pf`。

当前目标：**Solana sBPF**（`.so` / IDL）和 **EVM Yul**（`.bin` / ABI）。

- 网站：[https://davirain-su.github.io/ProofForge/](https://davirain-su.github.io/ProofForge/)
- 文档索引：[docs/INDEX.md](docs/INDEX.md)

## 为什么做

Lean 4 本身就是可执行语言 + 证明器。ProofForge 只补链上缺的那一层剖面：

| 原则 | 含义 |
| --- | --- |
| **同一主语** | 定理钉在用户 `def` 上，编译走同一抽出 IR。禁止「证的是 A，编的是 B」。 |
| **Fail-closed 子集** | Profile 只放行能降到链上的东西。`IO`、`partial`、`sorry`、`@[extern]`、`@[implemented_by]`、无界递归是拒绝，不是警告。 |
| **两个剖面，一条 Core** | SVM 与 EVM 共享 Lean / Profile / Extract / CFG，**不**共享物理存储模型。 |
| **诚实的信任边界** | Kernel 接受的是关于 `def` / IR 的定理。这不声称 loader 或公网部署正确。 |

## 编译链

```
普通 Lean def / theorem     ← 整段借 Lean
        │
        ▼
Profile（fail-closed 子集）
        │
        ▼
Extract Expr → typed Core + target-neutral Ops
        │
   ┌───┴───┐
   ▼         ▼
SVM IR     EVM IR
+ IDL      + ABI
   │         │
   ▼         ▼
sBPF / .so   Yul / .bin
```

`#pf_build Examples.Counter` 在 Lean 里抽出；`pf build --target svm` 走同一条 IR。

## 快速开始

### 1. 钉死工具链

不要用 `PATH` 里随便一个汇编器顶替锁版本。用下面这条装齐：

```bash
./.agents/setup
```

| 工具 | 版本 | 用途 |
| --- | --- | --- |
| Lean 4 | `v4.31.0` | 源语言与 kernel |
| sbpf | `0.2.2` | `.s` 汇编成 Solana `.so` |
| solc | `0.8.34` | Yul 汇编成 EVM `.bin` |
| Surfpool | `1.5.0` | Loader-v3 本地部署（不用 `solana-test-validator`） |
| Foundry / Anvil | `1.7.1` | EVM 工程门 |
| Rust | `1.90.0` | Mollusk 运行时测试 |

### 2. 构建编译器

```bash
lake build
```

这一步类型检查 ProofForge 与示例，并产出 `pf` 可执行文件。它**不会**写出链上制品。

### 3. 编译合约

`pf` 必须重新从用户模块抽 IR，不能组装 legacy Golden fixture。

```bash
# Solana：Counter.so / Counter.s / Counter.idl.json
lake exe pf -- build --target svm --out build/sbpf Counter

# EVM：Counter.bin / Counter.yul / Counter.abi.json
lake exe pf -- build --target evm --out build/evm Counter
```

`--target svm` 也可写成 `solana` 或 `sbpf`。不写程序名则构建该目标下全部已登记模块。详见 `lake exe pf -- --help`。

| 目标 | 制品 | 布局 |
| --- | --- | --- |
| SVM | `.so` / `.s` / `.idl.json` | Solana IDL spec 0.1.0，Loader V3 |
| EVM | `.bin` / `.yul` / `.abi.json` | selector / storage slot / ABI |

## 写合约

合约应 import **对应 target 的 SDK**，不要用 `ProofForge` 伞模块（会拖进 Emit / Assemble / Registry）。

| Target | Import |
| --- | --- |
| Solana / sBPF | `ProofForge.Attr` + `ProofForge.Svm.Sdk` |
| EVM | `ProofForge.Attr` + `ProofForge.Evm.Sdk` |

仓内好例子：[`Examples/Svm/VersionedLedger.lean`](Examples/Svm/VersionedLedger.lean)（SVM）、[`Examples/Evm/TipJar.lean`](Examples/Evm/TipJar.lean)（EVM）。最小形状：

```lean
import ProofForge.Attr
import ProofForge.Svm.Sdk

namespace MyProgram.Counter

structure State where
  value : UInt64

inductive Error where
  | overflow

@[pf_entry]
def init (initial : UInt64) : State :=
  { value := initial }

@[pf_entry]
def increment (s : State) (delta : UInt64) :
    Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow
```

内联用 `@[pf_inline]`。业务类型检查仍由 Lean 完成。抽出权威是 elaborated `Expr` 闭包，不是 `Lean.Compiler.IR`。

## 证合约

定理写在同一文件的 `Proofs` 节，是对 `@[pf_entry]` 函数的普通 kernel-checked 性质。

第一批（Counter、Capped、Token）：

- 成功路径后置条件
- 单调性
- Token supply 效应
- Capped cap 不变量

只依赖标准公理 `propext` / `Quot.sound`。CI（`scripts/check_no_sorry.py`）保证证明批次不含占位符。证明主语和编译主语必须共享同一个 IR digest。

## 运行时测试

这些**不是** `lake build` 的一部分。先用 `pf` 写出制品再跑。

### Mollusk（Solana 单测）

环境变量前缀已改为 `PF_*_SO`：

```bash
(cd runtime-tests/solana && \
  PF_COUNTER_SO=../../build/sbpf/Counter.so \
  cargo test --locked --test counter)
```

### Surfpool（Loader-v3 部署）

Phoenix 与 Phoenix-v1 profile verifier 走 Surfpool 部署，不用 `solana-test-validator`：

```bash
runtime-tests/surfpool/smoke.sh
runtime-tests/surfpool/smoke.sh PhoenixV1Profile
```

EVM 工程门是钉死的 Anvil。v0 拒绝公网 broadcast。

## 目标剖面

### Solana（sBPF / Loader V3）

SVM 拥有账户几何、CPI 和 IDL。持久 Map / Queue 是账户 bytes 上的固定容量 POD 视图。Heap 是 invocation-local 向下 bump（32 KiB，可到 256 KiB）：dealloc 不回收，指针不进账户。

编译器边界：

- `Svm.EntryAdapter` 拥有 packed wire decode、raw/generated dispatch、账户前缀。
- `Svm.AccountStorage` 拥有账户内 Region/Field 与有界 `Query` / `Call`（map、queue、allocator、tree）。
- 通用 Ops / IR / CFG / 主 Emit 只 dispatch 一次 `component`。新容器扩 component-owned 模块，不横向改 Extract 或主发射器。

### Phoenix-v1（当前最大的 SVM 切片）

[`Examples/Svm/PhoenixV1Profile.lean`](Examples/Svm/PhoenixV1Profile.lean) 是这条边界的压力测试，不是编译器特判。

| 区域 | 仓库里有什么 |
| --- | --- |
| 存储 | 128-seat trader tree 与双 512-node order book 直接驻留账户 bytes。槽位 one-based（`0` 为哨兵）。不用 heap `Map`、detached node、copied tree 或账户外 pointer。 |
| 撮合 | 固定容量 Sokoban 插入/删除、trader get-or-register deposit、bid/ask `ReduceOrderWithFreeFunds`（partial / full）、collateral unlock、checked preflight。 |
| 官方 tag 3–14 | Tag 3 `PlaceLimit` 严格子集（PostOnly、无 TIF、只用已存入资金）。Tag 4/5 `ReduceOrder(WithFreeFunds)` partial/full。Tag 6/7 `FifoCancel` 按 bids→asks 与各侧 FIFO 原位取消，带 owner 过滤、unlock、event index、released-lot 累加器；tag 6 再按 quote→base claim/withdraw，tag 7 完全不进 Token CPI。Tag 8/9 `CancelUpTo` 增加 side 与可选 tick/search/cancel 上限的有界 FIFO 过滤。Tag 10/11 `CancelMultipleOrdersById`（有界 id 向量）。Tag 12 `WithdrawFunds`、tag 13 `DepositFunds`（`Option<u64>` 全量变体）、tag 14 `RequestSeat`（System CPI seat PDA + trader 注册）。 |
| 审计 | `BatchRecorder.begin/append/finish` 用官方 SDK `0x300000000` / 32 KiB 向下 bump。32 条 35-byte Reduce record，第 33 条前自动 flush。empty finish 仍发 93-byte header-only batch。heap 地址不进 source 或账户。 |
| 游标 | PDA mint seed 读经过认证的 `MarketHeader` 固定 byte slice。FIFO cursor 只保留 `(price, sequence)` scalar key，从账户 root 做有界 strict upper-bound。删除后不保存 node address，也不收集 heap `Vec`。 |

官方指令面目前在同一 component 边界上覆盖 tag 3–14。细节见 [docs/modules/phoenix.md](docs/modules/phoenix.md)。

### EVM（Yul / ABI）

EVM 与 SVM 共享普通 Lean、Profile、Extract 和 Core CFG，**不**复制 SVM 账户几何。

合同源打开 `ProofForge.Evm.Sdk`：

- `Storage.Layout`：编译期 cursor，声明 typed hashed maps
- `Address`、`UInt256`、`Context`、`Immutable`、`Event`、`Revert`
- 封闭 call facade，不隐藏 `.ok` / `.error`

descriptor 在抽取期消去，不进入 storage。`Examples.Evm.Token` / `Examples.Evm.Capped` 已迁到该表面，target IR digest 不变。

## 信任边界

| 声明 | 含义 |
| --- | --- |
| **弱声明（对外 v0）** | Kernel 接受了关于用户 `def` / 抽出 IR 的定理。TCB = Lean kernel + 主语绑定。 |
| **工程声明** | 同一 IR 经发射器 + 钉死的 `sbpf` / `solc`，在 Mollusk 或 Anvil 上与夹具一致。 |
| **不做的声明** | `.so` / loader / 全 SVM refinement / 定理 ⇒ 已部署程序。定理不蕴含公网部署正确。 |

链上 discriminator 与 layout 域名仍是 `proof-forge-solana-v1:`。仓库改名不改变链上字节。

## 网站

产品站源码在 [`website/`](website/)，不另开仓库。GitHub Pages：[https://davirain-su.github.io/ProofForge/](https://davirain-su.github.io/ProofForge/)。

```bash
cd website && npm install && npm run dev
```

首次合并后在 **Settings → Pages → Source** 选 GitHub Actions。

远程 MCP 只提供文档与脚手架指导，不 spawn Lean，不持有密钥，不广播：

```text
https://proof-forge-mcp.davirain-yin.workers.dev/mcp
```

## 相关项目

[proof_forge](https://github.com/DaviRain-Su/proof_forge) 是早期的 `program … where` DSL。本仓复用 Lean 语法本身，抽出能 fail-closed 降到链上的子集。

## 证明

第一批 kernel-checked 合约性质已落在合约文件内的 `Proofs` 节
（`Examples/Counter.lean`、`Examples/Capped.lean`、`Examples/Token.lean`）：
成功路径精确后置条件、单调性、Token supply 效应与 Capped cap 不变量，
全部只依赖标准公理 `propext` / `Quot.sound`。

### 本地形式化门（`svm-eng-001`）

在开 PR 或合并前，本地可复现 Lean / SVM lane 的门禁：

```bash
python3 scripts/check_ownership.py
python3 scripts/check_no_sorry.py
lake build
lake build Tests.ProofSpec Tests.SolanalibSpec Tests.SemanticsSpec
lake build Tests
```

- `check_ownership.py`：拦截 `Examples`→`Emit` 越界 import 与 Runtime/SDK 协议词泄漏；失败打印 `path:line: …`。
- `check_no_sorry.py`：扫描 `ProofForge/`、`Examples/`、`Tests/` 中的 `sorry` / `sorryAx`；白名单仅负向夹具（见脚本头注释）；失败打印 `rel:line: message`。
- `Tests.ProofSpec` / `SolanalibSpec` / `SemanticsSpec`：Track A 与 L3 桥的具名形式化目标；CI 的 Lean lane 会先钉这三项，再跑全量 `lake build Tests`。SVM lane 同样跑 ownership + no-sorry，再构建/跑 Mollusk。

## 文档

从 [docs/INDEX.md](docs/INDEX.md) 进。

| 文档 | 作用 |
| --- | --- |
| [01-prd.md](docs/01-prd.md) | 做 / 不做 |
| [02-architecture.md](docs/02-architecture.md) | 模块边界与信任边界 |
| [modules/README.md](docs/modules/README.md) | 各模块合同 |
| [plan/svm-work-plan.md](docs/plan/svm-work-plan.md) | 当前 SVM 主线 |
