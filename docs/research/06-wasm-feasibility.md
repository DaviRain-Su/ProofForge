# WASM 作为第三个 target：可行性与路线选择

> Date: 2026-08-29
> Core question: ProofForge 要支持 WASM，应该「直接用 Lean 自身编译器编 wasm」，还是走现有 `Profile → Extract → Core.Ops → target` 管子加第三个 profile？
> Related: [03-feasibility.md](03-feasibility.md) · [04-evm-feasibility.md](04-evm-feasibility.md) · [02-architecture.md](../02-architecture.md) · [modules/README.md](../modules/README.md)

---

## 一、结论

**链上 wasm artifact 走第三个 profile（Core.Target.Registration + 新建 `Wasm/*`）。
「用 Lean 自家编译器产 wasm」只用于工具侧（浏览器 playground / 解释器 wasm 化），明确不做链上 artifact。**

先校准一个事实前提：「Lean 4 自身已支持 WASM target」**不成立**。Lean 4 的编译器后端是
**C**：`lake build` 产出 `.c`，由 `leanc` 调 clang 编成原生代码。所谓「Lean 跑在 wasm 上」
（live.lean-lang.org / lean4web）是官方用 **Emscripten 把 Lean 工具链本身**（含其 C 产物
与完整 runtime）编到 wasm。因此「直接用 Lean 编译器做 wasm」的真实含义是：

```
普通 Lean def → 生成的 C → emcc/wasi-sdk → wasm32
                          （整个 Lean runtime：GC、模块初始化、boxed 对象、闭包一起链入）
```

两条路线判定：

| 说法 | 判定 | 根因 |
|---|---|---|
| 「Lean 编译器内置 wasm backend」 | **不成立** | 后端是 C；wasm 是 Emscripten 在 C 之上给的 |
| Lean 生成的 C 能编成可运行 wasm | **可行** | lean4web / live editor 即此路线；带完整 runtime |
| 该路线可产出链上 artifact | **不可行** | 体积 MB 级、TCB 巨大、gas/确定性/宿主 ABI 全缺（见 §四） |
| 该路线用于工具侧（playground / 测试） | **可行且推荐** | 编 `Core.Eval` 解释器到 wasm，浏览器跑合约 smoke；零新后端代码 |
| `Core.Ops → wasm` 做第三个 profile | **可行** | Core 的 checked U64 / 分支 / loop 与 wasm i64 指令几乎 1:1，比 sBPF / Yul 都近 |
| 同一份合约双 target（svm + wasm） | **v0 只对无链特化叶子可行** | 与 EVM 切片同一约束：`clockSlot` / `signerKey0` / `systemTransfer` 是 SVM 叶子 |
| 定理蕴含已部署 wasm | **不可行** | 与 Solana / EVM 相同：定理钉用户 `def`；runtime 绿是工程门 |

---

## 二、两条路线各自是什么

### 路线 A：Lean 原生编译（`def → C → emcc`）

拿到的东西只有一个，但是很大：**摆脱 profile 子集检查**，任意 Lean 代码都能编。
代价是「欠缺的别的能力」，而且每一项都不是编译器能替你解决的：

| 缺口 | 问题 | 说明 |
|---|---|---|
| 入口 ABI | 宿主要调合约导出函数 | Lean 函数的 C ABI 涉及 boxed 对象 / closure / thunk；需自定 `ByteArray → ByteArray` 式入口（`@[export]`），手动 marshal 账户 / wire bytes 进 linear memory |
| 确定性 / 宿主接口 | 链上禁止 wall clock、随机、不受控 IO | 要么 Profile 再禁一遍（子集检查回来了），要么做成 host import —— 而 host import 就是 SVM `Syscall op` / EVM opcode 的对应物，且每个链不一样 |
| Gas / 有界执行 | wasm 本身没有 metering | 需编译后 wasm-instrument 加 fuel，或宿主侧断点计数；Lean runtime 的 GC 分配也进 gas 账 |
| 体积 | 带 Lean runtime + 依赖模块 | 用了 Mathlib 就把 Mathlib 的 C 链进去；MB 级起步，多数链 code size 上限直接死 |
| 模块初始化 | 每个依赖模块的 `initialize_*` 要按序跑 | wasm 启动时做一次可行，但属于额外合同 |
| 证明对应关系 | **最关键** | 见 §四.5 |

### 路线 B：WASM 作为第三个 profile

现有架构就是为此设计的。`Core.Target.Registration`（`ProofForge/Core/Target.lean`）把
target 差异收敛为「val/op ext 投影 + 验证合同 + CFG 方言」两个回调，SVM / EVM 已各注册
一份（`Svm/IR.lean` `extractRegistration`、`Evm/IR.lean` `extractRegistration`）。加 wasm
不动通用链：

```diagram
Core.Ops（target-neutral：checked U64 算术、ite、for、storeField、okState / error）
        │
        ▼  新增 Wasm.Registration（val/op ext 投影）
Wasm.IR
        ├── Core 标量运算 → wasm i64 指令（几乎 1:1）
        ├── Syscall → host import：pf.env_call / pf.storage_read / pf.storage_write / pf.hash
        └── 状态几何 → 复用 Svm.AccountStorage 的 region/field 模型
            （wasm linear memory 与 Solana 账户 bytes 同构，复用率最高的一块）
        ▼
WAT → wat2wasm（子进程，locked）→ wasm-opt -Os
```

从 Core IR 的视角，wasm **不比 SVM/EVM 更底层、更难做，反而更近**：
`checkedAddU64` 直映 `i64.add` + trap 检查，`ite` 直映 `if`，`forAccum` 直映
`loop`。「不像 SVM/EVM 那样转成底层 code」的直觉，在 Core.Ops 这一层看，
工作量是同构的，甚至发射器更薄。

真正的工作量和 SVM/EVM 一样落在**宿主合同**上：目标链是 CosmWasm？Arbitrum Stylus？
ink? 各自的 host ABI、存储模型、gas 规则不同。对应到本仓：
`Wasm.EntryAdapter` 承担与 `Svm.EntryAdapter` / `Evm.Sdk` 同构的角色。

---

## 三、同构点（所以第三个 profile 能做）

| 语义 | Core / SVM 现状 | wasm 对应 |
|---|---|---|
| checked U64 四则 | `checkedAddU64` 等 5 op | `i64.add/sub/mul` + overflow trap 或显式 `i64.lt_u` 检查（wasm 定义的 trap 语义与 `.error .overflow` 的「不提交」同构，但为了跨引擎稳定建议显式检查 + host revert） |
| 分支 | `ite` + CFG 方言 | `if` / block；CFG 直映 structured control |
| 有界循环 | `forAccum` / `forBody (n : Nat)` | `loop` + 计数器；n 是编译期已知，gas 天然可预估 |
| 状态 | 账户 bytes region / field | linear memory region：AccountStorage 的 one-based slot、bounded lookup 几何可原样搬 |
| wire decode | `Svm.EntryAdapter` packed wire | host 调用前把 calldata 写进 linear memory，或 import `pf.read_calldata` |
| 错误 | `errorOverflow` / `errorNamed` | export 一个返回 trap 或显式 `(result i32)` status 约定 |
| 锁定工具 | `sbpf 0.2.2` / `solc 0.8.34` 子进程 | `wat2wasm`（wabt，pin 版本）子进程，`wasm-opt`（binaryen）可选 |
| 运行时门 | Mollusk / Anvil / Surfpool | wasmtime（带 fuel）或目标链 devnet |

工具链位置与 EVM 切片完全平行：`Wasm.IR` 对标 `Evm.IR`，`Wasm.Emit` 对标
`Evm.Emit`（Yul），`Wasm.Assemble`（locked wat2wasm 子进程）对标 `Evm.Assemble`
（locked solc 子进程）。

---

## 四、断裂点（为什么不能「直接用 Lean 编译器」当 artifact）

### 1. TCB 爆炸

现在证明 ↔ artifact 之间只隔：小而可审计的 Extract、target-neutral Ops 投影、locked
emitter（sbpf 0.2.2 / solc 0.8.34）。走 Lean 自家编译器后，对应链变成
**Lean 编译器 + Lean runtime + Emscripten + 模块初始化序列**，体积与不可审计性都大
几个数量级。ProofForge 最值钱的东西——kernel-checked 定理与部署代码之间的薄对应——被放弃。

### 2. 体积与链限制

Lean runtime + 依赖模块的 C 全量链入。多数 wasm 链有 code size 上限
（如 CosmWasm、Stylus 都远小于此）。`-Os` + `wasm-opt` 救不了量级差距。

### 3. 确定性剖面回来了

绕开 Profile 子集检查的好处，链上一分钟就收回：链要么拒绝非确定 op
（浮点 NaN payload、wall clock、随机），要么要求它们走 host import ——
后者的形状就是现在的 `Svm.Ops` / `Evm.Ops`。路线 A 在链上等于重做一遍
Profile + Runtime，只是位置从「抽取期」挪到「编译期外部合同」。

### 4. 每条链的 host ABI 仍要逐个做

「一份 wasm 走天下」不存在。CosmWasm（JSON + Region 约定）、Stylus（EVM 兼容 + 
`ArbSys`）、ink!（polkadot-js 约定）各自不同。无论路线 A / B，宿主合同都是自建项。
区别只在：B 的合同钉在 Core.Ops 扩展上（和 SVM/EVM 同构），A 的合同钉在
「Lean 生成 C 的调用约定」上（无先例、无工具支持）。

### 5. 定理与 artifact 的距离

路线 A 下定理仍然只证用户 `def`，但 artifact 是「Lean+clang+emcc 从这个 def 产出的任何
东西」。与 Solana / EVM 切片相同的诚实分层要求：wasm artifact 不因定理而「被证明」；
区别是路线 B 的 lowering 小、locked、可审，声称的工程门（wasmtime fuel / 目标链
devnet）与 `.so` / `.bin` 同构。路线 A 连这个形状都给不出。

---

## 五、推荐切法

### 两条腿

| 腿 | 内容 | 位置 |
|---|---|---|
| 工具腿（先做，便宜） | 把 `Core.Eval`（或薄 harness）编成 wasm，浏览器跑合约 smoke / CFG 可视化。用 Lean→C→emcc，不碰编译链、不碰证明链 | `runtime-tests/` 或独立 `playground/`，产物**永不部署** |
| 链上腿（后做，竖切） | `--target wasm` 第三个 profile | `ProofForge/Wasm/*`，注册进 `Cli.Target` |

### 链上腿 v0 契约（建议钉死）

和 Solana / EVM 切片同构：同一 `Examples.Counter` 四场景。

| Lean | 链上（以通用 wasm 宿主为准，先不绑链） |
|---|---|
| `init` | deploy 期一次性 export `pf_init` |
| `increment` ok | export `pf_invoke`，写 memory region，返回 status 0 |
| `increment` overflow | 显式 checked 检查 → status = error code，memory 回滚由宿主处理（不写） |
| `get` | 只读 export |
| Runtime 叶子 | v0 不认 `clockSlot` / `signerKey0` / `systemTransfer`（抽到即 `unsupported`），与 EVM 切片同规矩 |

宿主 import 最小集（先按通用形状定义，绑链时再扩）：

```wat
(import "pf" "read_calldata" (func $read_calldata (param i32 i32)))
(import "pf" "write_returndata" (func $write_returndata (param i32 i32)))
(import "pf" "revert" (func $revert (param i32)))
(import "pf" "hash" (func $hash (param i32 i32 i32)))  ;; 先 SHA-256，绑链再换
```

gas：v0 用 wasmtime `fuel` 工程门；不做编译期 metering 注入（第二刀再评估
wasm-instrument）。

第一刀**先不选链**，宿主定为「wasmtime + pf import 合同」，工程门是 wasmtime
instantiate + fuel。选链（Stylus / CosmWasm / ink）是第二刀：届时
`Wasm.EntryAdapter` 落具体链 ABI，AccountStorage 几何建议挑 linear memory 语义
最接近 SVM 的链先落（Stylus 最像）。

### 明确不做（会杀死项目）

- 把 Lean 自家编译器（或其 C 产物 + emcc）的输出当链上 artifact
- 改造 `Core.Target` / `Core.Ops` 为「三 target 特判」——只加注册，不动通用链
- 第一刀就绑具体链 ABI、做 metering 注入、做浮点
- 把 SVM / EVM 的 Runtime 叶子映射成 wasm「等价物」（slot ≠ block number 教训同 EVM）
- 声称 wasmtime 绿 = artifact 被证明

### 工作量（量级，不是承诺）

| 切片 | 内容 | 对照本仓 |
|---|---|---|
| W0 | `Wasm.IR` + Registration + digest | `Evm/IR.lean` + `Registry.lean` |
| W1 | Ops → WAT（四场景 Counter 子集） | `Evm.Emit` 里 handler 那截，更薄 |
| W2 | `pf build --target wasm` + locked wat2wasm 子进程 | `Evm.Assemble` + `Cli` |
| W3 | wasmtime fuel 工程门（runtime-tests/wasm） | `runtime-tests/solana` Counter |
| W4 | AccountStorage 几何搬移 + 多字段 | SVM 槽表，只换 region 基址 |

W0–W3 是一条竖切；W4 才证明发射器不是 Counter 模板。

---

## 六、验证记录

| 断言 | 方法 | 结果 |
|---|---|---|
| Lean 4 后端是 C，无内置 wasm backend | Lean 4 工具链事实；`lake build` 产 `.c` | 成立；wasm 构建走 Emscripten（lean4web / live editor 路线） |
| `Core.Target.Registration` 是扩展点，加 target 不动通用链 | 读 `ProofForge/Core/Target.lean` | `Registration` 结构 + `projectVal/projectOps`，SVM / EVM 各注册一份 |
| Core 标量 op 与 wasm i64 几乎 1:1 | 读 `Core/Ops.lean` Val/Op 列表 | `checkedAddU64` 等 5 op、`ite`、`forAccum/forBody`、`storeField`、`okState/errorOverflow` 均有直映 |
| Cli target 枚举目前是 svm/evm | 读 `Cli.lean` `inductive Target` / `parseTarget` | 是；加 wasm 是小改 |
| SVM / EVM 各有 EntryAdapter / Sdk 承担宿主合同 | 读模块树 | `Svm/EntryAdapter.lean`、`Evm/Sdk/` |
| EVM 切片先例：Runtime 叶子不跨 target | 读 `04-evm-feasibility.md` §四.3 | 是；wasm 沿用同一规矩 |

---

## 七、盲区

- 未实测 `Core.Eval`（或任何本仓 Lean 代码）经 emcc 编到浏览器跑通——工具腿路径以
  lean4web 的公开做法为准，本轮不复现
- 未实测 wat2wasm / wasm-opt 版本锁定后的字节码稳定性；v0 必须 pin wabt 版本
- 未评估目标链（Stylus / CosmWasm / ink）的 code size / gas 常数对本仓四场景的实际余量
- 未定 wasm digest 域名（SVM 用 `proof-forge-solana-v1:`）；需在 W0 钉死，
  且与 SVM / EVM digest **故意不同**（宿主 ABI 规范不同）
- checked 算术用 trap 还是显式检查 + status，需在 W0 定；本文倾向显式检查
  （trap 语义跨引擎 / 跨版本稳定性未验证）
- 未调研 zkVM（SP1 / RISC Zero）侧的 wasm/zk 流水线是否可作为另一条第四 target 线

---

## 八、建议的下一步

1. 工具腿先行：把 `Core.Eval` 解释器 + Counter 夹具编成浏览器可跑 wasm，作为
   `runtime-tests/` 的平行工程门；产物永不部署，不进证明链。
2. 链上腿开 W0：`ProofForge/Wasm/IR.lean`（Registration + digest 域名钉死）、
   Cli 加 `--target wasm`、wasmtime fuel 工程门竖切。
3. 选链决策推迟到 W3 之后：先用「wasmtime + pf import」通用宿主把竖切跑通，
   再按 AccountStorage 几何复用率挑第一条真链（倾向 Stylus）。
4. 不开「Core 多 target 特判」重构；不引入 `SemanticProgramV1` 式的中间层；
   不做 Lean C → 链上。