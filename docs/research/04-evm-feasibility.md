# Lean 4 直写 EVM 合约：可行性（对照当前 proofforge）

> Date: 2026-08-22
> Core question: 以当前 proofforge 的普通 Lean 4 表面（`def` / `theorem` / attribute / Profile / Extract / Ops），能否做出 EVM target？ProofForge 已有 Yul lowering，是否该搬？
> Related: [03-feasibility.md](03-feasibility.md) · [gap-vs-proofforge.md](../plan/analysis/gap-vs-proofforge.md) · PF [01-evm.md](file:///Users/davirian/orca/projects/proof_forge/docs/targets/01-evm.md)

---

## 一、结论

**能做，而且应该按当前这条管子做。不能按「把 PF EVM lowering 接进来」做。**

| 说法 | 判定 | 根因 |
|---|---|---|
| 同一套普通 Lean `def` 当源语言 | **可行** | Counter / Pair 已经是参考语义；PF StateCell 只是同一转移函数的 `program … where` 写法 |
| 复用 Profile + Extract + Ops | **有条件可行** | 定宽整数、`ite`、checked 四则、init/mutate/view 与 EVM constructor/entry/view 同构 |
| 复用现在的 `IR.Program` + `Emit.lean` | **不可行** | IR/Emit 钉死 Loader V3、账户字节布局、SHA-256 8 字节 disc、sBPF |
| vendor PF `Targets/Evm/*` | **不可行** | Lower 吃的是 `SemanticProgramV1` + capability，不是本仓 Ops；EmitIRV1 2943 行覆盖 Map/Field/assets，远超当前剖面 |
| 自写薄 Yul 发射器 + locked `solc` 子进程 | **可行** | 与本仓 `Emit` + `sbpf` 子进程同构；PF 已证明这条工程链能跑 Anvil |
| 同一份 Lean 同时编 Solana 和 EVM | **v0 只对无链特化叶子可行** | `clockSlot` / `signerKey0` / `systemTransfer` 是 SVM 叶子，不能假装是 `NUMBER` / `CALLER` / `CALL` |
| 定理蕴含已部署 bytecode | **不可行** | 与 Solana 相同：定理钉用户 `def`；Anvil 绿是工程门 |

正确编译路径（对标本仓已通的 Solana 路径）：

```diagram
普通 Lean def / theorem          ← 整段借 Lean，不新 DSL
        │
        ▼
Profile 子集检查                 ← 复用（几乎不动）
        │
        ▼
Extract → Ops                    ← 复用；EVM 只加少量叶子
        │
        ▼
Evm.IR（storage / selector）     ← 自建，薄，对标 IR.lean
        │
        ▼
EmitYul → .yul + .abi.json       ← 自建；只覆盖当前 Ops
        │
        ▼
locked solc --strict-assembly    ← 子进程，不是 FFI
        │
        ▼
.bin → Anvil                     ← 对标 Mollusk
```

---

## 二、两边现在到底有什么

### 本仓（路径 B，已通）

用户写的是普通 Lean，不是 DSL：

```lean
@[pf_entry]
def increment (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  if s.value ≤ u64Max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow
```

管子：`Profile → Extract → Ops → IR.Program → emitCounterAsm → sbpf → .so → Mollusk`。

Ops 一共这些：

| 类 | 成员 |
|---|---|
| `Val` | `arg` / `field` / `lit` / `clockSlot` / `signerKey0` |
| `Op` | checked `+ - * / %`、`ite`、`systemTransfer`、`okState`、`errorOverflow`、`returnU64`、`returnState` |

IR 是 **SVM 形状**：单账户、header 后顺序槽、`sha256("proof-forge-solana-v1:…")` 前 8 字节 LE 当 disc、layout marker 写进账户数据。

### PF EVM（路径 A，DSL + 厚 lowering）

用户写的是：

```lean
program StateCell where
  state count : UInt64
  init(initial : UInt64) do count := initial
  entry increment(delta : UInt64) : UInt64 do
    count := count + delta
    return count
  view get() : UInt64 do return count
```

管子：`program where → SemanticProgramV1 → EvmPlan → Yul → solc 0.8.34 → .bin → Anvil`。

体量（只算 `Targets/Evm`，不含 Semantic/Compiler 闭包）：

| 文件 | 行 | 吃什么 |
|---|---:|---|
| `LowerSemanticV1.lean` | 5665 | `SemanticProgramV1` + capability |
| `EmitIRV1.lean` | 2943 | 完整 `EvmPlan`（Map / Field / Principal / token / merkle） |
| `ValidatePlanV1.lean` | 1035 | Plan 不变量 |
| `PlanSchemaV1.lean` | 572 | engineering digest |
| `Keccak.lean` | 135 | **只 import Std**，可搬 |
| 其余 | ~500 | Finalize / ValidateIR / catalog |

工程上已通：Yul object + constructor + `switch shr(224, calldataload(0))` + checked add `if gt(lhs, sub(0xffffffffffffffff, rhs)) { revert(0,0) }` + `sstore`/`sload` + locked solc。

形式化上未通：bytecode / Anvil refinement 不是产品声明。和本仓对 `.so` 的诚实分层一样。

---

## 三、同构点（所以能做）

同一份 Counter 转移函数，两边只是 ABI 不同。

| 语义 | 本仓 Lean | PF Solana | PF EVM |
|---|---|---|---|
| 状态 | `structure State (value : UInt64)` | 账户 data：marker + count | storage slot 0 |
| init | `def init (initial) : State` | instruction `initialize` | constructor |
| increment ok | 写回 `value+delta`，返回新值 | 写账户，return | `sstore` + `return` |
| increment overflow | `.error .overflow`，概念上不写 | `Custom(0x1001)`，账户不变 | `revert(0,0)`，storage 回滚 |
| get | 只读投影 | view instruction | `view` / `eth_call` |
| 证明主语 | 用户 `def` | `SemanticProgramV1` | 同左（本仓保持钉 `def`） |

checked 算术几乎逐字对应：

- 本仓 Extract：`if s.value ≤ u64Max - delta then … else overflow`
- PF Yul：`if gt(lhs, sub(0xffffffffffffffff, rhs)) { revert(0, 0) }` / `let x := add(lhs, rhs)`

`ite`、字面量、字段投影、init 多参数、view 返回 UInt64，Extract 已经会。EVM 发射器只是换汇编码。

Selector 也不神秘：PF `Keccak.selector "increment" #["uint64"]` = `keccak256("increment(uint64)")` 前 4 字节。本仓已有纯 Lean SHA-256；keccak 135 行可单独拷，不拖 PF。

工具链同构：

| | Solana（已做） | EVM（要做） |
|---|---|---|
| 文本 | `.s` | `.yul` + `.abi.json` |
| 锁定工具 | `sbpf 0.2.2` 子进程 | `solc 0.8.34 --strict-assembly --optimize` 子进程 |
| 运行时门 | Mollusk | Anvil |
| 禁止 | Lean FFI、Lean C → 链上 | 同样禁止 |

---

## 四、断裂点（所以不能「接上 PF」或「改两行 Emit」）

### 1. 状态模型不同，不是偏移不同

- SVM：状态在**调用者传入的账户**里；程序是无状态 ELF。
- EVM：状态在**合约自己的 storage**；部署一次，之后按 address 找。

因此：

- `IR.Slot` 的「header 后累加字节 + layout marker」不能当 EVM slot。
- EVM 不需要 Loader V3 input walk，也不需要 `ACC0_DATA`。
- `init` 在 EVM 是 constructor（部署时跑一次），不是之后还能调的 instruction。本仓把 `init` 当第三条可重复入口，语义要对齐成「只在 deploy」。

### 2. 当前 IR 钉死了 SVM 身份

`IR.discPreimage` = `proof-forge-solana-v1:name(u64,…)`。EVM 必须是 Solidity ABI selector。混用会让「同一 digest」变成谎言。

`IR.inputLayout` / `usesSystemTransfer` / 三账户 span 全部无 EVM 对应物。

### 3. 链特化叶子不能共用

| 本仓 Runtime | SVM 含义 | 若强行当 EVM |
|---|---|---|
| `clockSlot` | `sol_get_clock_sysvar` → `Clock.slot` | 不是 `number()`（slot ≠ block number） |
| `signerKey0` | 账户 0 公钥首 u64 | 不是 `caller()`（20 字节 address） |
| `systemTransfer` | 三账户 `invoke` System Program | 不是 `CALL` + value（重入模型也不同） |

v0 EVM **不要**抽这些叶子。`Examples/Transfer.lean` / `Clock.lean` 不是双 target 夹具。

### 4. PF EVM 发射器吃错 IR

`planFromCapability` → `materializePlanFromCapabilityV1` → 读 `CompiledSemanticV1`。本仓没有、也不该引入 `SemanticProgramV1`。S3 已经拒绝 import PF（`IR.mk` 私有会拖整仓）。EVM 这边更重：Lower 5665 行 + Semantic 闭包。

可搬的只有：

- `Keccak.lean`（Std-only）
- Counter 级 Yul 形状（object / constructor / switch selector / checked arith / sstore）
- Finalize 的 solc argv 约定（`--strict-assembly --optimize --bin`）

不可搬：LowerSemantic、ValidatePlan、PfAssets、capability、program DSL。

### 5. 失败码与 ABI 不同，但「不提交」同构

Solana overflow = 自定义错误码 `0x1001` + 账户字节保持。EVM overflow = 整笔 revert。对用户 `def` 来说都是「不是 `.ok`，状态不变」。定理继续钉 `increment`，不要钉错误码数字。

---

## 五、推荐切法

### 共享 / 分叉

| 层 | 动作 |
|---|---|
| 用户表面 | 共享。同一 `Examples.Counter` 可当双 target 源 |
| `@[pf_entry]` | 先加 `@[evm_entry]`，或抽成中性 `@[onchain_entry]`。种类仍由返回类型推断 |
| Profile | 共享 |
| Extract / Ops | 共享。EVM v0 不认 `clockSlot` / `signerKey0` / `systemTransfer`（抽到就 `extract/unsupported`） |
| IR | **不要**扩现在的 `IR.Program`。新建 `Evm.IR`：storage slot、constructor、entry selector、view |
| Emit | 新建 `Evm.Emit`：只覆盖当前 Ops 的 Yul 子集 |
| Assemble | 新建：写 `.yul`，子进程 locked solc，检查 hex bytecode 非空 |
| 运行时门 | Anvil：constructor / increment / get / overflow 四条，对标 Mollusk Counter |

### EVM v0 契约（建议钉死）

和 Solana Counter 同一用户函数：

| Lean | 链上 |
|---|---|
| `init initial` | constructor(`uint64`)，`sstore(0, initial)` |
| `increment` ok | selector `increment(uint64)`，写 slot 0，ABI 返回新值 |
| `increment` overflow | `revert(0,0)`，slot 0 不变 |
| `get` | `view get()`，`sload(0)` |
| 其它入口 | 先不做（decrement/scale 第二刀，和 L1 已通的 Extract 对齐） |

storage：一个 UInt64 占 slot 0。**不要**写 Solana layout marker。EVM 账户 storage 初始为 0，constructor 写 0 可以省略（PF 已这样做）。

calldata：精确 4 + 32×N 字节，否则 revert。`uint64` 高 192 位必须为 0，否则 revert。与 PF 工程门一致。

### 明确不做（会杀死项目）

- 搬 `program … where` / SemanticProgram / capability
- 把 `Emit.lean` 改成「if solana / if evm」
- Lean FFI 或 Lean C → solc
- 第一刀就做 Map / Principal / ERC-20 / `msg.value` / 重入
- 把 `systemTransfer` 翻译成 ETH transfer
- 声称 Anvil 绿 = bytecode 被证明
- 公网部署
- 活跟踪 PF `Targets/Evm` 1 万行

### 工作量（量级，不是承诺）

| 切片 | 内容 | 对照本仓 |
|---|---|---|
| E0 | `Evm.IR` + keccak selector + digest | `IR.lean` + `Sha256.lean` |
| E1 | Ops → Yul（constructor / increment / get / overflow） | `Emit.lean` 里 handler 那截 |
| E2 | `#pf_evm_build` + locked solc | `#pf_build` + `Assemble.lean` |
| E3 | Anvil 四场景 | `runtime-tests/solana` Counter |
| E4 | Pair / Flag / 多字段连续 slot | 已有 L2 槽表，只换 slot 编号 |

E0–E3 是一条竖切。E4 才证明发射器不是 Counter 模板。Map / caller / value 不在这条竖切里。

---

## 六、验证记录

| 断言 | 方法 | 结果 |
|---|---|---|
| 本仓表面是普通 Lean `def` | 读 `Examples/Counter.lean` | `@[pf_entry]` + 普通函数 + 宿主定理 |
| 本仓 Ops 很小 | 读 `ProofForge/Ops.lean` | 5 Val + 11 Op |
| 本仓 Emit 是 SVM | 读 `Emit.lean` entrypoint / ACC0_* | Loader V3，不是 Yul |
| PF 用户表面是 DSL | 读 `Examples/StateCell.lean` | `program … where` |
| PF EVM 已有 Yul+solc | 读 `EmitIRV1.renderYul`、`FinalizeV1` | object/constructor/switch；solc 0.8.34 |
| PF Lower 不能直接吃本仓 IR | 读 `Evm.lean` `planFromCapability` | 入口是 `ResolvedEngineeringBuildV1` |
| Keccak 可独立搬 | 读 `Keccak.lean` import | 仅 `Std` |
| checked add Yul 形状 | 读 `EmitIRV1` `.checkedAdd` | `gt` + `sub(0xfff…)` + `revert(0,0)` + `add` |
| 本仓调研曾排除 EVM | `03-feasibility.md` Scope Out | 当时只评 Solana 剥离；本次补评 |

---

## 七、建议的下一步

1. 产品句先定：独立（或本仓并列）`evm-lean` v0 =「同一普通 Lean Counter → Yul → locked solc → Anvil」。不包含 PF 表面，不包含 `.bin` refinement。
2. 不要开「把 IR.Program 参数化成多 target」的大重构。先平行做 `Evm/*`，Ops 共用。
3. 竖切夹具就是现在的 `Examples.Counter`。digest 与 Solana digest **故意不同**（selector/storage 规范不同）；相同的是用户 `def` 和宿主定理。
4. 第二刀再谈双 target 同一模块：只有没有 Runtime 叶子的程序能共享；有叶子的必须分模块或分属性。

---

## 八、盲区

- 未在本机跑 PF `pf test -t evm` / Anvil（工程路径以 PF 文档与源码为准，本轮不复现）
- 未实测把本仓抽出的 Counter Ops 手写进最小 Yul 再过 solc（架构可行，不是工期保证）
- 未评估本仓改名/拆包（`ProofForge` → 中性包名）的许可证与仓策略
- 未比较 Foundry / solc 不同 minor 的 bytecode 稳定性；v0 必须 pin 0.8.34
- 未处理 EVM 重入：v0 无外部 CALL，问题不出现
