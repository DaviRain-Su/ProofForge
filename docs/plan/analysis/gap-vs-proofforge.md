# 分析：相对 ProofForge Solana 的缺口

补全依据：[authority.md](authority.md)（官方运行时 + syscall，不是 PF 清单，也不是 `solana-program` crate）。
权威调研：[research/03-feasibility.md](../../research/03-feasibility.md)。
PF 工程面只作 ABI 对照：[proof_forge/docs/targets/02-solana.md](file:///Users/davirian/orca/projects/proof_forge/docs/targets/02-solana.md)。

本仓走的是调研路径 B：普通 Lean `def` / `theorem`，自建 Profile + Extract + 薄发射器。
**不**搬 PF 的 `program … where`、Normalize、167k 行闭包。
**不**声称追上 PF 全部工程面，也不声称实现官方 Rust SDK。天花板是 SVM syscall 表；产品面是能 fail-closed 抽出的 Lean 子集。PF 自己也没闭合 formal D1–D4、ELF/SVM refinement、公网部署。

## 本仓现在有

```
Examples/*.lean def/theorem
  → Profile（传递闭包门）
  → Extract（elaborated Expr → Ops）
  → IR.Program {fields, methods}
  → Emit（Loader V3 单账户 .s）
  → sbpf 0.2.2 子进程
  → Mollusk
```

| 层 | 已交付 |
|---|---|
| 表面 | 普通 Lean。Counter / Pair。无新 DSL |
| Profile | 拒 IO / partial / sorry / extern / implemented_by / 入口 Nat |
| Extract | `ite` + checked add/sub；从 `init` 返回 structure 收 UInt64 字段 |
| IR | 三方法形；字段偏移；登记过的 layout marker；按 `dataLen` 算 INSTRUCTION_DATA |
| Emit | 单账户 Loader V3；init / checked arith / get |
| Assemble | Counter.so + Pair.so |
| 证明 | 宿主 `theorem` 钉在用户 `def` 上，不钉 Ops |
| Mollusk | Counter 4/4；Pair 4/4（right 保持） |

## PF Solana 工程面（对照，不是抄作业清单）

PF 产品轨是 `solana-sbpf-cpi-elf-v1`。Mollusk 量级约 24 个 integration binary / 400+ 测。那是多年 recipe 堆出来的，不是本仓下一季度目标。

| 面 | PF | 本仓 | 本仓态度 |
|---|---|---|---|
| 前端 | `program … where` + Normalize | 普通 `def` | 保持 B，不搬 Syntax |
| 定宽整数 | UInt8/16/32/64、窄 Int、UInt128/256 多字 | 仅 UInt64 | 先开 UInt8/32 + 同形 checked 四则 |
| 控制流 | 多块 / match / for 有界 | 单层 `ite`，假支必须 overflow | 任意 if 树、match 枚举 |
| 状态 | 多字段、Option 双叶、Array、dense Map | 全 UInt64 structure | Option/Array 单账户先；Map 后 |
| 入口 | 任意 handler 名 + disc | 固定 init/increment/get 三个 disc | `@[solana_entry]` + 按名 disc |
| 账户 | 单账户 + CPI 多 role | 单账户 + transfer 三账户 walk | 编译期 N；不开放 remaining accounts |
| CPI / Token / PDA | System / Token / ATA / vault PDA 封闭目录 | `systemTransfer` 一条 | 抽出通用 `invoke`；特化仍具名 |
| sysvar | clock.slot / epoch / unixTime 已开 | L4-001 / L4-019 / L4-034 | unix 按无符号 u64 |
| caller | `context.caller` = 指定 outer signer | L4-001 开账户 0 `signerKey0`（首 u64） | 完整 32B / 独立 caller 账户后做 |
| 证明 | Reference / HandlerIR 有界证书；D1–D4 0/27 | 宿主 def 上的工程定理 | 继续钉用户 def；不承诺 `.so` refinement |
| CLI | `pf test/run/verify/deploy` | `lake` + 手工 Mollusk | 本仓小 CLI 即可 |
| 部署 | save-only；禁公网 | 无 | 保持不做 |

「PF 全都支持完了」不成立。它工程面宽，formal 仍停在 StateCell / OptionState 有界切片。本仓要对齐的是**诚实分层**，不是功能清单打勾。

## 本仓必须补、且仍在路径 B 里的缺口

按依赖排。上一行绿了才开下一行。CPI/Token 不是下一刀。

### L1 语言剖面（仍单账户 UInt64）

没有这一层，后面所有类型都编不出来。

| ID | 内容 | 完成定义 |
|---|---|---|
| L1-attr | `@[solana_entry kind]` 标 init / mutate / view；`#solana_build M` 收同一模块里的入口 | 不用手写三 ident；Counter / Pair 仍绿 |
| L1-disc | disc = `sha256("proof-forge-solana-v1:" ++ name ++ "(" ++ params ++ ")")` 前 8 字节 | decrement 不再盗用 increment disc |
| L1-if | Extract 任意 `ite` 树，假支不必是 overflow | `if a then x else y` 两支都是纯值 |
| L1-arith | checked mul / div / mod（与 add/sub 同守卫纪律） | wrapping 入口 fail closed；Mollusk 溢出保持 |
| L1-cmp | `=` `<` `≤` `≥` `>` 进 cond，不只 `LE`/`GE` | Pair `if left = 0` 可抽 |
| L1-digest | `Program` 内容寻址 digest；证明主语与发射主语同一 hash | 夹具钉 digest；改 ops 必变 |

### L2 类型与布局（仍单账户）

字段表已经从 structure 收。下一步是叶子类型，不是账户图。

| ID | 内容 | 完成定义 |
|---|---|---|
| L2-width | `UInt8/16/32` 叶子；偏移按宽度走，不再写死 `* 8` | 窄字段 Mollusk 读写对齐 |
| L2-option | `Option UInt64` = tag+payload 双叶；none 清零 payload | 对齐 PF OptionState 工程行为，不搬证书 |
| L2-array | `Array UInt64 n`（n 编译期常量）连续槽 | 越界 fail closed |
| L2-enum | 无 payload 枚举作 tag；带 payload 后做 | match 抽成分支 |
| L2-marker | layout marker 用本机 SHA-256 算，去掉手工登记表 | 新字段表不必改 `layoutMarkerHex` |

L2-marker 已落地：`SolanaLean.Sha256` 是 kernel 可算的纯函数，不是链上 syscall。disc 与 marker 都按预镜像现算。

### L3 程序形状

| ID | 内容 | 完成定义 |
|---|---|---|
| L3-nmethod | N 个入口，不限三方法 | Counter 同时编 increment 与 decrement |
| L3-view | 只读方法可返回任意已布局叶子，不改账户 | Pair.getRight |
| L3-init-all | `init` 写全部字段，不只第一槽+其余清零 | `init left right` 两个参数 |

### L4 账户与封闭 recipe（明显更贵）

L1–L3 已绿。CPI 先收成编译期钉死的 `invoke`，再往上叠具名特化。不开放运行时拼指令。

| ID | 内容 | 完成定义 |
|---|---|---|
| L4-caller | 读指定 signer 的 32B key | 对齐 PF CallerIsMe 行为，声明 ≠ tx.origin |
| L4-clock | `sol_get_clock_sysvar` → slot / epoch / unix | unix 按无符号 u64 |
| L4-system | 封闭 `system.transfer` recipe | TransferSol 形 Mollusk |
| L4-token | 封闭 Token `transferChecked` + ATA ensure | 只抄 PF catalog，不接 Token-2022 |
| L4-pda | 封闭 vault PDA find / bump | 种子字面量冻结 |

### 明确不做（会杀死项目，不是延期）

- 新 DSL / 搬 PF `program … where`
- Lean FFI → sBPF；Lean C/LLVM → Solana Clang
- 无约束 Lean（IO、partial、sorry、一般递归）
- 「定理 ⇒ 已部署 `.so` / loader / SVM」
- 运行时拼的 CPI（动态 program id、remaining accounts）
- Token-2022、upgradeable loader 管理、公网部署
- 活跟踪 PF 16 万行；把本仓 IR 填进私有 `HandlerIR.mk`（除非 PF 抽出公共构造）
- 换 Anza platform-tools（无强理由）

## 建议顺序

当前竖切已经证明：普通 Lean → 抽出 → `.so` → Mollusk 这条管子通。
下一大切面是 **L1（属性 + 多入口 disc + if/算术）**，不是 CPI。

L1 做完，本仓才像「编译剖面」而不是「两个示例的模板」。
L2/L3 让 Examples 能长出比 Counter/Pair 复杂的单账户合约。
L4 只在有真实第二合约（转账 / Token）时开，并且一条 recipe 一条任务。
