# 01 PRD

## 产品句

solana-lean 是 Lean 4 的一个 **Solana 编译剖面**：普通 `def` 写合约，普通 `theorem` 证合约，属性标记入口，fail-closed 子集检查，抽出到已有 sBPF lowering。

## 用户

会写 Lean、要上 Solana 的人。不要求学 `program … where`。

## v0 必须有

1. 用普通 Lean 写单账户 Counter（`UInt64` state，init / increment / get）。
2. `@[solana_entry]`（或等价属性）标记可编译根。
3. 传递闭包检查：拒绝 `IO`、`partial`、`sorry`、`@[extern]`、`@[implemented_by]`、无界递归。
4. 抽出后的语义对象可被 Lean 定理引用；证明主语与编译主语同一 identity。
5. 降到 sBPF `.s`，经 locked `sbpf` 得到 `.so`。
6. Mollusk：init 写回、increment 成功、get、overflow 保持。
7. 文档明确：定理不蕴含 loader / SVM / 公网部署正确。

## v0 不做

- 新具体语法（`program … where`）。
- 无约束 Lean。
- Lean FFI → 汇编。
- 通用 CPI / PDA / 多可变账户 / Token。
- EVM 及其它链。
- 「定理 ⇒ 已部署 `.so`」。
- 公网部署。

## 成功标准

同一份 `increment`：

- `lake build` 类型检查通过；
- 用户定理（例如 overflow 不改状态）被 kernel 接受；
- 同一闭包编出的 `.so` 在 Mollusk 上复现 PF StateCell 行为。

## 竖切之后才是通用合约

Counter 不是产品终点，是第一条打穿的竖切：

```
普通 Lean def → Profile → Extract → IR → .s → sbpf → .so → Mollusk
```

竖切绿了，才把中间三层做成**与业务无关的剖面**：

| 层 | Counter 现在 | 通用之后 |
|---|---|---|
| 用户表面 | `Examples.Counter`（init/increment/decrement/get） | 任意通过 Profile 的 `def` |
| Extract | 从 `init` 返回 structure 收字段表 | 属性标记入口 / 任意 if 树 |
| Emit | 按 `fields` 算偏移与 layout marker | CPI / 多账户 |

v0 通用面仍然单账户、`UInt64`、无 CPI。多账户 / Token 不在这条竖切里。

## 非目标指标

不和 Anchor 比功能面。不和 PF 比多链。只比「Lean 表面 + 可执行 + 可证」。
