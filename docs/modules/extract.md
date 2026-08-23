# ProofForge.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。v0 sketch = 定义体用到的常量名排序表。

## Boundary

递归下降 `Expr`。`x ≤ u64Max - y` → `checkedAddU64`；`y ≤ x` → `checkedSubU64`；`y = 0 ∨ x ≤ u64Max / y` → `checkedMulU64`；`y ≠ 0` 后 `/` `%` → `checkedDivU64` / `checkedModU64`。比较认 `=` `≠` `<` `≤` `>` `≥`。假支不必是 overflow。`match opt with | none => a | some n => b` 抽成 `ite (eq tag 0)`。`ProofForge.Runtime.clockSlot` / `signerKey0` / `acc*`（以及同名后缀）抽成运行时叶子。`invoke programIx metas data` 抽成 `Op.invoke`。`systemTransfer` / `invokeAcc1` 是普通包装，展开成同一条。`findPda "seed"` 抽成运行时叶子。`evmDeposit` / `evmSendEth` / `evmLog*` / pair-key Map / 全部 EVM 环境叶抽成独立 ops。位运算 / 有界 `forIn [:N]` / 运行时 `Vector` 下标 / 命名 `Error` 构造子 / `UInt64 × UInt64` view 也抽。SVM 发射器再拒语言叶和 EVM 叶。可变方法无 checked 算术 / ite / invoke / EVM 效应 / 语言叶则 fail closed。嵌套用户 structure 摊成 `parent_child` 槽；`Vector Nested n` 每个元素再摊，例如 `nodes_0_value`。`extends` 仍关。Sokoban 节点是普通 structure + `Vector Node n`。mutate 的 `State.mk` / `Vector.set` / 嵌套 `with` 按叶 diff：改了几个槽就发几条 `storeField`，不按合约猜 dest。单叶仍压成 `okState`。旋转 / 染色仍关。

`slots` 默认从 `init` 返回类型收：必须是已注册 `structure`、无 `extends`。叶子只接受 `UInt8/16/32/64`、`Bool`（1 字节 u8-le）、`Option UInt64`（展开双叶）、`Vector UInt64 n`（展开 `name_0…name_{n-1}`）、无 payload 用户枚举（一叶 tag），两构造子且其中一个带一个 `UInt64` 的 inductive（按 Option 双叶），以及嵌套用户 structure（摊成 `parent_child`）。不定长 `Array`、多字段 inductive fail closed。`#pf_extract … with "a","b"` 仍可覆盖槽名，且必须与推断表一致。ops 里出现的字段名必须在表内。

用户合约不绑仓库目录名。`#pf_build Ns` 收任意名字空间下的 `@[pf_entry]`。字段投影认已注册 structure，排除 `ProofForge` / `Lean` / `Std` / `Init`。`Examples.` / `Projects.` 不是准入条件。

`@[pf_entry]` 只是标记。种类从返回类型推断：structure → init；`Except` → mutate；`UInt64` → view。Lean `init` 的链上名是 `initialize`。允许多个 init / mutate / view；槽表从名为 `init` 的那个收。重复链上名 fail closed。`init` 的 `paramCount` 按 λ 个数算。抽出按类型展开槽名（`name_tag` / `name_i`），不按合约字段名写死。

## API

- `inferFields env initName : Except String (Array String)`
- `extractProgram env init increment get (name?) (fields?)`
- `#pf_extract init increment get`
- `#pf_extract init increment get with "left", "right"`
- `#pf_build Namespace`（收 `@[pf_entry]`）
- `extractModule env ns`

## Tests

`Tests/ExtractSpec.lean`：Counter / Pair / Flag / Maybe / Window 抽出；非支持叶子与不定长 Array 拒绝。
`Tests/BuildSpec.lean`：`#pf_build` 收入口；无标记 fail closed。
`Tests/LayoutSpec.lean`：窄字段偏移、Option 双叶、layout marker。
