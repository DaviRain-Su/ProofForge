# SolanaLean.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。v0 sketch = 定义体用到的常量名排序表。

## Boundary

递归下降 `Expr`。`x ≤ u64Max - y` → `checkedAddU64`；`y ≤ x` → `checkedSubU64`；`y = 0 ∨ x ≤ u64Max / y` → `checkedMulU64`；`y ≠ 0` 后 `/` `%` → `checkedDivU64` / `checkedModU64`。比较认 `=` `≠` `<` `≤` `>` `≥`。假支不必是 overflow。`match opt with | none => a | some n => b` 抽成 `ite (eq tag 0)`。可变方法无 checked 算术则 fail closed。

`slots` 默认从 `init` 返回类型收：必须是已注册 `structure`、无 `extends`。叶子只接受 `UInt8/16/32/64`、`Option UInt64`（展开双叶）、`Vector UInt64 n`（展开 `name_0…name_{n-1}`）与无 payload 用户枚举（一叶 tag，构造子按声明顺序编号）。不定长 `Array`、`Bool`、带 payload inductive fail closed。`#solana_extract … with "a","b"` 仍可覆盖槽名，且必须与推断表一致。ops 里出现的字段名必须在表内。

`@[solana_entry]` 只是标记。种类从返回类型推断：structure → init；`Except` → mutate；`UInt64` → view。Lean `init` 的链上名是 `initialize`。允许多个 init / mutate / view；槽表从名为 `init` 的那个收。重复链上名 fail closed。`init` 的 `paramCount` 按 λ 个数算。抽出按类型展开槽名（`name_tag` / `name_i`），不按合约字段名写死。

## API

- `inferFields env initName : Except String (Array String)`
- `extractProgram env init increment get (name?) (fields?)`
- `#solana_extract init increment get`
- `#solana_extract init increment get with "left", "right"`
- `#solana_build Namespace`（收 `@[solana_entry]`）
- `extractModule env ns`

## Tests

`Tests/ExtractSpec.lean`：Counter / Pair / Flag / Maybe / Window 抽出；非支持叶子与不定长 Array 拒绝。
`Tests/BuildSpec.lean`：`#solana_build` 收入口；无标记 fail closed。
`Tests/LayoutSpec.lean`：窄字段偏移、Option 双叶、layout marker。
