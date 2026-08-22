# SolanaLean.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。v0 sketch = 定义体用到的常量名排序表。

## Boundary

递归下降 `Expr`。`x ≤ u64Max - y` → `checkedAddU64`；`y ≤ x` → `checkedSubU64`。可变方法无守卫则 fail closed。

`fields` 默认从 `init` 返回类型收：必须是已注册 `structure`、无 `extends`、每个直接字段 `UInt64`。声明顺序 = 账户槽顺序。`#solana_extract … with "a","b"` 仍可覆盖。ops 里出现的字段名必须在表内。

`@[solana_entry]` 只是标记。种类从返回类型推断：structure → init；`Except` → mutate；`UInt64` → view。Lean `init` 的链上名是 `initialize`。同一名字空间允许多个 mutate。重复链上名 fail closed。

## API

- `inferFields env initName : Except String (Array String)`
- `extractProgram env init increment get (name?) (fields?)`
- `#solana_extract init increment get`
- `#solana_extract init increment get with "left", "right"`
- `#solana_build Namespace`（收 `@[solana_entry]`）
- `extractModule env ns`

## Tests

`Tests/ExtractSpec.lean`：Counter / Pair（无 `with`）抽出；非 `UInt64` 字段拒绝。
`Tests/BuildSpec.lean`：`#solana_build` 收入口；无标记 fail closed。
