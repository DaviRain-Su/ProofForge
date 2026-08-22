# SolanaLean.Attr

## Purpose

标记可编译根。不是新语法。种类不写在属性里，从 `def` 的返回类型推断。

## Boundary

只记录声明名。不检查闭包（那是 Profile）、不抽出（那是 Extract）。只能标 `def`。

## API

- `@[solana_entry]`
- `solanaEntryAttr.hasTag env decl`

## Tests

`Tests/BuildSpec.lean`：有标记则 `#solana_build` 成功；无标记 fail closed。
