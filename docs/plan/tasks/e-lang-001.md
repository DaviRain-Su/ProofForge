---
id: e-lang-001
scope: evm
status: done
depends-on: [e-rt-001]
---

# e-lang-001 位运算 · 有界 for · 下标 · ABI · 多叶 return · 命名 revert

## objective

E-LANG 整包，见 [05-evm-coverage-slices.md](../../research/05-evm-coverage-slices.md)。

- 位运算 Val：`&&& ||| ^^^ ~~~ <<< >>>`；移位 count≥64 revert
- 有界 `for i in [0:N]`（N 字面量 ≤64）抽成累加；UInt64 溢出 revert
- `Vector.get/set` 运行时下标；`i ≥ n` revert
- ABI 按 Lean 参数宽：`UInt8/16/32/64` → `uint8/16/32/64`
- `UInt64 × UInt64` view → ABI tuple
- `Error` 非 `overflow` 构造子 → `revert` 带 `keccak("name()")` 前 4 字节
- SVM 拒全部新语言叶/效应
- `Examples.Lang` + Anvil

## 不做

一般递归、`while`、动态 Array、嵌套 Option、改 Flag 的既有 `uint64` ABI。
