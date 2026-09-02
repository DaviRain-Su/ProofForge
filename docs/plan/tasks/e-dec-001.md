---
id: e-dec-001
scope: evm
status: done
depends-on: [e-allow-001]
---

# e-dec-001 Token.decimals 编译期 uint8 view

## objective

`Examples.Evm.Token.decimals` 返回字面量 `18`，ABI `decimals()(uint8)`。不是 storage，不是动态 string。

- 抽出认 `UInt8` view 的 `retWidths = #[1]`
- ABI JSON 输出 `uint8`
- Anvil：`decimals()` 读到 18；mint/transfer 后仍是 18
- SVM / Legacy adapter 不新增叶

## 不做

`name()` / `symbol()` 动态 string；可配置 decimals；构造期 immutable decimals。
