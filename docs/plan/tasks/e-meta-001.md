---
id: e-meta-001
scope: evm
status: done
depends-on: [e-zero-001]
---

# e-meta-001 Token.name / symbol 编译期 bytes32 view

## objective

`name()` / `symbol()` 返回编译期 `Bytes32` 字面量，ABI `bytes32`。不是动态 `string`，不是 storage。

- `name` = 右填充 ASCII `"Token"`
- `symbol` = 右填充 ASCII `"PF"`
- 抽出认 `Bytes32` view 的 `retWidths = #[33]`
- Anvil：读到固定 bytes32；mint 后不变
- SVM / Legacy adapter 不新增叶

## 不做

动态 `string`；可配置 name/version；把 DOMAIN_SEPARATOR 的 name 改成读这个 view。
