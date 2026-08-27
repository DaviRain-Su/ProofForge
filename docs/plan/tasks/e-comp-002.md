---
id: e-comp-002
scope: evm
status: done
depends-on: [e-comp-001]
---

# e-comp-002 迁 hashed-map / 256-bit 叶进 Component

## objective

把现有 hashed-map 读写和 packed 256-bit 比较/算术从 generic EVM Ops/IR/Emit 收进
`Evm.HashedMap` / `Evm.WideWord`。源侧 helper 和 Extract match_pattern 形状不变；
canonical 拼写保持旧闭包字符串，Token/Vault/Wide/Ownable digest 不变。

- `ValKind` 去掉 `mapGet*` / `ge256` / `eq20` / `arith256`
- `OpExt` / `IR.Op` 去掉平行 map get/set 构造子
- Yul 从主 Emit 挪到 component-owned emitter；主链路只走 `.component`

## 不做

封闭 CALL（tokenTransfer / WETH / swap / permit）；环境 opcode；Ownable mint / pause。
