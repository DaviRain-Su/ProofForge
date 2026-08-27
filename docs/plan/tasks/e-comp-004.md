---
id: e-comp-004
scope: evm
status: done
depends-on: [e-comp-003]
---

# e-comp-004 迁 ETH / LOG / revert / receive 进 Component

## objective

把现有 native ETH、LOG、参数化 revert、`receive` 叶从 generic EVM Ops/IR/Emit 收进
`Evm.NativeFx`。源侧 helper 和 Extract match_pattern 形状不变；canonical 拼写保持
`edep` / `esend` / `elog3.Transfer` / `err.ZeroAddress` / `erecv`，Token / Vault / TipJar /
Ownable digest 不变。

- `OpExt` / `IR.Op` 去掉平行 deposit / sendEth / log / revert / receive 构造子
- Yul 从主 Emit 挪到 component-owned emitter；ABI 的 Insufficient / Unauthorized /
  ZeroAddress / LOG 探测认 component
- 环境 opcode（`callValue256` / `selfBalance256` / `domainSep256`）仍顶层

## 不做

generic CALL；DAI permit；DELEGATECALL / proxy / CREATE2；Ownable mint / pause。
