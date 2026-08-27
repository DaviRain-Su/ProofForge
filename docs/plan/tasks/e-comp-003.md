---
id: e-comp-003
scope: evm
status: done
depends-on: [e-comp-002]
---

# e-comp-003 迁封闭 CALL 叶进 Component

## objective

把现有封闭 ERC-20 / WETH / Uniswap / permit 叶从 generic EVM Ops/IR/Emit 收进
`Evm.ClosedCall`。源侧 helper 和 Extract match_pattern 形状不变；canonical 拼写保持
`ttxfer` / `wethdep` / `permit` / `ext.tokenBalance256`，Token/Vault digest 不变。

- `ValKind` 去掉 `tokenBalance256` / `tokenAllowance256`
- `OpExt` / `IR.Op` 去掉平行 token/WETH/swap/permit 构造子
- Yul 从主 Emit 挪到 component-owned emitter；ABI 的 Expired/Unauthorized 探测认 component

## 不做

环境 opcode（`callValue256` / `selfBalance256` / `domainSep256` 仍顶层）；LOG3 / ETH send；
Ownable mint / pause。
