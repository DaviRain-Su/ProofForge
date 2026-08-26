---
id: e-swap3-001
scope: evm
status: done
depends-on: [e-swap-001]
---

# e-swap3-001 封闭 Uniswap V2 swapExactTokensForTokens，path 长度 3

## objective

在 path-2 之上再开一条编译期固定的 path-3 菜谱。仍然不是泛化 CALL，也不是动态 `address[]`。

- 新增 `evmSwapExact3 router tokenA tokenB tokenC amtIn minOut`
- Yul：selector `0x38ed1739`，path 长度 3，`to = address()`，`deadline = uint256.max`
- CALL 失败则 revert。返回动态 `uint256[]` 不解析。
- `Examples.Vault.swap3`
- Anvil：同一 Router mock 接受 path 2 或 3；swap3 从 tokenA 扣、给 tokenC mint
- SVM / Legacy adapter 拒新叶

## 不做

更长 path；泛化 CALL；动态数组类型；报价 / getAmountsOut；主网 router。
