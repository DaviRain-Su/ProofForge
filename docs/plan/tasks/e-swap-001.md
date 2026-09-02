---
id: e-swap-001
scope: evm
status: done
depends-on: [e-cmp20-001]
---

# e-swap-001 封闭 Uniswap V2 swapExactTokensForTokens，path 长度 2

## objective

封闭 router CALL。路径长度编译期固定为 2。不是泛化 CALL，也不是动态 `address[]`。

- 新增 `evmSwapExact2 router tokenA tokenB amtIn minOut`
- Yul：selector `0x38ed1739`，path 长度 2，`to = address()`，`deadline = uint256.max`
- CALL 失败则 revert。返回是动态 `uint256[]`，不按 ERC-20 bool 规则解析。
- `Examples.Evm.Vault.swap2`
- Anvil：最小 router mock（`transferFrom` tokenA，mint tokenB 给 `to`）
- SVM / Legacy adapter 拒新叶

## 不做

path 长度 3；泛化 CALL；动态数组类型；主网 router；报价 / getAmountsOut。
