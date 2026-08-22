---
id: e-asset-001
scope: evm
status: done
depends-on: [e-lang-001]
---

# e-asset-001 hashed Map + 封闭 ERC-20

## objective

E-ASSET 整包，见 [05-evm-coverage-slices.md](../../research/05-evm-coverage-slices.md)。

- `Map UInt64 UInt64`：一 base slot；`keccak256(key || base)` → occ + payload
- `Map` 按 Addr20 三叶当 key：`keccak256(w0||w1||w2||base)`
- `evmTokenTransfer tokenW0..W2 dstW0..W2 amt`：`transfer(address,uint256)` CALL
- `evmTokenBalanceOfSelf tokenW0..W2`：`STATICCALL balanceOf(address(this))`，超 UInt64 revert
- SVM 拒全部新叶/效应
- `Examples.Vault` + Anvil + testdata ERC-20 mock

## 不做

approve/allowance；Token-2022；任意 CALLEE；嵌套 Map；Map 作参数。
