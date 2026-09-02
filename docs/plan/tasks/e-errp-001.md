---
id: e-errp-001
scope: evm
status: done
depends-on: [e-swap-001]
---

# e-errp-001 参数化 Unauthorized / ZeroAddress

## objective

不够再开自定义 error DSL。只加两片封闭错误，和 `Insufficient(uint256,uint256)` 同一形状。

- `evmRevertUnauthorized who` → ABI `Unauthorized(address)`，`revert(0,36)`
- `evmRevertZeroAddress` → ABI `ZeroAddress()`，`revert(0,4)`
- `Examples.Evm.Ownable.bump` 非 owner 改走 `Unauthorized(caller)`，不再 selector-only `unauthorized`
- `Examples.Evm.Ownable.guardZero`：`who == 0` 则 `ZeroAddress()`
- ABI JSON 带这两条 error
- Anvil：非 owner bump 解码 `Unauthorized(address)`；`guardZero(0)` 解码 `ZeroAddress()`
- SVM / Legacy adapter 拒新叶

## 不做

自定义 error DSL；任意参数列表；把 overflow 也改成 ABI error。
