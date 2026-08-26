---
id: e-burn-001
scope: evm
status: done
depends-on: [e-supply-001]
---

# e-burn-001 Token.burn 扣余额并减 totalSupply

## objective

封闭 `burn(uint256)`：从 caller 扣余额，`evmSub256` 减账户 `supply`，LOG3 `Transfer(caller, 0, amt)`。

- 余额不足 → `Insufficient(have, want)`，状态保持
- 不做权限 / cap / burnFrom
- Anvil：burn 后余额和总量都减；超额 burn 解码 Insufficient
- SVM / Legacy adapter 不新增叶

## 不做

burnFrom；minter 角色；销毁到非零地址。
