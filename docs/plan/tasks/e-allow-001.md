---
id: e-allow-001
scope: evm
status: done
depends-on: [e-burn-001]
---

# e-allow-001 Token.increaseAllowance / decreaseAllowance

## objective

在现有 pair allowance 上做封闭加减，成功写回并 LOG3 `Approval(caller, spender, new)`。

- `increaseAllowance(spender, added)`：`evmAdd256` 现额度；溢出 revert
- `decreaseAllowance(spender, subtracted)`：不够 → `Insufficient(have, want)`
- Anvil：approve 20 后 increase 5 → 25；decrease 10 → 15；超额 decrease 解码 Insufficient
- SVM / Legacy adapter 不新增叶

## 不做

无限额度；Permit2；把 approve 改成这两条的包装。
