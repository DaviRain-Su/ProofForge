---
id: e-burnfrom-001
scope: evm
status: done
depends-on: [e-dec-001]
---

# e-burnfrom-001 Token.burnFrom 扣 owner 余额和额度

## objective

封闭 `burnFrom(owner, amt)`：caller 用额度烧掉 owner 的币。

- 额度不够或余额不够 → `Insufficient(have, want)`，状态保持
- 成功：扣 owner 余额、减 pair allowance、`evmSub256` 减 `supply`、LOG3 `Transfer(owner, 0, amt)`
- Anvil：approve 后 burnFrom；超额额度 / 超额余额失败
- SVM / Legacy adapter 不新增叶

## 不做

无限额度；permit 原子 burnFrom；权限角色。
