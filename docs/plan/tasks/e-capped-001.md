---
id: e-capped-001
scope: evm
status: done
depends-on: [e-cap-001]
---

# e-capped-001 Capped reuses owner + pause + cap

## objective

第二个合约证明 SDK 能组合，不用回改 Extract / Ops / IR / 主 Emit。
`Examples.Evm.Capped` 不是 Token：没有 hashed map、没有 ERC-20。只有构造期
owner、`paused`、固定 `cap`、账户里的 `supply`。

- ctor `constructor(address)`，owner 走 immutable `evmImm20`
- storage：`paused : UInt8`，`cap` / `supply : UInt256`；`init` 把 cap 写成 100
- `mint`：非 owner → `Unauthorized`；paused → `Paused()`；超过 cap →
  `CapExceeded()`；成功只加 supply
- `pause` / `unpause`：非 owner → `Unauthorized`
- view：`ownerOf` / `pausedOf` / `capOf` / `totalSupply`
- NativeFx 已有 `Paused` / `CapExceeded`，本切片不登记新叶子
- Anvil：owner mint 成功；非 owner mint 解码 Unauthorized；pause 后 mint
  解码 Paused()；超 cap 解码 CapExceeded()，supply 保持
- digest 是新程序

## 不做

generic CALL；DELEGATECALL；改 cap 的入口；把守卫收进新 Source 模块；
Token 再迁叶子。
