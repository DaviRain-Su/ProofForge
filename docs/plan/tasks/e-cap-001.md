---
id: e-cap-001
scope: evm
status: done
depends-on: [e-pause-001]
---

# e-cap-001 Token mint cap + CapExceeded

## objective

pause 之后的下一个封闭 recipe。`CapExceeded()` 和 `Paused()` 同构：无参 ABI
error，`revert(0,4)`。Token mint 不能把 totalSupply 推过固定 cap。

- NativeFx：`evmRevertCapExceeded` / `revertCapExceeded` / `err.CapExceeded`
- 只注册进 `opOfRuntimeApp`、NativeFx Call/Emit、ABI `CapExceeded()`、Legacy adapter 拒
- storage 加 `cap : UInt256`，`init` 写成 `1000`（不是 ctor 参数，也不改 immutable 槽）
- `mint`：`cap >= supply + amt` 才铸；否则 `CapExceeded()`，状态保持
- `capOf` view
- 其它入口不受 cap
- Anvil：mint 到 cap 成功；再 mint 解码 `CapExceeded()`，supply 保持
- digest 会变，这是新能力

## 不做

ctor 参数 cap；改 cap 的入口；generic CALL；DELEGATECALL；环境 opcode Source；
拆 asVal。
