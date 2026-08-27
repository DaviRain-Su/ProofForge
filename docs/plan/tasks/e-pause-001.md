---
id: e-pause-001
scope: evm
status: done
depends-on: [e-comp-013]
---

# e-pause-001 Token owner mint + Paused

## objective

第一个新封闭 recipe，不再迁 SDK 叶子。`Paused()` 和 `ZeroAddress()` 同构：无参
ABI error，`revert(0,4)`。Token 第一次有权限模型。

- NativeFx：`evmRevertPaused` / `revertPaused` / `err.Paused`
- 只注册进 `opOfRuntimeApp`、NativeFx Call/Emit、ABI `Paused()`、Legacy adapter 拒
- Token ctor 改 `constructor(address)`，owner 走 immutable `evmImm20`
- storage 加 `paused : UInt8`（0 运行，1 暂停）
- `pause` / `unpause`：非 owner → `Unauthorized(caller)`
- `mint`：非 owner → `Unauthorized`；paused → `Paused()`；零地址仍 `ZeroAddress()`
- `transfer` / `transferFrom` / `burn` / `burnFrom` / `approve` /
  `increaseAllowance` / `decreaseAllowance`：paused → `Paused()`，状态保持
- view 不受 pause
- Anvil：owner mint 成功；非 owner mint 解码 Unauthorized；pause 后 transfer
  解码 Paused()，余额保持
- digest 会变，这是新能力

## 不做

cap；generic CALL；DELEGATECALL；环境 opcode Source；拆 asVal。
