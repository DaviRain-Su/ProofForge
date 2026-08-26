---
id: e-immut-001
scope: evm
status: done
depends-on: [e-weth-001]
---

# e-immut-001 构造参数当 immutable

## objective

构造参数可以烘焙进 runtime bytecode，不占 storage。Yul 走 `setimmutable` / `loadimmutable`。

- 新增 `evmImmU64`：构造期 `uint64` 叶，runtime `loadimmutable("imm0")`
- 新增 `evmImm20`：构造期 `Addr20`，runtime `loadimmutable("immAddr")` 再拆三叶
- `init` 把 ctor 参数写进 dummy 以外的字段时，那些字段如果只被 `evmImm*` 读、从不 `sstore`，则改走 immutable。本刀用独立例子，不改 Counter / Ownable。
- `Examples.Const`：`init (seed : UInt64) (who : Addr20)`；`seedOf` 读 `evmImmU64`；`whoOf` 读 `evmImm20`。dummy 仍占槽。
- ctor Yul：`setimmutable("imm0", ctor_arg0)` / pack Addr20 后 `setimmutable("immAddr", packed)`
- runtime Yul：view 用 `loadimmutable`，不含 `sload` 读这两项
- Anvil：部署后 `seedOf()==seed`、`whoOf()==who`；改 storage dummy 不影响 immutable
- SVM 拒新叶；Legacy adapter 拒新叶

## 不做

把 Ownable.owner / Counter.initial 改成 immutable；动态 immutable 名字 DSL；多个同型 immutable 的通用表；主网声明。
