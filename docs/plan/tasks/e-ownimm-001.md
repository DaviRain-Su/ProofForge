---
id: e-ownimm-001
scope: evm
status: done
depends-on: [e-permit-001]
---

# e-ownimm-001 Ownable.owner 改构造期 immutable

## objective

`Examples.Ownable.owner` 不再占三槽 storage。ctor `Addr20` 烘焙进 bytecode，runtime `loadimmutable("immAddr")`。

- State 只留 `value`
- `bump` / `ownerOf` 读 `evmImm20`
- ctor 仍接收 owner；Anvil `ownerOf` 仍等于部署者
- `touch`/bump 改 `value` 不影响 owner
- SVM 仍拒 EVM 叶；Legacy adapter 已拒 `imm*`

## 不做

可转让 owner；多个 immutable address；Counter.initial 改 immutable。
