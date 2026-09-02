---
id: e-tok-001
scope: evm
status: done
depends-on: [e-own-001]
---

# e-tok-001 封闭 ERC-20 形：余额 + 真额度扣减 + Transfer/Approval

## objective

E-TOK 整包。本合约自己当 token，不是再调外部 ERC-20。

- `Map Addr20 UInt64` 记余额；pair-key 记 allowance
- `transfer`：扣 sender、加 recipient；不足 → 命名 revert，状态保持
- `approve`：caller → spender 写额度，并 LOG `Approval(uint64)`
- `transferFrom`：查 pair allowance 且 owner 余额够；成功则余额加减且额度相减
- LOG：`Transfer(uint64)` / `Approval(uint64)`（仍是 `Name(uint64)`，不编 indexed address）
- ABI JSON 带这两条 `event`
- SVM 拒全部新效应
- `Examples.Evm.Token` + Anvil

## 不做

外部 CALLEE `transferFrom`；indexed address topic；event 多叶 data；mint/burn 权限模型以外的 Token-2022；嵌套 Addr20 structure。
