---
id: e-wei-001
scope: evm
status: done
depends-on: [e-u256-001]
---

# e-wei-001 ETH 金额升到显式 UInt256

## objective

Token / Vault 余额已经是 `UInt256`；ETH 进出还停在 `UInt64`。这一刀把 wei 升宽，默认算术仍是 `UInt64`。

- 新增 `evmCallValue256` / `evmSelfBalance256`：四叶，ABI `uint256`
- 新增封闭 `evmDeposit256` / `evmSendEth256`：`eq(callvalue(), packed)` / value CALL 带 packed wei
- 旧 `evmCallValue` / `evmDeposit` / `evmSendEth` 仍是 UInt64 调试叶
- `Examples.Evm.TipJar` 的 `deposit` / `payout` / `callValue` / `selfBal` 改走 256
- Anvil：小额仍过；`deposit(uint256)` / `payout(address,uint256)` / `selfBal()(uint256)`
- SVM 拒新叶

## 不做

`div`/`mod` 256；把 Counter / Ownable 升宽；WETH 菜谱（下一刀）；immutable；主网 wei 声明。
