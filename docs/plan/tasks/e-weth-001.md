---
id: e-weth-001
scope: evm
status: done
depends-on: [e-wei-001]
---

# e-weth-001 封闭 WETH deposit / withdraw

## objective

ETH 进出已经是 `UInt256` wei。这一刀加封闭 WETH 菜谱，callee 编译期固定（WETH 地址是 `Addr20` 参数，和 Vault 的 token 一样）。

- 新增 `evmWethDeposit weth amt`：value CALL `deposit()`，selector `0xd0e30db0`，calldata 4 字节，value = packed wei。CALL 失败则 revert。宿主返回 `amt.w0`。
- 新增 `evmWethWithdraw weth amt`：CALL `withdraw(uint256)`，selector `0x2e1a7d4d`，36 字节 calldata，value 0。返回数据走和 ERC-20 transfer 一样的 fail-closed bool/empty 规则。宿主返回 `amt.w0`。
- `Examples.Evm.Vault` 增加 payable `wrap`（`evmDeposit256` + `evmWethDeposit`）和 `unwrap`（`evmWethWithdraw`）。Vault 加 `receive()`，否则 WETH 把 ETH 打回来会失败。
- Anvil：最小 WETH mock（ETH in → mint WETH 给 caller；withdraw 烧掉并打回 ETH）。wrap 后 `held(weth)` 增加；unwrap 后 ETH 回到 Vault。
- SVM 拒新叶；Legacy adapter 拒新叶。

## 不做

泛化 payable CALL；WETH9 全接口（transfer/approve 已有 ERC-20 菜谱）；DELEGATECALL / proxy / CREATE2；主网 WETH 声明。
