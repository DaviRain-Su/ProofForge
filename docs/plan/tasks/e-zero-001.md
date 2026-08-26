---
id: e-zero-001
scope: evm
status: done
depends-on: [e-burnfrom-001]
---

# e-zero-001 Token 地址参数拒绝零地址

## objective

封闭 `ZeroAddress()` 检查：mint / transfer / transferFrom dest / approve / increaseAllowance / decreaseAllowance / burnFrom owner 的 Addr20 若是 `⟨0,0,0⟩`，则 `evmRevertZeroAddress`，状态保持。

- 复用已有 `evmEq20` + `evmRevertZeroAddress` 叶，不新增 IR
- 成功路径保持原语义
- Anvil：对零地址 mint / transfer / approve 解码 `ZeroAddress()`；正常路径数字不变
- SVM / Legacy adapter 不新增叶

## 不做

暂停；mint cap；Ownable mint；把零检查做成独立 helper 入口；permit owner/spender 零地址（permit 仍是封闭 CALL）。
