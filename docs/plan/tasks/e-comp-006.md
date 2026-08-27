---
id: e-comp-006
scope: evm
status: done
depends-on: [e-comp-005]
---

# e-comp-006 给封闭 CALL / WideWord / NativeFx 加源侧 facade

## objective

合同代码不再直接点 Runtime 上的 `evmTokenTransfer` / `evmAdd256` / `evmLogTransfer256`。
各自经 `ClosedCall.Source` / `WideWord.Source` / `NativeFx.Source` 的 `@[pf_inline]`
helper；抽出时消去到已有 Runtime stub 和 component 计划。不新增 Ops / IR / 主 Emit
case，digest 不变。

- Vault 的 ERC-20 / WETH / swap / permit 走 `ClosedCall.Source`
- Token / Ownable / Wide 的 256-bit 算术和 Addr20 比较走 `WideWord.Source`
- Token / Ownable / Vault / TipJar 的 LOG / revert / ETH / receive 走 `NativeFx.Source`
- Extract 对这三组 Source 命名空间做与 HashedMap 相同的 inline 投影展开

## 不做

环境 opcode Source（`caller` / `callValue256` / immutables）；pause / cap / Ownable mint；
generic CALL。
