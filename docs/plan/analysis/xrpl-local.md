# XRPL：本地先做，公网先放

> 2026-08-30。权威排期仍是 [xrpl-next.md](xrpl-next.md)。
> 本文钉死开发策略，避免再把本地绿写成公开绿，也避免公开节点挡住就停工。

## 策略

两条网、两套事实。Lean 只接线已经在 **当前目标网** 上 tesSUCCESS 的 host。

| 网 | 节点 | host 名 | 本仓 target | 角色 |
|---|---|---|---|---|
| 本地 transia/alphanet 2.6.1-rc1 | nid **63456** | `get_*` | `--target xrpl` | **现在继续做的地方** |
| 公开 AlphaNet 3.3.0-rc1 | nid **21337** | XLS-0102 (`tx_field` / `home_le_field`) | `--target xrpl-alphanet` | 已绿的 caller 卡 / Parameters 继续用；被挡住的表面 **先放** |

公开节点挡住的三条，本仓改不了 `alphanet.xrpl.org`：

| 表面 | 公开 3.3.0 | 本地 2.6.1 | 公开 SDK |
|---|---|---|---|
| `emit_built_txn` Payment | **-196 tefBAD_AUTH**（伪账户 `checkSign`） | **绿**（`XrplEmit.ping`） | `Sdk.Payments` **关** |
| 程序拥有 ContractData | host **-22** | **绿**（`Card.storeSelf` / `XrplVault`） | `Sdk.Map` **关** |
| Create `tfSendAmount` / Function.ParameterType | 新 Create 常 temBAD_SIGNATURE；Call Parameters **已绿** | 注资 Create **绿**；Parameters **不能签**（skip） | 不发明 PDA |

所以：

1. **本地能 tesSUCCESS 的，就在本地接线**（Runtime 叶 → `pf_inline` → Example → `runtime-tests/xrpl/*.sh`）。
2. **公开仍 -196 / -22 的，门面继续关。** 不把 `Pay.emitToCaller` 叫成 `Sdk.Payments`，不把 `Card.storeSelf` 叫成 `Sdk.Map`。
3. 公开已经绿的（caller 卡、Mint/Lock/Pay、Parameters）继续用 `--target xrpl-alphanet` 做组合层，不必等那三条。
4. 公开节点修好之后，同一套叶子再挂到 `xrpl-alphanet` 并改门面名字。在那之前不要承诺活网 Payment / 程序卡。

```diagram
┌──────────────────────┐          ┌─────────────────────────┐
│ 本地 2.6.1 / 63456   │          │ 公开 3.3.0 / 21337      │
│ get_*  host          │          │ XLS-0102 host           │
│                      │          │                         │
│ emit Payment 绿      │──先做──▶│ emit 仍 -196  → 先放    │
│ 程序卡 storeSelf 绿  │──先做──▶│ 程序卡仍 -22 → 先放     │
│ Parameters 不能签    │──先放──▶│ Parameters 已绿          │
│                      │          │ caller 卡 / Mint 已绿   │
└──────────────────────┘          └─────────────────────────┘
```

## 本地已接线（不要再探针一遍）

| SDK / Runtime | 程序 | 活脚本 |
|---|---|---|
| `Pay.emitToCaller` → `xrplEmitPay`（192 drops 给 caller） | `XrplEmit.ping` | `emit.sh` |
| `Pay.emitToCallerDrops` → STAmount `0x40…` OR drops | `XrplTip.ping`（编译期 384） | `tip.sh` |
| `Pay.emitToLit hex` → 192 drops to compile-time AccountID | `XrplGift.ping`（钱包 B） | `gift.sh` |
| `Card.storeSelf` → 合约 AccountID 卡 | `XrplVault.credit` | `vault.sh` |
| `storeSelf` + `emitToCaller` 兑 192 drops | `XrplCash.credit` / `cash` | `cash.sh` |
| Access + Pausable + 程序卡 + 兑 XRP | `XrplBank` pause/credit/cash | `bank.sh` |
| + per-user `lock` 挡 cash（状态码 5） | `XrplSafe` freeze/cash | `safe.sh` |
| 积分转 B + 兑 XRP 给 B + pause/freeze | `XrplPool` | `pool.sh` |
| + `cap=10` + B operator pause | `XrplFund` | `fund.sh` |
| + clawB / burn / cashSelf | `XrplTreasury` | `treasury.sh` |
| + pause / freeze 合成 11 export | `XrplToken` | `token.sh` |
| mintToB / cashToB + `Card.persistCaller` | `XrplShare` | `share.sh` |
| grant `allw` / B `takeB` | `XrplTake` | `take.sh` |
| 合约卡 `esc` lockIn / releaseToB / refund | `XrplHoldEsc` | `holdesc.sh` |
| `due = ledgerSqn+2` 再 refund | `XrplVest` | `vest.sh` |
| B `claimB` after due | `XrplClaim` | `claim.sh` |
| B `cashB` after due + 192 drops | `XrplPayout` | `payout.sh` |
| A `cancel` before due / B `claimB` after | `XrplDual` | `dual.sh` |
| caller 卡 / dest 卡 / `supp` `lock` `allw` | Mint / Lock / Pay / Card | 公开脚本仍有效 |

本地 `sfContractAccount` = ACCOUNT/25 = **524313**。公开是 **524320**。不要写回 524315。

## 本地下一刀（公网先放，这里继续）

依赖只能：本地探针或已绿 host → Runtime 叶（wasm v0 ext arity 0/1/3）→ SDK → Example。

| 下一刀 | 物理 | 不做 |
|---|---|---|
| 可变 drops Payment（arity 1） | STAmount `0x40…` \| drops，仍付给 caller | 公开 `Sdk.Payments` |
| 编译期目的地 Payment | dest 走 `accountLit` / 三叶，金额先固定 | 任意账户参数（本地不能签 Parameters） |
| 程序卡 + XRP 组合 | `storeSelf` 记账，再 `emitToCaller` 付 drops | 把它叫成 AMM / Uniswap |
| 更多编译期 JSON key | 程序卡或 caller 卡 | 任意 KV `Sdk.Map` |
| IOU / TrustSet / AMMDeposit | 要另编 STAmount / 对象 id | 现在不要 |

本地不能做、也先放：Function.ParameterType（2.6.1 `sign` 拒）、公开 -196/-22、主网 `ContractCreate`。

## 脚本约定

- 本地脚本（`vault.sh` / `emit.sh` / `blocked.sh`）默认 `http://127.0.0.1:15005`。`nid=21337` → skip，不当绿。
- 公开脚本继续打 `https://alphanet.xrpl.org`。不要拿本地 tesSUCCESS 改公开验收句。
- 缺 docker → skip。

## 验收句

- 新本地叶必须有 `runtime-tests/xrpl/*.sh` tesSUCCESS，且脚本在 21337 上 skip。
- 文档写清「本地绿 / 公开仍挡」，不要只写「已绿」。
- `Sdk.Payments` / `Sdk.Map` / `Sdk.Amm` 在公开 pokeEmit / pokeSelf tesSUCCESS 之前不加。
