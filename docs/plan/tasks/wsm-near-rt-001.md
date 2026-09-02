---
id: wsm-near-rt-001
scope: wasm
status: done
depends-on: [wsm-004]
---

# wsm-near-rt-001 NEAR Runtime 叶子 + 薄 SDK（对标 SVM/EVM）

> 原 NEAR 分支误用了 XRPL 的 `wsm-018` 号。rebase 到 `wasm-feature` 后改用本 id。

## objective

SVM / EVM 的能力分层是：

```text
Examples
  → target SDK（源名字，`@[pf_inline]` 消去）
    → Runtime 不可约 stub（抽出按名认）
      → Extract.IR.ValKind.<target>
        → target Ops / Emit / host import
```

NEAR 现在只有 Core UInt64 + `env` KV。本切片加 **Runtime 层**（host 读叶子）和
**薄 SDK**（`Context.*` 名字），不发明跨链通用 host，也不做 Promise / NEP-141。

## v0 Runtime 叶子（全部 fail closed 于 view 的付款/caller）

| 源名 | NEAR host | 视图 |
|---|---|---|
| `blockIndex` | `env.block_index` → u64 | view-safe |
| `blockTimestamp` | `env.block_timestamp` ns÷10^9 | view-safe |
| `predecessor` | `predecessor_account_id`，取 UTF-8 前 8 字节 LE | **init/entry only** |
| `attachedDeposit` | `attached_deposit` u128，hi64≠0 trap，返回 lo64 | **init/entry only** |
| `accountBalance` | `account_balance` 同 u128 截断 | view-safe |

不是 `clockSlot`，不是 `evmCaller`。SVM/EVM/XRPL 碰到这些叶子 fail closed。

## SDK

`ProofForge.Wasm.Near.Sdk.Context.{blockHeight,unixTimeSeconds,caller,attachedDeposit,balanceOfSelf}`
inline 到 Runtime stub。无存储 SDK、无 Promise。

## 不做什么

- 不扩 `Wasm.Host.Contract`（仍是 XRPL Data-blob 形状）
- 不同步 `call` / `transfer`；Promise 仍缺席
- 不把 Principal 做成 9 叶（那是后续切片）
- 不改 Counter digest

## path

`ProofForge/Wasm/Near/{Runtime,Ops,Sdk,IR,Emit}.lean`，
`ProofForge/Extract/{IR,Ops,Decode}.lean`，`ProofForge/Wasm/Family.lean`，
`ProofForge/Svm/IR.lean`，`ProofForge/Evm/IR.lean`，
`Examples/Near/NearCtx.lean`，`Tests/NearCtxSpec.lean`，
`runtime-tests/near/context.sh`

## verification

- `#pf_near_build Examples.Near.NearCtx` digest 钉死
- `#pf_near_reject Examples.Svm.Clock` / `Examples.Evm.EvmCtx` 仍拒 svm/evm
- `#pf_xrpl_reject Examples.Near.NearCtx`（near 叶）
- WAT 锚点：`block_index` / `block_timestamp` / `predecessor_account_id` /
  `attached_deposit` / `account_balance`；**没有** `host_lib`
- view 用 `predecessor` / `attachedDeposit` 在发射期拒绝
- `runtime-tests/near/context.sh`：sandbox 上 `height` 可读（缺工具 skip）
