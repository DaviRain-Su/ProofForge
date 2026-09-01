---
id: wsm-near-u128-001
scope: wasm
status: done
depends-on: [wsm-020]
---

# wsm-near-u128-001 NEAR lossless u128 token context

> 原 NEAR 分支误用了 XRPL 的 `wsm-021` 号。rebase 到 `wasm-feature` 后改用本 id。

## Objective

Bind NEAR's little-endian u128 `attached_deposit` and `account_balance` host values to the shared,
allocation-free `Core.Value.UInt128`. This is the first independently runnable NEAR-F0-BYTES
slice and the amount foundation required by later Promise function calls and native transfers.

## Delivered

- `Runtime.NearToken` aliases the shared two-word `UInt128`; it introduces no target heap value.
- `Context.attachedDeposit` and `Context.balanceOfSelf` expose complete low/high words.
- Explicit `attachedDepositLo` / `balanceOfSelfLo` APIs preserve the old UInt64 contract.
- Full-value low words use dedicated leaves. A valid amount above UInt64 therefore does not trap
  merely because source code observes `NearToken.w0`; only an explicit legacy leaf checks high=0.
- The emitter invokes each host function once per method, loads both words from that observation,
  and emits imports/locals even for a high-word-only method.
- Every full attached-deposit leaf remains forbidden in views. Both balance words are view-safe.
- Exact Runtime constructor/projection matching prevents NEAR values from becoming EVM wide-word
  operations or matching unrelated user helpers by suffix.

## Not included

- No arithmetic on `NearToken` beyond ordinary scalar word access.
- No gas type, Promise, transfer, callback, bytes/string ABI, arbitrary storage, or collection.
- No change to the raw-u64 entry/output ABI; examples return one selected word at a time.

## Verification

- Focused extraction tests pin full w0/w1 leaves, high-word-only host imports, view rejection, and
  the distinction between full and legacy overflow behavior.
- WAT assembly and the NEAR engineering gate cover Counter and NearCtx; Counter stays unchanged.
- near-sandbox 2.13.0 compares both `account_balance` words to RPC state, submits
  `2^64 + 7` yoctoNEAR, observes low=7 and high=1 through the full API, and observes the explicit
  legacy API trap on the same amount.
