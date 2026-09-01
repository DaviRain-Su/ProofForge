---
id: svm-rt-002
track: B-runtime
status: done
plan: ../svm-work-plan.md
priority: F2
depends-on: []
---

# svm-rt-002 Token-2022 第一个 typed extension 语义

## 目标

在已有 TLV envelope（未知 extension 原子拒绝）上，开放 **一个** 完整 typed extension 语义。

选择：`MintCloseAuthority`（ordinal 3，body 32）。未选 transfer-fee：fee 会改变转账金额，现有 base `Token2022` Mollusk 期望仍 fail-closed。

## 交付

1. 有界解析 + 状态视图 + 必要 CPI/状态更新语义 — **done**
   - `ProofForge.Svm.Cpi.TokenTlv`：`.token2022MintClose`、`mintCloseAccept?`、`evaluatePolicy`
   - Emit 直写 type 3 / len 32；未知 extension 仍原子拒绝
2. 两个非 Phoenix consumer — **done**
   - CPI：`Examples.Token2022MintClose.send` → `Runtime.token2022TransferCheckedMintClose`（digest `607b3786fb54eaee`）
   - Sdk host：`Sdk.Token2022.parseMintCloseAuthority` + `Tests.Token2022MintCloseSpec`
3. 未建模 extension 继续 fail closed — **done**
   - base `Token2022` 对 MintClose/fee/hook 仍拒绝；mint-close 程序对 fee/hook 仍拒绝
4. 不把 extension 名写进通用 Emit — **done**（仅 TokenTlv policy 特化）

## 验收证据

- Lean：`lake build Examples.Token2022MintClose Tests.Token2022MintCloseSpec`
- Mollusk：`token_2022` 9/9（含 mint-close fail-closed on base）；`token_2022_mint_close` 4/4
- Gates：`scripts/check_no_sorry.py` / `scripts/check_ownership.py` ok

## 非目标

一次做完所有 Token-2022 extension。
