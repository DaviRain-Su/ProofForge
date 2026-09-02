---
id: erg-evm-effect-001
scope: ergonomics
status: todo
depends-on: [erg-do-001]
plan: ../multi-target-strategy.md
updated: 2026-09-02
---

# erg-evm-effect-001 — EVM Effect / CallResult 链式 surface

## 目标

在 **不改 R5-012 CallResult 策略** 的前提下，让 Token 级 example 读起来像
**顺序 fail-closed 步骤**（`guard` / `andThen` / `Effect.thenTrue`），而不是嵌套
`if`/`match`。

## 现状

- `ProofForge/Evm/Sdk/Base.lean` 已有 `Effect.thenTrue`
- `Examples/Token.lean` 已部分使用，但 `transfer` / `approve` / `transferFrom` 仍偏嵌套分支
- 能力已在 R5；本包只改 **source surface** + digest pin

## 第一切片

1. 重写 `Examples/Token.lean` 的 `transfer` / `approve`（必要时 `transferFrom`）为顺序组合
2. bodies 不出现 `Runtime.evm*` stub 名
3. `pf build --target evm` + 原 Token Anvil 门仍绿；**新 IR digest 钉死**
4. 更新 `docs/plan/do-notation-guide.md`（去掉过时的 N13 PromiseHandle 备注）

## 非目标

- CallResult interpreter / R5-012 策略变更
- `erg-svm-account-001` cookbook
- `erg-state-001` 隐式 state（Extract lock）
- Import guard 全面禁止 `Runtime`（另包）

## 验收

§5.3「Token mint/transfer 像顺序语句」对 EVM Token 成立；digest 测试更新。
