---
id: svm-app-012
track: D-app
status: doing
plan: ../svm-work-plan.md
depends-on: [svm-app-011]
---

# svm-app-012 Phoenix WithdrawFunds tag 12 (exact-lots slice)

## 目标

在 CancelMultiple 容量轴齐备之后，推进 full Phoenix quality matrix：新增官方
`WithdrawFunds` tag 12。本片使用 **exact-lots** 线：`0c || quote:u64 || base:u64`
（max wire 17）；零 lots 跳过该侧；零/零为 header-only sequence bump。复用既有
九账户 classic Token withdraw 上下文。

## 交付

1. `Examples/PhoenixV1Profile.lean`：`withdrawFunds` raw tag 12
2. Spec：adapter `dataLen==17`；ASM `jne r2, 17` + `jeq r1, 12`
3. Mollusk：quote+base withdraw；zero/zero header-only；insufficient free reject
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean extract/emit ×3 → digest TBD
- Mollusk: `official_raw_withdraw_funds_*`

## 仍未覆盖

官方 `Option<u64>` withdraw-all；DepositFunds tag 13；tags 0–2 / 14–17 / admin 100+；
tag-3 完整 TIF/self-trade/eviction。
