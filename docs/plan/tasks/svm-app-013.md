---
id: svm-app-013
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-012]
---

# svm-app-013 Phoenix DepositFunds tag 13 (exact-lots slice)

## 目标

在 WithdrawFunds exact-lots 之后，推进 full Phoenix quality matrix：新增官方
`DepositFunds` tag 13。本片使用 **exact-lots** 线：`0d || quote:u64 || base:u64`
（max wire 17）；零 lots 跳过该侧；零/零为 header-only sequence bump。复用既有
九账户 classic Token 上下文；trader signer 向 vault 转入后 credit free lots。

## 交付

1. `Examples/PhoenixV1Profile.lean`：`depositFunds` raw tag 13；`tokenTransferIx` /
   `Token.transferWith`（ordinary signer，非 PDA）
2. Spec：adapter `dataLen==17`；CPI metas quote `.at 7 4 6 2` / base `.at 7 3 5 2`
   （authority = external trader index 2）；ASM `jne r2, 17` + `jeq r1, 13`
3. Mollusk：quote+base deposit credits free；zero/zero header-only；token underflow reject
4. digest 纪律；无 Phoenix 名进入 `ProofForge/Svm`

## Evidence

- Lean extract/emit → digest `5e9097d41f7cefbf`
- CPI authority is trader (external 2 / physical 3), not trader_base — privilege escalation closed
- Mollusk: `official_raw_deposit_funds_credits_quote_and_base_free`、
  `official_raw_deposit_funds_zero_zero_is_header_only`、
  `official_raw_deposit_funds_rejects_token_underflow_atomically`

## 仍未覆盖

官方 `Option<u64>` deposit-all / withdraw-all；tags 0–2 / 14–17 / admin 100+；
tag-3 完整 TIF/self-trade/eviction。
