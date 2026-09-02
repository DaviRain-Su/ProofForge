---
id: svm-app-002
track: D-app
status: done
plan: ../svm-work-plan.md
depends-on: [svm-app-001]
---

# svm-app-002 Phoenix matching / fee / remainder 宣称面补齐

## 目标

把文档已宣称、但代码仍缺的 matching/fee/remainder 策略补到与能力叙述一致。

## 交付

策略测试 + 文档同步；仍只在 Examples — **done**

## Evidence

- Code already present: `placePostOnlyFreeFunds512At` /
  `placeLimitOneMatchFreeFunds512At` / `placeLimitTwoMatchesFreeFunds512At` /
  `takerFeeQuoteLots512At` / `postingQuoteLotsOrZero512At` / `twoMatchPostingValid512At`
- Pure policy pin: `takerFeeQuoteLotsOf` + Spec `#guard`s (`Tests/PhoenixV1ProfileSpec.lean`)
- Mollusk: `official_raw_limit_*` fee / remainder / unsupported-shape suite (11 passed)
- Docs: `docs/modules/phoenix.md` claims tag-3 bounded matching/fee/remainder surface

## 仍未宣称

完整 TIF/self-trade/eviction/crossing-remainder 矩阵；公网 Phoenix-v1 全指令集。
