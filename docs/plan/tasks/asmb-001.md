---
id: asmb-001
scope: assemble
status: pending
depends-on: [lowr-001]
---

# asmb-001 sbpf + Mollusk

## objective

locked `sbpf` 产出 `.so`；Mollusk 复现 StateCell 四行为。

## context

docs/01-prd.md 成功标准；PF runtime-tests/solana/tests/state_cell_shaped_product.rs

## path

SolanaLean/Assemble.lean；runtime-tests/

## verification

init / increment / get / overflow 保持。
