# 05 测试规格

## S0（现在）

| ID | 类型 | 输入 | 期望 |
|---|---|---|---|
| T-S0-01 | happy | `increment {0} 1` | `.ok ({1}, 1)` |
| T-S0-02 | boundary | `increment {0} 0` | `.ok ({0}, 0)` |
| T-S0-03 | boundary | `increment {max} 0` | `.ok ({max}, max)` |
| T-S0-04 | error | `increment {max} 1` | `.error .overflow` |
| T-S0-05 | error | `increment {max-1} 2` | `.error .overflow` |
| T-S0-06 | happy | `increment {max-1} 1` | `.ok ({max}, max)` |
| T-S0-07 | happy | `init 7` / `get` | value 7 |
| T-S0-08 | theorem | overflow 情况 | `increment` 不是 `.ok` |
| T-S0-09 | ir | 手工 program | 含 init/increment/get |

用 `#guard` / `example` 钉在 Examples 或 Tests 里，随 `lake build` 检查。

## S1 / S2

| ID | 类型 | 输入 | 期望 |
|---|---|---|---|
| T-S1-01 | happy | `#solana_check` Counter 三根 | accept |
| T-S1-02 | error | `usesNat` | `Nat in root type` |
| T-S1-03 | error | `partial` / `sorry` / `IO` / `extern` / `implemented_by` | 对应 reject |
| T-S2-01 | happy | `#solana_extract` Counter | 抽出；increment sketch 含 `u64Max` |
| T-S2-02 | error | extract 夹带 `usesNat` | fail closed |
| T-S3-01 | happy | `#solana_extract` 后发射 | 含 entrypoint / overflow / disc / return data |
| T-S3-03 | error | 空 ops 的 `counterProgram` | 缺 `returnState` / `checkedAddU64` |
| T-S3-02 | error | 空 IR | `not counter shape` |
| T-S4-01 | happy | Mollusk init(5) | 账户 count=5 |
| T-S4-02 | happy | increment 5+3 | return 8，写回 8 |
| T-S4-03 | happy | get | return 8，不改账户 |
| T-S4-04 | error | increment max+1 | `0x1001`，状态保持 |
| T-S5-01 | happy | extract increment | ops 含 `checkedAddU64` |
| T-S5-02 | error | `wrappingAdd` | `increment not ite` |
| T-S5-03 | happy | 抽出 Counter | increment 先 load 账户再 load ix |
| T-S5-04 | happy | 对调 checkedAdd 左右 | 先 load ix 再 load 账户 |
| T-S5-05 | happy | extract decrement | ops 含 `checkedSubU64` |
| T-S5-06 | error | wrappingSub | mutating 缺 checked arith |
| T-F-01 | happy | Pair fields left/right | right 偏移 16；data_len 24 |
| T-F-02 | happy | extract Pair.creditLeft | ops 含 `field left` |
| T-F-03 | happy | 无 `with` 抽 Pair | fields = left, right |
| T-F-04 | error | structure 含 `Bool` 字段 | `extract/unsupported: field … is not UInt64` |
| T-F-05 | happy | Pair Mollusk init(7) | left=7，right=0，data_len 24 |
| T-F-06 | happy | creditLeft 5+3，right=99 | left=8，right 保持 99 |
| T-F-07 | happy | getLeft | return left，不改账户 |
| T-F-08 | error | creditLeft max+1 | `0x1001`，两字段保持 |
| T-L1-01 | happy | `#solana_build Examples.Counter` | 四方法；decrement 有独立 disc |
| T-L1-02 | error | 无 entry 的名字空间 | `extract/unsupported: no solana_entry` |
| T-L1-03 | happy | Pair Mollusk | disc 为 creditLeft / getLeft |
| T-L1-04 | happy | decrement 8-3 | return 5，写回 5 |
| T-L1-05 | error | decrement 2-3 | `0x1001`，状态保持 |
| T-L1-06 | happy | scale 5×3 | 15 |
| T-L1-07 | happy | scale 5×0 | 0 |
| T-L1-08 | error | scale max×2 | `0x1001` 保持 |
| T-L1-09 | happy | divide 8/3 | 2 |
| T-L1-10 | error | divide n/0 | `0x1001` 保持 |
| T-L1-11 | happy | modulo 8%3 | 2 |
| T-L1-12 | happy | nonzero 0 / 7 | return 1 / 0 |
| T-L1-13 | happy | 同一 Program 两次 digest | 相等 |
| T-L1-14 | happy | 改一个 op | digest 变 |
| T-L1-15 | happy | 发射文本 | 含 `digest=` |
| T-L2-01 | happy | Flag slots | flag 偏移 8 宽 1；count 偏移 9 宽 8 |
| T-L2-02 | happy | Maybe slots | slot_tag 8、slot_p0 16 |
| T-L2-03 | error | 嵌套 Option / Bool | `extract/unsupported` |
| T-L2-04 | happy | Flag Mollusk init | flag=0，count=7 |
| T-L2-05 | happy | Maybe none | 两叶清零 |
| T-L2-06 | happy | Maybe some 77 | tag=1，payload=77 |
| T-L2-07 | happy | SHA-256 `""` / `abc` | FIPS 向量 |
| T-L2-08 | happy | 未挂过的 `neverSeen(u64,u64)` | 算出 disc，不必改表 |
| T-L2-09 | happy | Window slots | cells_0=8、cells_1=16；data_len 24 |
| T-L2-10 | error | 不定长 Array 字段 | `use Vector` |
| T-L2-11 | happy | Window Mollusk init(7) | head=7，tail=0 |
| T-L2-12 | happy | setTail 9 | head 保持 7，tail=9 |
| T-L2-13 | happy | Phase slots | mode 偏移 8 |
| T-L2-14 | error | 带 payload inductive | `enum has payload` |
| T-L2-15 | happy | Phase Mollusk init | mode=0 |
| T-L2-16 | happy | setLive / isLive | tag=1，view 返回 1 |
| T-L3-01 | happy | Pair.initBoth 3 9 | left=3，right=9 |
| T-L3-02 | happy | getRight | return right，不改账户 |
| T-L3-03 | happy | Maybe.getValue none | return 0 |
| T-L3-04 | happy | Maybe.getValue some 77 | return 77 |
| T-L3-05 | happy | Choice slots | pick_tag 8、pick_p0 16 |
| T-L3-06 | happy | getHeld empty / hold 77 | 0 / 77 |
