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
