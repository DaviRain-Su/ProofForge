import ProofForge
import Examples.Counter
import Examples.Capped
import Examples.Token

/-!
# 第一批 kernel 证明的连通性抽查

权威证明在合约文件内（`Examples/Counter.lean`、`Examples/Capped.lean`、
`Examples/Token.lean` 的 `Proofs` 节），由 `lake build Examples` 直接做 kernel 检查。
本文件只做两件事：

1. 抽查定理在具体值上可用（防止签名漂移后测试面失联）。
2. 记录公理审计基线。CI 侧由 `scripts/check_no_sorry.py` 保证这批证明
   不含未完成占位。

公理审计基线（`#print axioms`，2026-08-28）：

- `Examples.Counter.increment_ok` / `decrement_ok` / `scale_zero` / `scale_ok`
  / `divide_zero_error` / `modulo_zero_error` / `increment_ok_bound`
  / `decrement_ok_le`：`propext`、`Quot.sound`（标准公理，无未完成占位公理）
- `Examples.Capped.mint_supply_within_cap` / `mint_supply_effect`：`propext`
- `Examples.Token.transfer_preserves_supply` / `mint_supply_effect`
  / `burn_supply_effect` / `transferFrom_preserves_supply`
  / `approve_preserves_supply`：`propext`（部分含 `Quot.sound`）
-/

namespace Tests.ProofSpec

open Examples.Counter

-- Counter：具体值抽查
#guard
  match increment ({ value := 2 } : State) 3 with
  | .ok (t, ret) => t.value == 5 && ret == 5
  | .error _ => false

#guard
  match decrement ({ value := 2 } : State) 5 with
  | .error .overflow => true
  | .ok _ => false

-- 定理连通性：`increment_ok` 的返回值一致性分量可直接复用
example (s : State) (d : UInt64) (t : State) (r : UInt64)
    (h : increment s d = .ok (t, r)) : r = t.value :=
  (increment_ok s d h).2

end Tests.ProofSpec