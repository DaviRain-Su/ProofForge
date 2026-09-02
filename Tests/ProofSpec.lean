import ProofForge
import Examples.Counter
import Examples.Evm.Capped
import Examples.Evm.Token
import Examples.Svm.Tree
import ProofForge.Evm.Sdk.Pausable
import ProofForge.Evm.Sdk.Fungible
import ProofForge.Evm.Sdk.Reentrancy
import ProofForge.Evm.Sdk.Payments
import ProofForge.Svm.Sdk.AssociatedToken
import ProofForge.Svm.Sdk.Pda
import ProofForge.Svm.Sdk.Memo
import ProofForge.Svm.Sdk.Program
import ProofForge.Svm.Sdk.Pubkey

/-!
# 第一批 kernel 证明的连通性抽查

权威证明在合约文件内（`Examples/Counter.lean`、`Examples/Evm/Capped.lean`、
`Examples/Evm/Token.lean` 的 `Proofs` 节），由 `lake build Examples` 直接做 kernel 检查。
本文件只做两件事：

1. 抽查定理在具体值上可用（防止签名漂移后测试面失联）。
2. 记录公理审计基线。CI 侧由 `scripts/check_no_sorry.py` 保证这批证明
   不含未完成占位。

公理审计基线（`#print axioms`，2026-08-28）：

- `Examples.Counter.increment_ok` / `decrement_ok` / `scale_zero` / `scale_ok`
  / `divide_zero_error` / `modulo_zero_error` / `increment_ok_bound`
  / `decrement_ok_le`：`propext`、`Quot.sound`（标准公理，无未完成占位公理）
- `Examples.Evm.Capped.mint_supply_within_cap` / `mint_supply_effect`：`propext`
- `Examples.Evm.Token.transfer_preserves_supply` / `mint_supply_effect`
  / `burn_supply_effect` / `transferFrom_preserves_supply`
  / `approve_preserves_supply`：`propext`（部分含 `Quot.sound`）
- `Examples.Svm.Tree.init_state` / `setHead_roundtrip` / `setAt_roundtrip`
  / `allocNode_size` / `rotateLeft_size` / `rotateRight_size`
  / `rotateLeft_root` / `rotateRight_root`：`propext`（部分含 `Quot.sound`）
- `Examples.Svm.Tree.removeNode_size` / `init_wf` / `allocNode_wf`：
  `propext`（部分含 `Quot.sound`）
- `Evm.Sdk.Payments` 委托透明性（accept/send/transfer/transferFrom/...）：零公理（rfl 级）
- `Evm.Sdk.Reentrancy` fail-closed 包（unknown_neither / 互斥）：`propext`
- `Evm.Sdk.Fungible` guard 链：`propext`（两个零公理）
- `Svm.Sdk.AssociatedToken` 角色索引界（Create 7/Recover 8）：`propext`
- `Svm.Sdk.Pda/Memo/System` wellFormed 界：`propext`
- `Svm.Sdk.Program/Pubkey` 构造/等式透明性：`propext`
- `Svm.Sdk.Storage.OrderedMap` 委托/slotValue/Allocator cursor：6 零公理
- `Evm.Sdk.Reentrancy` fail-closed 包（unknown_neither / 互斥）：`propext`
- `Evm.Sdk.Fungible` guard 链（canTransfer→canDebit/canCredit、canSpend→canDecrease）：
  两个零公理
- `Evm.Sdk.Pausable` fail-closed 包（unknown_neither / 互斥 / 转换常值 /
  unpause 恢复 / roundtrip）：`propext`；`isRunning_unpause` 零公理
- `Svm.Sdk.StorageModel`：字段代数 / wf 桥 / `mBvPush_twoWrites`：
  `propext`（部分含 `Quot.sound`）
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

-- Tree：旋转不改变节点数、分配器成功恰好占一槽
#guard
  match Examples.Svm.Tree.allocNode (Examples.Svm.Tree.init 0) 7 7 with
  | .ok (t, a) => Examples.Svm.Tree.getSize t == 1 && a == 1
  | .error _ => false

-- Tree wf：init 良构（wf 谓词第一批切片；kernel 检查，不求值）
example : Examples.Svm.Tree.wf (Examples.Svm.Tree.init 0) := Examples.Svm.Tree.init_wf 0

-- Pausable fail-closed：unknown flag 门关且不误报 paused
#guard
  match (2 : UInt8) with
  | f => !ProofForge.Evm.Sdk.Pausable.isRunning f
      && !ProofForge.Evm.Sdk.Pausable.isPaused f

-- 定理连通性：`increment_ok` 的返回值一致性分量可直接复用
example (s : State) (d : UInt64) (t : State) (r : UInt64)
    (h : increment s d = .ok (t, r)) : r = t.value :=
  (increment_ok s d h).2

end Tests.ProofSpec