---
id: e-own-001
scope: evm
status: done
depends-on: [e-asset-001]
---

# e-own-001 Ownable + 通用 event + allowance

## objective

E-OWN 整包，见 [05-evm-coverage-slices.md](../../research/05-evm-coverage-slices.md) 第四节之后。

- Ownable：`owner0/1/2` 三槽；`require callerW* = owner*`；非 owner → `unauthorized`
- 通用 LOG：`Op.evmLog name amt`；`evmLogTipped` / `evmLogIncremented` 抽成同构；topic = `keccak("Name(uint64)")`
- pair-key hashed Map：`keccak256(o0||o1||o2||s0||s1||s2||base)` → occ + payload
- `approve` / `allowance` = pair set/get；`spend` = 封闭额度扣减（不足 revert，状态保持）
- SVM 拒全部新叶/效应
- `Examples.Evm.Ownable` + Anvil

## 不做

嵌套 `Addr20` structure 展开；event ABI JSON；任意 LOG 签名；真正的 ERC-20 `transferFrom` 改余额；Window；SVM CPI。
