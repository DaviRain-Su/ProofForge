---
id: prof-001
scope: profile
status: done
depends-on: [skel-001]
---

# prof-001 子集剖面

## objective

对一组声明名给出 accept/reject。拒绝 IO / sorry / extern 的夹具必须失败。

## context

docs/03-technical-spec.md § Profile

## path

ProofForge/Profile.lean, Tests/ProfileSpec.lean

## verification

正向 Counter 三函数 accept；负向夹具 reject。
