---
id: e-comp-008
scope: evm
status: done
depends-on: [e-comp-007]
---

# e-comp-008 Extract 读路径按 Runtime 命名空间收集

## objective

EVM 语句级读查询不再走 Extract 里按 recipe 名枚举的 finder 表。`decodeEvmEffect`
在写路径空时，展开 `@[pf_inline]` Source helper，只认 `queryOfRuntimeApp` 对
`ProofForge.Evm.Runtime` stub 的解码。新封闭 query 注册进 `queryOfRuntimeApp` 即可，
不必再改 walker / `decodeEvmEffect`。Ops / IR / 主 Emit 不变，digest 不变。

- hashed-map get / closed-CALL balance+allowance 走 query decoder
- `callValue256` / `selfBalance256` / `domainSep256` 作为已有 ValKind 语句返回，
  不新增 Source / Component
- `asVal` 里的投影读（UInt256 limb / Addr20 / wide arith）仍走现有 case

## 不做

把 `asVal` 再拆进各 Source 模块；环境 opcode Source；pause / mint。
