---
id: e-comp-007
scope: evm
status: done
depends-on: [e-comp-006]
---

# e-comp-007 Extract 写路径按 Runtime 命名空间收集

## objective

EVM 写副作用不再走 Extract 里按 recipe 名枚举的 fallback 表。`collectEvmEffectOps`
展开 `@[pf_inline]` Source helper 后，只认 `opOfRuntimeApp` 对
`ProofForge.Evm.Runtime` stub 的解码。新封闭 recipe 注册进 `opOfRuntimeApp` 即可，
不必再改 walker / `decodeEvmEffect`。读查询（map get / token balance / env 256）仍
走现有 finder。Ops / IR / 主 Emit 不变，digest 不变。

## 不做

把 `opOfRuntimeApp` 再拆进各 Source 模块；环境 opcode Source；pause / mint。
