# ProofForge.Wasm

## Purpose

第三个 target profile（调研判定见
[research/06-wasm-feasibility.md](../research/06-wasm-feasibility.md) 路线 B）：经
`Core.Target.Registration` 注册的 WASM 切片，v0 绑定 **XRPL Bedrock（XLS-0101）**，
artifact 是 scaffold-xrp 方言 Rust 源（`xrpl_wasm_std` 的
`get_current_contract_call` / `get_data` / `set_data`、`#[unsafe(no_mangle)]
pub extern "C"` 导出）。不改通用 `Core.Ops` / `Core.CFG` / frontend，只加注册。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Wasm.Ops` | WASM 方言 `ValKind` / `OpExt`（v0 无宿主叶子；`reserved` 仅保 inhabitance，`wellFormed` 拒绝） | XRPL host capability 键 |
| `Wasm.IR` | `extractRegistration`（拒绝 svm/evm 叶）、v0 子集 fail-closed 检查、`Program` / `Method`、canonical digest（域 `wasm-xrpl|`） | Yul、sBPF、loop / vector / map |
| `Wasm.Emit` | `Program` → Bedrock 方言 Rust 源；checked `+ - * / %` → `checked_*` + 钉死错误码（1 overflow/underflow、2 divide-by-zero）；guard 算术 `wrapping_*`；view `-> u64`，mutating entry `-> i32` status | 真 XRPL host 语义、metering、部署 |
| `Wasm.Assemble` | zero-tool 写 `{name}.rs`（digest 行钉 canonical 身份） | rustc / cargo / bedrock / AlphaNet |
| `Wasm.Registry` | 可构建模块 + canonical digest | 部署声明 |
| `Wasm.Commands` | `#pf_wasm_build` / `#pf_wasm_dump` | 新 DSL |

## v0 子集（全部 fail closed）

- 状态：全部 UInt64 槽（width 8），经合约 pseudo-account 的
  `read_u64` / `write_u64` 读写；
- 参数：scalar UInt64；view 结果：恰好一个 UInt64，`-> u64` FFI-safe 导出；
  mutating entry 只返回 `i32` 状态码（源声明的 public 返回值被省略，读 view）；
- ops：checked 五则、`ite`、`okState` / `returnState` / `returnU64`、
  `errorOverflow`、`storeField`；loop / local / vector / map / `errorNamed` /
  位运算 / 移位 / 未检查 `/ %` 全部拒绝；
- Runtime 叶子不跨 target：`clockSlot` / `signerKey0` / `systemTransfer` /
  EVM `caller` 等在抽取期即 `wasm rejects svm/evm value`（与 EVM 切片同规矩）；
- 无宿主 capability：ledger time / caller account / hashing 不在方言里，直到
  其 XRPL wasm 级 import ABI 被钉死（旧仓 proof_forge 的 ADR-0052 已冻 Rust 侧
  符号，但 wasm 级 ABI 未钉）。

## 诚实边界（来自 proof_forge XRPL 研究的事实）

- artifact 是 **source-only、zero-tool**：`deployable=false`；不声称 bedrock /
  rippled / `ContractCreate` / `ContractCall` / AlphaNet / 主网；
- 真实编译面是 ambient `cargo build --target wasm32-unknown-unknown --release`
  + `xrpl-wasm-std`（git rev `ffbe88da26df27e59a72b6202883f42f696933cc`，来自
  scaffold-xrp）；rustc/cargo 不是 Tool Lock 成员；
- XRPL 主网没有 `ContractCreate`；Hooks / EVM sidechain 不属于本 target；
- 本仓工程门是 `runtime-tests/wasm/check.sh`：生成源对**本地 stub crate**
  cargo check。stub 不是真 crate，该门只验证生成源的类型正确性，不是
  「artifact 已被证明」或「可在 XRPL 部署」的声称。

## 摘要

```text
frontend Core.IR.Program（已过 Profile）
        │  Wasm.IR.extractRegistration（拒绝 svm/evm 叶）
        ▼
Wasm.IR.Program（v0 子集 fail-closed；digest 域 wasm-xrpl|）
        ▼
Bedrock 方言 Rust 源 {name}.rs（zero-tool）
        ▼  runtime-tests/wasm/check.sh（stub crate cargo check，工程门）
```

CLI：`pf build --target wasm`（别名 `xrpl`）。注册程序见 `Wasm.Registry`；
当前为 `Counter`（四场景：initialize / increment ok / increment overflow / get，
加 decrement / divide / modulo / scale / nonzero 同子集）。

## 与调研文档 WAT 设想的关系

`research/06-wasm-feasibility.md` 的链上腿最初设想「通用 wasmtime + `pf` import
合同 → WAT → wat2wasm，选链推迟」。本切片按 owner 决定把第一条链定为
XRPL：XRPL Bedrock 的真实编译面是 Rust + ambient cargo + `xrpl_wasm_std`，且其
wasm 级 host import ABI 从未被钉死（旧仓只钉了 Rust crate rev）。因此 v0 的
artifact 改为该方言的 Rust 源——与 EVM 发 Yul 给 locked solc 同构（源语言交给
链生态自己的编译面），而不是发明一套未经验证的 WAT import 表。通用
`pf` import / wasmtime fuel / wat2wasm 路线仍是后续选项，但需先钉真实宿主 ABI。