# ProofForge

Lean 4 多目标合约编译器。普通 `def` 写合约，普通 `theorem` 证合约。不是一门新合约语言。

当前：Solana（sBPF）+ EVM（Yul）两个剖面。`@[pf_entry]` 标记入口。CLI 是 `pf`。

和 [proof_forge](https://github.com/DaviRain-Su/proof_forge) 的关系：那边是 `program … where` DSL。这边复用 Lean 语法本身，抽出能 fail-closed 降到链上的子集。disc / layout 域名仍是 `proof-forge-solana-v1:`，链上字节不因改名而变。

```
普通 Lean def / theorem     ← 借 Lean
        │
        ▼
Profile 子集检查
        │
        ▼
Extract Expr → typed Core + target-neutral Ops
        │
   ┌────┴────┐
   ▼         ▼
SVM IR     EVM IR
+ IDL      + ABI
   │         │
   ▼         ▼
sBPF/.so   Yul/.bin
```

## 构建

```bash
lake build
lake exe pf -- build --target svm --out build/sbpf Counter
lake exe pf -- build --target evm --out build/evm Counter
```

SVM 写出 `Name.so` / `Name.s` / `Name.idl.json`（Solana IDL spec 0.1.0）。
EVM 写出 `Name.bin` / `Name.yul` / `Name.abi.json`。

Mollusk（环境变量已改成 `PF_*_SO`）：

```bash
(cd runtime-tests/solana && \
  PF_COUNTER_SO=../../build/sbpf/Counter.so \
  cargo test --locked --test counter)
```

Phoenix 与 Phoenix-v1 profile verifier 的本地 Loader-v3 交易部署使用 Surfpool，不使用
`solana-test-validator`：

```bash
runtime-tests/surfpool/smoke.sh
runtime-tests/surfpool/smoke.sh PhoenixV1Profile
```

Toolchain：`leanprover/lean4:v4.31.0`、`sbpf 0.2.2`、Surfpool `1.5.0`。

`PhoenixV1Profile` 当前可在 128-seat trader tree 与双 512-node order books 中执行
fixed-capacity Sokoban insertion/removal，并支持 trader get-or-register deposit。所有
持久结构都直接驻留在账户 bytes 中，只保存 one-based slot index（`0` 为 sentinel），
不使用 heap `Map`、detached node、copied tree 或账户外 pointer。底层 account-storage
backend 另提供共用的 bounded Key4/FIFO lookup；Runtime source 可在 complete validator 后
组合 lookup 与 one-based field read/write/remove，而不用增加顶层 Ops/IR/主 Emit 特判。
最小 profile 已用这套组合实现 bid/ask `ReduceOrderWithFreeFunds` 的 partial/full、trader
collateral unlock 与 checked preflight。target-owned `EntryAdapter` 已统一 packed wire decode、
raw/generated dispatch 与账户合同，`AccountStorage` 继续统一 account-resident
map/queue/allocator/tree；官方 Phoenix tag 4/5 wire、账户合同、93/128-byte authenticated
audit，以及 tag 4 classic Token vault withdrawal 已由两层组合完成。PDA mint seed 直接引用
经过认证的 MarketHeader 固定 byte slice，不创建 heap buffer。storage-owned FIFO cursor 只
保留 `(price, sequence)` scalar key，每次从账户 root 做有界 strict upper-bound，因此删除后
不保存 node address，也不收集 heap `Vec`。下一步补 reusable bounded audit batching，再组合
无 payload 的 tag 6/7 CancelAll pair，不增加 Phoenix-specific 顶层 Ops/IR/主 Emit case。

## 入口

```lean
import ProofForge

namespace Examples.Counter

@[pf_entry]
def init (_seed : UInt64) : State := { value := 0 }

@[pf_entry]
def increment (s : State) (delta : UInt64) : Except Error (State × UInt64) :=
  ...
```

`#pf_build Examples.Counter` 在 Lean 里抽出；`pf build --target svm` 走同一条 IR。

## 文档

从 [docs/INDEX.md](docs/INDEX.md) 进。
