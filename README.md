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

## 网站

产品站源码在 [`website/`](website/)，不另开仓库。GitHub Pages：
[https://davirain-su.github.io/ProofForge/](https://davirain-su.github.io/ProofForge/)。

```bash
cd website && npm install && npm run dev
```

首次合并后在 **Settings → Pages → Source** 选 GitHub Actions。

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
map/queue/allocator/tree；后者现在从稳定的 `Svm.Component.Query/Call` bridge 降低：generic
Ops、IR、CFG 与主 Emit 只 dispatch 一次 `component`，组件自己拥有 operand traversal、effects、
geometry、canonical spelling、scratch boundary 与 emitter dispatch。以后增加 bounded queue、
recorder 或 transient allocator 只扩 component-owned 模块，不再横向修改整条通用编译链。
官方 Phoenix tag 4–7 wire/account contract 已由两层组合完成：tag 6/7 的 bounded
`FifoCancel` component 在完整 trader/bid/ask validator 后按 bids→asks 和各侧 FIFO 顺序
原位取消，owner 过滤、collateral unlock、global event index 与 released-lot accumulator 都不再
向通用 Ops/IR/主 Emit 泄漏；tag 6 再按 quote→base 顺序 claim/withdraw 本次释放量，tag 7
完全不进入 Token CPI。
authenticated audit 已迁入 `BatchRecorder.begin/append/finish`：payload 使用官方 SDK
`0x300000000` / 固定 32 KiB downward bump cursor，32 条 35-byte Reduce records 后在第 33 条前
自动 flush，empty finish 仍发 93-byte header-only batch；heap 地址不进入 source 或账户。
PDA mint seed 直接引用
经过认证的 MarketHeader 固定 byte slice，不创建 heap buffer。storage-owned FIFO cursor 只
保留 `(price, sequence)` scalar key，每次从账户 root 做有界 strict upper-bound，因此删除后
不保存 node address，也不收集 heap `Vec`。下一步在同一 component boundary 上增加 tags 8/9
CancelUpTo 的静态过滤条件，而不是重新扩张底层指令集。

EVM 采用平行但不复制 SVM 账户几何的 SDK：合同打开 `ProofForge.Evm.Sdk`，通过
`Storage.Layout` 的编译期 cursor 声明 typed hashed maps，并使用 `Address`、`UInt256`、
`Context`、`Immutable`、`Event`、`Revert` 和封闭 call facade。descriptor 在抽取期消去，
不进入 storage；`Examples.Token` / `Examples.Capped` 已迁移到该表面且 target IR digest 不变。

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

## 证明

第一批 kernel-checked 合约性质已落在合约文件内的 `Proofs` 节
（`Examples/Counter.lean`、`Examples/Capped.lean`、`Examples/Token.lean`）：
成功路径精确后置条件、单调性、Token supply 效应与 Capped cap 不变量，
全部只依赖标准公理 `propext` / `Quot.sound`。CI 由
`scripts/check_no_sorry.py` 保证证明批次不含占位符。

## 文档

从 [docs/INDEX.md](docs/INDEX.md) 进。
