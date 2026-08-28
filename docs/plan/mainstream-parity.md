# Mainstream Runtime / SDK parity baseline

> 基线：2026-08-28。本文定义“达到主流开发环境能力”的含义。SVM 对照当前官方拆分后的
> Solana on-chain Rust SDK 与 SPL interfaces；EVM 对照 Solidity 语言/runtime 与
> OpenZeppelin Contracts。它是能力和优先级基线，不要求复制 Rust `std`、Solidity 语法或
> 两条链的物理 storage。

## 1. Parity 不是一层 API

```diagram
┌─────────────────────────────────────────────────────────────┐
│ Shared bounded language                                    │
│ values · Vec/bytes · codecs · checked math · bounded loops │
└──────────────────────────┬──────────────────────────────────┘
                           ▼
┌─────────────────────────────────────────────────────────────┐
│ Target Runtime                                             │
│ SVM syscalls/account/CPI/sysvar   EVM opcodes/call/ABI     │
└──────────────────────────┬──────────────────────────────────┘
                           ▼
┌─────────────────────────────────────────────────────────────┐
│ Reusable target SDK policy                                 │
│ storage containers · access · safe calls · assets/lifecycle│
└──────────────────────────┬──────────────────────────────────┘
                           ▼
┌─────────────────────────────────────────────────────────────┐
│ Examples / applications                                    │
│ concrete account/slot layout · protocol and business rules │
└─────────────────────────────────────────────────────────────┘
```

- **Shared language** 要提供确定性、可预算、可提取的语言组件，不规定 Borsh、ABI、账户偏移或
  storage slot。
- **Runtime** 是目标 VM 的真实 Host Function/opcode 合同。只有这里确实缺少 VM effect 时才扩
  Ops/IR/Emit。
- **SDK** 用普通 Lean 组合 Runtime/Component，拥有可复用的数据结构和安全策略，不隐藏业务
  storage write，也不增加协议专用 opcode。
- “主流 parity”是这三层共同达到可写真实合约的水平，不是只数 syscall/opcode，也不是把
  OpenZeppelin 或 SPL 的每个扩展一次性搬完。

## 2. Vector、Map 和 allocation 的准确含义

同一个名字在不同生命周期下不是同一个物件：

| 生命周期 | 正确表示 | 当前状态 | 必须补齐 |
|---|---|---|---|
| source/ABI 边界 | compile-time capacity + runtime length + fixed scalar frame | shared `Core.Value.BoundedVec`; SVM Borsh 与 EVM ABI bounded input 已有 | operations、bytes/string specialization、tagged/bounded return |
| invocation-local | bounded scratch/heap region，OOM 显式失败，调用结束即失效 | SVM `Sdk.Transient` 有 buffer/fixed-vector/writer **plan** | 可提取的 bounded byte/vector operations；EVM bounded memory binding |
| SVM persistent | canonical account bytes + count/capacity/index，绝不存 pointer | `Sdk.Storage.BoundedVec`、Queue、ordered Map/RBMap、allocator 已有 u64/固定 schema | richer POD element/key/value shapes、set/bitset、versioned codecs |
| EVM persistent | static consecutive slots 或 typed hashed namespace | fixed `Vector` state、static declarations、typed maps 已有 | reusable bounded vector/set/queue/bitmap operations 与 documented gas bounds |

因此：

- SVM 可以在调用期使用受限 allocator，但 `Vec`/`Box`/`Rc`/raw pointer 的内存表示永远不能
  持久化到 account data。
- EVM mapping 没有长度和枚举；需要枚举时必须用 bounded tracked keys/static set，并把 O(n)
  gas 上限写进合同。
- 默认不开放 unbounded `Array`、hash table、递归容器或隐式增长。所有集合都有静态 capacity、
  canonical encoding、checked length/index 和明确的 full/OOM 结果。

## 3. Shared bounded language gap

| 能力 | 当前 | Parity gap | 优先级 |
|---|---|---|---|
| integers/fixed bytes | Bool、u8/16/32/64、allocation-free u128/u256/`FixedBytes n`；u256 EVM arithmetic 已覆盖主要 unsigned op | signed widths、safe narrowing/casts、saturating/full-precision helpers、统一 overflow vocabulary | F0/F1 |
| aggregate values | record/tuple/Option/bounded enum/fixed Vector；bounded input carrier | reusable bounded Vec operations、bytes/string、set/map/queue/bitset logical contracts；nested bounded shapes | F0 |
| codecs | target-neutral schema；SVM Borsh 与 EVM static/tagged/bounded input bindings | tagged/bounded returns、canonical bytes/string、version/discriminator、strict trailing policy 的统一 source contract | F0 |
| control/resources | checked arithmetic、bounded `for`、fixed scalar frame | per-method collection/codec/memory budget manifest；禁止隐式 allocation/clone/format | F1 |

Shared 层只定义 logical value 和 operation laws。同一 `BoundedVec` 可以在 SVM 绑定为 Borsh
`u32 length + active prefix`，在 EVM 绑定为 canonical ABI dynamic tail；不能为了“共享”而制造
第三套 wire layout。

## 4. SVM Runtime parity

官方基线以拆分后的 [`solana-account-info`](https://github.com/anza-xyz/solana-sdk/tree/master/account-info)、
[`solana-cpi`](https://github.com/anza-xyz/solana-sdk/tree/master/cpi)、
[`solana-sysvar`](https://github.com/anza-xyz/solana-sdk/tree/master/sysvar) 和
[`program-memory`](https://github.com/anza-xyz/solana-sdk/tree/master/program-memory) 为准；完整 syscall
类别见 [`define-syscall`](https://github.com/anza-xyz/solana-sdk/blob/master/define-syscall/src/definitions.rs)。

| 类别 | 当前 source surface | 主要缺口 | 优先级 |
|---|---|---|---|
| AccountInfo | fixed Account/Signer handle；key/owner/data words、lamports/length/flags；read-only bounded remaining-account view；program-owned checked data word writes | 一等 32-byte address；checked lamport mutation；account resize/zero-fill；duplicate-account alias policy；完整 initialization/close helpers | F0/F1 |
| memory | official-shaped 32 KiB downward bump model、bounded scratch plans | `memcpy/memmove/memcmp/memset` host contracts；source-visible bounded bytes/vector operations；显式 OOM propagation | F0/F1 |
| instruction/CPI/PDA | static bounded metas/data、multi-seed signed CPI、return-data staging、PDA find/check | bounded full return data + returned program-id check；more generic bounded instruction bytes；stack/sibling/instruction introspection only when required | F1 |
| sysvar/runtime query | Clock slot/epoch/unix、Rent、EpochSchedule | remaining Clock/Epoch fields、generic sliced sysvar、remaining compute/stack height、instructions sysvar；advanced sysvars on demand | F1/F2 |
| crypto | literal SHA-256/Keccak first word、PDA host calls | full 32-byte/multi-slice hashes；Blake3/SHA-512/secp recovery/Poseidon/curve/big-mod-exp；signature-program instruction validation | F1/F2 |
| log/error | authenticated bounded `sol_log_data` recorder、custom failure terminal | generic bounded log-data/numeric/key API；stable typed event convention；complete ProgramError/custom-code mapping | F1 |
| serialization | exact scalar/static/tagged/bounded Borsh input、raw entry、Token-2022 TLV envelope | bounded returns、Pack/POD/COption/versioned account codecs、strict reusable readers/writers | F0/F2 |

Rust 的 `Rc<RefCell<_>>` borrow API 是 Rust host representation，不应原样复制成 Lean SDK。
ProofForge 要保存的是相同的安全合同：写权限、owner、alias、长度和 CPI 前状态必须被验证，且
不能形成可持久化 reference/pointer。

## 5. SVM SDK parity

| 组件 | 当前 | 主要缺口 | 优先级 |
|---|---|---|---|
| System/PDA | static ASCII PDA；non-seeded transfer/create/assign/allocate/nonce；generic compile-time ASCII seeded allocate/create/assign/transfer with checked bincode length | rent-aware create/resize helpers、remaining System lifecycle policy | F1 |
| SPL Token | `Svm.Sdk.Token` 已统一 fixed classic surface，并以 CPI-relative role descriptors 提供 checked/unchecked ordinary/PDA-signed transfer；concrete account layout 留在应用 | state parsers、program-id policy、更多 honest generic authority/multisig variants | F1 |
| Token-2022 | base-layout transfer + bounded TLV envelope，未知 extension 原子拒绝 | typed extension lookup/account-size；transfer-fee/hook/memo/CPI-guard 等逐扩展完整语义 | F2 |
| ATA/Memo | SDK 已有 fixed ATA CreateIdempotent（Token program 由 caller account 显式提供）与 ≤512-byte compile-time ASCII Memo；`writeOk` 仅为兼容 delegate | ordinary Create/RecoverNested、derived address/program-id policy；runtime-selected/UTF-8 Memo bytes | F1/F2 |
| loader/lifecycle | Loader-v3 assembly/deploy qualification exists | typed loader state/instructions、upgrade authority/immutability lifecycle facade | F3 |
| persistent collections | POD Field、Vec、Queue、ordered Map/RBMap、allocator | generic bounded POD records、Set/BitSet、versioned initialization/close policy | F1/F2 |

SPL Token 对照官方 [`token/interface`](https://github.com/solana-program/token/tree/master/interface)，
ATA 必须显式携带 token program id，不能把 classic Token 的默认值误用于 Token-2022。

## 6. EVM Runtime and Solidity parity

EVM Runtime 以 Solidity 的 [types](https://docs.soliditylang.org/en/latest/types.html)、
[ABI](https://docs.soliditylang.org/en/latest/abi-spec.html) 和
[global/runtime functions](https://docs.soliditylang.org/en/latest/units-and-global-variables.html)
为基线；SDK policy 再对照 OpenZeppelin。

| 类别 | 当前 source surface | 主要缺口 | 优先级 |
|---|---|---|---|
| values/ABI | typed scalars、Address/u128/u256/bytesN、static aggregates、tagged input、one bounded dynamic-array input | signed ints、safe casts、bytes/string、nested dynamic、tagged/bounded return、dynamic constructor/fallback returndata | F0/F1 |
| data/storage | ordinary typed State flattening、static declarations、address/address-pair hashed maps | reusable bounded storage vector/set/queue/bitmap；explicit bounded memory/transient contracts；namespaced storage | F0/F2 |
| environment | caller/self/block number/timestamp/chain id/value/balance/immutables | gasleft、basefee/prevrandao/coinbase/gaslimit、blockhash、code/codehash and target-version gates | F1 |
| call/create | closed ERC-20/WETH/router/permit CALL/STATICCALL、typed ≤32-byte result policies、safe ETH send | bounded generic call data/result/revert bubbling；static/delegate semantics；CREATE/CREATE2；code-existence and reentrancy contracts | F1/F2 |
| crypto | host Keccak selector tooling、closed ecrecover precompile plan | source hash API、sha256/ripemd/precompiles、ECDSA anti-malleability、EIP-191/712、ERC-1271、Merkle | F1/F2 |
| log/error | typed bounded LOG0..4/custom-error plans behind closed events/errors | source-declared generic typed events/errors、dynamic indexed/data encoding、Panic/revert-data propagation | F1 |
| resources | checked u256 math and bounded ABI frame | gas/code/init-code/memory/stack manifest and compiler-version feature gates | F1/F3 |

不是所有 low-level EVM primitive 都应该直接变成默认安全 SDK。`delegatecall`、raw call、packed
encoding 和 arbitrary revert bytes 必须位于显式 unsafe/advanced boundary；普通 SDK 首先提供
typed bounded call 和验证后的 result contract。

## 7. EVM SDK and OpenZeppelin parity

| 组件 | 当前 | 主要缺口 | 优先级 |
|---|---|---|---|
| collections/math | typed maps、static declarations、capacity-2 role set、checked u256 operations | bounded enumerable Set/Map/Queue/Bitmap/Checkpoints、SafeCast/Math/String/Bytes utilities | F0/F2 |
| access/safety | owner/two-step ownership、bounded static roles、explicit fail-closed Pausable flag policy | typed Paused/Unpaused events, ReentrancyGuard, enumerable/admin roles, timelock/access manager | F1/F2 |
| calls/payments | `Evm.Sdk.Payments` bounded Ether/ERC20/WETH/fixed-router facade；Vault/TipJar 只消费 SDK，typed closed result policy 保持不变 | code-existence policy、revert bubbling、pull payment/multicall；arbitrary call 继续留在 advanced boundary | F1/F2 |
| signatures | permit-specific ecrecover/domain paths | ECDSA/SignatureChecker/EIP-712/nonce/deadline/Merkle reusable components | F2 |
| assets | `Fungible.Balances` O(1) checked movement；`Fungible.Allowances` explicit pair-handle approve/checked increase/decrease/spend；Token/Credits/Vault/Ownable independently consume slices；wrap/alias/over-spend 已由 Anvil 验收 | ERC-721 owner/approval/receiver；bounded ERC-1155；standard events/errors | F2 |
| lifecycle | constructor/receive/immutable basics | Initializable、ERC-1967/UUPS/proxy/clones、namespaced storage and layout compatibility | F3 |

OpenZeppelin 的 [`utils/structs`](https://github.com/OpenZeppelin/openzeppelin-contracts/tree/master/contracts/utils/structs)、
[`access`](https://github.com/OpenZeppelin/openzeppelin-contracts/tree/master/contracts/access) 和
[`token`](https://github.com/OpenZeppelin/openzeppelin-contracts/tree/master/contracts/token) 是 reusable
policy baseline，不属于 EVM opcode 层。

## 8. Priority waves

这些 F-wave 是跨现有 R-phase 的优先级，不替代 R2/R3/R4/R5 task id，也不与历史 Phoenix
P0–P6 混用。

1. **F0 — shared substrate**：bounded Vec/bytes operations、honest tagged/bounded return contract、
   32-byte values、safe casts/math 和 canonical codec readers/writers。
2. **F1 — target Runtime**：SVM AccountInfo/memory/sysvar/full-hash/error gaps；EVM bounded
   call/result/revert、environment/events/resources；同时完成已有 Runtime recipe 的稳定 SDK facade。
3. **F2 — reusable policy**：SVM Token-2022 extension slices；EVM reentrancy/safe-call/signature、
   ERC-20/721/bounded-1155；两边的 Set/Queue/Bitmap richer shapes。
4. **F3 — lifecycle/ecosystem**：SVM loader interface、EVM proxy/upgrade/clone、advanced crypto/sysvar
   和跨 target resource/reproducibility qualification。

每个切片仍遵守：至少两个独立 consumer；unsupported shape 在 Extract/component validation
fail closed；SVM persistent state 无 pointer/heap collection；EVM 无 runtime slot allocator；主
Emit 不出现应用或协议名字。SVM runtime gate 用 Mollusk，部署资格只用 Surfpool 1.5.0；EVM
用 solc 0.8.34 + Anvil。
