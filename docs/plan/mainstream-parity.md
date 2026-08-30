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
| source/ABI 边界 | compile-time capacity + runtime length + fixed scalar frame | shared `BoundedVec` operations、Map/Set/Queue/BitSet laws、distinct bounded bytes/string + strict UTF-8 source contract；SVM Borsh 与 EVM ABI generic bounded/bytes/string input 已有；两边 top-level one-limb bounded/tagged return 已有独立 target plan；packed BitSet word policy 已由 SVM/EVM 分别绑定持久状态 | remaining collection persistence bindings、nested/constructed tagged shapes、wide/aggregate dynamic elements |
| invocation-local | bounded scratch/heap region，OOM 显式失败，调用结束即失效 | SVM `Sdk.Transient.Vector64` 与 `Bytes` 各有两个可同时 active 的编译期 slot；`Record64` 在同一 Vector64 slot 上提供派生 geometry、aligned count/access 和 fixed-arity `append1..4` whole-record preflight；共同提供 begin/pop/truncate/clear/finish、独立 metadata/payload 与真实 OOM | wider/typed POD element shapes、更多 resource-manifest slots、insert/remove-at/iteration；EVM bounded memory binding |
| SVM persistent | canonical account bytes + count/capacity/index，绝不存 pointer | `Sdk.Storage.BoundedVec`、Queue、packed BitSet、ordered Map/RBMap、allocator 已有 u64/固定 schema | richer POD element/key/value shapes、enumerable Set、versioned codecs |
| EVM persistent | static consecutive slots 或 typed hashed namespace | fixed `Vector` state、static declarations、typed maps、bounded UInt64 storage vector、packed bitmap、ring queue、enumerable set/map 与 capacity-4 checkpoints 均为 compile-time geometry 和显式 checked policy | richer key/value/element shapes、wider checkpoint ceiling、bulk bounded iteration 与 namespaced storage |

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
| aggregate values | record/tuple/Option/bounded enum/fixed Vector；bounded input carrier；capacity-preserving bounded Vec semantics 与 cross-target scalar dynamic read；bounded Map/Set/Queue/BitSet、bytes、UTF-8 string logical contracts；bytes/string 已分别绑定 SVM/EVM input；BitSet word policy 已分别绑定 SVM account words 与 EVM static slots | remaining collection persistence bindings、bounded mutation writeback、wide/aggregate dynamic elements；nested bounded shapes | F0 |
| codecs | target-neutral schema；SVM Borsh 与 EVM static/tagged/bounded/bytes/string input bindings；两边 independent top-level bounded/tagged output plan | nested/constructed/wide dynamic returns、version/discriminator、reusable account/storage codecs | F0 |
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
| AccountInfo | fixed Account/Signer handle；一等 compiler-erased `Pubkey` 值：key/owner 投影、全四字 equality/inequality 与 canonical matching（`R3-023`），并以 generic `@[pf_boundary]` static-record frame 完成 whole-value exact Borsh entry/return（`R3-024`）；key/owner/data words、lamports/length/flags；read-only bounded remaining-account view；program-owned checked data word writes；fixed-handle checked lamport transfer；fixed external handle 的 zero-initializing resize 验证 managed-state alias/writable/current owner/10 MiB ceiling/+10,240 original-growth（`R2-010`）；`closeTo` 组合 pre-effect balance snapshot、resize-to-zero 与 checked refund（`R3-025`） | 完整 initialization/rent-top-up/owner-reassign policy；AccountView 与 direct mutation 同时使用时的 alias-aware variable walk；runtime-selected account geometry | F0/F1 |
| memory | official-shaped 32 KiB downward bump model、bounded scratch plans；checked account spans 已绑定 `memcpy/memmove/memcmp/memset`；source-visible bounded `Vector64` 与 checked byte writer 已绑定真实 heap，各有两个可同时 active 的同类型 slot，支持 checked LIFO pop 与 shared Rust-style truncate；`Record64` 再组合 1–4 UInt64 limbs 的 whole-record append/aligned access，保留显式 OOM/full/OOB/state/range errors；共享 lifecycle interpreter 统一 allocation/metadata/clear/truncate/finish | wider/typed POD shapes、更多 manifest-bounded handles、bounded insert/remove/iteration；allocator/resource manifest | F0/F1 |
| instruction/CPI/PDA | static bounded metas/data、multi-seed signed CPI、return-data staging、PDA find/check | bounded full return data + returned program-id check；more generic bounded instruction bytes；stack/sibling/instruction introspection only when required | F1 |
| sysvar/runtime query | `Svm.Sdk.Sysvar` 已通过 target-owned Component 覆盖 Clock/EpochSchedule 全部 unsigned/Bool native fields 与 compile-time Rent；Telemetry 覆盖 remaining compute/stack height | signed Clock timestamps、generic sliced sysvar、instructions sysvar；advanced sysvars on demand | F1/F2 |
| crypto | literal SHA-256/Keccak first word、PDA host calls | full 32-byte/multi-slice hashes；Blake3/SHA-512/secp recovery/Poseidon/curve/big-mod-exp；signature-program instruction validation | F1/F2 |
| log/error | authenticated bounded `sol_log_data` recorder；active transient bytes 可作为一个 bounded field 直接发布；custom failure terminal | multi-field/字符串/numeric/key log API；stable typed event convention；complete ProgramError/custom-code mapping | F1 |
| serialization | exact scalar/static/tagged/bounded Borsh input、canonical bounded bytes/String（strict UTF-8）、top-level one-limb bounded/tagged Borsh return、raw entry、Token-2022 TLV envelope | nested/constructed/wide dynamic returns、Pack/POD/COption/versioned account codecs、strict reusable readers/writers | F0/F2 |

Rust 的 `Rc<RefCell<_>>` borrow API 是 Rust host representation，不应原样复制成 Lean SDK。
ProofForge 要保存的是相同的安全合同：写权限、owner、alias、长度和 CPI 前状态必须被验证，且
不能形成可持久化 reference/pointer。

## 5. SVM SDK parity

| 组件 | 当前 | 主要缺口 | 优先级 |
|---|---|---|---|
| System/PDA | static ASCII PDA；non-seeded transfer/create/assign/allocate/nonce；generic compile-time ASCII seeded allocate/create/assign/transfer with checked bincode length；regular/seeded/PDA create 可把 compile-time space 与当前 Rent minimum 组合；fixed program-account close/refund 由 `Account.Handle.closeTo` 组合 | resize rent top-up、owner-reassign lifecycle policy、runtime-selected geometry | F1 |
| SPL Token | `Svm.Sdk.Program/Token` 已统一 canonical classic/Token-2022 identity、exact 82/165-byte base-state views、fixed classic effects，并以 CPI-relative role descriptors 提供 checked/unchecked ordinary/PDA-signed transfer | extension-bearing Token-2022 state views、更多 honest generic authority/multisig variants | F1/F2 |
| Token-2022 | base-layout transfer + bounded TLV envelope，未知 extension 原子拒绝 | typed extension lookup/account-size；transfer-fee/hook/memo/CPI-guard 等逐扩展完整语义 | F2 |
| ATA/Memo | SDK 已有 canonical ATA/Memo ids、role-typed static ATA Create/CreateIdempotent/RecoverNested（Token 与 ATA program 由 caller account 显式提供）与 ≤512-byte compile-time ASCII Memo；`writeOk` 仅为兼容 delegate | canonical derived-address validation、runtime-selected account geometry；runtime-selected/UTF-8 Memo bytes | F1/F2 |
| loader/lifecycle | Loader-v3 assembly/deploy qualification exists | typed loader state/instructions、upgrade authority/immutability lifecycle facade | F3 |
| persistent collections | POD Field、Vec、Queue、packed BitSet、ordered Map/RBMap、allocator | generic bounded POD records、enumerable Set、versioned initialization/close policy | F1/F2 |

SPL Token 对照官方 [`token/interface`](https://github.com/solana-program/token/tree/master/interface)，
ATA 必须显式携带 token program id，不能把 classic Token 的默认值误用于 Token-2022。

## 6. EVM Runtime and Solidity parity

EVM Runtime 以 Solidity 的 [types](https://docs.soliditylang.org/en/latest/types.html)、
[ABI](https://docs.soliditylang.org/en/latest/abi-spec.html) 和
[global/runtime functions](https://docs.soliditylang.org/en/latest/units-and-global-variables.html)
为基线；SDK policy 再对照 OpenZeppelin。

| 类别 | 当前 source surface | 主要缺口 | 优先级 |
|---|---|---|---|
| values/ABI | typed scalars、Address/u128/u256/bytesN、static aggregates、tagged input、bounded dynamic-array/bytes/string input、top-level one-limb bounded/tagged output、strict UTF-8 | signed ints、safe casts、nested/constructed/wide dynamic return、dynamic constructor/fallback returndata | F0/F1 |
| data/storage | ordinary typed State flattening、static declarations、address/address-pair hashed maps、bounded UInt64 storage vector、packed static bitmap、persistent ring queue、enumerable set/map 与 bounded checkpoints | explicit bounded memory/transient contracts；richer persistent shapes；namespaced storage | F0/F2 |
| environment | caller/origin/self/coinbase、`msg.sig`、exact `msg.data.length`、block number/hash、timestamp/chain id/value/selfBalance/immutables；full-width gasleft/gasprice/basefee/prevrandao/gaslimit/blobbasefee/blobhash/blockhash；Address balance/codeSize/codeHash；solc 0.8.34 + Cancun target pin | blob payload、bounded raw `msg.data` byte view、broader target-version matrix；raw code bytes 不进入 safe SDK，blockhash/blobhash input 暂为 checked UInt64 index/height | F1 |
| call/create | closed ERC-20/WETH/router/permit CALL/STATICCALL、typed ≤32-byte result policies、safe ETH send、explicit ordered reentrancy guard；ERC-20 exact canonical `1` / code-backed empty 与 success-only empty-code policy；`Address.hasCode` 提供诚实的观察点 predicate | bounded generic call data/result/revert bubbling；static/delegate semantics；CREATE/CREATE2；arbitrary-call policy | F1/F2 |
| crypto | host Keccak selector tooling、closed ecrecover precompile plan | source hash API、sha256/ripemd/precompiles、ECDSA anti-malleability、EIP-191/712、ERC-1271、Merkle | F1/F2 |
| log/error | typed bounded LOG0..4/custom-error plans behind closed events/errors；source enum 的 zero-argument named errors 已自动进入 ABI metadata | source-declared parameterized typed events/errors、dynamic indexed/data encoding、Panic/revert-data propagation | F1 |
| resources | checked u256 math and bounded ABI frame | gas/code/init-code/memory/stack manifest and compiler-version feature gates | F1/F3 |

不是所有 low-level EVM primitive 都应该直接变成默认安全 SDK。`delegatecall`、raw call、packed
encoding 和 arbitrary revert bytes 必须位于显式 unsafe/advanced boundary；普通 SDK 首先提供
typed bounded call 和验证后的 result contract。

## 7. EVM SDK and OpenZeppelin parity

| 组件 | 当前 | 主要缺口 | 优先级 |
|---|---|---|---|
| collections/math | typed maps、static declarations、capacity-2 role set、checked u256 operations、persistent bounded UInt64 vector/bitmap/ring/enumerable set/map/checkpoints | SafeCast/Math/String/Bytes utilities、richer keys/values/elements、wider checkpoints and iteration shapes | F0/F2 |
| access/safety | owner/two-step ownership、bounded static roles、explicit Pausable、OpenZeppelin-shaped nonzero-sentinel Reentrancy guard | typed Paused/Unpaused events, enumerable/admin roles, timelock/access manager | F1/F2 |
| calls/payments | `Evm.Sdk.Payments` bounded Ether/ERC20/WETH/fixed-router facade；共享 CallResult 拒绝 false/noncanonical/no-code empty，并兼容 code-backed no-return；`Effect.thenTrue` 提供 canonical Bool composition；exact-32 比 OpenZeppelin ≥32 更严格 | bounded revert bubbling、pull payment/multicall；generic/arbitrary call 继续留在 advanced boundary | F1/F2 |
| signatures | permit-specific ecrecover/domain paths | ECDSA/SignatureChecker/EIP-712/nonce/deadline/Merkle reusable components | F2 |
| assets | `Fungible.Balances` O(1) checked movement；`Fungible.Allowances` explicit pair-handle approve/checked increase/decrease/spend；`Erc721` bounded 192-bit-key owner/per-token approval/operator/balance core；`Erc1155` bounded 192-bit-key single-id balance/operator/mint/burn/transfer core；六个独立 asset consumers 的 wrap/alias/over-spend/token-id truncation 已由 Anvil 验收 | ERC-721 standard Address views/full-width id/receiver callback；ERC-1155 batch/receiver/metadata；standard typed events/errors | F2 |
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
3. **F2 — reusable policy**：SVM Token-2022 extension slices；EVM safe-call/signature、
   ERC-20/721/bounded-1155；两边的 Set/Queue/Bitmap richer shapes。
4. **F3 — lifecycle/ecosystem**：SVM loader interface、EVM proxy/upgrade/clone、advanced crypto/sysvar
   和跨 target resource/reproducibility qualification。

每个切片仍遵守：至少两个独立 consumer；unsupported shape 在 Extract/component validation
fail closed；SVM persistent state 无 pointer/heap collection；EVM 无 runtime slot allocator；主
Emit 不出现应用或协议名字。SVM runtime gate 用 Mollusk，部署资格只用 Surfpool 1.5.0；EVM
用 solc 0.8.34 + Anvil。
