# 剩余表面：一次收口

> 历史 L4-033 快照：账户下标现已支持编译期常量 `acc < 64`，不再用本文作当前上限。
> 当前 backlog 见 [../backlog.md](../backlog.md)。

依据：[authority.md](authority.md)、[sdk-surface.md](sdk-surface.md)。
不是 30 个 syscall 全开，也不是 Token-2022 / 运行时 CPI。

## 上一刀做完（L4-033）

仍落在现有抽出器上、且不改 return_data ABI：

| ID | Lean 表面 | 约束 |
|---|---|---|
| L4-acc-n | `accLamports` / `accDataLen` / `isSigner` / `isWritable` / `isExecutable` `acc` | `acc`∈{0,1,2} 编译期常量 |
| L4-key-2 | `accKeyWord` / `accOwnerWord` 扩到 `acc=2` | 仍按字；不是 `ByteArray 32` |
| L4-signer-n | `signerKey acc` | 该账户入口 `is_signer`；walk 也查 |
| L4-owner-self | `ownerIsSelf acc` | owner 32B == 当前 program id；成功 0 / 否则 1 |

旧名 `accLamports0` / `signerKey0` 等保持独立不可约 stub，Info / Peer / Clock digest 不回退。

## 规划了、本切片不做

| 项 | 为什么不做 |
|---|---|
| 完整 32B 一次返回 | 要改 `sol_set_return_data` 8B ABI |
| 账户 3+ | walk 下界再涨；0..3 抽出上限已开，Mollusk 只钉到 2 |
| 多构造子 inductive 带 payload | L2 剖面。`Bool` 已在 L4-034 开成 1 字节 u8-le |
| `sol_secp256k1_recover` | 要 32B hash + 64B sig；不是 ASCII 字面量 |
| blake3 / poseidon / 曲线 | feature-gated，权威表默认关 |

## 完成定义

- 新例子 Trio：三账户 walk；读账户 2 header / key 字；`signerKey 1` 缺签名 Custom(1)；`ownerIsSelf 0` 为 0，`ownerIsSelf 2` 在异 owner 时为 1
- 只给 2 个账户调账户 2 叶子 → Custom(1)
- Peer / Keys / Hash / Clock digest 不回退
