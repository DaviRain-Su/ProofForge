# 关着的格子：能开的一次开完

用户要求：不要等具体合约。能 fail-closed 抽出的都做。L4-034 已绿。

## 本切片做完（L4-034）

| 类 | Lean 表面 | 约束 |
|---|---|---|
| 剖面 | `Bool` 字段 | 1 字节 u8-le；true=1 / false=0 |
| sysvar | `unixTime` | Clock.unix_timestamp@32，按无符号 u64 读 |
| 账户 | `acc` 上限 0..3 | 已有下标叶子扩到 3 |
| System | `systemAdvanceNonce` | tag 4；nonce w + authority s |
| Token | `tokenSetAccountAuthority` | SetAuthority AccountOwner；新 owner = acc2 |
| Token | `tokenInitMultisig` | InitializeMultisig2 tag 19；m=2；signers acc2/acc3 |
| Token | `tokenApprove` | 未检查 Approve tag 4；decimals 不进 data |

旧 digest 不回退。新例子：Gate（Bool+unixTime）、Nonce、TokenOwner、TokenMs。

## 仍关（会拆抽出，或官方禁用）

- 运行时 program id / remaining accounts / 变长 data
- Token-2022 及全部 extension
- blake3 / poseidon / curve25519 / alt_bn128 / `sol_get_sysvar`
- `sol_secp256k1_recover`（要 32B+64B 运行时缓冲）
- `ByteArray 32` 一次返回（改 8B return_data ABI）
- 多构造子 inductive 带 payload
- `sol_alloc_free_`、`sol_log_*` 当产品语义
