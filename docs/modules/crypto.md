# ProofForge.Crypto

## Purpose

本机、kernel 可算的哈希。不是链上 syscall，也不属于某一条链。

## Boundary

| 模块 | 拥有 | 不拥有 |
|---|---|---|
| `Crypto.Sha256` | FIPS 180-4 SHA-256；disc / layout marker | `sol_sha256` |
| `Crypto.Keccak` | Ethereum Keccak-256（domain `0x01`）；ABI selector | `sol_keccak256`、链上 opcode |

`ProofForge.Sha256` 和 `ProofForge.Evm.Keccak` 只是旧名转发。新代码应 `import ProofForge.Crypto.Sha256` / `ProofForge.Crypto.Keccak`。

## Tests

`Tests/Sha256Spec.lean`、`Tests/EvmSpec.lean` 的空串 / `abc` / selector 夹具。
