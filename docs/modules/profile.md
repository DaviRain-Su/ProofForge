# ProofForge.Profile

## Purpose

对普通 Lean 声明做 Solana 编译剖面检查。

## Boundary

走 `Environment.find?` 传递闭包。不解析源文本，不跑业务类型检查。

## API

- `check env root : Decision`
- `checkAll env roots : Decision`
- `#pf_check ident`

拒绝：unknown、partial（含用户模块里落成 `opaque` 的 `partial def`）、unsafe、用户 `extern` / `implemented_by`、axiom/`sorryAx`、IO/EIO/Task/BaseIO、入口类型含 `Nat`、闭包 > 4096。

用户门只打在根名为 `ProofForge` / `Examples` / `Tests` 的声明上。Init 原语（`UInt64.add`、`Nat.pow` 等）自带 `@[extern]`，必须放行，否则连加法都过不了。`sorryAx` 无论在哪一模块都拒绝。

## Tests

`Tests/ProfileSpec.lean`：Counter 三根 accept；Nat / partial / sorry / IO / extern / implemented_by reject。
