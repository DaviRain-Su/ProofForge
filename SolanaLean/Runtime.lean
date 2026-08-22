namespace SolanaLean.Runtime

/--
当前 slot。抽出器认这个名字，发射 `sol_get_clock_sysvar` 后读
`Clock.slot`（偏移 0）。这是物理 slot，不是逻辑 block。

宿主侧是不可约 stub：定理把它当未指定的 `UInt64`，不要unfold成 0。
`unixTime` / 其余 Clock 字段本剖面 fail closed。
-/
@[irreducible] def clockSlot : UInt64 := 0

/--
账户 0 公钥的第一个小端 `u64`（`ACC0_KEY+0`）。
用到这个叶子的入口会检查 `is_signer`。

这是指定账户的 key，不是 `tx.origin`，也不是 fee payer。
完整 32 字节以后再开。
-/
@[irreducible] def signerKey0 : UInt64 := 0

/--
封闭 `system.transfer`。抽出器认这个名字，发射固定三账户 CPI：
payer / recipient / System Program，内层 `u32le(2) || u64le(lamports)`，
`sol_invoke_signed_c`，无 signer seeds。

宿主侧是不可约 stub，返回传入的 `lamports`，不要当链上余额用。
这是编译期钉死的 `invoke` 特化。运行时拼 program id / remaining accounts 仍 fail closed。
-/
@[irreducible] def systemTransfer (lamports : UInt64) : UInt64 := lamports

/--
`CALLER` 的低 8 字节：`and(caller(), 0xffffffffffffffff)`。
这是 20 字节地址的末 8 字节，不是完整 address，也不是 `tx.origin`。
SVM 发射器碰到这个叶子 fail closed。
-/
@[irreducible] def evmCaller : UInt64 := 0

/--
`NUMBER`，超出 `UInt64` 则 revert。这是 EVM block number，不是 Solana slot。
`clockSlot` 继续只表示 `Clock.slot`。
-/
@[irreducible] def evmBlockNumber : UInt64 := 0

@[irreducible] def evmTimestamp : UInt64 := 0
@[irreducible] def evmChainId : UInt64 := 0
/-- `ADDRESS` 低 8 字节。完整 20B 用 `evmSelfW*`。 -/
@[irreducible] def evmSelf : UInt64 := 0
@[irreducible] def evmCallValue : UInt64 := 0
@[irreducible] def evmSelfBalance : UInt64 := 0

/-- `CALLER` 20 字节拆成三叶：w0、w1 各 8 字节，w2 低 4 字节。小端装地址字节 0..19。 -/
@[irreducible] def evmCallerW0 : UInt64 := 0
@[irreducible] def evmCallerW1 : UInt64 := 0
@[irreducible] def evmCallerW2 : UInt64 := 0
@[irreducible] def evmSelfW0 : UInt64 := 0
@[irreducible] def evmSelfW1 : UInt64 := 0
@[irreducible] def evmSelfW2 : UInt64 := 0

/-- `eq(callvalue(), amt)`。入口因此 payable。宿主返回 amt。 -/
@[irreducible] def evmDeposit (amt : UInt64) : UInt64 := amt

/-- value CALL 到 20B 地址。失败应 revert。重入不进参考语义。宿主返回 amt。 -/
@[irreducible] def evmSendEth (w0 w1 w2 amt : UInt64) : UInt64 :=
  let _ := w0; let _ := w1; let _ := w2; amt

/-- LOG1 `Tipped(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogTipped (amt : UInt64) : UInt64 := amt

/-- LOG1 `Incremented(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogIncremented (amt : UInt64) : UInt64 := amt

/-- hashed `Map` 读 payload。缺席是 0。宿主返回 0。 -/
@[irreducible] def evmMapGetU64 (_base _key : UInt64) : UInt64 := 0

/-- hashed `Map` 写 payload，occ=1。宿主返回 val。 -/
@[irreducible] def evmMapSetU64 (_base _key val : UInt64) : UInt64 := val

/-- hashed `Map Addr20` 读。缺席是 0。 -/
@[irreducible] def evmMapGetAddr (_base w0 w1 w2 : UInt64) : UInt64 :=
  let _ := w0; let _ := w1; let _ := w2; 0

/-- hashed `Map Addr20` 写。 -/
@[irreducible] def evmMapSetAddr (_base w0 w1 w2 val : UInt64) : UInt64 :=
  let _ := w0; let _ := w1; let _ := w2; val

/-- pair-key hashed Map 读：owner 三叶 + spender 三叶。缺席是 0。 -/
@[irreducible] def evmMapGetPair
    (_base o0 o1 o2 s0 s1 s2 : UInt64) : UInt64 :=
  let _ := o0; let _ := o1; let _ := o2
  let _ := s0; let _ := s1; let _ := s2
  0

/-- pair-key hashed Map 写。 -/
@[irreducible] def evmMapSetPair
    (_base o0 o1 o2 s0 s1 s2 val : UInt64) : UInt64 :=
  let _ := o0; let _ := o1; let _ := o2
  let _ := s0; let _ := s1; let _ := s2
  val

/-- 封闭 ERC-20 `transfer`。callee 20B；失败 / 假返回 revert。宿主返回 amt。 -/
@[irreducible] def evmTokenTransfer
    (tw0 tw1 tw2 dw0 dw1 dw2 amt : UInt64) : UInt64 :=
  let _ := tw0; let _ := tw1; let _ := tw2
  let _ := dw0; let _ := dw1; let _ := dw2
  amt

/-- 封闭 ERC-20 `balanceOf(address(this))`。超 UInt64 应 revert。宿主返回 0。 -/
@[irreducible] def evmTokenBalanceOfSelf (tw0 tw1 tw2 : UInt64) : UInt64 :=
  let _ := tw0; let _ := tw1; let _ := tw2; 0

end SolanaLean.Runtime
