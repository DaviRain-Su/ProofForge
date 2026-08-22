namespace ProofForge.Evm.Runtime

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

/-- LOG1 `Transfer(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogTransfer (amt : UInt64) : UInt64 := amt

/-- LOG1 `Approval(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogApproval (amt : UInt64) : UInt64 := amt

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

end ProofForge.Evm.Runtime
