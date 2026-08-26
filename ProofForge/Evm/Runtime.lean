namespace ProofForge.Evm.Runtime

/--
20 字节地址，三个 `UInt64` 叶：w0/w1 各 8 字节，w2 只低 4 字节。
小端装地址字节 0..19。ABI 是一个 `address`，storage 仍三槽。
-/
structure Addr20 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

/--
256 位金额，四个 `UInt64` 叶：w0 最低 64 位，w3 最高。
ABI / 单次 calldata word 是一个 `uint256`；storage 仍四槽。
默认算术还是 `UInt64`。溢出在 Yul 里 `revert(0,0)`，宿主 stub 不模拟溢出。
-/
structure UInt256 where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  deriving Repr, DecidableEq, Inhabited, BEq

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
/-- `ADDRESS` 低 8 字节。完整 20B 用 `evmSelf20`。 -/
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

/-- 完整 `CALLER`。抽出认三叶，不把 Addr20 当单一 UInt64。 -/
def evmCaller20 : Addr20 :=
  { w0 := evmCallerW0, w1 := evmCallerW1, w2 := evmCallerW2 }

/-- 完整 `ADDRESS`。 -/
def evmSelf20 : Addr20 :=
  { w0 := evmSelfW0, w1 := evmSelfW1, w2 := evmSelfW2 }

/-- `eq(callvalue(), amt)`。入口因此 payable。宿主返回 amt。 -/
@[irreducible] def evmDeposit (amt : UInt64) : UInt64 := amt

/-- value CALL 到 20B 地址。失败应 revert。重入不进参考语义。宿主返回 amt。 -/
@[irreducible] def evmSendEth (dst : Addr20) (amt : UInt64) : UInt64 :=
  let _ := dst; amt

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
@[irreducible] def evmMapGetAddr (_base : UInt64) (_key : Addr20) : UInt64 := 0

/-- hashed `Map Addr20` 写。 -/
@[irreducible] def evmMapSetAddr (_base : UInt64) (_key : Addr20) (val : UInt64) : UInt64 :=
  val

/-- pair-key hashed Map 读：owner + spender。缺席是 0。 -/
@[irreducible] def evmMapGetPair
    (_base : UInt64) (_owner _spender : Addr20) : UInt64 := 0

/-- pair-key hashed Map 写。 -/
@[irreducible] def evmMapSetPair
    (_base : UInt64) (_owner _spender : Addr20) (val : UInt64) : UInt64 :=
  val

/-- hashed `Map Addr20 → UInt256` 读。缺席是 0。宿主返回 0。 -/
@[irreducible] def evmMapGetAddr256 (_base : UInt64) (_key : Addr20) : UInt256 :=
  ⟨0, 0, 0, 0⟩

/-- hashed `Map Addr20 → UInt256` 写。宿主返回 `val.w0`。 -/
@[irreducible] def evmMapSetAddr256
    (_base : UInt64) (_key : Addr20) (val : UInt256) : UInt64 :=
  val.w0

/-- pair-key hashed Map 读 256-bit。缺席是 0。 -/
@[irreducible] def evmMapGetPair256
    (_base : UInt64) (_owner _spender : Addr20) : UInt256 :=
  ⟨0, 0, 0, 0⟩

/-- pair-key hashed Map 写 256-bit。宿主返回 `val.w0`。 -/
@[irreducible] def evmMapSetPair256
    (_base : UInt64) (_owner _spender : Addr20) (val : UInt256) : UInt64 :=
  val.w0

/-- 封闭 ERC-20 `transfer(address,uint256)`。失败 / 假返回 revert。宿主返回 `amt.w0`。 -/
@[irreducible] def evmTokenTransfer
    (_token _dest : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

/-- 封闭 ERC-20 `balanceOf(address(this))`。完整 256-bit。宿主返回 0。 -/
@[irreducible] def evmTokenBalanceOfSelf (_token : Addr20) : UInt256 :=
  ⟨0, 0, 0, 0⟩

/-- checked `a + b`。溢出 revert。宿主返回 `a`。 -/
@[irreducible] def evmAdd256 (a b : UInt256) : UInt256 :=
  let _ := b; a

/-- checked `a - b`。不足 revert。宿主返回 `a`。 -/
@[irreducible] def evmSub256 (a b : UInt256) : UInt256 :=
  let _ := b; a

/-- checked `a * b`。溢出 revert。宿主返回 `a`。 -/
@[irreducible] def evmMul256 (a b : UInt256) : UInt256 :=
  let _ := b; a

/-- `a ≥ b`。Yul 比打包后的 256-bit word。宿主返回 `true`。 -/
@[irreducible] def evmGe256 (_a _b : UInt256) : Bool := true

end ProofForge.Evm.Runtime
