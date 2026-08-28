import ProofForge.Core.Value

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

/-! EVM compatibility names for target-neutral allocation-free source values. -/

/--
256 位金额的兼容名。逻辑值由 shared Core 所有；EVM 只拥有 ABI / storage 物理布局。
-/
abbrev UInt256 := ProofForge.Core.Value.UInt256

/-- Compatibility constructor for code that named the old EVM-owned structure constructor. -/
abbrev UInt256.mk := ProofForge.Core.Value.UInt256.mk

/-- 32 字节哈希 / 签名半段的兼容名。EVM ABI 是 `bytes32`，不是 `uint256`。 -/
abbrev Bytes32 := ProofForge.Core.Value.FixedBytes 32

/-- Compatibility constructor for code that named the old EVM-owned structure constructor. -/
abbrev Bytes32.mk (w0 w1 w2 w3 : UInt64) : Bytes32 := ⟨w0, w1, w2, w3⟩

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

/-- 构造期烘焙的 `uint64`。runtime `loadimmutable("imm0")`。宿主返回 0。 -/
@[irreducible] def evmImmU64 : UInt64 := 0

/-- 第二套构造期 `uint64`。runtime `loadimmutable("imm1")`。宿主返回 0。 -/
@[irreducible] def evmImmU64b : UInt64 := 0

/-- 构造期烘焙的 Addr20 三叶。runtime `loadimmutable("immAddr")` 再拆。宿主返回 0。 -/
@[irreducible] def evmImmW0 : UInt64 := 0
@[irreducible] def evmImmW1 : UInt64 := 0
@[irreducible] def evmImmW2 : UInt64 := 0

/-- 第二套构造期 Addr20 三叶。runtime `loadimmutable("immAddr2")` 再拆。宿主返回 0。 -/
@[irreducible] def evmImmX0 : UInt64 := 0
@[irreducible] def evmImmX1 : UInt64 := 0
@[irreducible] def evmImmX2 : UInt64 := 0

/-- 完整构造期 Addr20。抽出认三叶。 -/
def evmImm20 : Addr20 :=
  { w0 := evmImmW0, w1 := evmImmW1, w2 := evmImmW2 }

/-- 第二套完整构造期 Addr20。抽出认三叶。 -/
def evmImm20b : Addr20 :=
  { w0 := evmImmX0, w1 := evmImmX1, w2 := evmImmX2 }

/-- `eq(callvalue(), amt)`。入口因此 payable。宿主返回 amt。 -/
@[irreducible] def evmDeposit (amt : UInt64) : UInt64 := amt

/-- value CALL 到 20B 地址。失败应 revert。重入不进参考语义。宿主返回 amt。 -/
@[irreducible] def evmSendEth (dst : Addr20) (amt : UInt64) : UInt64 :=
  let _ := dst; amt

/-- 完整 `CALLVALUE`。抽出认四叶，不把 wei 当单一 UInt64。宿主返回 0。 -/
@[irreducible] def evmCallValue256 : UInt256 := ⟨0, 0, 0, 0⟩

/-- 完整 `SELFBALANCE`。超宽不截断。宿主返回 0。 -/
@[irreducible] def evmSelfBalance256 : UInt256 := ⟨0, 0, 0, 0⟩

/-- `eq(callvalue(), packed uint256)`。入口因此 payable。宿主返回 `amt.w0`。 -/
@[irreducible] def evmDeposit256 (amt : UInt256) : UInt64 := amt.w0

/-- value CALL，金额是 packed wei。失败 revert。重入不进参考语义。宿主返回 `amt.w0`。 -/
@[irreducible] def evmSendEth256 (dst : Addr20) (amt : UInt256) : UInt64 :=
  let _ := dst; amt.w0

/-- LOG1 `Tipped(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogTipped (amt : UInt64) : UInt64 := amt

/-- LOG1 `Incremented(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogIncremented (amt : UInt64) : UInt64 := amt

/-- LOG1 `Transfer(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogTransfer (amt : UInt64) : UInt64 := amt

/-- LOG1 `Approval(uint64)`。宿主返回 amt。 -/
@[irreducible] def evmLogApproval (amt : UInt64) : UInt64 := amt

/-- LOG3 `Transfer(address,address,uint256)`。indexed from/to，data 是金额。宿主返回 `amt.w0`。 -/
@[irreducible] def evmLogTransfer256
    (_from _to : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

/-- LOG3 `Approval(address,address,uint256)`。indexed owner/spender。宿主返回 `amt.w0`。 -/
@[irreducible] def evmLogApproval256
    (_owner _spender : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

/-- 参数化 `Insufficient(uint256,uint256)`。宿主返回 `have.w0`。 -/
@[irreducible] def evmRevertInsufficient (_have _want : UInt256) : UInt64 := 0

/-- 参数化 `Unauthorized(address)`。宿主返回 0。 -/
@[irreducible] def evmRevertUnauthorized (_who : Addr20) : UInt64 := 0

/-- 无参 `ZeroAddress()`。宿主返回 0。 -/
@[irreducible] def evmRevertZeroAddress : UInt64 := 0

/-- 无参 `Paused()`。宿主返回 0。 -/
@[irreducible] def evmRevertPaused : UInt64 := 0

/-- 无参 `CapExceeded()`。宿主返回 0。 -/
@[irreducible] def evmRevertCapExceeded : UInt64 := 0

/-- 无 calldata 的 payable `receive()`。宿主返回 `callvalue`。 -/
@[irreducible] def evmReceive : UInt64 := 0

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

/-- 封闭 ERC-20 `approve(address,uint256)`。失败 / 假返回 revert。宿主返回 `amt.w0`。 -/
@[irreducible] def evmTokenApprove
    (_token _spender : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

/-- 封闭 ERC-20 `transferFrom(address,address,uint256)`。失败 / 假返回 revert。宿主返回 `amt.w0`。 -/
@[irreducible] def evmTokenTransferFrom
    (_token _owner _dest : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

/-- 封闭 ERC-20 `allowance(owner,spender)`。完整 256-bit。宿主返回 0。 -/
@[irreducible] def evmTokenAllowanceOf
    (_token _owner _spender : Addr20) : UInt256 :=
  ⟨0, 0, 0, 0⟩

/-- 封闭 WETH `deposit()`。value CALL，selector `0xd0e30db0`，calldata 4 字节。失败 revert。宿主返回 `amt.w0`。 -/
@[irreducible] def evmWethDeposit
    (_weth : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

/-- 封闭 WETH `withdraw(uint256)`。CALL，selector `0x2e1a7d4d`，36 字节 calldata，value 0。失败 / 假返回 revert。宿主返回 `amt.w0`。 -/
@[irreducible] def evmWethWithdraw
    (_weth : Addr20) (amt : UInt256) : UInt64 :=
  amt.w0

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

/-- `a = b` on packed 256-bit words. The host stub returns `true`. -/
@[irreducible] def evmEq256 (_a _b : UInt256) : Bool := true

/-- Unsigned `a < b` on packed 256-bit words. The host stub returns `true`. -/
@[irreducible] def evmLt256 (_a _b : UInt256) : Bool := true

/-- Unsigned `a ≤ b` on packed 256-bit words. The host stub returns `true`. -/
@[irreducible] def evmLe256 (_a _b : UInt256) : Bool := true

/-- Unsigned `a > b` on packed 256-bit words. The host stub returns `true`. -/
@[irreducible] def evmGt256 (_a _b : UInt256) : Bool := true

/-- 两份 Addr20 整值相等。Yul pack 成 address 再 `eq`。宿主返回 `true`。 -/
@[irreducible] def evmEq20 (_a _b : Addr20) : Bool := true

/-- 封闭 Uniswap V2 `swapExactTokensForTokens`，path 长度 2。`to` 是本合约，deadline 是 `uint256.max`。失败 revert。宿主返回 `amtIn.w0`。 -/
@[irreducible] def evmSwapExact2
    (_router _tokenA _tokenB : Addr20) (amtIn _minOut : UInt256) : UInt64 :=
  amtIn.w0

/-- 封闭 Uniswap V2 `swapExactTokensForTokens`，path 长度 3。`to` 是本合约，deadline 是 `uint256.max`。失败 revert。宿主返回 `amtIn.w0`。 -/
@[irreducible] def evmSwapExact3
    (_router _tokenA _tokenB _tokenC : Addr20) (amtIn _minOut : UInt256) : UInt64 :=
  amtIn.w0

/-- 封闭 EIP-2612 `permit`。name=`Token`，version=`1`，nonce base=2，allowance base=1。失败 revert。宿主返回 `value.w0`。 -/
@[irreducible] def evmPermit
    (_owner _spender : Addr20) (value _deadline : UInt256) (_v : UInt8) (_r _s : Bytes32) : UInt64 :=
  value.w0

/-- 封闭 EIP-712 domain separator。name=`Token`，version=`1`。宿主返回 0。 -/
@[irreducible] def evmDomainSeparator : Bytes32 := ⟨0, 0, 0, 0⟩

/-- 封闭外部 EIP-2612 `permit` CALL。失败 / 假返回 revert。宿主返回 `value.w0`。 -/
@[irreducible] def evmTokenPermit
    (_token _owner _spender : Addr20) (value _deadline : UInt256)
    (_v : UInt8) (_r _s : Bytes32) : UInt64 :=
  value.w0

end ProofForge.Evm.Runtime
