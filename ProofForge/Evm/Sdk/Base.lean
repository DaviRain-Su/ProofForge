import ProofForge.Attr
import ProofForge.Evm.Runtime
import ProofForge.Evm.HashedMap.Source
import ProofForge.Evm.WideWord.Source
import ProofForge.Evm.ClosedCall.Source
import ProofForge.Evm.NativeFx.Source

namespace ProofForge.Evm.Sdk

/-!
The base contract-facing EVM SDK definitions. They give source programs stable names and typed
static storage handles while erasing through `@[pf_inline]` to the target-owned component bridge.
They do not add runtime layout objects, EVM operations, IR nodes, or emitter cases. Public consumers
import `ProofForge.Evm.Sdk`, whose umbrella also exposes reusable policy components.
-/

notation "Address" => Runtime.Addr20
notation "UInt256" => Runtime.UInt256
notation "Bytes32" => Runtime.Bytes32

namespace «Address»

@[pf_inline] def zero : Address := WideWord.Source.zero20

@[pf_inline] def eq (left right : Address) : Bool :=
  Runtime.evmEq20 left right

@[pf_inline] def isZero (address : Address) : Bool :=
  WideWord.Source.eq20 address WideWord.Source.zero20

@[pf_inline] def eqImmutable (address : Address) : Bool :=
  WideWord.Source.eq20 address Runtime.evmImm20

end «Address»

namespace «UInt256»

@[pf_inline] def zero : UInt256 := ⟨0, 0, 0, 0⟩

@[pf_inline] def add (left right : UInt256) : UInt256 :=
  ⟨WideWord.Source.addW0 left right, WideWord.Source.addW1 left right,
    WideWord.Source.addW2 left right, WideWord.Source.addW3 left right⟩

@[pf_inline] def sub (left right : UInt256) : UInt256 :=
  ⟨WideWord.Source.subW0 left right, WideWord.Source.subW1 left right,
    WideWord.Source.subW2 left right, WideWord.Source.subW3 left right⟩

@[pf_inline] def mul (left right : UInt256) : UInt256 :=
  ⟨WideWord.Source.mulW0 left right, WideWord.Source.mulW1 left right,
    WideWord.Source.mulW2 left right, WideWord.Source.mulW3 left right⟩

@[pf_inline] def atLeast (left right : UInt256) : Bool :=
  Runtime.evmGe256 left right

end «UInt256»

namespace Storage

abbrev U64Map := HashedMap.Source.MapU64
abbrev AddressMap := HashedMap.Source.MapAddr
abbrev AddressPairMap := HashedMap.Source.MapPair
abbrev AddressMap256 := HashedMap.Source.MapAddr256
abbrev AddressPairMap256 := HashedMap.Source.MapPair256

/-- Compile-time cursor for assigning disjoint hashed-map namespaces. -/
structure Layout where
  nextSlot : Nat
  deriving BEq, Repr, Inhabited

/-- A statically allocated handle and the cursor for the next declaration. -/
structure Allocated (α : Type) where
  handle : α
  next : Layout
  deriving Repr

attribute [pf_inline] Layout.nextSlot Allocated.handle Allocated.next

@[pf_inline] def Layout.root : Layout := ⟨0⟩

@[pf_inline] private def Layout.advance (layout : Layout) : Layout :=
  ⟨layout.nextSlot + 1⟩

@[pf_inline] def Layout.u64Map (layout : Layout) : Allocated U64Map :=
  { handle := { base := UInt64.ofNat layout.nextSlot }, next := layout.advance }

@[pf_inline] def Layout.addressMap (layout : Layout) : Allocated AddressMap :=
  { handle := { base := UInt64.ofNat layout.nextSlot }, next := layout.advance }

@[pf_inline] def Layout.addressPairMap (layout : Layout) : Allocated AddressPairMap :=
  { handle := { base := UInt64.ofNat layout.nextSlot }, next := layout.advance }

@[pf_inline] def Layout.addressMap256 (layout : Layout) : Allocated AddressMap256 :=
  { handle := { base := UInt64.ofNat layout.nextSlot }, next := layout.advance }

@[pf_inline] def Layout.addressPairMap256 (layout : Layout) : Allocated AddressPairMap256 :=
  { handle := { base := UInt64.ofNat layout.nextSlot }, next := layout.advance }

@[pf_inline] def U64Map.get (map : U64Map) (key : UInt64) : UInt64 :=
  Runtime.evmMapGetU64 map.base key

@[pf_inline] def U64Map.put (map : U64Map) (key value : UInt64) : UInt64 :=
  Runtime.evmMapSetU64 map.base key value

@[pf_inline] def AddressMap.get (map : AddressMap) (key : Address) : UInt64 :=
  Runtime.evmMapGetAddr map.base key

@[pf_inline] def AddressMap.put (map : AddressMap) (key : Address) (value : UInt64) : UInt64 :=
  Runtime.evmMapSetAddr map.base key value

@[pf_inline] def AddressPairMap.get (map : AddressPairMap)
    (owner spender : Address) : UInt64 :=
  Runtime.evmMapGetPair map.base owner spender

@[pf_inline] def AddressPairMap.put (map : AddressPairMap)
    (owner spender : Address) (value : UInt64) : UInt64 :=
  Runtime.evmMapSetPair map.base owner spender value

@[pf_inline] def AddressMap256.get (map : AddressMap256) (key : Address) : UInt256 :=
  Runtime.evmMapGetAddr256 map.base key

@[pf_inline] def AddressMap256.put (map : AddressMap256)
    (key : Address) (value : UInt256) : UInt64 :=
  Runtime.evmMapSetAddr256 map.base key value

@[pf_inline] def AddressMap256.containsAtLeast (map : AddressMap256)
    (key : Address) (amount : UInt256) : Bool :=
  WideWord.Source.ge256 (HashedMap.Source.getAddr256 map key) amount

@[pf_inline] def AddressMap256.nextAdd (map : AddressMap256)
    (key : Address) (amount : UInt256) : UInt256 :=
  WideWord.Source.add256 (HashedMap.Source.getAddr256 map key) amount

@[pf_inline] def AddressMap256.nextSub (map : AddressMap256)
    (key : Address) (amount : UInt256) : UInt256 :=
  WideWord.Source.sub256 (HashedMap.Source.getAddr256 map key) amount

@[pf_inline] def AddressMap256.revertInsufficient (map : AddressMap256)
    (key : Address) (wanted : UInt256) : UInt64 :=
  NativeFx.Source.revertInsufficient (HashedMap.Source.getAddr256 map key) wanted

@[pf_inline] def AddressPairMap256.get (map : AddressPairMap256)
    (owner spender : Address) : UInt256 :=
  Runtime.evmMapGetPair256 map.base owner spender

@[pf_inline] def AddressPairMap256.put (map : AddressPairMap256)
    (owner spender : Address) (value : UInt256) : UInt64 :=
  Runtime.evmMapSetPair256 map.base owner spender value

@[pf_inline] def AddressPairMap256.containsAtLeast (map : AddressPairMap256)
    (owner spender : Address) (amount : UInt256) : Bool :=
  WideWord.Source.ge256 (HashedMap.Source.getPair256 map owner spender) amount

@[pf_inline] def AddressPairMap256.nextAdd (map : AddressPairMap256)
    (owner spender : Address) (amount : UInt256) : UInt256 :=
  WideWord.Source.add256 (HashedMap.Source.getPair256 map owner spender) amount

@[pf_inline] def AddressPairMap256.nextSub (map : AddressPairMap256)
    (owner spender : Address) (amount : UInt256) : UInt256 :=
  WideWord.Source.sub256 (HashedMap.Source.getPair256 map owner spender) amount

@[pf_inline] def AddressPairMap256.revertInsufficient (map : AddressPairMap256)
    (owner spender : Address) (wanted : UInt256) : UInt64 :=
  NativeFx.Source.revertInsufficient (HashedMap.Source.getPair256 map owner spender) wanted

end Storage

namespace Context

@[pf_inline] def caller : Address := Runtime.evmCaller20
@[pf_inline] def self : Address := Runtime.evmSelf20
@[pf_inline] def blockNumber : UInt64 := Runtime.evmBlockNumber
@[pf_inline] def timestamp : UInt64 := Runtime.evmTimestamp
@[pf_inline] def chainId : UInt64 := Runtime.evmChainId
@[pf_inline] def callValue : UInt256 := Runtime.evmCallValue256
@[pf_inline] def selfBalance : UInt256 := Runtime.evmSelfBalance256

end Context

namespace Immutable

@[pf_inline] def address : Address := Runtime.evmImm20
@[pf_inline] def address2 : Address := Runtime.evmImm20b
@[pf_inline] def u64 : UInt64 := Runtime.evmImmU64
@[pf_inline] def u64b : UInt64 := Runtime.evmImmU64b

end Immutable

namespace Ether

@[pf_inline] def accept (amount : UInt256) : UInt64 :=
  Runtime.evmDeposit256 amount

@[pf_inline] def send (destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmSendEth256 destination amount

@[pf_inline] def receive : UInt64 := Runtime.evmReceive

end Ether

namespace Event

@[pf_inline] def tipped (amount : UInt64) : UInt64 := Runtime.evmLogTipped amount
@[pf_inline] def incremented (amount : UInt64) : UInt64 := Runtime.evmLogIncremented amount
@[pf_inline] def transferU64 (amount : UInt64) : UInt64 := Runtime.evmLogTransfer amount
@[pf_inline] def approvalU64 (amount : UInt64) : UInt64 := Runtime.evmLogApproval amount

@[pf_inline] def transfer (source destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmLogTransfer256 source destination amount

@[pf_inline] def approval (owner spender : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmLogApproval256 owner spender amount

end Event

namespace Revert

@[pf_inline] def insufficient (held wanted : UInt256) : UInt64 :=
  Runtime.evmRevertInsufficient held wanted

@[pf_inline] def unauthorized (who : Address) : UInt64 :=
  Runtime.evmRevertUnauthorized who

@[pf_inline] def zeroAddress : UInt64 := Runtime.evmRevertZeroAddress
@[pf_inline] def paused : UInt64 := Runtime.evmRevertPaused
@[pf_inline] def capExceeded : UInt64 := Runtime.evmRevertCapExceeded

end Revert

namespace ERC20

@[pf_inline] def transfer (token destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmTokenTransfer token destination amount

@[pf_inline] def balanceOfSelf (token : Address) : UInt256 :=
  Runtime.evmTokenBalanceOfSelf token

@[pf_inline] def approve (token spender : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmTokenApprove token spender amount

@[pf_inline] def transferFrom (token owner destination : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmTokenTransferFrom token owner destination amount

@[pf_inline] def allowance (token owner spender : Address) : UInt256 :=
  Runtime.evmTokenAllowanceOf token owner spender

@[pf_inline] def permit (token owner spender : Address) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : UInt64 :=
  Runtime.evmTokenPermit token owner spender value deadline v r s

end ERC20

namespace WETH

@[pf_inline] def deposit (weth : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmWethDeposit weth amount

@[pf_inline] def withdraw (weth : Address) (amount : UInt256) : UInt64 :=
  Runtime.evmWethWithdraw weth amount

end WETH

namespace UniswapV2

@[pf_inline] def swapExact2 (router tokenA tokenB : Address)
    (amountIn minimumOut : UInt256) : UInt64 :=
  Runtime.evmSwapExact2 router tokenA tokenB amountIn minimumOut

@[pf_inline] def swapExact3 (router tokenA tokenB tokenC : Address)
    (amountIn minimumOut : UInt256) : UInt64 :=
  Runtime.evmSwapExact3 router tokenA tokenB tokenC amountIn minimumOut

end UniswapV2

namespace Permit

@[pf_inline] def authorize (owner spender : Address) (value deadline : UInt256)
    (v : UInt8) (r s : Bytes32) : UInt64 :=
  Runtime.evmPermit owner spender value deadline v r s

@[pf_inline] def domainSeparator : Bytes32 :=
  ⟨Runtime.evmDomainSeparator.w0, Runtime.evmDomainSeparator.w1,
    Runtime.evmDomainSeparator.w2, Runtime.evmDomainSeparator.w3⟩

end Permit

end ProofForge.Evm.Sdk
