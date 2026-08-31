import ProofForge.Core.Ops
import ProofForge.Core.CFG
import ProofForge.Wasm.Near.Memory
import ProofForge.Wasm.Near.Codec

/-!
# NEAR target dialect

Value/effect extensions owned by the NEAR Protocol chain. v0 admits scalar
context reads, lossless u128 token values, lossless 64-byte account-id leaves,
invocation-memory operations, bounded raw storage, static Promise calls, one static self-callback
edge, native transfers, and bounded callback-result observation. Promise joins and hashing stay
absent.
`reserved` is rejected by `wellFormed`.
-/

namespace ProofForge.Wasm.Near.Ops

/-- NEAR-owned value intrinsics. -/
inductive ValKind where
  | blockIndex
  | blockTimestamp
  | storageUsage
  /-- Legacy predecessor w0 plus the remaining lossless AccountId leaves. -/
  | predecessor
  | predecessorLen
  | predecessorW1 | predecessorW2 | predecessorW3 | predecessorW4
  | predecessorW5 | predecessorW6 | predecessorW7
  /-- Legacy checked UInt64 leaves plus lossless u128 low/high leaves. -/
  | attachedDeposit
  | attachedDepositW0 | attachedDepositW1
  | accountBalance
  | accountBalanceW0 | accountBalanceW1
  /-- Pure checked-u128 predicates and modular limbs; operands are left lo/hi, right lo/hi. -/
  | nearTokenAddOk | nearTokenAddW0 | nearTokenAddW1
  | nearTokenSubOk | nearTokenSubW0 | nearTokenSubW1
  /-- Legacy current-account w0 plus the remaining lossless AccountId leaves. -/
  | currentAccountId
  | currentAccountIdLen
  | currentAccountIdW1 | currentAccountIdW2 | currentAccountIdW3 | currentAccountIdW4
  | currentAccountIdW5 | currentAccountIdW6 | currentAccountIdW7
  /-- Read from the one active invocation-local UInt64 buffer. -/
  | transientBuffer64Get (capacity : Nat)
  /-- Metadata and byte access for the latest raw-storage operation. -/
  | storageResultStatus (capacity : Nat)
  | storageResultLength (capacity : Nat)
  | storageResultFits (capacity : Nat)
  | storageResultByte (capacity : Nat)
  /-- Callback-result count plus metadata and byte access for the latest bounded read. -/
  | promiseResultsCount
  | promiseResultStatus (capacity : Nat)
  | promiseResultLength (capacity : Nat)
  | promiseResultFits (capacity : Nat)
  | promiseResultByte (capacity : Nat)
  | promiseResultBorshUInt64D (capacity : Nat)
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .nearTokenAddOk | .nearTokenAddW0 | .nearTokenAddW1
  | .nearTokenSubOk | .nearTokenSubW0 | .nearTokenSubW1 => 4
  | .transientBuffer64Get _ | .storageResultByte _ | .promiseResultByte _
  | .promiseResultBorshUInt64D _ => 1
  | .reserved => 0
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- NEAR-owned effects. Logging accepts deterministic static data or a fixed-capacity dynamic
UTF-8 frame; the emitter stages the latter through invocation-local linear memory. -/
inductive OpExt (V : Type) where
  | logUtf8 (message : String)
  | logUtf8Bounded (capacity : Nat) (message : Array V)
  | nep297StringData (standard version event : String) (capacity : Nat) (data : Array V)
  | nep141FtMint (owner : Array V) (amountLo amountHi : V)
  | nep141FtTransfer (oldOwner newOwner : Array V) (amountLo amountHi : V)
  | nep141FtBurn (owner : Array V) (amountLo amountHi : V)
  | nep141FtMintMemo (memoCapacity : Nat) (owner : Array V) (amountLo amountHi : V)
      (memo : Array V)
  | nep141FtTransferMemo (memoCapacity : Nat) (oldOwner newOwner : Array V)
      (amountLo amountHi : V) (memo : Array V)
  | nep141FtBurnMemo (memoCapacity : Nat) (owner : Array V) (amountLo amountHi : V)
      (memo : Array V)
  | promiseFunctionCallDetached (receiver method : String) (argsCapacity : Nat)
      (arguments : Array V) (depositLo depositHi gas : V)
  | promiseFunctionCallReturned (receiver method : String) (argsCapacity : Nat)
      (arguments : Array V) (depositLo depositHi gas : V)
  | promiseTransferDetached (receiver : String) (amountLo amountHi : V)
  | promiseTransferReturned (receiver : String) (amountLo amountHi : V)
  | promiseFunctionCallThenReturned (receiver childMethod callbackMethod : String)
      (childArgsCapacity callbackArgsCapacity : Nat)
      (childArguments callbackArguments : Array V)
      (childDepositLo childDepositHi childGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseFunctionCallAndThenReturned
      (leftReceiver leftMethod rightReceiver rightMethod callbackMethod : String)
      (leftArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat)
      (leftArguments rightArguments callbackArguments : Array V)
      (leftDepositLo leftDepositHi leftGas : V)
      (rightDepositLo rightDepositHi rightGas : V)
      (callbackDepositLo callbackDepositHi callbackGas : V)
  | promiseResultRead (capacity : Nat) (index : V)
  | transientBuffer64Begin (capacity : Nat)
  | transientBuffer64Set (capacity : Nat) (index value : V)
  | transientBuffer64Finish (capacity : Nat)
  | storageRead (resultCapacity keyCapacity : Nat) (key : Array V)
  | storageWrite (resultCapacity keyCapacity valueCapacity : Nat)
      (key value : Array V)
  | storageRemove (resultCapacity keyCapacity : Nat) (key : Array V)
  | storageHasKey (resultCapacity keyCapacity : Nat) (key : Array V)
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

abbrev Op := ProofForge.Core.Ops.Op ValKind OpExt

private def storageFrameWellFormed (capacity : Nat) (values : Array Val) : Bool :=
  Codec.storageCapacityValid capacity && values.size == capacity + 1 &&
    values.all (·.wellFormed ValKind.arity)

private def storageKeyFrameWellFormed (capacity : Nat) (values : Array Val) : Bool :=
  Codec.rawStorageKeyCapacityValid capacity && values.size == capacity + 1 &&
    values.all (·.wellFormed ValKind.arity)

private def accountIdFrameWellFormed (values : Array Val) : Bool :=
  values.size == 9 && values.all (·.wellFormed ValKind.arity)

def OpExt.wellFormed : OpExt Val → Bool
  | .logUtf8 message => message.toUTF8.size ≤ 1024
  | .logUtf8Bounded capacity message => storageFrameWellFormed capacity message
  | .nep297StringData standard version event capacity data =>
      standard.toUTF8.size ≤ 64 && version.toUTF8.size ≤ 64 && event.toUTF8.size ≤ 64 &&
        storageFrameWellFormed capacity data
  | .nep141FtMint owner amountLo amountHi =>
      accountIdFrameWellFormed owner && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
      accountIdFrameWellFormed oldOwner && accountIdFrameWellFormed newOwner &&
        amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
  | .nep141FtBurn owner amountLo amountHi =>
      accountIdFrameWellFormed owner && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .nep141FtMintMemo memoCapacity owner amountLo amountHi memo =>
      Codec.nep141MemoCapacityValid memoCapacity && accountIdFrameWellFormed owner &&
        storageFrameWellFormed memoCapacity memo &&
        amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
  | .nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo =>
      Codec.nep141MemoCapacityValid memoCapacity && accountIdFrameWellFormed oldOwner &&
        accountIdFrameWellFormed newOwner &&
        storageFrameWellFormed memoCapacity memo && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .nep141FtBurnMemo memoCapacity owner amountLo amountHi memo =>
      Codec.nep141MemoCapacityValid memoCapacity && accountIdFrameWellFormed owner &&
        storageFrameWellFormed memoCapacity memo &&
        amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
  | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
      Codec.accountIdLiteralValid receiver && Codec.promiseMethodLiteralValid method &&
        storageFrameWellFormed argsCapacity arguments &&
        depositLo.wellFormed ValKind.arity && depositHi.wellFormed ValKind.arity &&
        gas.wellFormed ValKind.arity
  | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
      Codec.accountIdLiteralValid receiver && Codec.promiseMethodLiteralValid method &&
        storageFrameWellFormed argsCapacity arguments &&
        depositLo.wellFormed ValKind.arity && depositHi.wellFormed ValKind.arity &&
        gas.wellFormed ValKind.arity
  | .promiseTransferDetached receiver amountLo amountHi
  | .promiseTransferReturned receiver amountLo amountHi =>
      Codec.accountIdLiteralValid receiver && amountLo.wellFormed ValKind.arity &&
        amountHi.wellFormed ValKind.arity
  | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
      childArgsCapacity callbackArgsCapacity childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid receiver && Codec.promiseMethodLiteralValid childMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed childArgsCapacity childArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        childDepositLo.wellFormed ValKind.arity &&
        childDepositHi.wellFormed ValKind.arity && childGas.wellFormed ValKind.arity &&
        callbackDepositLo.wellFormed ValKind.arity &&
        callbackDepositHi.wellFormed ValKind.arity && callbackGas.wellFormed ValKind.arity
  | .promiseFunctionCallAndThenReturned
      leftReceiver leftMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      Codec.accountIdLiteralValid leftReceiver && Codec.promiseMethodLiteralValid leftMethod &&
        Codec.accountIdLiteralValid rightReceiver && Codec.promiseMethodLiteralValid rightMethod &&
        Codec.promiseMethodLiteralValid callbackMethod &&
        storageFrameWellFormed leftArgsCapacity leftArguments &&
        storageFrameWellFormed rightArgsCapacity rightArguments &&
        storageFrameWellFormed callbackArgsCapacity callbackArguments &&
        #[leftDepositLo, leftDepositHi, leftGas, rightDepositLo, rightDepositHi, rightGas,
          callbackDepositLo, callbackDepositHi, callbackGas].all
          (·.wellFormed ValKind.arity)
  | .promiseResultRead capacity index =>
      Codec.storageCapacityValid capacity && index.wellFormed ValKind.arity
  | .transientBuffer64Begin capacity | .transientBuffer64Finish capacity =>
      Memory.buffer64CapacityValid capacity
  | .transientBuffer64Set capacity index value =>
      Memory.buffer64CapacityValid capacity &&
        index.wellFormed ValKind.arity && value.wellFormed ValKind.arity
  | .storageRead resultCapacity keyCapacity key
  | .storageRemove resultCapacity keyCapacity key
  | .storageHasKey resultCapacity keyCapacity key =>
      Codec.storageCapacityValid resultCapacity && storageKeyFrameWellFormed keyCapacity key
  | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
      Codec.storageCapacityValid resultCapacity && storageKeyFrameWellFormed keyCapacity key &&
        storageFrameWellFormed valueCapacity value
  | .reserved => false

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

private def mapCfgPayload (mapValue : Val → Val) : OpExt Val → OpExt Val
  | .logUtf8 message => .logUtf8 message
  | .logUtf8Bounded capacity message => .logUtf8Bounded capacity (message.map mapValue)
  | .nep297StringData standard version event capacity data =>
      .nep297StringData standard version event capacity (data.map mapValue)
  | .nep141FtMint owner amountLo amountHi =>
      .nep141FtMint (owner.map mapValue) (mapValue amountLo) (mapValue amountHi)
  | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
      .nep141FtTransfer (oldOwner.map mapValue) (newOwner.map mapValue)
        (mapValue amountLo) (mapValue amountHi)
  | .nep141FtBurn owner amountLo amountHi =>
      .nep141FtBurn (owner.map mapValue) (mapValue amountLo) (mapValue amountHi)
  | .nep141FtMintMemo memoCapacity owner amountLo amountHi memo =>
      .nep141FtMintMemo memoCapacity (owner.map mapValue) (mapValue amountLo)
        (mapValue amountHi) (memo.map mapValue)
  | .nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo =>
      .nep141FtTransferMemo memoCapacity (oldOwner.map mapValue) (newOwner.map mapValue)
        (mapValue amountLo) (mapValue amountHi) (memo.map mapValue)
  | .nep141FtBurnMemo memoCapacity owner amountLo amountHi memo =>
      .nep141FtBurnMemo memoCapacity (owner.map mapValue) (mapValue amountLo)
        (mapValue amountHi) (memo.map mapValue)
  | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
      .promiseFunctionCallDetached receiver method argsCapacity (arguments.map mapValue)
        (mapValue depositLo) (mapValue depositHi) (mapValue gas)
  | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
      .promiseFunctionCallReturned receiver method argsCapacity (arguments.map mapValue)
        (mapValue depositLo) (mapValue depositHi) (mapValue gas)
  | .promiseTransferDetached receiver amountLo amountHi =>
      .promiseTransferDetached receiver (mapValue amountLo) (mapValue amountHi)
  | .promiseTransferReturned receiver amountLo amountHi =>
      .promiseTransferReturned receiver (mapValue amountLo) (mapValue amountHi)
  | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
      childArgsCapacity callbackArgsCapacity childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallThenReturned receiver childMethod callbackMethod
        childArgsCapacity callbackArgsCapacity (childArguments.map mapValue)
        (callbackArguments.map mapValue) (mapValue childDepositLo) (mapValue childDepositHi)
        (mapValue childGas) (mapValue callbackDepositLo) (mapValue callbackDepositHi)
        (mapValue callbackGas)
  | .promiseFunctionCallAndThenReturned
      leftReceiver leftMethod rightReceiver rightMethod callbackMethod
      leftArgsCapacity rightArgsCapacity callbackArgsCapacity
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      .promiseFunctionCallAndThenReturned
        leftReceiver leftMethod rightReceiver rightMethod callbackMethod
        leftArgsCapacity rightArgsCapacity callbackArgsCapacity
        (leftArguments.map mapValue) (rightArguments.map mapValue)
        (callbackArguments.map mapValue)
        (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
        (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
        (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas)
  | .promiseResultRead capacity index => .promiseResultRead capacity (mapValue index)
  | .transientBuffer64Begin capacity => .transientBuffer64Begin capacity
  | .transientBuffer64Set capacity index value =>
      .transientBuffer64Set capacity (mapValue index) (mapValue value)
  | .transientBuffer64Finish capacity => .transientBuffer64Finish capacity
  | .storageRead resultCapacity keyCapacity key =>
      .storageRead resultCapacity keyCapacity (key.map mapValue)
  | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
      .storageWrite resultCapacity keyCapacity valueCapacity (key.map mapValue) (value.map mapValue)
  | .storageRemove resultCapacity keyCapacity key =>
      .storageRemove resultCapacity keyCapacity (key.map mapValue)
  | .storageHasKey resultCapacity keyCapacity key =>
      .storageHasKey resultCapacity keyCapacity (key.map mapValue)
  | .reserved => .reserved

private def cfgPayloadValues : OpExt Val → Array Val
  | .logUtf8 _ => #[]
  | .logUtf8Bounded _ message => message
  | .nep297StringData _ _ _ _ data => data
  | .nep141FtMint owner amountLo amountHi => owner ++ #[amountLo, amountHi]
  | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
      oldOwner ++ newOwner ++ #[amountLo, amountHi]
  | .nep141FtBurn owner amountLo amountHi => owner ++ #[amountLo, amountHi]
  | .nep141FtMintMemo _ owner amountLo amountHi memo
  | .nep141FtBurnMemo _ owner amountLo amountHi memo => owner ++ #[amountLo, amountHi] ++ memo
  | .nep141FtTransferMemo _ oldOwner newOwner amountLo amountHi memo =>
      oldOwner ++ newOwner ++ #[amountLo, amountHi] ++ memo
  | .promiseFunctionCallDetached _ _ _ arguments depositLo depositHi gas =>
      arguments ++ #[depositLo, depositHi, gas]
  | .promiseFunctionCallReturned _ _ _ arguments depositLo depositHi gas =>
      arguments ++ #[depositLo, depositHi, gas]
  | .promiseTransferDetached _ amountLo amountHi
  | .promiseTransferReturned _ amountLo amountHi => #[amountLo, amountHi]
  | .promiseFunctionCallThenReturned _ _ _ _ _ childArguments callbackArguments
      childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
      childArguments ++ callbackArguments ++
        #[childDepositLo, childDepositHi, childGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseFunctionCallAndThenReturned _ _ _ _ _ _ _ _
      leftArguments rightArguments callbackArguments
      leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
      callbackDepositLo callbackDepositHi callbackGas =>
      leftArguments ++ rightArguments ++ callbackArguments ++
        #[leftDepositLo, leftDepositHi, leftGas, rightDepositLo, rightDepositHi, rightGas,
          callbackDepositLo, callbackDepositHi, callbackGas]
  | .promiseResultRead _ index => #[index]
  | .transientBuffer64Begin _ | .transientBuffer64Finish _ => #[]
  | .transientBuffer64Set _ index value => #[index, value]
  | .storageRead _ _ key | .storageRemove _ _ key | .storageHasKey _ _ key => key
  | .storageWrite _ _ _ key value => key ++ value
  | .reserved => #[]

def cfgDialect : Core.CFG.Dialect ValKind OpExt where
  mapValues := mapCfgPayload
  values := cfgPayloadValues
  payloadEq := fun left right => left == right

end ProofForge.Wasm.Near.Ops
