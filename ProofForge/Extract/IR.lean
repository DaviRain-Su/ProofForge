import ProofForge.Core.Ops
import ProofForge.Core.IR
import ProofForge.Core.CFG
import ProofForge.Svm.Ops
import ProofForge.Evm.Ops
import ProofForge.Wasm.Xrpl.Ops
import ProofForge.Wasm.Near.Ops

namespace ProofForge.Extract.IR

/-- The extractor is the only layer that combines target-owned value extensions. -/
inductive ValKind where
  | svm (kind : Svm.Ops.ValKind)
  | evm (kind : Evm.Ops.ValKind)
  | xrpl (kind : Wasm.Xrpl.Ops.ValKind)
  | near (kind : ProofForge.Wasm.Near.Ops.ValKind)
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .svm kind => kind.arity
  | .evm kind => kind.arity
  | .xrpl kind => kind.arity
  | .near kind => kind.arity

/-- Target effects stay strongly typed while sharing the extractor's recursive value type. -/
inductive OpExt (V : Type) where
  | svm (payload : Svm.Ops.OpExt V)
  | evm (payload : Evm.Ops.OpExt V)
  | xrpl (payload : Wasm.Xrpl.Ops.OpExt V)
  | near (payload : ProofForge.Wasm.Near.Ops.OpExt V)
  deriving BEq, Repr, Inhabited

abbrev Cmp := Core.Ops.Cmp
abbrev Val := Core.Ops.Val ValKind
abbrev Op := Core.Ops.Op ValKind OpExt
abbrev Evaluation := Core.Evaluation ValKind
abbrev Method := Core.IR.Method ValKind OpExt
abbrev Program := Core.IR.Program ValKind OpExt
abbrev CFG := Core.CFG.Graph ValKind OpExt

private def mapSvmPayload (mapValue : Val → Val) : Svm.Ops.OpExt Val → Svm.Ops.OpExt Val
  | .invoke programIx metas data seeds bump =>
      .invoke programIx metas (data.map (Svm.Ops.CpiWord.map mapValue)) seeds (bump.map mapValue)
  | .component call => .component (call.mapValues mapValue)

private def svmPayloadValues : Svm.Ops.OpExt Val → Array Val
  | .invoke _ _ data _ bump =>
      data.filterMap Svm.Ops.CpiWord.value? ++ match bump with
        | some value => #[value]
        | none => #[]
  | .component call => call.values

private def mapEvmPayload (mapValue : Val → Val) : Evm.Ops.OpExt Val → Evm.Ops.OpExt Val
  | .component call => .component (call.mapValues mapValue)

private def evmPayloadValues : Evm.Ops.OpExt Val → Array Val
  | .component call => call.values

private def mapXrplPayload (_mapValue : Val → Val) : Wasm.Xrpl.Ops.OpExt Val → Wasm.Xrpl.Ops.OpExt Val
  | .reserved => .reserved

private def xrplPayloadValues : Wasm.Xrpl.Ops.OpExt Val → Array Val
  | .reserved => #[]

def OpExt.mapValues (mapValue : Val → Val) : OpExt Val → OpExt Val
  | .svm payload => .svm (mapSvmPayload mapValue payload)
  | .evm payload => .evm (mapEvmPayload mapValue payload)
  | .xrpl payload => .xrpl (mapXrplPayload mapValue payload)
  | .near payload =>
      match payload with
      | .logUtf8 message => .near (.logUtf8 message)
      | .logUtf8Bounded capacity message =>
          .near (.logUtf8Bounded capacity (message.map mapValue))
      | .storageUnregisteredLog account =>
          .near (.storageUnregisteredLog (account.map mapValue))
      | .nep297StringData standard version event capacity data =>
          .near (.nep297StringData standard version event capacity (data.map mapValue))
      | .nep141FtMint owner amountLo amountHi =>
          .near (.nep141FtMint (owner.map mapValue) (mapValue amountLo) (mapValue amountHi))
      | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
          .near (.nep141FtTransfer (oldOwner.map mapValue) (newOwner.map mapValue)
            (mapValue amountLo) (mapValue amountHi))
      | .nep141FtBurn owner amountLo amountHi =>
          .near (.nep141FtBurn (owner.map mapValue) (mapValue amountLo) (mapValue amountHi))
      | .nep141FtMintMemo memoCapacity owner amountLo amountHi memo =>
          .near (.nep141FtMintMemo memoCapacity (owner.map mapValue) (mapValue amountLo)
            (mapValue amountHi) (memo.map mapValue))
      | .nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo =>
          .near (.nep141FtTransferMemo memoCapacity (oldOwner.map mapValue)
            (newOwner.map mapValue) (mapValue amountLo) (mapValue amountHi) (memo.map mapValue))
      | .nep141FtBurnMemo memoCapacity owner amountLo amountHi memo =>
          .near (.nep141FtBurnMemo memoCapacity (owner.map mapValue) (mapValue amountLo)
            (mapValue amountHi) (memo.map mapValue))
      | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
          .near (.promiseFunctionCallDetached receiver method argsCapacity
            (arguments.map mapValue) (mapValue depositLo) (mapValue depositHi) (mapValue gas))
      | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
          .near (.promiseFunctionCallReturned receiver method argsCapacity
            (arguments.map mapValue) (mapValue depositLo) (mapValue depositHi) (mapValue gas))
      | .promiseTransferDetached receiver amountLo amountHi =>
          .near (.promiseTransferDetached receiver (mapValue amountLo) (mapValue amountHi))
      | .promiseTransferReturned receiver amountLo amountHi =>
          .near (.promiseTransferReturned receiver (mapValue amountLo) (mapValue amountHi))
      | .promiseTransferAccountDetached receiver amountLo amountHi =>
          .near (.promiseTransferAccountDetached (receiver.map mapValue)
            (mapValue amountLo) (mapValue amountHi))
      | .promiseTransferAccountReturned receiver amountLo amountHi =>
          .near (.promiseTransferAccountReturned (receiver.map mapValue)
            (mapValue amountLo) (mapValue amountHi))
      | .promiseFtOnTransferReturned receiver sender amountLo amountHi message =>
          .near (.promiseFtOnTransferReturned (receiver.map mapValue) (sender.map mapValue)
            (mapValue amountLo) (mapValue amountHi) (message.map mapValue))
      | .promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message =>
          .near (.promiseFtOnTransferThenResolveReturned (receiver.map mapValue)
            (sender.map mapValue) (mapValue amountLo) (mapValue amountHi) (message.map mapValue))
      | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
          childArgsCapacity callbackArgsCapacity childArguments callbackArguments
          childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
          .near (.promiseFunctionCallThenReturned receiver childMethod callbackMethod
            childArgsCapacity callbackArgsCapacity (childArguments.map mapValue)
            (callbackArguments.map mapValue) (mapValue childDepositLo) (mapValue childDepositHi)
            (mapValue childGas) (mapValue callbackDepositLo) (mapValue callbackDepositHi)
            (mapValue callbackGas))
      | .promiseFunctionCallAndThenReturned
          leftReceiver leftMethod rightReceiver rightMethod callbackMethod
          leftArgsCapacity rightArgsCapacity callbackArgsCapacity
          leftArguments rightArguments callbackArguments
          leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
          callbackDepositLo callbackDepositHi callbackGas =>
          .near (.promiseFunctionCallAndThenReturned
            leftReceiver leftMethod rightReceiver rightMethod callbackMethod
            leftArgsCapacity rightArgsCapacity callbackArgsCapacity
            (leftArguments.map mapValue) (rightArguments.map mapValue)
            (callbackArguments.map mapValue)
            (mapValue leftDepositLo) (mapValue leftDepositHi) (mapValue leftGas)
            (mapValue rightDepositLo) (mapValue rightDepositHi) (mapValue rightGas)
            (mapValue callbackDepositLo) (mapValue callbackDepositHi) (mapValue callbackGas))
      | .promiseResultRead capacity index =>
          .near (.promiseResultRead capacity (mapValue index))
      | .transientBuffer64Begin capacity => .near (.transientBuffer64Begin capacity)
      | .transientBuffer64Set capacity index value =>
          .near (.transientBuffer64Set capacity (mapValue index) (mapValue value))
      | .transientBuffer64Finish capacity => .near (.transientBuffer64Finish capacity)
      | .storageRead resultCapacity keyCapacity key =>
          .near (.storageRead resultCapacity keyCapacity (key.map mapValue))
      | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
          .near (.storageWrite resultCapacity keyCapacity valueCapacity
            (key.map mapValue) (value.map mapValue))
      | .storageRemove resultCapacity keyCapacity key =>
          .near (.storageRemove resultCapacity keyCapacity (key.map mapValue))
      | .storageHasKey resultCapacity keyCapacity key =>
          .near (.storageHasKey resultCapacity keyCapacity (key.map mapValue))
      | .reserved => .near .reserved

def OpExt.values : OpExt Val → Array Val
  | .svm payload => svmPayloadValues payload
  | .evm payload => evmPayloadValues payload
  | .xrpl payload => xrplPayloadValues payload
  | .near payload =>
      match payload with
      | .logUtf8 _ => #[]
      | .logUtf8Bounded _ message => message
      | .storageUnregisteredLog account => account
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
      | .promiseTransferAccountDetached receiver amountLo amountHi
      | .promiseTransferAccountReturned receiver amountLo amountHi =>
          receiver ++ #[amountLo, amountHi]
      | .promiseFtOnTransferReturned receiver sender amountLo amountHi message =>
          receiver ++ sender ++ #[amountLo, amountHi] ++ message
      | .promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message =>
          receiver ++ sender ++ #[amountLo, amountHi] ++ message
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
  mapValues := OpExt.mapValues
  values := OpExt.values
  payloadEq := fun left right => left == right

/-- Build and optimize the shared target-neutral CFG for one extracted method. -/
def toCFG (ops : Array Op) : Except String CFG := do
  let graph ← Core.CFG.lower cfgDialect ops
  Core.CFG.optimize cfgDialect graph

def methodToCFG (method : Method) : Except String CFG := do
  let graph ←
    if method.kind == .init then Core.CFG.lowerInit cfgDialect method.ops
    else Core.CFG.lower cfgDialect method.ops
  Core.CFG.optimize cfgDialect graph

private def svmExtWellFormed : Svm.Ops.OpExt Val → Bool
  | .invoke _ _ data _ bump =>
      data.all (fun word => word.value?.all (·.wellFormed ValKind.arity)) &&
      match bump with
      | some value => value.wellFormed ValKind.arity
      | none => true
  | .component call =>
      call.wellFormed (·.wellFormed ValKind.arity) Svm.Ops.maxTxAccountLocks

private def evmExtWellFormed : Evm.Ops.OpExt Val → Bool
  | .component call => call.wellFormed (·.wellFormed ValKind.arity)

private def xrplExtWellFormed : Wasm.Xrpl.Ops.OpExt Val → Bool
  | .reserved => false

def OpExt.wellFormed : OpExt Val → Bool
  | .svm payload => svmExtWellFormed payload
  | .evm payload => evmExtWellFormed payload
  | .xrpl payload => xrplExtWellFormed payload
  | .near payload =>
      match payload with
      | .logUtf8 message => message.toUTF8.size ≤ 1024
      | .logUtf8Bounded capacity message =>
          Wasm.Near.Codec.storageCapacityValid capacity &&
            message.size == capacity + 1 &&
            message.all (·.wellFormed ValKind.arity)
      | .storageUnregisteredLog account =>
          account.size == 9 && account.all (·.wellFormed ValKind.arity)
      | .nep297StringData standard version event capacity data =>
          standard.toUTF8.size ≤ 64 && version.toUTF8.size ≤ 64 && event.toUTF8.size ≤ 64 &&
            Wasm.Near.Codec.storageCapacityValid capacity && data.size == capacity + 1 &&
            data.all (·.wellFormed ValKind.arity)
      | .nep141FtMint owner amountLo amountHi =>
          owner.size == 9 && owner.all (·.wellFormed ValKind.arity) &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .nep141FtTransfer oldOwner newOwner amountLo amountHi =>
          oldOwner.size == 9 && oldOwner.all (·.wellFormed ValKind.arity) &&
            newOwner.size == 9 && newOwner.all (·.wellFormed ValKind.arity) &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .nep141FtBurn owner amountLo amountHi =>
          owner.size == 9 && owner.all (·.wellFormed ValKind.arity) &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .nep141FtMintMemo memoCapacity owner amountLo amountHi memo
      | .nep141FtBurnMemo memoCapacity owner amountLo amountHi memo =>
          owner.size == 9 && owner.all (·.wellFormed ValKind.arity) &&
            Wasm.Near.Codec.nep141MemoCapacityValid memoCapacity && memo.size == memoCapacity + 1 &&
            memo.all (·.wellFormed ValKind.arity) && amountLo.wellFormed ValKind.arity &&
            amountHi.wellFormed ValKind.arity
      | .nep141FtTransferMemo memoCapacity oldOwner newOwner amountLo amountHi memo =>
          oldOwner.size == 9 && oldOwner.all (·.wellFormed ValKind.arity) &&
            newOwner.size == 9 && newOwner.all (·.wellFormed ValKind.arity) &&
            Wasm.Near.Codec.nep141MemoCapacityValid memoCapacity && memo.size == memoCapacity + 1 &&
            memo.all (·.wellFormed ValKind.arity) && amountLo.wellFormed ValKind.arity &&
            amountHi.wellFormed ValKind.arity
      | .promiseFunctionCallDetached receiver method argsCapacity arguments depositLo depositHi gas =>
          Wasm.Near.Codec.accountIdLiteralValid receiver &&
            Wasm.Near.Codec.promiseMethodLiteralValid method &&
            Wasm.Near.Codec.storageCapacityValid argsCapacity &&
            arguments.size == argsCapacity + 1 &&
            arguments.all (·.wellFormed ValKind.arity) &&
            depositLo.wellFormed ValKind.arity && depositHi.wellFormed ValKind.arity &&
            gas.wellFormed ValKind.arity
      | .promiseFunctionCallReturned receiver method argsCapacity arguments depositLo depositHi gas =>
          Wasm.Near.Codec.accountIdLiteralValid receiver &&
            Wasm.Near.Codec.promiseMethodLiteralValid method &&
            Wasm.Near.Codec.storageCapacityValid argsCapacity &&
            arguments.size == argsCapacity + 1 &&
            arguments.all (·.wellFormed ValKind.arity) &&
            depositLo.wellFormed ValKind.arity && depositHi.wellFormed ValKind.arity &&
            gas.wellFormed ValKind.arity
      | .promiseFtOnTransferReturned receiver sender amountLo amountHi message =>
          receiver.size == 9 && receiver.all (·.wellFormed ValKind.arity) &&
            sender.size == 9 && sender.all (·.wellFormed ValKind.arity) &&
            message.size == 9 && message.all (·.wellFormed ValKind.arity) &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .promiseFtOnTransferThenResolveReturned receiver sender amountLo amountHi message =>
          receiver.size == 9 && receiver.all (·.wellFormed ValKind.arity) &&
            sender.size == 9 && sender.all (·.wellFormed ValKind.arity) &&
            message.size == 9 && message.all (·.wellFormed ValKind.arity) &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .promiseTransferDetached receiver amountLo amountHi
      | .promiseTransferReturned receiver amountLo amountHi =>
          Wasm.Near.Codec.accountIdLiteralValid receiver &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .promiseTransferAccountDetached receiver amountLo amountHi
      | .promiseTransferAccountReturned receiver amountLo amountHi =>
          receiver.size == 9 && receiver.all (·.wellFormed ValKind.arity) &&
            amountLo.wellFormed ValKind.arity && amountHi.wellFormed ValKind.arity
      | .promiseFunctionCallThenReturned receiver childMethod callbackMethod
          childArgsCapacity callbackArgsCapacity childArguments callbackArguments
          childDepositLo childDepositHi childGas callbackDepositLo callbackDepositHi callbackGas =>
          Wasm.Near.Codec.accountIdLiteralValid receiver &&
            Wasm.Near.Codec.promiseMethodLiteralValid childMethod &&
            Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
            Wasm.Near.Codec.storageCapacityValid childArgsCapacity &&
            Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity &&
            childArguments.size == childArgsCapacity + 1 &&
            callbackArguments.size == callbackArgsCapacity + 1 &&
            childArguments.all (·.wellFormed ValKind.arity) &&
            callbackArguments.all (·.wellFormed ValKind.arity) &&
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
          Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
            Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
            Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
            Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
            Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
            Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
            Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
            Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity &&
            leftArguments.size == leftArgsCapacity + 1 &&
            rightArguments.size == rightArgsCapacity + 1 &&
            callbackArguments.size == callbackArgsCapacity + 1 &&
            (leftArguments ++ rightArguments ++ callbackArguments ++
              #[leftDepositLo, leftDepositHi, leftGas, rightDepositLo, rightDepositHi, rightGas,
                callbackDepositLo, callbackDepositHi, callbackGas]).all
              (·.wellFormed ValKind.arity)
      | .promiseResultRead capacity index =>
          Wasm.Near.Codec.storageCapacityValid capacity &&
            index.wellFormed ValKind.arity
      | .transientBuffer64Begin capacity | .transientBuffer64Finish capacity =>
          Wasm.Near.Memory.buffer64CapacityValid capacity
      | .transientBuffer64Set capacity index value =>
          Wasm.Near.Memory.buffer64CapacityValid capacity &&
            index.wellFormed ValKind.arity && value.wellFormed ValKind.arity
      | .storageRead resultCapacity keyCapacity key
      | .storageRemove resultCapacity keyCapacity key
      | .storageHasKey resultCapacity keyCapacity key =>
          Wasm.Near.Codec.storageCapacityValid resultCapacity &&
            Wasm.Near.Codec.rawStorageKeyCapacityValid keyCapacity &&
            key.size == keyCapacity + 1 && key.all (·.wellFormed ValKind.arity)
      | .storageWrite resultCapacity keyCapacity valueCapacity key value =>
          Wasm.Near.Codec.storageCapacityValid resultCapacity &&
            Wasm.Near.Codec.rawStorageKeyCapacityValid keyCapacity &&
            Wasm.Near.Codec.storageCapacityValid valueCapacity &&
            key.size == keyCapacity + 1 && value.size == valueCapacity + 1 &&
            key.all (·.wellFormed ValKind.arity) && value.all (·.wellFormed ValKind.arity)
      | .reserved => false

def Op.wellFormed (op : Op) : Bool :=
  Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

end ProofForge.Extract.IR
