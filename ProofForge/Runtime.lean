import ProofForge.Svm.Runtime
import ProofForge.Evm.Runtime

/-!
链上宿主 stub 按 target 分目录：

* `ProofForge.Svm.Runtime` — sysvar / AccountInfo / CPI
* `ProofForge.Evm.Runtime` — opcode / hashed map / LOG / 封闭 ERC-20

这个模块把两边再挂到旧名 `ProofForge.Runtime.*`，
现有 `open ProofForge.Runtime` 例子才能继续编过。
新代码应直接 `open ProofForge.Svm.Runtime` 或
`open ProofForge.Evm.Runtime`。
-/
namespace ProofForge.Runtime

def clockSlot : UInt64 := ProofForge.Svm.Runtime.clockSlot
def clockEpoch : UInt64 := ProofForge.Svm.Runtime.clockEpoch
def unixTime : UInt64 := ProofForge.Svm.Runtime.unixTime
def rentExemption (dataLen : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.rentExemption dataLen
def slotsPerEpoch : UInt64 := ProofForge.Svm.Runtime.slotsPerEpoch
def signerKey0 : UInt64 := ProofForge.Svm.Runtime.signerKey0

structure CpiMeta where
  acc : UInt64
  signer : Bool := false
  writable : Bool := false
  deriving Repr, DecidableEq, Inhabited

inductive CpiWord where
  | u8le (n : UInt64)
  | u32le (n : UInt64)
  | u64le (v : UInt64)
  | ascii (s : String)
  | programId
  | accKey (i : UInt64)
  deriving Repr, Inhabited

def invoke (programIx : UInt64) (metas : Array CpiMeta) (data : Array CpiWord) :
    UInt64 :=
  ProofForge.Svm.Runtime.invoke programIx
    (metas.map fun m =>
      { acc := m.acc, signer := m.signer, writable := m.writable })
    (data.map fun
      | .u8le n => .u8le n
      | .u32le n => .u32le n
      | .u64le v => .u64le v
      | .ascii s => .ascii s
      | .programId => .programId
      | .accKey i => .accKey i)

def invokeSigned (programIx : UInt64) (metas : Array CpiMeta)
    (data : Array CpiWord) (seed : String) (bump : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.invokeSigned programIx
    (metas.map fun m =>
      { acc := m.acc, signer := m.signer, writable := m.writable })
    (data.map fun
      | .u8le n => .u8le n
      | .u32le n => .u32le n
      | .u64le v => .u64le v
      | .ascii s => .ascii s
      | .programId => .programId
      | .accKey i => .accKey i)
    seed bump

def systemTransfer (lamports : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemTransfer lamports
def invokeAcc1 : UInt64 := ProofForge.Svm.Runtime.invokeAcc1
def systemCreate (lamports space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemCreate lamports space
def systemAssign : UInt64 := ProofForge.Svm.Runtime.systemAssign
def systemAllocate (space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemAllocate space
def systemAllocateWithSeed (space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemAllocateWithSeed space
def systemCreateWithSeed (lamports space : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemCreateWithSeed lamports space
def systemAssignWithSeed : UInt64 := ProofForge.Svm.Runtime.systemAssignWithSeed
def systemTransferWithSeed (lamports : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.systemTransferWithSeed lamports
def tokenInitMint : UInt64 := ProofForge.Svm.Runtime.tokenInitMint
def tokenSyncNative : UInt64 := ProofForge.Svm.Runtime.tokenSyncNative
def tokenTransferChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenTransferChecked amount decimals
def tokenMintToChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenMintToChecked amount decimals
def tokenBurnChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenBurnChecked amount decimals
def tokenInitAccount : UInt64 := ProofForge.Svm.Runtime.tokenInitAccount
def tokenCloseAccount : UInt64 := ProofForge.Svm.Runtime.tokenCloseAccount
def tokenApproveChecked (amount decimals : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenApproveChecked amount decimals
def tokenFreezeAccount : UInt64 := ProofForge.Svm.Runtime.tokenFreezeAccount
def tokenThawAccount : UInt64 := ProofForge.Svm.Runtime.tokenThawAccount
def tokenSetMintAuthority : UInt64 := ProofForge.Svm.Runtime.tokenSetMintAuthority
def tokenSetAccountAuthority : UInt64 :=
  ProofForge.Svm.Runtime.tokenSetAccountAuthority
def tokenApprove (amount : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.tokenApprove amount
def tokenInitMultisig : UInt64 := ProofForge.Svm.Runtime.tokenInitMultisig
def systemAdvanceNonce : UInt64 := ProofForge.Svm.Runtime.systemAdvanceNonce
def tokenRevoke : UInt64 := ProofForge.Svm.Runtime.tokenRevoke
def cpiReturn : UInt64 := ProofForge.Svm.Runtime.cpiReturn
def tokenAccountSize : UInt64 := ProofForge.Svm.Runtime.tokenAccountSize
def memoWrite : UInt64 := ProofForge.Svm.Runtime.memoWrite
def ataCreateIdempotent : UInt64 := ProofForge.Svm.Runtime.ataCreateIdempotent
def findPda (seed : String) : UInt64 := ProofForge.Svm.Runtime.findPda seed
def checkPda (seed : String) (bump : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.checkPda seed bump
def createPda (lamports : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.createPda lamports
def accLamports0 : UInt64 := ProofForge.Svm.Runtime.accLamports0
def accOwner0 : UInt64 := ProofForge.Svm.Runtime.accOwner0
def accDataLen0 : UInt64 := ProofForge.Svm.Runtime.accDataLen0
def accN : UInt64 := ProofForge.Svm.Runtime.accN
def isSigner0 : UInt64 := ProofForge.Svm.Runtime.isSigner0
def isWritable0 : UInt64 := ProofForge.Svm.Runtime.isWritable0
def isExecutable0 : UInt64 := ProofForge.Svm.Runtime.isExecutable0
def accLamports1 : UInt64 := ProofForge.Svm.Runtime.accLamports1
def accOwner1 : UInt64 := ProofForge.Svm.Runtime.accOwner1
def accDataLen1 : UInt64 := ProofForge.Svm.Runtime.accDataLen1
def isSigner1 : UInt64 := ProofForge.Svm.Runtime.isSigner1
def isWritable1 : UInt64 := ProofForge.Svm.Runtime.isWritable1
def isExecutable1 : UInt64 := ProofForge.Svm.Runtime.isExecutable1
def sha256Lit (seed : String) : UInt64 := ProofForge.Svm.Runtime.sha256Lit seed
def keccak256Lit (seed : String) : UInt64 :=
  ProofForge.Svm.Runtime.keccak256Lit seed
def accKeyWord (acc word : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.accKeyWord acc word
def accOwnerWord (acc word : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.accOwnerWord acc word
def accLamports (acc : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.accLamports acc
def accDataLen (acc : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.accDataLen acc
def isSigner (acc : UInt64) : UInt64 := ProofForge.Svm.Runtime.isSigner acc
def isWritable (acc : UInt64) : UInt64 := ProofForge.Svm.Runtime.isWritable acc
def isExecutable (acc : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.isExecutable acc
def signerKey (acc : UInt64) : UInt64 := ProofForge.Svm.Runtime.signerKey acc
def ownerIsSelf (acc : UInt64) : UInt64 :=
  ProofForge.Svm.Runtime.ownerIsSelf acc

def evmCaller : UInt64 := ProofForge.Evm.Runtime.evmCaller
def evmBlockNumber : UInt64 := ProofForge.Evm.Runtime.evmBlockNumber
def evmTimestamp : UInt64 := ProofForge.Evm.Runtime.evmTimestamp
def evmChainId : UInt64 := ProofForge.Evm.Runtime.evmChainId
def evmSelf : UInt64 := ProofForge.Evm.Runtime.evmSelf
def evmCallValue : UInt64 := ProofForge.Evm.Runtime.evmCallValue
def evmSelfBalance : UInt64 := ProofForge.Evm.Runtime.evmSelfBalance
def evmCallerW0 : UInt64 := ProofForge.Evm.Runtime.evmCallerW0
def evmCallerW1 : UInt64 := ProofForge.Evm.Runtime.evmCallerW1
def evmCallerW2 : UInt64 := ProofForge.Evm.Runtime.evmCallerW2
def evmSelfW0 : UInt64 := ProofForge.Evm.Runtime.evmSelfW0
def evmSelfW1 : UInt64 := ProofForge.Evm.Runtime.evmSelfW1
def evmSelfW2 : UInt64 := ProofForge.Evm.Runtime.evmSelfW2
def evmDeposit (amt : UInt64) : UInt64 := ProofForge.Evm.Runtime.evmDeposit amt
def evmSendEth (w0 w1 w2 amt : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmSendEth w0 w1 w2 amt
def evmLogTipped (amt : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmLogTipped amt
def evmLogIncremented (amt : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmLogIncremented amt
def evmLogTransfer (amt : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmLogTransfer amt
def evmLogApproval (amt : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmLogApproval amt
def evmMapGetU64 (base key : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmMapGetU64 base key
def evmMapSetU64 (base key val : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmMapSetU64 base key val
def evmMapGetAddr (base w0 w1 w2 : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmMapGetAddr base w0 w1 w2
def evmMapSetAddr (base w0 w1 w2 val : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmMapSetAddr base w0 w1 w2 val
def evmMapGetPair (base o0 o1 o2 s0 s1 s2 : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmMapGetPair base o0 o1 o2 s0 s1 s2
def evmMapSetPair (base o0 o1 o2 s0 s1 s2 val : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmMapSetPair base o0 o1 o2 s0 s1 s2 val
def evmTokenTransfer (tw0 tw1 tw2 dw0 dw1 dw2 amt : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amt
def evmTokenBalanceOfSelf (tw0 tw1 tw2 : UInt64) : UInt64 :=
  ProofForge.Evm.Runtime.evmTokenBalanceOfSelf tw0 tw1 tw2

end ProofForge.Runtime
