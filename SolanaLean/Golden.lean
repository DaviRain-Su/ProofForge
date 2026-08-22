import SolanaLean.IR
import SolanaLean.Ops

namespace SolanaLean.Golden

open SolanaLean.IR
open SolanaLean.Ops

def extractedCounter : Program :=
  { name := "Counter"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "Examples.Counter.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Counter.increment", ixName := "increment", paramCount := 1
        ops := #[
          .checkedAddU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .increment, name := "Examples.Counter.decrement", ixName := "decrement", paramCount := 1
        ops := #[
          .checkedSubU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Counter.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "value")] },
      { kind := .increment, name := "Examples.Counter.scale", ixName := "scale", paramCount := 1
        ops := #[
          .ite .eq (.arg 0) (.lit 0)
            #[.okState (.lit 0)]
            #[.checkedMulU64 (.field (.arg 1) "value") (.arg 0), .okState (.arg 0), .errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Counter.divide", ixName := "divide", paramCount := 1
        ops := #[.checkedDivU64 (.field (.arg 1) "value") (.arg 0), .okState (.arg 0), .errorOverflow] },
      { kind := .increment, name := "Examples.Counter.modulo", ixName := "modulo", paramCount := 1
        ops := #[.checkedModU64 (.field (.arg 1) "value") (.arg 0), .okState (.arg 0), .errorOverflow] },
      { kind := .get, name := "Examples.Counter.nonzero", ixName := "nonzero", paramCount := 0
        ops := #[
          .ite .eq (.field (.arg 0) "value") (.lit 0)
            #[.returnU64 (.lit 1)]
            #[.returnU64 (.lit 0)]
        ] }
    ] }

def extractedPair : Program :=
  { name := "Pair"
    slots := #[{ name := "left" }, { name := "right" }]
    methods := #[
      { kind := .init, name := "Examples.Pair.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .init, name := "Examples.Pair.initBoth", ixName := "initBoth", paramCount := 2
        ops := #[.returnState (.arg 0), .returnState (.arg 1)] },
      { kind := .increment, name := "Examples.Pair.creditLeft", ixName := "creditLeft", paramCount := 1
        ops := #[
          .checkedAddU64 (.field (.arg 1) "left") (.arg 0),
          .okState (.field (.arg 2) "right"),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Pair.getLeft", ixName := "getLeft", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "left")] },
      { kind := .get, name := "Examples.Pair.getRight", ixName := "getRight", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "right")] }
    ] }

def extractedFlag : Program :=
  { name := "Flag"
    slots := #[{ name := "flag", width := 1, abi := "u8-le" }, { name := "count" }]
    methods := #[
      { kind := .init, name := "Examples.Flag.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0), .returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Flag.setFlag", ixName := "setFlag", paramCount := 1
        ops := #[
          .ite .le (.arg 0) (.lit 255)
            #[.okState (.field (.arg 2) "count")]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Flag.getFlag", ixName := "getFlag", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "flag")] }
    ] }

def extractedPhase : Program :=
  { name := "Phase"
    slots := #[{ name := "mode" }]
    methods := #[
      { kind := .init, name := "Examples.Phase.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Phase.setIdle", ixName := "setIdle", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Phase.setLive", ixName := "setLive", paramCount := 1
        ops := #[
          .ite .le (.arg 0) (.lit (~~~(0 : UInt64)))
            #[.okState (.lit 1)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Phase.isLive", ixName := "isLive", paramCount := 0
        ops := #[
          .ite .eq (.field (.arg 0) "mode") (.lit 1)
            #[.returnU64 (.lit 1)]
            #[.returnU64 (.lit 0)]
        ] }
    ] }

def extractedWindow : Program :=
  { name := "Window"
    slots := #[{ name := "cells_0" }, { name := "cells_1" }]
    methods := #[
      { kind := .init, name := "Examples.Window.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Window.setTail", ixName := "setTail", paramCount := 1
        ops := #[
          .ite .le (.arg 0) (.lit (~~~(0 : UInt64)))
            #[.okState (.field (.arg 0) "cells_1")]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Window.getHead", ixName := "getHead", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "cells_0")] }
    ] }

def extractedMaybe : Program :=
  { name := "Maybe"
    slots := #[{ name := "slot_tag" }, { name := "slot_p0" }]
    methods := #[
      { kind := .init, name := "Examples.Maybe.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Maybe.setNone", ixName := "setNone", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Maybe.setSome", ixName := "setSome", paramCount := 1
        ops := #[
          .ite .le (.arg 0) (.lit (~~~(0 : UInt64)))
            #[.okState (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Maybe.isSome", ixName := "isSome", paramCount := 0
        ops := #[
          .ite .eq (.field (.arg 0) "slot_tag") (.lit 1)
            #[.returnU64 (.lit 1)]
            #[.returnU64 (.lit 0)]
        ] },
      { kind := .get, name := "Examples.Maybe.getValue", ixName := "getValue", paramCount := 0
        ops := #[
          .ite .eq (.field (.arg 0) "slot_tag") (.lit 0)
            #[.returnU64 (.lit 0)]
            #[.returnU64 (.field (.arg 0) "slot_p0")]
        ] }
    ] }

def extractedChoice : Program :=
  { name := "Choice"
    slots := #[{ name := "pick_tag" }, { name := "pick_p0" }]
    methods := #[
      { kind := .init, name := "Examples.Choice.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Choice.setEmpty", ixName := "setEmpty", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Choice.setHold", ixName := "setHold", paramCount := 1
        ops := #[
          .ite .le (.arg 0) (.lit (~~~(0 : UInt64)))
            #[.okState (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Choice.getHeld", ixName := "getHeld", paramCount := 0
        ops := #[
          .ite .eq (.field (.arg 0) "pick_tag") (.lit 0)
            #[.returnU64 (.lit 0)]
            #[.returnU64 (.field (.arg 0) "pick_p0")]
        ] }
    ] }

def extractedClock : Program :=
  { name := "Clock"
    slots := #[{ name := "stamped" }]
    methods := #[
      { kind := .init, name := "Examples.Clock.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Clock.stamp", ixName := "stamp", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState .clockSlot]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Clock.height", ixName := "height", paramCount := 0
        ops := #[.returnU64 .clockSlot] },
      { kind := .get, name := "Examples.Clock.era", ixName := "era", paramCount := 0
        ops := #[.returnU64 .clockEpoch] },
      { kind := .get, name := "Examples.Clock.key0", ixName := "key0", paramCount := 0
        ops := #[.returnU64 .signerKey0] },
      { kind := .get, name := "Examples.Clock.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "stamped")] }
    ] }

def extractedTransfer : Program :=
  { name := "Transfer"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Transfer.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Transfer.transfer", ixName := "transfer", paramCount := 1
        ops := #[Ops.systemTransfer (.arg 0), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Transfer.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedPing : Program :=
  { name := "Ping"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Ping.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Ping.ping", ixName := "ping", paramCount := 0
        ops := #[Ops.invokeAcc1, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Ping.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedCall : Program :=
  { name := "Call"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Call.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Call.call", ixName := "call", paramCount := 0
        ops := #[.invoke 1 #[] #[], .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Call.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedInfo : Program :=
  { name := "Info"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Info.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Info.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Info.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Info.lamports", ixName := "lamports", paramCount := 0
        ops := #[.returnU64 .accLamports0] },
      { kind := .get, name := "Examples.Info.owner0", ixName := "owner0", paramCount := 0
        ops := #[.returnU64 .accOwner0] },
      { kind := .get, name := "Examples.Info.dataLen", ixName := "dataLen", paramCount := 0
        ops := #[.returnU64 .accDataLen0] },
      { kind := .get, name := "Examples.Info.nacc", ixName := "nacc", paramCount := 0
        ops := #[.returnU64 .accN] },
      { kind := .get, name := "Examples.Info.signer", ixName := "signer", paramCount := 0
        ops := #[.returnU64 .isSigner0] },
      { kind := .get, name := "Examples.Info.writable", ixName := "writable", paramCount := 0
        ops := #[.returnU64 .isWritable0] },
      { kind := .get, name := "Examples.Info.executable", ixName := "executable", paramCount := 0
        ops := #[.returnU64 .isExecutable0] }
    ] }

def extractedSigned : Program :=
  { name := "Signed"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Signed.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Signed.signed", ixName := "signed", paramCount := 0
        ops := #[.invoke 1 #[] #[] (some "vault") (some (.findPda "vault")),
          .returnU64 (.lit 0)] },
      { kind := .increment, name := "Examples.Signed.badBump", ixName := "badBump", paramCount := 0
        ops := #[.invoke 1 #[] #[] (some "vault") (some (.lit 0)),
          .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Signed.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedCreate : Program :=
  { name := "Create"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Create.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Create.create", ixName := "create", paramCount := 1
        ops := #[Ops.systemCreate (.arg 0) (.lit 16), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Create.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenXfer : Program :=
  { name := "TokenXfer"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenXfer.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenXfer.send", ixName := "send", paramCount := 1
        ops := #[Ops.tokenTransferChecked (.arg 0) 6, .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.TokenXfer.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenApprove : Program :=
  { name := "TokenApprove"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenApprove.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenApprove.approve", ixName := "approve", paramCount := 1
        ops := #[Ops.tokenApproveChecked (.arg 0) 6, .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.TokenApprove.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenAuth : Program :=
  { name := "TokenAuth"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenAuth.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenAuth.setAuth", ixName := "setAuth", paramCount := 0
        ops := #[Ops.tokenSetMintAuthority, .returnU64 (.lit 0)] },
      { kind := .increment, name := "Examples.TokenAuth.revoke", ixName := "revoke", paramCount := 0
        ops := #[Ops.tokenRevoke, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenAuth.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenFreeze : Program :=
  { name := "TokenFreeze"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenFreeze.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenFreeze.freeze", ixName := "freeze", paramCount := 0
        ops := #[Ops.tokenFreezeAccount, .returnU64 (.lit 0)] },
      { kind := .increment, name := "Examples.TokenFreeze.thaw", ixName := "thaw", paramCount := 0
        ops := #[Ops.tokenThawAccount, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenFreeze.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedCreatePda : Program :=
  { name := "CreatePda"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.CreatePda.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.CreatePda.openPda", ixName := "openPda", paramCount := 1
        ops := #[Ops.createPda (.arg 0), .returnU64 (.arg 0)] },
      { kind := .increment, name := "Examples.CreatePda.openBad", ixName := "openBad", paramCount := 1
        ops := #[
          .invoke 2
            #[{ acc := 0, signer := true, writable := true },
              { acc := 1, signer := true, writable := true }]
            #[.u32le 0, .u64le (.arg 0), .u64le (.lit 16), .programId]
            (some "vault") (some (.lit 0)),
          .returnU64 (.arg 0)
        ] },
      { kind := .get, name := "Examples.CreatePda.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedMemo : Program :=
  { name := "Memo"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Memo.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Memo.write", ixName := "write", paramCount := 0
        ops := #[Ops.memoWrite, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Memo.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenAcc : Program :=
  { name := "TokenAcc"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenAcc.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenAcc.openAcc", ixName := "openAcc", paramCount := 0
        ops := #[Ops.tokenInitAccount, .returnU64 (.lit 0)] },
      { kind := .increment, name := "Examples.TokenAcc.closeAcc", ixName := "closeAcc", paramCount := 0
        ops := #[Ops.tokenCloseAccount, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenAcc.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedSysAlloc : Program :=
  { name := "SysAlloc"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.SysAlloc.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.SysAlloc.alloc", ixName := "alloc", paramCount := 0
        ops := #[Ops.systemAllocate (.lit 16), .returnU64 (.lit 16)] },
      { kind := .increment, name := "Examples.SysAlloc.assign", ixName := "assign", paramCount := 0
        ops := #[Ops.systemAssign, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.SysAlloc.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenMint : Program :=
  { name := "TokenMint"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenMint.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenMint.mintTo", ixName := "mintTo", paramCount := 1
        ops := #[Ops.tokenMintToChecked (.arg 0) 6, .returnU64 (.arg 0)] },
      { kind := .increment, name := "Examples.TokenMint.burn", ixName := "burn", paramCount := 1
        ops := #[Ops.tokenBurnChecked (.arg 0) 6, .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.TokenMint.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedSysSeed : Program :=
  { name := "SysSeed"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.SysSeed.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.SysSeed.openSeed", ixName := "openSeed", paramCount := 0
        ops := #[Ops.systemAllocateWithSeed (.lit 16), .returnU64 (.lit 16)] },
      { kind := .increment, name := "Examples.SysSeed.createSeed", ixName := "createSeed", paramCount := 1
        ops := #[Ops.systemCreateWithSeed (.arg 0) (.lit 16), .returnU64 (.arg 0)] },
      { kind := .increment, name := "Examples.SysSeed.assignSeed", ixName := "assignSeed", paramCount := 0
        ops := #[Ops.systemAssignWithSeed, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.SysSeed.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedSysXfer : Program :=
  { name := "SysXfer"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.SysXfer.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.SysXfer.sendSeed", ixName := "sendSeed", paramCount := 1
        ops := #[Ops.systemTransferWithSeed (.arg 0), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.SysXfer.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenMint2 : Program :=
  { name := "TokenMint2"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenMint2.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenMint2.openMint", ixName := "openMint", paramCount := 0
        ops := #[Ops.tokenInitMint, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenMint2.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenNative : Program :=
  { name := "TokenNative"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenNative.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenNative.syncNative", ixName := "syncNative", paramCount := 0
        ops := #[Ops.tokenSyncNative, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenNative.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenSize : Program :=
  { name := "TokenSize"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenSize.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenSize.size", ixName := "size", paramCount := 0
        ops := #[Ops.tokenAccountSize, .returnU64 .cpiReturn] },
      { kind := .get, name := "Examples.TokenSize.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedEpoch : Program :=
  { name := "Epoch"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Epoch.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Epoch.stamp", ixName := "stamp", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState .slotsPerEpoch]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Epoch.span", ixName := "span", paramCount := 0
        ops := #[.returnU64 .slotsPerEpoch] },
      { kind := .get, name := "Examples.Epoch.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "dummy")] }
    ] }

def extractedRent : Program :=
  { name := "Rent"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Rent.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Rent.stamp", ixName := "stamp", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.rentExemption 16)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Rent.exempt", ixName := "exempt", paramCount := 0
        ops := #[.returnU64 (.rentExemption 16)] },
      { kind := .get, name := "Examples.Rent.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "dummy")] }
    ] }

def extractedAta : Program :=
  { name := "Ata"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Ata.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Ata.openAta", ixName := "openAta", paramCount := 0
        ops := #[Ops.ataCreateIdempotent, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Ata.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedPda : Program :=
  { name := "Pda"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Pda.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Pda.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Pda.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Pda.bump", ixName := "bump", paramCount := 0
        ops := #[.returnU64 (.findPda "vault")] },
      { kind := .get, name := "Examples.Pda.check", ixName := "check", paramCount := 0
        ops := #[.returnU64 (.checkPda "vault" (.findPda "vault"))] },
      { kind := .get, name := "Examples.Pda.checkBad", ixName := "checkBad", paramCount := 0
        ops := #[.returnU64 (.checkPda "vault" (.lit 0))] }
    ] }

def programs : Array Program := #[
  extractedCounter, extractedPair, extractedFlag,
  extractedMaybe, extractedWindow, extractedPhase, extractedChoice,
  extractedClock, extractedTransfer, extractedPing, extractedCall, extractedInfo,
  extractedPda, extractedSigned, extractedCreate, extractedTokenXfer, extractedAta,
  extractedRent, extractedTokenMint, extractedSysAlloc, extractedTokenAcc, extractedMemo,
  extractedCreatePda, extractedTokenApprove, extractedTokenFreeze, extractedTokenAuth,
  extractedEpoch, extractedTokenSize, extractedSysSeed, extractedSysXfer, extractedTokenMint2,
  extractedTokenNative
]

/-- `#solana_build` 抽出的 digest 必须钉住。新例子加进 `programs`，不必改 IR。 -/
def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map digestHex

end SolanaLean.Golden
