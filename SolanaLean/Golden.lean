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
      { kind := .get, name := "Examples.Clock.key0", ixName := "key0", paramCount := 0
        ops := #[.returnU64 .signerKey0] },
      { kind := .get, name := "Examples.Clock.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "stamped")] }
    ] }

def extractedEvmCtx : Program :=
  { name := "EvmCtx"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.EvmCtx.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.EvmCtx.stamp", ixName := "stamp", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState .evmBlockNumber]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.EvmCtx.caller", ixName := "caller", paramCount := 0
        ops := #[.returnU64 .evmCaller] },
      { kind := .get, name := "Examples.EvmCtx.height", ixName := "height", paramCount := 0
        ops := #[.returnU64 .evmBlockNumber] },
      { kind := .get, name := "Examples.EvmCtx.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "dummy")] }
    ] }

def extractedTransfer : Program :=
  { name := "Transfer"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Transfer.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Transfer.transfer", ixName := "transfer", paramCount := 1
        ops := #[.systemTransfer (.arg 0), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Transfer.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTipJar : Program :=
  { name := "TipJar"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TipJar.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TipJar.deposit", ixName := "deposit", paramCount := 1
        ops := #[.evmDeposit (.arg 0), .returnU64 (.arg 0)] },
      { kind := .increment, name := "Examples.TipJar.logTip", ixName := "logTip", paramCount := 1
        ops := #[.evmLogTipped (.arg 0), .returnU64 (.arg 0)] },
      { kind := .increment, name := "Examples.TipJar.payout", ixName := "payout", paramCount := 4
        ops := #[.evmSendEth (.arg 0) (.arg 1) (.arg 2) (.arg 3), .returnU64 (.arg 3)] },
      { kind := .get, name := "Examples.TipJar.callValue", ixName := "callValue", paramCount := 0
        ops := #[.returnU64 .evmCallValue] },
      { kind := .get, name := "Examples.TipJar.callerW0", ixName := "callerW0", paramCount := 0
        ops := #[.returnU64 .evmCallerW0] },
      { kind := .get, name := "Examples.TipJar.callerW1", ixName := "callerW1", paramCount := 0
        ops := #[.returnU64 .evmCallerW1] },
      { kind := .get, name := "Examples.TipJar.callerW2", ixName := "callerW2", paramCount := 0
        ops := #[.returnU64 .evmCallerW2] },
      { kind := .get, name := "Examples.TipJar.chainId", ixName := "chainId", paramCount := 0
        ops := #[.returnU64 .evmChainId] },
      { kind := .get, name := "Examples.TipJar.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TipJar.selfBal", ixName := "selfBal", paramCount := 0
        ops := #[.returnU64 .evmSelfBalance] },
      { kind := .get, name := "Examples.TipJar.selfLow", ixName := "selfLow", paramCount := 0
        ops := #[.returnU64 .evmSelf] },
      { kind := .get, name := "Examples.TipJar.selfW0", ixName := "selfW0", paramCount := 0
        ops := #[.returnU64 .evmSelfW0] },
      { kind := .get, name := "Examples.TipJar.selfW1", ixName := "selfW1", paramCount := 0
        ops := #[.returnU64 .evmSelfW1] },
      { kind := .get, name := "Examples.TipJar.selfW2", ixName := "selfW2", paramCount := 0
        ops := #[.returnU64 .evmSelfW2] },
      { kind := .get, name := "Examples.TipJar.timestamp", ixName := "timestamp", paramCount := 0
        ops := #[.returnU64 .evmTimestamp] }
    ] }

def programs : Array Program := #[
  extractedCounter, extractedPair, extractedFlag,
  extractedMaybe, extractedWindow, extractedPhase, extractedChoice,
  extractedClock, extractedTransfer, extractedEvmCtx, extractedTipJar
]

/-- `#solana_build` 抽出的 digest 必须钉住。新例子加进 `programs`，不必改 IR。 -/
def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map digestHex

end SolanaLean.Golden
