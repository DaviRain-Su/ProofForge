import ProofForge.Extract.LegacyIR
import ProofForge.Extract.LegacyOps

/-! Hand-authored fixtures for the legacy mixed extraction IR. -/
namespace ProofForge.Golden

open ProofForge.Extract.Legacy
open ProofForge.Ops

def extractedCounter : Program :=
  { name := "Counter"
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "Examples.Counter.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Counter.increment", ixName := "increment", paramCount := 1
        ops := #[
          .checkedAddU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.field (.arg 1) "value"),
          .errorOverflow
        ] },
      { kind := .increment, name := "Examples.Counter.decrement", ixName := "decrement", paramCount := 1
        ops := #[
          .checkedSubU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.field (.arg 1) "value"),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Counter.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "value")] },
      { kind := .increment, name := "Examples.Counter.scale", ixName := "scale", paramCount := 1
        ops := #[
          .ite .eq (.arg 0) (.lit 0)
            #[.okState (.lit 0)]
            #[.checkedMulU64 (.field (.arg 1) "value") (.arg 0), .okState (.field (.arg 1) "value"), .errorOverflow]
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
          .okState (.field (.arg 1) "left"),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Pair.getLeft", ixName := "getLeft", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "left")] },
      { kind := .get, name := "Examples.Pair.getRight", ixName := "getRight", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "right")] }
    ] }

def extractedNested : Program :=
  { name := "Nested"
    slots := #[{ name := "book_price" }, { name := "book_size" }, { name := "baseFree" }]
    methods := #[
      { kind := .init, name := "Examples.Nested.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Nested.postAsk", ixName := "postAsk", paramCount := 1
        ops := #[
          .checkedAddU64 (.field (.arg 1) "book_size") (.arg 0),
          .okState (.field (.arg 1) "book_size"),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Nested.askSize", ixName := "askSize", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "book_size")] },
      { kind := .get, name := "Examples.Nested.bestAsk", ixName := "bestAsk", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "book_price")] }
    ] }

def extractedTree : Program :=
  { name := "Tree"
    slots := #[
      { name := "root" }, { name := "size" },
      { name := "nodes_0_left" }, { name := "nodes_0_right" },
      { name := "nodes_0_parent" }, { name := "nodes_0_color" },
      { name := "nodes_0_key" }, { name := "nodes_0_value" },
      { name := "nodes_1_left" }, { name := "nodes_1_right" },
      { name := "nodes_1_parent" }, { name := "nodes_1_color" },
      { name := "nodes_1_key" }, { name := "nodes_1_value" },
      { name := "nodes_2_left" }, { name := "nodes_2_right" },
      { name := "nodes_2_parent" }, { name := "nodes_2_color" },
      { name := "nodes_2_key" }, { name := "nodes_2_value" },
      { name := "nodes_3_left" }, { name := "nodes_3_right" },
      { name := "nodes_3_parent" }, { name := "nodes_3_color" },
      { name := "nodes_3_key" }, { name := "nodes_3_value" }
    ]
    methods := #[
      { kind := .init, name := "Examples.Tree.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Tree.bumpInsert", ixName := "bumpInsert", paramCount := 2
        ops := #[
          .ite .eq (.field (.arg 2) "root") (.lit 0)
            #[.ite .eq (.field (.arg 2) "size") (.lit 0)
              #[
                .storeField "root" (.lit 1),
                .storeField "size" (.lit 1),
                .storeField "nodes_0_left" (.lit 0),
                .storeField "nodes_0_right" (.lit 0),
                .storeField "nodes_0_parent" (.lit 0),
                .storeField "nodes_0_color" (.lit 1),
                .storeField "nodes_0_key" (.arg 0),
                .storeField "nodes_0_value" (.arg 1),
                .okState (.arg 0)
              ]
              #[.errorOverflow]]
            #[.ite .eq (.field (.arg 2) "nodes_0_right") (.lit 0)
              #[.ite .lt (.field (.arg 2) "size") (.lit 4)
                #[
                  .storeField "size" (.addU64 (.field (.arg 2) "size") (.lit 1)),
                  .storeField "nodes_0_right" (.lit 2),
                  .storeField "nodes_1_left" (.lit 0),
                  .storeField "nodes_1_right" (.lit 0),
                  .storeField "nodes_1_parent" (.lit 1),
                  .storeField "nodes_1_color" (.lit 1),
                  .storeField "nodes_1_key" (.arg 0),
                  .storeField "nodes_1_value" (.arg 1),
                  .okState (.arg 0)
                ]
                #[.errorOverflow]]
              #[.errorOverflow]]
        ] },
      { kind := .increment, name := "Examples.Tree.setAt", ixName := "setAt", paramCount := 2
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.indexSet "nodes" (.arg 0) (.arg 1) 4 40, .okState (.arg 1)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Tree.setHead", ixName := "setHead", paramCount := 1
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.field (.arg 1) "nodes_0_value")]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Tree.setParent", ixName := "setParent", paramCount := 2
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.indexSet "nodes" (.arg 0) (.arg 1) 4 16, .okState (.arg 1)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Tree.setRight", ixName := "setRight", paramCount := 2
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.indexSet "nodes" (.arg 0) (.arg 1) 4 8, .okState (.arg 1)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Tree.rotateLeft", ixName := "rotateLeft", paramCount := 1
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.ite .ne
                (.indexGet (.arg 1) "nodes" (.arg 0) 0 8)
                (.lit 0)
                #[.ite .lt
                    (.subU64 (.indexGet (.arg 1) "nodes" (.arg 0) 0 8) (.lit 1))
                    (.lit 4)
                    #[
                      .indexSet "nodes" (.arg 0)
                        (.indexGet (.arg 1) "nodes"
                          (.subU64 (.indexGet (.arg 1) "nodes" (.arg 0) 0 8) (.lit 1)) 0 0)
                        4 8,
                      .indexSet "nodes"
                        (.subU64 (.indexGet (.arg 1) "nodes" (.arg 0) 0 8) (.lit 1))
                        (.addU64 (.arg 0) (.lit 1))
                        4 0,
                      .indexSet "nodes"
                        (.subU64 (.indexGet (.arg 1) "nodes" (.arg 0) 0 8) (.lit 1))
                        (.indexGet (.arg 1) "nodes" (.arg 0) 0 16)
                        4 16,
                      .okState (.indexGet (.arg 1) "nodes" (.arg 0) 0 8)
                    ]
                    #[.errorOverflow]]
                #[.errorOverflow]]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Tree.getAt", ixName := "getAt", paramCount := 1
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.returnU64 (.indexGet (.arg 1) "nodes" (.arg 0) 0 40)]
            #[.returnU64 (.lit 0)]
        ] },
      { kind := .get, name := "Examples.Tree.getRight", ixName := "getRight", paramCount := 1
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.returnU64 (.indexGet (.arg 1) "nodes" (.arg 0) 0 8)]
            #[.returnU64 (.lit 0)]
        ] },
      { kind := .get, name := "Examples.Tree.getHead", ixName := "getHead", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "nodes_0_value")] },
      { kind := .get, name := "Examples.Tree.getRoot", ixName := "getRoot", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "root")] },
      { kind := .get, name := "Examples.Tree.getSize", ixName := "getSize", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "size")] }
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
            #[.okState (.field (.arg 1) "count")]
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
            #[
              .storeField "pick_tag" (.lit 1),
              .storeField "pick_p0" (.arg 0),
              .okState (.arg 0)
            ]
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
        ops := #[Ops.systemTransfer (.arg 0), .returnU64 (.arg 0)] },
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
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmDeposit (.arg 0), .returnU64 (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.TipJar.logTip", ixName := "logTip", paramCount := 1
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmLog "Tipped" (.arg 0), .returnU64 (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.TipJar.payout", ixName := "payout", paramCount := 4
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmSendEth (.arg 0) (.arg 1) (.arg 2) (.arg 3), .returnU64 (.arg 3)]
            #[.errorOverflow]
        ] },
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

def extractedLang : Program :=
  { name := "Lang"
    slots := #[
      { name := "cells_0" }, { name := "cells_1" },
      { name := "cells_2" }, { name := "cells_3" }
    ]
    methods := #[
      { kind := .init, name := "Examples.Lang.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Lang.setAt", ixName := "setAt", paramCount := 2
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.indexSet "cells" (.arg 0) (.arg 1) 4, .okState (.arg 1)]
            #[.errorNamed "oob"]
        ] },
      { kind := .get, name := "Examples.Lang.band", ixName := "band", paramCount := 2
        ops := #[.returnU64 (.bitAnd (.arg 0) (.arg 1))] },
      { kind := .get, name := "Examples.Lang.bor", ixName := "bor", paramCount := 2
        ops := #[.returnU64 (.bitOr (.arg 0) (.arg 1))] },
      { kind := .get, name := "Examples.Lang.both", ixName := "both", paramCount := 0
        retCount := 2
        ops := #[
          .returnU64 (.field (.arg 0) "cells_0"),
          .returnU64 (.field (.arg 0) "cells_1")
        ] },
      { kind := .get, name := "Examples.Lang.bnot", ixName := "bnot", paramCount := 1
        ops := #[.returnU64 (.bitNot (.arg 0))] },
      { kind := .get, name := "Examples.Lang.bxor", ixName := "bxor", paramCount := 2
        ops := #[.returnU64 (.bitXor (.arg 0) (.arg 1))] },
      { kind := .get, name := "Examples.Lang.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "cells_0")] },
      { kind := .get, name := "Examples.Lang.getAt", ixName := "getAt", paramCount := 1
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.returnU64 (.indexGet (.arg 1) "cells" (.arg 0) 0)]
            #[.returnU64 (.lit 0)]
        ] },
      { kind := .get, name := "Examples.Lang.mask8", ixName := "mask8", paramCount := 1
        paramWidths := #[1]
        ops := #[.returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Lang.shl", ixName := "shl", paramCount := 2
        ops := #[.returnU64 (.shiftL (.arg 0) (.arg 1))] },
      { kind := .get, name := "Examples.Lang.shr", ixName := "shr", paramCount := 2
        ops := #[.returnU64 (.shiftR (.arg 0) (.arg 1))] },
      { kind := .get, name := "Examples.Lang.sum4", ixName := "sum4", paramCount := 0
        ops := #[
          .forAccum 4 (.indexGet (.arg 0) "cells" .loopIx 0),
          .returnU64 (.indexGet (.arg 0) "cells" .loopIx 0)
        ] }
    ] }

def extractedVault : Program :=
  { name := "Vault"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Vault.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Vault.credit", ixName := "credit", paramCount := 4
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.mapSetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2) (.arg 3), .returnU64 (.arg 3)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Vault.pull", ixName := "pull", paramCount := 7
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmTokenTransfer (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6),
              .returnU64 (.arg 6)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Vault.setU64", ixName := "setU64", paramCount := 2
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.mapSetU64 (.lit 0) (.arg 0) (.arg 1), .returnU64 (.arg 1)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Vault.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Vault.getU64", ixName := "getU64", paramCount := 1
        ops := #[.mapGetU64 (.lit 0) (.arg 0), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Vault.held", ixName := "held", paramCount := 3
        ops := #[.evmTokenBalanceOfSelf (.arg 0) (.arg 1) (.arg 2), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Vault.shareOf", ixName := "shareOf", paramCount := 3
        ops := #[.mapGetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2), .returnU64 (.arg 0)] }
    ] }

def extractedOwnable : Program :=
  { name := "Ownable"
    slots := #[
      { name := "owner0" }, { name := "owner1" },
      { name := "owner2" }, { name := "value" }
    ]
    methods := #[
      { kind := .init, name := "Examples.Ownable.init", ixName := "initialize", paramCount := 3
        ops := #[
          .returnState (.arg 0), .returnState (.arg 1),
          .returnState (.arg 2), .returnState (.lit 0)
        ] },
      { kind := .increment, name := "Examples.Ownable.approve", ixName := "approve", paramCount := 7
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.mapSetPair (.lit 0) (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6),
              .returnU64 (.arg 6)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Ownable.bump", ixName := "bump", paramCount := 1
        ops := #[
          .ite .eq .evmCallerW0 (.field (.arg 1) "owner0")
            #[.ite .eq .evmCallerW1 (.field (.arg 1) "owner1")
              #[.ite .eq .evmCallerW2 (.field (.arg 1) "owner2")
                #[.checkedAddU64 (.field (.arg 1) "value") (.arg 0),
                  .okState (.field (.arg 1) "value"), .errorOverflow]
                #[.errorNamed "unauthorized"]]
              #[.errorNamed "unauthorized"]]
            #[.errorNamed "unauthorized"]
        ] },
      { kind := .increment, name := "Examples.Ownable.logInc", ixName := "logInc", paramCount := 1
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmLog "Incremented" (.arg 0), .returnU64 (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Ownable.spend", ixName := "spend", paramCount := 7
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.mapSetPair (.lit 0) (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6),
              .returnU64 (.arg 6)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Ownable.allowance", ixName := "allowance", paramCount := 6
        ops := #[
          .mapGetPair (.lit 0) (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5),
          .returnU64 (.arg 0)
        ] },
      { kind := .get, name := "Examples.Ownable.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "value")] },
      { kind := .get, name := "Examples.Ownable.ownerW0", ixName := "ownerW0", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "owner0")] },
      { kind := .get, name := "Examples.Ownable.ownerW1", ixName := "ownerW1", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "owner1")] },
      { kind := .get, name := "Examples.Ownable.ownerW2", ixName := "ownerW2", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "owner2")] }
      ] }

def extractedToken : Program :=
  { name := "Token"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Token.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Token.approve", ixName := "approve", paramCount := 4
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.mapSetPair (.lit 1) .evmCallerW0 .evmCallerW1 .evmCallerW2
                (.arg 0) (.arg 1) (.arg 2) (.arg 3),
              .evmLog "Approval" (.arg 3), .returnU64 (.arg 3)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Token.logApprove", ixName := "logApprove", paramCount := 1
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmLog "Approval" (.arg 0), .returnU64 (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Token.logXfer", ixName := "logXfer", paramCount := 1
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.evmLog "Transfer" (.arg 0), .returnU64 (.arg 0)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Token.mint", ixName := "mint", paramCount := 4
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.mapSetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2) (.arg 3), .returnU64 (.arg 3)]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Token.transfer", ixName := "transfer", paramCount := 4
        ops := #[
          .ite .ge
            (.mapGetAddr (.lit 0) .evmCallerW0 .evmCallerW1 .evmCallerW2) (.arg 3)
            #[.mapSetAddr (.lit 0) .evmCallerW0 .evmCallerW1 .evmCallerW2
                (.subU64 (.mapGetAddr (.lit 0) .evmCallerW0 .evmCallerW1 .evmCallerW2) (.arg 3)),
              .mapSetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2)
                (.addU64 (.mapGetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2)) (.arg 3)),
              .evmLog "Transfer" (.arg 3), .returnU64 (.arg 3)]
            #[.errorNamed "insufficient"]
        ] },
      { kind := .increment, name := "Examples.Token.transferFrom", ixName := "transferFrom",
        paramCount := 7
        ops := #[
          .ite .ge
            (.mapGetPair (.lit 1) (.arg 0) (.arg 1) (.arg 2)
              .evmCallerW0 .evmCallerW1 .evmCallerW2) (.arg 6)
            #[.ite .ge
                (.mapGetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2)) (.arg 6)
                #[.mapSetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2)
                    (.subU64 (.mapGetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2)) (.arg 6)),
                  .mapSetAddr (.lit 0) (.arg 3) (.arg 4) (.arg 5)
                    (.addU64 (.mapGetAddr (.lit 0) (.arg 3) (.arg 4) (.arg 5)) (.arg 6)),
                  .mapSetPair (.lit 1) (.arg 0) (.arg 1) (.arg 2)
                    .evmCallerW0 .evmCallerW1 .evmCallerW2
                    (.subU64
                      (.mapGetPair (.lit 1) (.arg 0) (.arg 1) (.arg 2)
                        .evmCallerW0 .evmCallerW1 .evmCallerW2) (.arg 6)),
                  .evmLog "Transfer" (.arg 6), .returnU64 (.arg 6)]
                #[.errorNamed "insufficient"]]
            #[.errorNamed "insufficient"]
        ] },
      { kind := .get, name := "Examples.Token.allowanceOf", ixName := "allowanceOf", paramCount := 6
        ops := #[
          .mapGetPair (.lit 1) (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5),
          .returnU64 (.arg 0)
        ] },
      { kind := .get, name := "Examples.Token.balanceOf", ixName := "balanceOf", paramCount := 3
        ops := #[.mapGetAddr (.lit 0) (.arg 0) (.arg 1) (.arg 2), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Token.get", ixName := "get", paramCount := 0
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

def extractedPeer : Program :=
  { name := "Peer"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Peer.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Peer.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Peer.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Peer.lamports1", ixName := "lamports1", paramCount := 0
        ops := #[.returnU64 .accLamports1] },
      { kind := .get, name := "Examples.Peer.owner1", ixName := "owner1", paramCount := 0
        ops := #[.returnU64 .accOwner1] },
      { kind := .get, name := "Examples.Peer.dataLen1", ixName := "dataLen1", paramCount := 0
        ops := #[.returnU64 .accDataLen1] },
      { kind := .get, name := "Examples.Peer.signer1", ixName := "signer1", paramCount := 0
        ops := #[.returnU64 .isSigner1] },
      { kind := .get, name := "Examples.Peer.writable1", ixName := "writable1", paramCount := 0
        ops := #[.returnU64 .isWritable1] },
      { kind := .get, name := "Examples.Peer.executable1", ixName := "executable1", paramCount := 0
        ops := #[.returnU64 .isExecutable1] }
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

def extractedHash : Program :=
  { name := "Hash"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Hash.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Hash.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Hash.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Hash.vault", ixName := "vault", paramCount := 0
        ops := #[.returnU64 (.sha256Lit "vault")] },
      { kind := .get, name := "Examples.Hash.ok", ixName := "ok", paramCount := 0
        ops := #[.returnU64 (.sha256Lit "ok")] },
      { kind := .get, name := "Examples.Hash.empty", ixName := "empty", paramCount := 0
        ops := #[.returnU64 (.sha256Lit "")] }
    ] }

def extractedKeys : Program :=
  { name := "Keys"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Keys.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Keys.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Keys.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Keys.key00", ixName := "key00", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 0 0)] },
      { kind := .get, name := "Examples.Keys.key01", ixName := "key01", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 0 1)] },
      { kind := .get, name := "Examples.Keys.key02", ixName := "key02", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 0 2)] },
      { kind := .get, name := "Examples.Keys.key03", ixName := "key03", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 0 3)] },
      { kind := .get, name := "Examples.Keys.owner00", ixName := "owner00", paramCount := 0
        ops := #[.returnU64 (.accOwnerWord 0 0)] },
      { kind := .get, name := "Examples.Keys.owner03", ixName := "owner03", paramCount := 0
        ops := #[.returnU64 (.accOwnerWord 0 3)] },
      { kind := .get, name := "Examples.Keys.key10", ixName := "key10", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 1 0)] },
      { kind := .get, name := "Examples.Keys.key13", ixName := "key13", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 1 3)] },
      { kind := .get, name := "Examples.Keys.owner10", ixName := "owner10", paramCount := 0
        ops := #[.returnU64 (.accOwnerWord 1 0)] },
      { kind := .get, name := "Examples.Keys.owner13", ixName := "owner13", paramCount := 0
        ops := #[.returnU64 (.accOwnerWord 1 3)] }
    ] }

def extractedKeccak : Program :=
  { name := "Keccak"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Keccak.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Keccak.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Keccak.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Keccak.vault", ixName := "vault", paramCount := 0
        ops := #[.returnU64 (.keccak256Lit "vault")] },
      { kind := .get, name := "Examples.Keccak.ok", ixName := "ok", paramCount := 0
        ops := #[.returnU64 (.keccak256Lit "ok")] },
      { kind := .get, name := "Examples.Keccak.empty", ixName := "empty", paramCount := 0
        ops := #[.returnU64 (.keccak256Lit "")] }

    ] }

def extractedTrio : Program :=
  { name := "Trio"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Trio.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Trio.touch", ixName := "touch", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[.okState (.lit 0)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Trio.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Trio.lamports2", ixName := "lamports2", paramCount := 0
        ops := #[.returnU64 (.accLamportsN 2)] },
      { kind := .get, name := "Examples.Trio.dataLen2", ixName := "dataLen2", paramCount := 0
        ops := #[.returnU64 (.accDataLenN 2)] },
      { kind := .get, name := "Examples.Trio.signer2", ixName := "signer2", paramCount := 0
        ops := #[.returnU64 (.isSignerN 2)] },
      { kind := .get, name := "Examples.Trio.writable2", ixName := "writable2", paramCount := 0
        ops := #[.returnU64 (.isWritableN 2)] },
      { kind := .get, name := "Examples.Trio.executable2", ixName := "executable2", paramCount := 0
        ops := #[.returnU64 (.isExecutableN 2)] },
      { kind := .get, name := "Examples.Trio.key20", ixName := "key20", paramCount := 0
        ops := #[.returnU64 (.accKeyWord 2 0)] },
      { kind := .get, name := "Examples.Trio.needSig1", ixName := "needSig1", paramCount := 0
        ops := #[.returnU64 (.signerKeyN 1)] },
      { kind := .get, name := "Examples.Trio.self0", ixName := "self0", paramCount := 0
        ops := #[.returnU64 (.ownerIsSelf 0)] },
      { kind := .get, name := "Examples.Trio.self2", ixName := "self2", paramCount := 0
        ops := #[.returnU64 (.ownerIsSelf 2)] }
    ] }

def extractedGate : Program :=
  { name := "Gate"
    slots := #[{ name := "open_", width := 1, abi := "u8-le" }, { name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Gate.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Gate.openGate", ixName := "openGate", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[
              .storeField "open_" (.lit 1),
              .storeField "dummy" (.lit 0),
              .okState (.lit 1)
            ]
            #[.errorOverflow]
        ] },
      { kind := .increment, name := "Examples.Gate.closeGate", ixName := "closeGate", paramCount := 0
        ops := #[
          .ite .ne (.lit 0) (.lit 1)
            #[
              .storeField "open_" (.lit 0),
              .storeField "dummy" (.lit 0),
              .okState (.lit 0)
            ]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Gate.isOpen", ixName := "isOpen", paramCount := 0
        ops := #[
          .ite .eq (.field (.arg 0) "open_") (.lit 1)
            #[.returnU64 (.lit 1)]
            #[.returnU64 (.lit 0)]
        ] },
      { kind := .get, name := "Examples.Gate.now", ixName := "now", paramCount := 0
        ops := #[.returnU64 .unixTime] }
    ] }

def extractedNonce : Program :=
  { name := "Nonce"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Nonce.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Nonce.advance", ixName := "advance", paramCount := 0
        ops := #[Ops.systemAdvanceNonce, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.Nonce.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenOwner : Program :=
  { name := "TokenOwner"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenOwner.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenOwner.setOwner", ixName := "setOwner", paramCount := 0
        ops := #[Ops.tokenSetAccountAuthority, .returnU64 (.lit 0)] },
      { kind := .increment, name := "Examples.TokenOwner.approve", ixName := "approve", paramCount := 1
        ops := #[Ops.tokenApprove (.arg 0), .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenOwner.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedTokenMs : Program :=
  { name := "TokenMs"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.TokenMs.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.TokenMs.openMs", ixName := "openMs", paramCount := 0
        ops := #[Ops.tokenInitMultisig, .returnU64 (.lit 0)] },
      { kind := .get, name := "Examples.TokenMs.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.lit 0)] }
    ] }

def extractedBook : Program :=
  { name := "Book"
    slots := #[
      { name := "cells_0" }, { name := "cells_1" },
      { name := "cells_2" }, { name := "cells_3" }
    ]
    methods := #[
      { kind := .init, name := "Examples.Book.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Book.fillFirst", ixName := "fillFirst", paramCount := 1
        ops := #[
          .forBody 4 #[
            .ite .eq (.indexGet (.arg 1) "cells" .loopIx 0) (.lit 0)
              #[
                .ite .lt .loopIx (.lit 4)
                  #[.indexSet "cells" .loopIx (.arg 0) 4, .okState (.arg 0)]
                  #[.errorOverflow]
              ]
              #[]
          ],
          .errorOverflow
        ] },
      { kind := .increment, name := "Examples.Book.setAt", ixName := "setAt", paramCount := 2
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.indexSet "cells" (.arg 0) (.arg 1) 4, .okState (.arg 1)]
            #[.errorOverflow]
        ] },
      { kind := .get, name := "Examples.Book.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "cells_0")] },
      { kind := .get, name := "Examples.Book.getAt", ixName := "getAt", paramCount := 1
        ops := #[
          .ite .lt (.arg 0) (.lit 4)
            #[.returnU64 (.indexGet (.arg 1) "cells" (.arg 0) 0)]
            #[.returnU64 (.lit 0)]
        ] },
      { kind := .get, name := "Examples.Book.sum4", ixName := "sum4", paramCount := 0
        ops := #[
          .forAccum 4 (.indexGet (.arg 0) "cells" .loopIx 0),
          .returnU64 (.indexGet (.arg 0) "cells" .loopIx 0)
        ] }
    ] }

def extractedSeat : Program :=
  { name := "Seat"
    slots := #[{ name := "dummy" }]
    methods := #[
      { kind := .init, name := "Examples.Seat.init", ixName := "initialize", paramCount := 1
        ops := #[.returnState (.lit 0)] },
      { kind := .increment, name := "Examples.Seat.openBase", ixName := "openBase", paramCount := 0
        ops := #[Ops.tokenInitAccount, .returnU64 (.lit 0)] },
      { kind := .increment, name := "Examples.Seat.openSeat", ixName := "openSeat", paramCount := 1
        ops := #[Ops.createPda (.arg 0), .returnU64 (.arg 0)] },
      { kind := .get, name := "Examples.Seat.get", ixName := "get", paramCount := 0
        ops := #[.returnU64 (.findPda "vault")] }
    ] }

private def phoenixState : Ops.Val := .arg 2

private def phoenixSize : Ops.Val := .field phoenixState "sizes_0"

private def phoenixSettle (fill : Ops.Val) : Array Ops.Op :=
  #[
    .checkedAddU64 (.field phoenixState "baseFree") fill,
    Ops.tokenTransferChecked fill 6,
    .storeField "sizes_0" (.subU64 phoenixSize fill),
    .storeField "baseFree" (.addU64 (.field phoenixState "baseFree") fill),
    .okState fill
  ]

private def phoenixTrade : Array Ops.Op :=
  #[.ite .le (.arg 0) phoenixSize (phoenixSettle (.arg 0)) (phoenixSettle phoenixSize)]

private def phoenixTif : Array Ops.Op :=
  #[
    .ite .eq (.field phoenixState "lastTimes_0") (.lit 0)
      phoenixTrade
      #[
        .ite .lt .unixTime (.field phoenixState "lastTimes_0")
          phoenixTrade
          #[.errorOverflow]
      ]
  ]

private def phoenixSwapBuy : Array Ops.Op :=
  #[
    .ite .ne phoenixSize (.lit 0)
      #[
        .ite .le (.field phoenixState "priceTicks_0") (.arg 1)
          phoenixTif
          #[.errorOverflow]
      ]
      #[.errorOverflow]
  ]

def extractedPhoenix : Program :=
  { name := "Phoenix"
    slots := #[
      { name := "baseLotsPerBaseUnit" }, { name := "tickSize" },
      { name := "sequence" }, { name := "takerFeeBps" },
      { name := "collectedFees" }, { name := "unclaimedFees" },
      { name := "priceTicks_0" }, { name := "priceTicks_1" },
      { name := "priceTicks_2" }, { name := "priceTicks_3" },
      { name := "sequences_0" }, { name := "sequences_1" },
      { name := "sequences_2" }, { name := "sequences_3" },
      { name := "traders_0" }, { name := "traders_1" },
      { name := "traders_2" }, { name := "traders_3" },
      { name := "sizes_0" }, { name := "sizes_1" },
      { name := "sizes_2" }, { name := "sizes_3" },
      { name := "lastSlots_0" }, { name := "lastSlots_1" },
      { name := "lastSlots_2" }, { name := "lastSlots_3" },
      { name := "lastTimes_0" }, { name := "lastTimes_1" },
      { name := "lastTimes_2" }, { name := "lastTimes_3" },
      { name := "quoteLocked" }, { name := "quoteFree" },
      { name := "baseLocked" }, { name := "baseFree" },
      { name := "matchFilled" }, { name := "matchQuote" },
      { name := "matchExpired" }, { name := "matchStopped" },
      { name := "matchError" }, { name := "matchLevel" }, { name := "matchWant" },
      { name := "matchLimit" }
    ]
    methods := #[
      { kind := .init, name := "Projects.Phoenix.init", ixName := "initialize", paramCount := 1
        ops := #[
          .returnState (.lit 1), .returnState (.arg 0), .returnState (.lit 1),
          .returnState (.lit 0), .returnState (.lit 0), .returnState (.lit 0),
          .returnState (.lit 0), .returnState (.lit 0), .returnState (.lit 0),
          .returnState (.lit 0), .returnState (.lit 0), .returnState (.lit 0),
          .returnState (.lit 0), .returnState (.lit 0), .returnState (.lit 0),
          .returnState (.lit 0), .returnState (.lit 0)
        ] },
      { kind := .increment, name := "Projects.Phoenix.postAsk", ixName := "postAsk", paramCount := 1
        ops := #[
          .ite .eq (.field (.arg 1) "sizes_0") (.lit 0)
            #[.okState (.field (.arg 0) "sizes_0")]
            #[
              .ite .eq (.field (.arg 1) "sizes_1") (.lit 0)
                #[.okState (.field (.arg 0) "sizes_1")]
                #[
                  .ite .eq (.field (.arg 1) "sizes_2") (.lit 0)
                    #[.okState (.field (.arg 0) "sizes_2")]
                    #[
                      .ite .eq (.field (.arg 1) "sizes_3") (.lit 0)
                        #[.okState (.field (.arg 0) "sizes_3")]
                        #[.errorOverflow]
                    ]
                ]
            ]
        ] },
      { kind := .increment, name := "Projects.Phoenix.reduceAsk", ixName := "reduceAsk", paramCount := 1
        ops := #[
          .checkedSubU64 (.field (.arg 1) "sizes_0") (.arg 0),
          .okState (.field (.arg 1) "sizes_0"),
          .errorOverflow
        ] },
      { kind := .increment, name := "Projects.Phoenix.swapBuy", ixName := "swapBuy", paramCount := 2
        ops := phoenixSwapBuy },
      { kind := .get, name := "Projects.Phoenix.askQty", ixName := "askQty", paramCount := 0
        ops := #[.returnU64
          (.addU64
            (.addU64
              (.addU64 (.field (.arg 0) "sizes_0") (.field (.arg 0) "sizes_1"))
              (.field (.arg 0) "sizes_2"))
            (.field (.arg 0) "sizes_3"))] },
      { kind := .get, name := "Projects.Phoenix.bestAsk", ixName := "bestAsk", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "priceTicks_0")] },
      { kind := .get, name := "Projects.Phoenix.feeBpsOf", ixName := "feeBpsOf", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "takerFeeBps")] },
      { kind := .get, name := "Projects.Phoenix.level0", ixName := "level0", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "sizes_0")] },
      { kind := .get, name := "Projects.Phoenix.makerBase", ixName := "makerBase", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "baseLocked")] },
      { kind := .get, name := "Projects.Phoenix.nextSeq", ixName := "nextSeq", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "sequence")] },
      { kind := .get, name := "Projects.Phoenix.takerBase", ixName := "takerBase", paramCount := 0
        ops := #[.returnU64 (.field (.arg 0) "baseFree")] }
    ] }

def programs : Array Program := #[
  extractedCounter, extractedPair, extractedNested, extractedTree, extractedFlag,
  extractedMaybe, extractedWindow, extractedPhase, extractedChoice,
  extractedClock, extractedTransfer, extractedPing, extractedCall, extractedInfo, extractedPeer,
  extractedPda, extractedSigned, extractedCreate, extractedTokenXfer, extractedAta,
  extractedRent, extractedTokenMint, extractedSysAlloc, extractedTokenAcc, extractedMemo,
  extractedCreatePda, extractedTokenApprove, extractedTokenFreeze, extractedTokenAuth,
  extractedEpoch, extractedTokenSize, extractedSysSeed, extractedSysXfer, extractedTokenMint2,
  extractedTokenNative, extractedHash, extractedKeys, extractedKeccak, extractedTrio,
  extractedGate, extractedNonce, extractedTokenOwner, extractedTokenMs,
  extractedPhoenix, extractedBook, extractedSeat,
  extractedEvmCtx, extractedTipJar, extractedLang, extractedVault, extractedOwnable,
  extractedToken
]

/--
`#pf_build` 抽出的 digest 必须钉住。Phoenix 的 bounded-fold IR 和 Tree 的动态
allocator / insertion IR 直接钉 canonical digest；对应手写 fixture 继续作为布局/发射 smoke。
-/
def digestOf (name : String) : Option String :=
  if name == "Phoenix" then some "b5f356df375a759e"
  else if name == "Tree" then some "1d4a472be13bbdbd"
  else (programs.find? (·.name == name)).map digestHex

end ProofForge.Golden
