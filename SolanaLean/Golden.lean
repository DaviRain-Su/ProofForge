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

def programs : Array Program := #[
  extractedCounter, extractedPair, extractedFlag,
  extractedMaybe, extractedWindow, extractedPhase
]

/-- `#solana_build` 抽出的 digest 必须钉住。新例子加进 `programs`，不必改 IR。 -/
def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map digestHex

end SolanaLean.Golden
