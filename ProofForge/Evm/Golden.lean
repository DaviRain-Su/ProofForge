import ProofForge.Extract.LegacyGolden
import ProofForge.Evm.IRCompat
import ProofForge.Evm.Ops
import ProofForge.Evm.NativeFx
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.Golden

open ProofForge.Evm
open ProofForge.Crypto

/-- 竖切夹具：无 SVM 叶子。窄槽 / Option 双叶已开。 -/
def sources : Array Extract.Legacy.Program := #[
  ProofForge.Golden.extractedCounter,
  ProofForge.Golden.extractedPair,
  ProofForge.Golden.extractedWindow,
  ProofForge.Golden.extractedPhase,
  ProofForge.Golden.extractedFlag,
  ProofForge.Golden.extractedMaybe,
  ProofForge.Golden.extractedEvmCtx,
  ProofForge.Golden.extractedLang
]

private def u256Field (i : Nat) (limb : String) : Ops.Val :=
  .field (.arg i) limb

private def addrField (i : Nat) (limb : String) : Ops.Val :=
  .field (.arg i) limb

private def callerW : Nat → Ops.Val
  | 0 => .ext .callerW0 #[]
  | 1 => .ext .callerW1 #[]
  | _ => .ext .callerW2 #[]

private def limbName : Nat → String
  | 0 => "w0" | 1 => "w1" | 2 => "w2" | _ => "w3"

private def arith256Val (op limb a b : Nat) : Ops.Val :=
  Ops.arith256 op limb
    (u256Field a "w0") (u256Field a "w1") (u256Field a "w2") (u256Field a "w3")
    (u256Field b "w0") (u256Field b "w1") (u256Field b "w2") (u256Field b "w3")

private def return256 (mk : Nat → Ops.Val) : Array IR.Op :=
  #[.returnU64 (mk 0), .returnU64 (mk 1), .returnU64 (mk 2), .returnU64 (mk 3)]

private def view256 (mod ix : String) (paramCount : Nat) (widths : Array Nat)
    (ops : Array IR.Op) : IR.Method :=
  let widths := if widths.size == paramCount then widths else Array.replicate paramCount 8
  {
    kind := .get
    name := s!"Examples.{mod}.{ix}"
    ixName := ix
    selector := Keccak.selectorOfWidths ix widths
    paramCount
    paramWidths := widths
    retWidths := #[32]
    retCount := 4
    ops
    view := true
  }

private def mutEntry (mod ix : String) (paramCount : Nat) (widths : Array Nat)
    (ops : Array IR.Op) : IR.Method :=
  let widths := if widths.size == paramCount then widths else Array.replicate paramCount 8
  {
    kind := .increment
    name := s!"Examples.{mod}.{ix}"
    ixName := ix
    selector := Keccak.selectorOfWidths ix widths
    paramCount
    paramWidths := widths
    ops
  }

private def dummyCtor (mod : String) : IR.Method :=
  {
    kind := .init
    name := s!"Examples.{mod}.init"
    ixName := "initialize"
    paramCount := 1
    paramWidths := #[8]
    ops := #[.returnState (.lit 0)]
  }

private def dummyGet (mod : String) : IR.Method :=
  {
    kind := .get
    name := s!"Examples.{mod}.get"
    ixName := "get"
    selector := Keccak.selectorOfWidths "get" #[]
    ops := #[.returnU64 (.lit 0)]
    view := true
  }

private def payEntry (mod ix : String) (paramCount : Nat) (widths : Array Nat)
    (ops : Array IR.Op) : IR.Method :=
  { mutEntry mod ix paramCount widths ops with payable := true }

private def viewEnv (mod ix : String) (v : Ops.Val) : IR.Method :=
  {
    kind := .get
    name := s!"Examples.{mod}.{ix}"
    ixName := ix
    selector := Keccak.selectorOfWidths ix #[]
    ops := #[.returnU64 v]
    view := true
  }

private def viewAddr20 (mod ix : String) (w0 w1 w2 : Ops.Val) : IR.Method :=
  {
    kind := .get
    name := s!"Examples.{mod}.{ix}"
    ixName := ix
    selector := Keccak.selectorOfWidths ix #[]
    retWidths := #[20]
    retCount := 3
    ops := #[.returnU64 w0, .returnU64 w1, .returnU64 w2]
    view := true
  }

private def dummySlot : Array IR.Slot := #[{ name := "dummy", index := 0, width := 8 }]

private def getAddr256 (limb : Nat) (base key : Nat) : Ops.Val :=
  Ops.mapGetAddr256 limb (.lit (UInt64.ofNat base))
    (addrField key "w0") (addrField key "w1") (addrField key "w2")

private def getCaller256 (limb : Nat) (base : Nat) : Ops.Val :=
  Ops.mapGetAddr256 limb (.lit (UInt64.ofNat base)) (callerW 0) (callerW 1) (callerW 2)

private def getPair256 (limb : Nat) (base owner spender : Nat) : Ops.Val :=
  Ops.mapGetPair256 limb (.lit (UInt64.ofNat base))
    (addrField owner "w0") (addrField owner "w1") (addrField owner "w2")
    (addrField spender "w0") (addrField spender "w1") (addrField spender "w2")

private def getPairCaller256 (limb : Nat) (base owner : Nat) : Ops.Val :=
  Ops.mapGetPair256 limb (.lit (UInt64.ofNat base))
    (addrField owner "w0") (addrField owner "w1") (addrField owner "w2")
    (callerW 0) (callerW 1) (callerW 2)

private def getPairCallerSpender256 (limb : Nat) (base spender : Nat) : Ops.Val :=
  Ops.mapGetPair256 limb (.lit (UInt64.ofNat base))
    (callerW 0) (callerW 1) (callerW 2)
    (addrField spender "w0") (addrField spender "w1") (addrField spender "w2")

private def arithGet (op limb : Nat) (lhs : Nat → Ops.Val) (rhs : Nat) : Ops.Val :=
  Ops.arith256 op limb
    (lhs 0) (lhs 1) (lhs 2) (lhs 3)
    (u256Field rhs "w0") (u256Field rhs "w1") (u256Field rhs "w2") (u256Field rhs "w3")

private def ge256 (lhs : Nat → Ops.Val) (rhs : Nat) : Ops.Val :=
  Ops.ge256
    (lhs 0) (lhs 1) (lhs 2) (lhs 3)
    (u256Field rhs "w0") (u256Field rhs "w1") (u256Field rhs "w2") (u256Field rhs "w3")

private def hashedCall (call : HashedMap.Call Ops.Val) : IR.Op :=
  .component (.hashedMap call)

private def closedCall (call : ClosedCall.Call Ops.Val) : IR.Op :=
  .component (.closedCall call)

private def nativeFx (call : NativeFx.Call Ops.Val) : IR.Op :=
  .component (.nativeFx call)

private def setAddr256 (base key : Nat) (val : Nat → Ops.Val) : IR.Op :=
  hashedCall (.setAddr256 (.lit (UInt64.ofNat base))
    (addrField key "w0") (addrField key "w1") (addrField key "w2")
    (val 0) (val 1) (val 2) (val 3))

private def setCaller256 (base : Nat) (val : Nat → Ops.Val) : IR.Op :=
  hashedCall (.setAddr256 (.lit (UInt64.ofNat base)) (callerW 0) (callerW 1) (callerW 2)
    (val 0) (val 1) (val 2) (val 3))

private def setPairCaller256 (base owner : Nat) (val : Nat → Ops.Val) : IR.Op :=
  hashedCall (.setPair256 (.lit (UInt64.ofNat base))
    (addrField owner "w0") (addrField owner "w1") (addrField owner "w2")
    (callerW 0) (callerW 1) (callerW 2)
    (val 0) (val 1) (val 2) (val 3))

private def setPairCallerSpender256 (base spender : Nat) (val : Nat → Ops.Val) : IR.Op :=
  hashedCall (.setPair256 (.lit (UInt64.ofNat base))
    (callerW 0) (callerW 1) (callerW 2)
    (addrField spender "w0") (addrField spender "w1") (addrField spender "w2")
    (val 0) (val 1) (val 2) (val 3))

private def eq20Zero (key : Nat) : Ops.Val :=
  Ops.eq20
    (addrField key "w0") (addrField key "w1") (addrField key "w2")
    (.lit 0) (.lit 0) (.lit 0)

private def guardZero (key : Nat) (ok : Array IR.Op) : Array IR.Op :=
  #[.ite .eq (eq20Zero key) (.lit 1)
      #[nativeFx .revertZeroAddress, .returnU64 (.lit 0)]
      ok]

/-- `s.paused != 0` 抽出成嵌套 `select`。state 参数是 mutate 的最后一个 arg。 -/
private def pausedNe0 (stateArg : Nat) : Ops.Val :=
  .select .eq
    (.select .eq (.field (.arg stateArg) "paused") (.lit 0) (.lit 1) (.lit 0))
    (.lit 0) (.lit 1) (.lit 0)

private def guardPaused (stateArg : Nat) (ok : Array IR.Op) : Array IR.Op :=
  #[.ite .ne (pausedNe0 stateArg) (.lit 0)
      #[nativeFx .revertPaused, .returnU64 (.lit 0)]
      ok]

private def eqImmCaller : Ops.Val :=
  Ops.eq20
    (.ext .callerW0 #[]) (.ext .callerW1 #[]) (.ext .callerW2 #[])
    (.ext .immW0 #[]) (.ext .immW1 #[]) (.ext .immW2 #[])

private def ownerGate (ok : Array IR.Op) : Array IR.Op :=
  #[.ite .eq eqImmCaller (.lit 1)
      ok
      #[nativeFx (.revertUnauthorized (.ext .callerW0 #[]) (.ext .callerW1 #[]) (.ext .callerW2 #[])),
        .returnU64 (.ext .callerW0 #[])]]

private def capGeNext (stateArg amt : Nat) : Ops.Val :=
  Ops.ge256
    (.field (.arg stateArg) "cap_w0") (.field (.arg stateArg) "cap_w1")
    (.field (.arg stateArg) "cap_w2") (.field (.arg stateArg) "cap_w3")
    (Ops.arith256 0 0
      (.field (.arg stateArg) "supply_w0") (.field (.arg stateArg) "supply_w1")
      (.field (.arg stateArg) "supply_w2") (.field (.arg stateArg) "supply_w3")
      (u256Field amt "w0") (u256Field amt "w1") (u256Field amt "w2") (u256Field amt "w3"))
    (Ops.arith256 0 1
      (.field (.arg stateArg) "supply_w0") (.field (.arg stateArg) "supply_w1")
      (.field (.arg stateArg) "supply_w2") (.field (.arg stateArg) "supply_w3")
      (u256Field amt "w0") (u256Field amt "w1") (u256Field amt "w2") (u256Field amt "w3"))
    (Ops.arith256 0 2
      (.field (.arg stateArg) "supply_w0") (.field (.arg stateArg) "supply_w1")
      (.field (.arg stateArg) "supply_w2") (.field (.arg stateArg) "supply_w3")
      (u256Field amt "w0") (u256Field amt "w1") (u256Field amt "w2") (u256Field amt "w3"))
    (Ops.arith256 0 3
      (.field (.arg stateArg) "supply_w0") (.field (.arg stateArg) "supply_w1")
      (.field (.arg stateArg) "supply_w2") (.field (.arg stateArg) "supply_w3")
      (u256Field amt "w0") (u256Field amt "w1") (u256Field amt "w2") (u256Field amt "w3"))

private def guardCap (stateArg amt : Nat) (ok : Array IR.Op) : Array IR.Op :=
  #[.ite .eq (capGeNext stateArg amt) (.lit 1)
      ok
      #[nativeFx .revertCapExceeded, .returnU64 (.lit 0)]]

/-- Live extract of `Examples.Wide`; Legacy IR has no `arith256` leaf. -/
def extractedWide : IR.Program :=
  let ctor : IR.Method := {
    kind := .init
    name := "Examples.Wide.init"
    ixName := "initialize"
    paramCount := 1
    paramWidths := #[8]
    ops := #[.returnState (.lit 0)]
  }
  let touch : IR.Method := {
    kind := .increment
    name := "Examples.Wide.touch"
    ixName := "touch"
    selector := Keccak.selectorOfWidths "touch" #[]
    ops := #[
      .ite .ne (.lit 0) (.lit 1)
        #[.storeField "dummy" (.lit 0), .okState (.lit 0)]
        #[.errorOverflow]
    ]
  }
  let get : IR.Method := {
    kind := .get
    name := "Examples.Wide.get"
    ixName := "get"
    selector := Keccak.selectorOfWidths "get" #[]
    ops := #[.returnU64 (.lit 0)]
    view := true
  }
  {
    name := "Wide"
    slots := #[{ name := "dummy", index := 0, width := 8 }]
    constructor := ctor
    entries := #[
      touch,
      view256 "Wide" "add" 2 #[32, 32] (return256 fun limb => arith256Val 0 limb 0 1),
      view256 "Wide" "echo" 1 #[32] (return256 fun limb =>
        u256Field 0 (match limb with | 0 => "w0" | 1 => "w1" | 2 => "w2" | _ => "w3")),
      get,
      view256 "Wide" "mul" 2 #[32, 32] (return256 fun limb => arith256Val 2 limb 0 1),
      view256 "Wide" "sub" 2 #[32, 32] (return256 fun limb => arith256Val 1 limb 0 1)
    ]
  }

/-- Live extract of `Examples.Vault`; Legacy IR has no 256-bit map/token leaves. -/
def extractedVault : IR.Program :=
  {
    name := "Vault"
    slots := dummySlot
    constructor := dummyCtor "Vault"
    entries := #[
      mutEntry "Vault" "credit" 2 #[20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[setAddr256 0 0 (fun limb => u256Field 1 (limbName limb)),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "grant" 3 #[20, 20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.approve256
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3")),
            .returnU64 (u256Field 2 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "permit" 8 #[20, 20, 20, 32, 32, 1, 33, 33] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.tokenPermit
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (addrField 2 "w0") (addrField 2 "w1") (addrField 2 "w2")
              (u256Field 3 "w0") (u256Field 3 "w1") (u256Field 3 "w2") (u256Field 3 "w3")
              (u256Field 4 "w0") (u256Field 4 "w1") (u256Field 4 "w2") (u256Field 4 "w3")
              (.arg 5)
              (u256Field 6 "w0") (u256Field 6 "w1") (u256Field 6 "w2") (u256Field 6 "w3")
              (u256Field 7 "w0") (u256Field 7 "w1") (u256Field 7 "w2") (u256Field 7 "w3")),
            .returnU64 (u256Field 3 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "pull" 3 #[20, 20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.transfer256
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3")),
            .returnU64 (u256Field 2 "w0")]
          #[.errorOverflow]
      ],
      payEntry "Vault" "receive" 0 #[] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx .receive, .returnU64 (.lit 0)]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "setU64" 2 #[8, 8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[hashedCall (.setU64 (.lit 0) (.arg 0) (.arg 1)), .returnU64 (.arg 1)]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "swap2" 5 #[20, 20, 20, 32, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.swapExact2
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (addrField 2 "w0") (addrField 2 "w1") (addrField 2 "w2")
              (u256Field 3 "w0") (u256Field 3 "w1") (u256Field 3 "w2") (u256Field 3 "w3")
              (u256Field 4 "w0") (u256Field 4 "w1") (u256Field 4 "w2") (u256Field 4 "w3")),
            .returnU64 (u256Field 3 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "swap3" 6 #[20, 20, 20, 20, 32, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.swapExact3
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (addrField 2 "w0") (addrField 2 "w1") (addrField 2 "w2")
              (addrField 3 "w0") (addrField 3 "w1") (addrField 3 "w2")
              (u256Field 4 "w0") (u256Field 4 "w1") (u256Field 4 "w2") (u256Field 4 "w3")
              (u256Field 5 "w0") (u256Field 5 "w1") (u256Field 5 "w2") (u256Field 5 "w3")),
            .returnU64 (u256Field 4 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "take" 4 #[20, 20, 20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.transferFrom256
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (addrField 2 "w0") (addrField 2 "w1") (addrField 2 "w2")
              (u256Field 3 "w0") (u256Field 3 "w1") (u256Field 3 "w2") (u256Field 3 "w3")),
            .returnU64 (u256Field 3 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "unwrap" 2 #[20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.wethWithdraw256
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ],
      payEntry "Vault" "wrap" 2 #[20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.deposit256 (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            closedCall (.wethDeposit256
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ],
      view256 "Vault" "allowed" 3 #[20, 20, 20] (return256 fun limb =>
        Ops.tokenAllowance256 limb
          (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
          (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
          (addrField 2 "w0") (addrField 2 "w1") (addrField 2 "w2")),
      dummyGet "Vault",
      {
        kind := .get
        name := "Examples.Vault.getU64"
        ixName := "getU64"
        selector := Keccak.selectorOfWidths "getU64" #[8]
        paramCount := 1
        paramWidths := #[8]
        ops := #[hashedCall (.getU64 (.lit 0) (.arg 0)), .returnU64 (.arg 0)]
        view := true
      },
      view256 "Vault" "held" 1 #[20] (return256 fun limb =>
        Ops.tokenBalance256 limb (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")),
      view256 "Vault" "shareOf" 1 #[20] (return256 fun limb => getAddr256 limb 0 0)
    ]
  }

/-- Live extract of `Examples.Token`; Legacy IR has no 256-bit map/arith leaves. -/
def extractedToken : IR.Program :=
  let callerBal (limb : Nat) := getCaller256 limb 0
  let destBal (limb : Nat) := getAddr256 limb 0 0
  let ownerBal (limb : Nat) := getAddr256 limb 0 0
  let destFrom (limb : Nat) := getAddr256 limb 0 1
  let pairAllow (limb : Nat) := getPairCaller256 limb 1 0
  let pairSelf (limb : Nat) := getPairCallerSpender256 limb 1 0
  {
    name := "Token"
    slots := #[
      { name := "dummy", index := 0, width := 8 },
      { name := "paused", index := 1, width := 1 },
      { name := "cap_w0", index := 2, width := 8 },
      { name := "cap_w1", index := 3, width := 8 },
      { name := "cap_w2", index := 4, width := 8 },
      { name := "cap_w3", index := 5, width := 8 },
      { name := "supply_w0", index := 6, width := 8 },
      { name := "supply_w1", index := 7, width := 8 },
      { name := "supply_w2", index := 8, width := 8 },
      { name := "supply_w3", index := 9, width := 8 }
    ]
    constructor := {
      kind := .init
      name := "Examples.Token.init"
      ixName := "initialize"
      paramCount := 1
      paramWidths := #[20]
      ops := #[
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 1000),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0)
      ]
    }
    entries := #[
      mutEntry "Token" "approve" 2 #[20, 32] (guardPaused 2 (guardZero 0 #[
        .ite .ne (.lit 0) (.lit 1)
          #[hashedCall (.setPair256 (.lit 1)
              (callerW 0) (callerW 1) (callerW 2)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            nativeFx (.logApproval256 (callerW 0) (callerW 1) (callerW 2) (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (u256Field 1 "w0")]
            #[.errorOverflow]
            ])),
            mutEntry "Token" "burn" 1 #[32] (guardPaused 1 #[
              .ite .eq (ge256 callerBal 0) (.lit 1)
                #[setCaller256 0 (fun limb => arithGet 1 limb callerBal 0),
                  setCaller256 0 (fun limb => arithGet 1 limb callerBal 0),
                  nativeFx (.logTransfer256 (callerW 0) (callerW 1) (callerW 2) (.lit 0) (.lit 0) (.lit 0) (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .storeField "supply_w0" (Ops.arith256 1 0
              (.field (.arg 1) "supply_w0") (.field (.arg 1) "supply_w1")
              (.field (.arg 1) "supply_w2") (.field (.arg 1) "supply_w3")
              (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .storeField "supply_w1" (Ops.arith256 1 1
              (.field (.arg 1) "supply_w0") (.field (.arg 1) "supply_w1")
              (.field (.arg 1) "supply_w2") (.field (.arg 1) "supply_w3")
              (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .storeField "supply_w2" (Ops.arith256 1 2
              (.field (.arg 1) "supply_w0") (.field (.arg 1) "supply_w1")
              (.field (.arg 1) "supply_w2") (.field (.arg 1) "supply_w3")
              (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .storeField "supply_w3" (Ops.arith256 1 3
              (.field (.arg 1) "supply_w0") (.field (.arg 1) "supply_w1")
              (.field (.arg 1) "supply_w2") (.field (.arg 1) "supply_w3")
              (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .returnU64 (u256Field 0 "w0")]
          #[nativeFx (.revertInsufficient (callerBal 0) (callerBal 1) (callerBal 2) (callerBal 3) (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .returnU64 (callerBal 0)]
          ]),
          mutEntry "Token" "burnFrom" 2 #[20, 32] (guardPaused 2 (guardZero 0 #[
            .ite .eq (ge256 pairAllow 1) (.lit 1)
              #[.ite .eq (ge256 ownerBal 1) (.lit 1)
                  #[setAddr256 0 0 (fun limb => arithGet 1 limb ownerBal 1),
                    setPairCaller256 1 0 (fun limb => arithGet 1 limb pairAllow 1),
                    setAddr256 0 0 (fun limb => arithGet 1 limb ownerBal 1),
                    setPairCaller256 1 0 (fun limb => arithGet 1 limb pairAllow 1),
                    nativeFx (.logTransfer256 (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (.lit 0) (.lit 0) (.lit 0) (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                    .storeField "supply_w0" (Ops.arith256 1 0
                      (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
                      (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
                      (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                    .storeField "supply_w1" (Ops.arith256 1 1
                      (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
                      (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
                      (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                    .storeField "supply_w2" (Ops.arith256 1 2
                      (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
                      (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
                      (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                    .storeField "supply_w3" (Ops.arith256 1 3
                      (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
                      (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
                      (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                    .returnU64 (u256Field 1 "w0")]
                  #[nativeFx (.revertInsufficient (ownerBal 0) (ownerBal 1) (ownerBal 2) (ownerBal 3) (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                    .returnU64 (ownerBal 0)]]
              #[nativeFx (.revertInsufficient (pairAllow 0) (pairAllow 1) (pairAllow 2) (pairAllow 3) (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                .returnU64 (pairAllow 0)]
              ])),
              mutEntry "Token" "decreaseAllowance" 2 #[20, 32] (guardPaused 2 (guardZero 0 #[
            .ite .eq (ge256 pairSelf 1) (.lit 1)
              #[setPairCallerSpender256 1 0 (fun limb => arithGet 1 limb pairSelf 1),
                nativeFx (.logApproval256 (callerW 0) (callerW 1) (callerW 2) (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (arithGet 1 0 pairSelf 1) (arithGet 1 1 pairSelf 1) (arithGet 1 2 pairSelf 1) (arithGet 1 3 pairSelf 1)),
                .returnU64 (arithGet 1 0 pairSelf 1)]
              #[nativeFx (.revertInsufficient (pairSelf 0) (pairSelf 1) (pairSelf 2) (pairSelf 3) (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
                .returnU64 (pairSelf 0)]
              ])),
              mutEntry "Token" "increaseAllowance" 2 #[20, 32] (guardPaused 2 (guardZero 0 #[
            .ite .ne (.lit 0) (.lit 1)
              #[setPairCallerSpender256 1 0 (fun limb => arithGet 0 limb pairSelf 1),
                nativeFx (.logApproval256 (callerW 0) (callerW 1) (callerW 2) (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (arithGet 0 0 pairSelf 1) (arithGet 0 1 pairSelf 1) (arithGet 0 2 pairSelf 1) (arithGet 0 3 pairSelf 1)),
                .returnU64 (arithGet 0 0 pairSelf 1)]
                #[.errorOverflow]
                ])),
                mutEntry "Token" "logApprove" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.log "Approval" (.arg 0)), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "Token" "logXfer" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.log "Transfer" (.arg 0)), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "Token" "mint" 2 #[20, 32] (ownerGate (guardPaused 2 (guardZero 0 (guardCap 2 1 #[
        .ite .ne (.lit 0) (.lit 1)
          #[setAddr256 0 0 (fun limb => u256Field 1 (limbName limb)),
            nativeFx (.logTransfer256 (.lit 0) (.lit 0) (.lit 0) (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .storeField "supply_w0" (Ops.arith256 0 0
              (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
              (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .storeField "supply_w1" (Ops.arith256 0 1
              (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
              (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .storeField "supply_w2" (Ops.arith256 0 2
              (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
              (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .storeField "supply_w3" (Ops.arith256 0 3
              (.field (.arg 2) "supply_w0") (.field (.arg 2) "supply_w1")
              (.field (.arg 2) "supply_w2") (.field (.arg 2) "supply_w3")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ])))),
      mutEntry "Token" "pause" 0 #[] (ownerGate #[
        .ite .ne (.lit 0) (.lit 1)
          #[.storeField "paused" (.lit 1), .okState (.lit 1)]
          #[.errorOverflow]
      ]),
      mutEntry "Token" "permit" 7 #[20, 20, 32, 32, 1, 33, 33] (guardPaused 7 #[
        .ite .ne (.lit 0) (.lit 1)
          #[closedCall (.permit
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3")
              (u256Field 3 "w0") (u256Field 3 "w1") (u256Field 3 "w2") (u256Field 3 "w3")
              (.arg 4)
              (u256Field 5 "w0") (u256Field 5 "w1") (u256Field 5 "w2") (u256Field 5 "w3")
              (u256Field 6 "w0") (u256Field 6 "w1") (u256Field 6 "w2") (u256Field 6 "w3")),
            .returnU64 (u256Field 2 "w0")]
          #[.errorOverflow]
      ]),
      mutEntry "Token" "transfer" 2 #[20, 32] (guardPaused 2 (guardZero 0 #[
        .ite .eq (ge256 callerBal 1) (.lit 1)
          #[setCaller256 0 (fun limb => arithGet 1 limb callerBal 1),
            setAddr256 0 0 (fun limb => arithGet 0 limb destBal 1),
            setCaller256 0 (fun limb => arithGet 1 limb callerBal 1),
            setAddr256 0 0 (fun limb => arithGet 0 limb destBal 1),
            nativeFx (.logTransfer256 (callerW 0) (callerW 1) (callerW 2) (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (u256Field 1 "w0")]
          #[nativeFx (.revertInsufficient (callerBal 0) (callerBal 1) (callerBal 2) (callerBal 3) (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (callerBal 0)]
      ])),
      mutEntry "Token" "transferFrom" 3 #[20, 20, 32] (guardPaused 3 (guardZero 1 #[
        .ite .eq (ge256 pairAllow 2) (.lit 1)
          #[.ite .eq (ge256 ownerBal 2) (.lit 1)
              #[setAddr256 0 0 (fun limb => arithGet 1 limb ownerBal 2),
                setAddr256 0 1 (fun limb => arithGet 0 limb destFrom 2),
                setPairCaller256 1 0 (fun limb => arithGet 1 limb pairAllow 2),
                setAddr256 0 0 (fun limb => arithGet 1 limb ownerBal 2),
                setAddr256 0 1 (fun limb => arithGet 0 limb destFrom 2),
                setPairCaller256 1 0 (fun limb => arithGet 1 limb pairAllow 2),
                nativeFx (.logTransfer256 (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2") (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3")),
                .returnU64 (u256Field 2 "w0")]
              #[nativeFx (.revertInsufficient (ownerBal 0) (ownerBal 1) (ownerBal 2) (ownerBal 3) (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3")),
                .returnU64 (ownerBal 0)]]
          #[nativeFx (.revertInsufficient (pairAllow 0) (pairAllow 1) (pairAllow 2) (pairAllow 3) (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3")),
            .returnU64 (pairAllow 0)]
      ])),
      mutEntry "Token" "unpause" 0 #[] (ownerGate #[
        .ite .ne (.lit 0) (.lit 1)
          #[.storeField "paused" (.lit 0), .okState (.lit 0)]
          #[.errorOverflow]
      ]),
      {
        kind := .get
        name := "Examples.Token.DOMAIN_SEPARATOR"
        ixName := "DOMAIN_SEPARATOR"
        selector := Keccak.selectorOfWidths "DOMAIN_SEPARATOR" #[]
        retWidths := #[33]
        retCount := 4
        ops := return256 fun limb => .ext (.domainSep256 limb) #[]
        view := true
      },
      view256 "Token" "allowanceOf" 2 #[20, 20] (return256 fun limb => getPair256 limb 1 0 1),
      view256 "Token" "balanceOf" 1 #[20] (return256 fun limb => getAddr256 limb 0 0),
      view256 "Token" "capOf" 0 #[] (return256 fun limb =>
        .field (.arg 0) s!"cap_{limbName limb}"),
      {
        kind := .get
        name := "Examples.Token.decimals"
        ixName := "decimals"
        selector := Keccak.selectorOfWidths "decimals" #[]
        retWidths := #[1]
        ops := #[.returnU64 (.lit 18)]
        view := true
      },
      dummyGet "Token",
      {
        kind := .get
        name := "Examples.Token.name"
        ixName := "name"
        selector := Keccak.selectorOfWidths "name" #[]
        retWidths := #[33]
        retCount := 4
        ops := #[
          .returnU64 (.lit 362646562158),
          .returnU64 (.lit 0),
          .returnU64 (.lit 0),
          .returnU64 (.lit 0)
        ]
        view := true
      },
      view256 "Token" "nonceOf" 1 #[20] (return256 fun limb => getAddr256 limb 2 0),
      {
        kind := .get
        name := "Examples.Token.ownerOf"
        ixName := "ownerOf"
        selector := Keccak.selectorOfWidths "ownerOf" #[]
        retWidths := #[20]
        retCount := 3
        ops := #[
          .returnU64 (.ext .immW0 #[]),
          .returnU64 (.ext .immW1 #[]),
          .returnU64 (.ext .immW2 #[])
        ]
        view := true
      },
      {
        kind := .get
        name := "Examples.Token.pausedOf"
        ixName := "pausedOf"
        selector := Keccak.selectorOfWidths "pausedOf" #[]
        retWidths := #[1]
        ops := #[.returnU64 (.field (.arg 0) "paused")]
        view := true
      },
      {
        kind := .get
        name := "Examples.Token.symbol"
        ixName := "symbol"
        selector := Keccak.selectorOfWidths "symbol" #[]
        retWidths := #[33]
        retCount := 4
        ops := #[
          .returnU64 (.lit 20550),
          .returnU64 (.lit 0),
          .returnU64 (.lit 0),
          .returnU64 (.lit 0)
        ]
        view := true
      },
      view256 "Token" "totalSupply" 0 #[] (return256 fun limb =>
        .field (.arg 0) s!"supply_{limbName limb}")
    ]
  }

/-- Live extract of `Examples.TipJar`; Legacy IR cannot represent `receive()`. -/
def extractedTipJar : IR.Program :=
  {
    name := "TipJar"
    slots := dummySlot
    constructor := dummyCtor "TipJar"
    entries := #[
      payEntry "TipJar" "deposit" 1 #[32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.deposit256 (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")),
            .returnU64 (u256Field 0 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "TipJar" "logTip" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.log "Tipped" (.arg 0)), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "TipJar" "payout" 2 #[20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.sendEth256 (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3")),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ],
      payEntry "TipJar" "receive" 0 #[] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx .receive, .returnU64 (.lit 0)]
          #[.errorOverflow]
      ],
      view256 "TipJar" "callValue" 0 #[] (return256 fun limb => .ext (.callValue256 limb) #[]),
      viewAddr20 "TipJar" "caller20" (.ext .callerW0 #[]) (.ext .callerW1 #[]) (.ext .callerW2 #[]),
      viewEnv "TipJar" "callerW0" (.ext .callerW0 #[]),
      viewEnv "TipJar" "callerW1" (.ext .callerW1 #[]),
      viewEnv "TipJar" "callerW2" (.ext .callerW2 #[]),
      viewEnv "TipJar" "chainId" (.ext .chainId #[]),
      dummyGet "TipJar",
      viewAddr20 "TipJar" "self20" (.ext .selfW0 #[]) (.ext .selfW1 #[]) (.ext .selfW2 #[]),
      view256 "TipJar" "selfBal" 0 #[] (return256 fun limb => .ext (.selfBalance256 limb) #[]),
      viewEnv "TipJar" "selfLow" (.ext .self #[]),
      viewEnv "TipJar" "selfW0" (.ext .selfW0 #[]),
      viewEnv "TipJar" "selfW1" (.ext .selfW1 #[]),
      viewEnv "TipJar" "selfW2" (.ext .selfW2 #[]),
      viewEnv "TipJar" "timestamp" (.ext .timestamp #[])
    ]
  }

/-- Live extract of `Examples.Ownable`; Legacy IR has no `eq20` leaf. -/
def extractedOwnable : IR.Program :=
  {
    name := "Ownable"
    slots := #[{ name := "value", index := 0, width := 8 }]
    constructor := {
      kind := .init
      name := "Examples.Ownable.init"
      ixName := "initialize"
      paramCount := 1
      paramWidths := #[20]
      ops := #[.returnState (.lit 0)]
    }
    entries := #[
      mutEntry "Ownable" "approve" 3 #[20, 20, 8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[hashedCall (.setPair (.lit 0)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (.arg 2)),
            .returnU64 (.arg 2)]
          #[.errorOverflow]
      ],
      {
        kind := .increment
        name := "Examples.Ownable.bump"
        ixName := "bump"
        selector := Keccak.selectorOfWidths "bump" #[8]
        paramCount := 1
        paramWidths := #[8]
        ops := #[
          .ite .eq
            (Ops.eq20
              (.ext .callerW0 #[]) (.ext .callerW1 #[]) (.ext .callerW2 #[])
              (.ext .immW0 #[]) (.ext .immW1 #[]) (.ext .immW2 #[]))
            (.lit 1)
            #[.checkedAddU64 (.field (.arg 1) "value") (.arg 0),
              .okState (.field (.arg 1) "value"),
              .errorOverflow]
            #[nativeFx (.revertUnauthorized (.ext .callerW0 #[]) (.ext .callerW1 #[]) (.ext .callerW2 #[])),
              .returnU64 (.ext .callerW0 #[])]
        ]
      },
      mutEntry "Ownable" "guardZero" 1 #[20] #[
        .ite .eq
          (Ops.eq20
            (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
            (.lit 0) (.lit 0) (.lit 0))
          (.lit 1)
          #[nativeFx .revertZeroAddress, .returnU64 (.lit 0)]
          #[.returnU64 (addrField 0 "w0")]
      ],
      mutEntry "Ownable" "logInc" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[nativeFx (.log "Incremented" (.arg 0)), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "Ownable" "spend" 3 #[20, 20, 8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[hashedCall (.setPair (.lit 0)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (.arg 2)),
            .returnU64 (.arg 2)]
          #[.errorOverflow]
      ],
      {
        kind := .get
        name := "Examples.Ownable.allowance"
        ixName := "allowance"
        selector := Keccak.selectorOfWidths "allowance" #[20, 20]
        paramCount := 2
        paramWidths := #[20, 20]
        ops := #[
          hashedCall (.getPair (.lit 0)
            (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
            (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")),
          .returnU64 (addrField 0 "w0")
        ]
        view := true
      },
      {
        kind := .get
        name := "Examples.Ownable.get"
        ixName := "get"
        selector := Keccak.selectorOfWidths "get" #[]
        ops := #[.returnU64 (.field (.arg 0) "value")]
        view := true
      },
      {
        kind := .get
        name := "Examples.Ownable.ownerOf"
        ixName := "ownerOf"
        selector := Keccak.selectorOfWidths "ownerOf" #[]
        retWidths := #[20]
        retCount := 3
        ops := #[
          .returnU64 (.ext .immW0 #[]),
          .returnU64 (.ext .immW1 #[]),
          .returnU64 (.ext .immW2 #[])
        ]
        view := true
      }
    ]
  }

/-- Live extract of `Examples.Const`; Legacy IR has no immutable leaves. -/
def extractedConst : IR.Program :=
  {
    name := "Const"
    slots := dummySlot
    constructor := {
      kind := .init
      name := "Examples.Const.init"
      ixName := "initialize"
      paramCount := 4
      paramWidths := #[8, 8, 20, 20]
      ops := #[.returnState (.lit 0)]
    }
    entries := #[
      mutEntry "Const" "touch" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.storeField "dummy" (.arg 0), .okState (.arg 0)]
          #[.errorOverflow]
      ],
      {
        kind := .get
        name := "Examples.Const.get"
        ixName := "get"
        selector := Keccak.selectorOfWidths "get" #[]
        ops := #[.returnU64 (.field (.arg 0) "dummy")]
        view := true
      },
      viewAddr20 "Const" "peerOf" (.ext .immX0 #[]) (.ext .immX1 #[]) (.ext .immX2 #[]),
      {
        kind := .get
        name := "Examples.Const.saltOf"
        ixName := "saltOf"
        selector := Keccak.selectorOfWidths "saltOf" #[]
        ops := #[.returnU64 (.ext .immU64b #[])]
        view := true
      },
      {
        kind := .get
        name := "Examples.Const.seedOf"
        ixName := "seedOf"
        selector := Keccak.selectorOfWidths "seedOf" #[]
        ops := #[.returnU64 (.ext .immU64 #[])]
        view := true
      },
      viewAddr20 "Const" "whoOf" (.ext .immW0 #[]) (.ext .immW1 #[]) (.ext .immW2 #[])
    ]
  }

/-- Live extract of `Examples.Capped`; reuses owner + pause + cap, no hashed map. -/
def extractedCapped : IR.Program :=
  let nextSupply (limb : Nat) : Ops.Val :=
    Ops.arith256 0 limb
      (.field (.arg 1) "supply_w0") (.field (.arg 1) "supply_w1")
      (.field (.arg 1) "supply_w2") (.field (.arg 1) "supply_w3")
      (u256Field 0 "w0") (u256Field 0 "w1") (u256Field 0 "w2") (u256Field 0 "w3")
  {
    name := "Capped"
    slots := #[
      { name := "paused", index := 0, width := 1 },
      { name := "cap_w0", index := 1, width := 8 },
      { name := "cap_w1", index := 2, width := 8 },
      { name := "cap_w2", index := 3, width := 8 },
      { name := "cap_w3", index := 4, width := 8 },
      { name := "supply_w0", index := 5, width := 8 },
      { name := "supply_w1", index := 6, width := 8 },
      { name := "supply_w2", index := 7, width := 8 },
      { name := "supply_w3", index := 8, width := 8 }
    ]
    constructor := {
      kind := .init
      name := "Examples.Capped.init"
      ixName := "initialize"
      paramCount := 1
      paramWidths := #[20]
      ops := #[
        .returnState (.lit 0),
        .returnState (.lit 100),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0),
        .returnState (.lit 0)
      ]
    }
    entries := #[
      mutEntry "Capped" "mint" 1 #[32] (ownerGate (guardPaused 1 (guardCap 1 0 #[
        .ite .ne (.lit 0) (.lit 1)
          #[.letLocal 0 (nextSupply 1),
            .letLocal 1 (nextSupply 2),
            .letLocal 2 (nextSupply 3),
            .storeField "supply_w0" (nextSupply 0),
            .storeField "supply_w1" (.local 0),
            .storeField "supply_w2" (.local 1),
            .storeField "supply_w3" (.local 2),
            .okState (u256Field 0 "w0")]
          #[.errorOverflow]
      ]))),
      mutEntry "Capped" "pause" 0 #[] (ownerGate #[
        .ite .ne (.lit 0) (.lit 1)
          #[.storeField "paused" (.lit 1), .okState (.lit 1)]
          #[.errorOverflow]
      ]),
      mutEntry "Capped" "unpause" 0 #[] (ownerGate #[
        .ite .ne (.lit 0) (.lit 1)
          #[.storeField "paused" (.lit 0), .okState (.lit 0)]
          #[.errorOverflow]
      ]),
      view256 "Capped" "capOf" 0 #[] (return256 fun limb =>
        .field (.arg 0) s!"cap_{limbName limb}"),
      {
        kind := .get
        name := "Examples.Capped.ownerOf"
        ixName := "ownerOf"
        selector := Keccak.selectorOfWidths "ownerOf" #[]
        retWidths := #[20]
        retCount := 3
        ops := #[
          .returnU64 (.ext .immW0 #[]),
          .returnU64 (.ext .immW1 #[]),
          .returnU64 (.ext .immW2 #[])
        ]
        view := true
      },
      {
        kind := .get
        name := "Examples.Capped.pausedOf"
        ixName := "pausedOf"
        selector := Keccak.selectorOfWidths "pausedOf" #[]
        retWidths := #[1]
        ops := #[.returnU64 (.field (.arg 0) "paused")]
        view := true
      },
      view256 "Capped" "totalSupply" 0 #[] (return256 fun limb =>
        .field (.arg 0) s!"supply_{limbName limb}")
    ]
  }

def programs : Array IR.Program :=
  (sources.filterMap fun src =>
    match IR.fromProgram src with
    | .ok p => some p
    | .error _ => none) ++ #[extractedTipJar, extractedVault, extractedToken, extractedWide,
      extractedConst, extractedOwnable, extractedCapped]

def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map IR.digestHex

end ProofForge.Evm.Golden
