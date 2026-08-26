import ProofForge.Extract.LegacyGolden
import ProofForge.Evm.IRCompat
import ProofForge.Evm.Ops
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
  ProofForge.Golden.extractedLang,
  ProofForge.Golden.extractedOwnable
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
  .ext (.arith256 op limb) #[
    u256Field a "w0", u256Field a "w1", u256Field a "w2", u256Field a "w3",
    u256Field b "w0", u256Field b "w1", u256Field b "w2", u256Field b "w3"
  ]

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
  .ext (.mapGetAddr256 limb)
    #[.lit (UInt64.ofNat base), addrField key "w0", addrField key "w1", addrField key "w2"]

private def getCaller256 (limb : Nat) (base : Nat) : Ops.Val :=
  .ext (.mapGetAddr256 limb) #[.lit (UInt64.ofNat base), callerW 0, callerW 1, callerW 2]

private def getPair256 (limb : Nat) (base owner spender : Nat) : Ops.Val :=
  .ext (.mapGetPair256 limb) #[
    .lit (UInt64.ofNat base),
    addrField owner "w0", addrField owner "w1", addrField owner "w2",
    addrField spender "w0", addrField spender "w1", addrField spender "w2"
  ]

private def getPairCaller256 (limb : Nat) (base owner : Nat) : Ops.Val :=
  .ext (.mapGetPair256 limb) #[
    .lit (UInt64.ofNat base),
    addrField owner "w0", addrField owner "w1", addrField owner "w2",
    callerW 0, callerW 1, callerW 2
  ]

private def arithGet (op limb : Nat) (lhs : Nat → Ops.Val) (rhs : Nat) : Ops.Val :=
  .ext (.arith256 op limb) #[
    lhs 0, lhs 1, lhs 2, lhs 3,
    u256Field rhs "w0", u256Field rhs "w1", u256Field rhs "w2", u256Field rhs "w3"
  ]

private def ge256 (lhs : Nat → Ops.Val) (rhs : Nat) : Ops.Val :=
  .ext .ge256 #[
    lhs 0, lhs 1, lhs 2, lhs 3,
    u256Field rhs "w0", u256Field rhs "w1", u256Field rhs "w2", u256Field rhs "w3"
  ]

private def setAddr256 (base key : Nat) (val : Nat → Ops.Val) : IR.Op :=
  .mapSetAddr256 (.lit (UInt64.ofNat base))
    (addrField key "w0") (addrField key "w1") (addrField key "w2")
    (val 0) (val 1) (val 2) (val 3)

private def setCaller256 (base : Nat) (val : Nat → Ops.Val) : IR.Op :=
  .mapSetAddr256 (.lit (UInt64.ofNat base)) (callerW 0) (callerW 1) (callerW 2)
    (val 0) (val 1) (val 2) (val 3)

private def setPairCaller256 (base owner : Nat) (val : Nat → Ops.Val) : IR.Op :=
  .mapSetPair256 (.lit (UInt64.ofNat base))
    (addrField owner "w0") (addrField owner "w1") (addrField owner "w2")
    (callerW 0) (callerW 1) (callerW 2)
    (val 0) (val 1) (val 2) (val 3)

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
      mutEntry "Vault" "pull" 3 #[20, 20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmTokenTransfer256
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
              (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3"),
            .returnU64 (u256Field 2 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Vault" "setU64" 2 #[8, 8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.mapSetU64 (.lit 0) (.arg 0) (.arg 1), .returnU64 (.arg 1)]
          #[.errorOverflow]
      ],
      dummyGet "Vault",
      {
        kind := .get
        name := "Examples.Vault.getU64"
        ixName := "getU64"
        selector := Keccak.selectorOfWidths "getU64" #[8]
        paramCount := 1
        paramWidths := #[8]
        ops := #[.mapGetU64 (.lit 0) (.arg 0), .returnU64 (.arg 0)]
        view := true
      },
      view256 "Vault" "held" 1 #[20] (return256 fun limb =>
        .ext (.tokenBalance256 limb) #[addrField 0 "w0", addrField 0 "w1", addrField 0 "w2"]),
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
  {
    name := "Token"
    slots := dummySlot
    constructor := dummyCtor "Token"
    entries := #[
      mutEntry "Token" "approve" 2 #[20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.mapSetPair256 (.lit 1)
              (callerW 0) (callerW 1) (callerW 2)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3"),
            .evmLogApproval256 (callerW 0) (callerW 1) (callerW 2)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3"),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Token" "logApprove" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmLog "Approval" (.arg 0), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "Token" "logXfer" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmLog "Transfer" (.arg 0), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "Token" "mint" 2 #[20, 32] #[
        .ite .ne (.lit 0) (.lit 1)
          #[setAddr256 0 0 (fun limb => u256Field 1 (limbName limb)),
            .evmLogTransfer256 (.lit 0) (.lit 0) (.lit 0)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3"),
            .returnU64 (u256Field 1 "w0")]
          #[.errorOverflow]
      ],
      mutEntry "Token" "transfer" 2 #[20, 32] #[
        .ite .eq (ge256 callerBal 1) (.lit 1)
          #[setCaller256 0 (fun limb => arithGet 1 limb callerBal 1),
            setAddr256 0 0 (fun limb => arithGet 0 limb destBal 1),
            .evmLogTransfer256 (callerW 0) (callerW 1) (callerW 2)
              (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3"),
            .returnU64 (u256Field 1 "w0")]
          #[.evmRevertInsufficient (callerBal 0) (callerBal 1) (callerBal 2) (callerBal 3)
              (u256Field 1 "w0") (u256Field 1 "w1") (u256Field 1 "w2") (u256Field 1 "w3"),
            .returnU64 (callerBal 0)]
      ],
      mutEntry "Token" "transferFrom" 3 #[20, 20, 32] #[
        .ite .eq (ge256 pairAllow 2) (.lit 1)
          #[.ite .eq (ge256 ownerBal 2) (.lit 1)
              #[setAddr256 0 0 (fun limb => arithGet 1 limb ownerBal 2),
                setAddr256 0 1 (fun limb => arithGet 0 limb destFrom 2),
                setPairCaller256 1 0 (fun limb => arithGet 1 limb pairAllow 2),
                .evmLogTransfer256 (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2")
                  (addrField 1 "w0") (addrField 1 "w1") (addrField 1 "w2")
                  (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3"),
                .returnU64 (u256Field 2 "w0")]
              #[.evmRevertInsufficient (ownerBal 0) (ownerBal 1) (ownerBal 2) (ownerBal 3)
                  (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3"),
                .returnU64 (ownerBal 0)]]
          #[.evmRevertInsufficient (pairAllow 0) (pairAllow 1) (pairAllow 2) (pairAllow 3)
              (u256Field 2 "w0") (u256Field 2 "w1") (u256Field 2 "w2") (u256Field 2 "w3"),
            .returnU64 (pairAllow 0)]
      ],
      view256 "Token" "allowanceOf" 2 #[20, 20] (return256 fun limb => getPair256 limb 1 0 1),
      view256 "Token" "balanceOf" 1 #[20] (return256 fun limb => getAddr256 limb 0 0),
      dummyGet "Token"
    ]
  }

/-- Live extract of `Examples.TipJar`; Legacy IR cannot represent `receive()`. -/
def extractedTipJar : IR.Program :=
  {
    name := "TipJar"
    slots := dummySlot
    constructor := dummyCtor "TipJar"
    entries := #[
      payEntry "TipJar" "deposit" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmDeposit (.arg 0), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "TipJar" "logTip" 1 #[8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmLog "Tipped" (.arg 0), .returnU64 (.arg 0)]
          #[.errorOverflow]
      ],
      mutEntry "TipJar" "payout" 2 #[20, 8] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmSendEth (addrField 0 "w0") (addrField 0 "w1") (addrField 0 "w2") (.arg 1),
            .returnU64 (.arg 1)]
          #[.errorOverflow]
      ],
      payEntry "TipJar" "receive" 0 #[] #[
        .ite .ne (.lit 0) (.lit 1)
          #[.evmReceive, .returnU64 (.lit 0)]
          #[.errorOverflow]
      ],
      viewEnv "TipJar" "callValue" (.ext .callValue #[]),
      viewAddr20 "TipJar" "caller20" (.ext .callerW0 #[]) (.ext .callerW1 #[]) (.ext .callerW2 #[]),
      viewEnv "TipJar" "callerW0" (.ext .callerW0 #[]),
      viewEnv "TipJar" "callerW1" (.ext .callerW1 #[]),
      viewEnv "TipJar" "callerW2" (.ext .callerW2 #[]),
      viewEnv "TipJar" "chainId" (.ext .chainId #[]),
      dummyGet "TipJar",
      viewAddr20 "TipJar" "self20" (.ext .selfW0 #[]) (.ext .selfW1 #[]) (.ext .selfW2 #[]),
      viewEnv "TipJar" "selfBal" (.ext .selfBalance #[]),
      viewEnv "TipJar" "selfLow" (.ext .self #[]),
      viewEnv "TipJar" "selfW0" (.ext .selfW0 #[]),
      viewEnv "TipJar" "selfW1" (.ext .selfW1 #[]),
      viewEnv "TipJar" "selfW2" (.ext .selfW2 #[]),
      viewEnv "TipJar" "timestamp" (.ext .timestamp #[])
    ]
  }

def programs : Array IR.Program :=
  (sources.filterMap fun src =>
    match IR.fromProgram src with
    | .ok p => some p
    | .error _ => none) ++ #[extractedTipJar, extractedVault, extractedToken, extractedWide]

def digestOf (name : String) : Option String :=
  (programs.find? (·.name == name)).map IR.digestHex

end ProofForge.Evm.Golden
