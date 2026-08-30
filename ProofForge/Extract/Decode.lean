import Lean
import ProofForge.Extract.Ops
import ProofForge.Profile
import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Svm.Runtime
import ProofForge.Evm.Runtime
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Promise
import ProofForge.Wasm.Near.Sdk.Transient
import ProofForge.Wasm.Near.Sdk.Storage
import ProofForge.Evm.Codec
import ProofForge.Wasm.Xrpl.Runtime
import ProofForge.Extract.Lexical

open Lean

namespace ProofForge.Extract

/-- NEAR Runtime host reads. Matched by const name before any empty-arg UInt64
unfold that would bake the irreducible stub body `0` into a literal. -/
private def nearRuntimeLeaf? (e : Expr) : Option Ops.Val :=
  if isConstNamed e ``ProofForge.Wasm.Near.Runtime.blockIndex then
    some Ops.Val.nearBlockIndex
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.blockTimestamp then
    some Ops.Val.nearBlockTimestamp
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessor then
    some Ops.Val.nearPredecessor
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorLen then
    some Ops.Val.nearPredecessorLen
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW1 then
    some Ops.Val.nearPredecessorW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW2 then
    some Ops.Val.nearPredecessorW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW3 then
    some Ops.Val.nearPredecessorW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW4 then
    some Ops.Val.nearPredecessorW4
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW5 then
    some Ops.Val.nearPredecessorW5
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW6 then
    some Ops.Val.nearPredecessorW6
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.predecessorW7 then
    some Ops.Val.nearPredecessorW7
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.attachedDeposit then
    some Ops.Val.nearAttachedDeposit
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.attachedDepositW0 then
    some Ops.Val.nearAttachedDepositW0
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.attachedDepositW1 then
    some Ops.Val.nearAttachedDepositW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountBalance then
    some Ops.Val.nearAccountBalance
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountBalanceW0 then
    some Ops.Val.nearAccountBalanceW0
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.accountBalanceW1 then
    some Ops.Val.nearAccountBalanceW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountId then
    some Ops.Val.nearCurrentAccountId
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdLen then
    some Ops.Val.nearCurrentAccountIdLen
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW1 then
    some Ops.Val.nearCurrentAccountIdW1
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW2 then
    some Ops.Val.nearCurrentAccountIdW2
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW3 then
    some Ops.Val.nearCurrentAccountIdW3
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW4 then
    some Ops.Val.nearCurrentAccountIdW4
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW5 then
    some Ops.Val.nearCurrentAccountIdW5
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW6 then
    some Ops.Val.nearCurrentAccountIdW6
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.currentAccountIdW7 then
    some Ops.Val.nearCurrentAccountIdW7
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultsCount then
    some Ops.Val.nearPromiseResultsCount
  else none

set_option maxRecDepth 2048 in
mutual
private partial def asVal (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    match e with
    | .letE _ _ value body _ => asVal env fuel' (body.instantiate1 value)
    | .bvar i => some (.arg i)
    | _ =>
      if let some reduced := reduceCtorProjection? env e then
        asVal env fuel' reduced
      else if let some reduced := reducePureInlineMatch? env e then
        asVal env fuel' reduced
      else if let some reduced := reduceInlineProjection? env e then
        asVal env fuel' reduced
      else if let some reduced := reduceUInt64NewtypeMatch? env e then
        asVal env fuel' reduced
      else if let some v := asLit fuel' e then some v
      else if let some payload := uint64NewtypeCtorPayload? env e then
        asVal env fuel' payload
      else if isConstNamed e ``localRef && e.getAppArgs.size ≥ 1 then
        match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
        | some (.lit i) => some (.local i.toNat)
        | _ => none
      else if isConstNamed e ``methodArgRef && e.getAppArgs.size ≥ 1 then
        match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
        | some (.lit i) => some (.local (methodArgLocalBase + i.toNat))
        | _ => none
      else if isConstNamed e ``ite && e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        let rawCond := strip args[args.size - 4]!
        let (cond, negate) :=
          if isConstNamed rawCond ``Not && rawCond.getAppArgs.size ≥ 1 then
            (strip rawCond.getAppArgs[rawCond.getAppArgs.size - 1]!, true)
          else
            (rawCond, false)
        let cmp? : Option Ops.Cmp :=
          if isConstNamed cond ``Eq || isConstNamed cond ``BEq.beq then some .eq
          else if isConstNamed cond ``Ne then some .ne
          else if isConstNamed cond ``LT.lt then some .lt
          else if isConstNamed cond ``LE.le then some .le
          else if isConstNamed cond ``GT.gt then some .gt
          else if isConstNamed cond ``GE.ge || endsWith cond ".ge" || endsWith cond ".hGe" then
            some .ge
          else none
        let invert : Ops.Cmp → Option Ops.Cmp
          | .eq => some .ne | .ne => some .eq
          | .lt => some .ge | .le => some .gt
          | .gt => some .le | .ge => some .lt
        let condArgs := cond.getAppArgs
        match cmp? with
        | some cmp =>
          if h : condArgs.size ≥ 2 then
            let lhs := condArgs[condArgs.size - 2]
            let rhs := condArgs[condArgs.size - 1]
            let cmp? := if negate then invert cmp else some cmp
            match cmp?, asVal env fuel' lhs, asVal env fuel' rhs,
                asVal env fuel' args[args.size - 2]!, asVal env fuel' args[args.size - 1]! with
            | some cmp, some lv, some rv, some thn, some els =>
                some (.select cmp lv rv thn els)
            | _, _, _, _, _ => none
          else none
        | none =>
          match asVal env fuel' rawCond,
              asVal env fuel' args[args.size - 2]!, asVal env fuel' args[args.size - 1]! with
          | some cond, some thn, some els => some (.select .ne cond (.lit 0) thn els)
          | _, _, _ => none
      else
        match e.getAppFn.constName? with
        | some n => asValNamed env fuel' n e
        | none => none

/-- The `constName` dispatch arm of `asVal`, extracted so the recursive value decoder
stays navigable. `fuel` here is the caller's already-decremented budget. -/
private partial def asValNamed (env : Environment) (fuel : Nat) (n : Name) (e : Expr) :
    Option Ops.Val :=
  let field := n.toString
  let user := isUserName env n || isBoundaryProjectionName env n
  if isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Get &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some index =>
        if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity.toNat then
          some (.nearTransientBuffer64Get capacity.toNat index)
        else none
    | _, _ => none
  else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultStatus ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultLength ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultFits) &&
      e.getAppArgs.size ≥ 1 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 1]!
    match asStaticLit env fuel capacityExpr with
    | some (.lit capacity) =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultStatus then
            some (.nearStorageResultStatus capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultLength then
            some (.nearStorageResultLength capacity)
          else
            some (.nearStorageResultFits capacity)
        else none
    | _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageResultByte &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some index =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          some (.nearStorageResultByte capacity index)
        else none
    | _, _ => none
  else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultStatus ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultLength ||
      isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultFits) &&
      e.getAppArgs.size ≥ 1 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 1]!
    match asStaticLit env fuel capacityExpr with
    | some (.lit capacity) =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultStatus then
            some (.nearPromiseResultStatus capacity)
          else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultLength then
            some (.nearPromiseResultLength capacity)
          else
            some (.nearPromiseResultFits capacity)
        else none
    | _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultByte &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some index =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          some (.nearPromiseResultByte capacity index)
        else none
    | _, _ => none
  else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultBorshUInt64D &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let capacityExpr := unfoldUserHelpers env 8 args[args.size - 2]!
    match asStaticLit env fuel capacityExpr, asVal env fuel args[args.size - 1]! with
    | some (.lit capacity), some fallback =>
        let capacity := capacity.toNat
        if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
          some (.nearPromiseResultBorshUInt64D capacity fallback)
        else none
    | _, _ => none
  else if let some leaf := nearRuntimeLeaf? e then
    some leaf
  else if (isConstNamed e ``Eq || isConstNamed e ``BEq.beq || isConstNamed e ``Ne ||
      isConstNamed e ``bne ||
      isConstNamed e ``LT.lt || isConstNamed e ``LE.le || isConstNamed e ``GT.gt ||
      isConstNamed e ``GE.ge || endsWith e ".ge" || endsWith e ".hGe") &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    let cmp : Ops.Cmp :=
      if isConstNamed e ``Eq || isConstNamed e ``BEq.beq then .eq
      else if isConstNamed e ``Ne || isConstNamed e ``bne then .ne
      else if isConstNamed e ``LT.lt then .lt
      else if isConstNamed e ``LE.le then .le
      else if isConstNamed e ``GT.gt then .gt
      else .ge
    let lhsE := args[args.size - 2]!
    let rhsE := args[args.size - 1]!
    if isAddr20Type (lhsE) || isAddr20Type (rhsE) ||
        isConstNamed lhsE ``ProofForge.Evm.Runtime.evmCaller20 ||
        isConstNamed rhsE ``ProofForge.Evm.Runtime.evmCaller20 ||
        isConstNamed lhsE ``ProofForge.Evm.Runtime.evmSelf20 ||
        isConstNamed rhsE ``ProofForge.Evm.Runtime.evmSelf20 then
      none
    else
      match asVal env fuel lhsE, asVal env fuel rhsE with
      | some lhs, some rhs => some (.select cmp lhs rhs (.lit 1) (.lit 0))
      | _, _ => none
  else if isConstNamed e ``Bool.or && e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 2]!,
        asVal env fuel args[args.size - 1]! with
    | some lhs, some rhs => some (.bitOr lhs rhs)
    | _, _ => none
  else if isConstNamed e ``Bool.and && e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 2]!,
        asVal env fuel args[args.size - 1]! with
    | some lhs, some rhs => some (.bitAnd lhs rhs)
    | _, _ => none
  else if isConstNamed e ``Bool.not && e.getAppArgs.size ≥ 1 then
    (asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!).map fun value =>
      .select .eq value (.lit 0) (.lit 1) (.lit 0)
  else if (isConstNamed e ``Prod.fst || isConstNamed e ``Prod.snd) &&
      e.getAppArgs.size ≥ 1 then
    let leaf := if isConstNamed e ``Prod.fst then "fst" else "snd"
    (asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!).map (flattenField · leaf)
  else if isConstNamed e ``Decidable.decide && e.getAppArgs.size ≥ 2 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!
  else if (endsWith e ".svmByteSwap64" ||
      isConstNamed e ``ProofForge.Svm.Runtime.svmByteSwap64) && e.getAppArgs.size ≥ 1 then
    (asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!).map Ops.Val.byteSwap64
  else if let some (_, unfolded) := unfoldUserHelper env e then
    match env.find? n with
    | some (.defnInfo info) =>
      if isScalarResult env info.type || isUInt256Type (resultType 16 info.type) ||
          isAddr20Type (resultType 16 info.type) ||
          isBytes32Type (resultType 16 info.type) then
        asVal env fuel unfolded
      else none
    | _ => none
  else if (endsWith e ".checkPdaSeeds" ||
      isConstNamed e ``ProofForge.Svm.Runtime.checkPdaSeeds) && e.getAppArgs.size ≥ 2 then
    match asLit fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asPdaSeeds e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit account), some seeds =>
        let account := account.toNat
        if Svm.Ops.cpiAccInRange account then some (.checkPdaSeeds account seeds) else none
    | _, _ => none
  else if (endsWith e ".findPdaSeeds" ||
      isConstNamed e ``ProofForge.Svm.Runtime.findPdaSeeds) && e.getAppArgs.size ≥ 1 then
    (asPdaSeeds e.getAppArgs[e.getAppArgs.size - 1]!).map Ops.Val.findPdaSeeds
  else if (endsWith e ".findPda" || isConstNamed e ``ProofForge.Svm.Runtime.findPda) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => if s.isEmpty then none else some (.findPda s)
    | _ => none
  else if (endsWith e ".sha256Lit" || isConstNamed e ``ProofForge.Svm.Runtime.sha256Lit) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.sha256Lit s)
    | _ => none
  else if isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplSha512HalfLit &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.xrplSha512HalfLit s)
    | _ => none
  else if (endsWith e ".xrplAccountLitW0" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplAccountLitW0) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.xrplAccountLitW0 s)
    | _ => none
  else if (endsWith e ".xrplAccountLitW1" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplAccountLitW1) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.xrplAccountLitW1 s)
    | _ => none
  else if (endsWith e ".xrplAccountLitW2" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplAccountLitW2) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.xrplAccountLitW2 s)
    | _ => none
  else if (endsWith e ".xrplLitBalanceDrops" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplLitBalanceDrops) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.xrplLitBalanceDrops s)
    | _ => none
  else if (endsWith e ".xrplStoreOwner" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplStoreOwner) &&
      e.getAppArgs.size ≥ 3 then
    let args := e.getAppArgs
    match asVal env fuel args[args.size - 3]!,
        asVal env fuel args[args.size - 2]!,
        asVal env fuel args[args.size - 1]! with
    | some w0, some w1, some w2 => some (.xrplStoreOwner w0 w1 w2)
    | _, _, _ => none
  else if (endsWith e ".keccak256Lit" || isConstNamed e ``ProofForge.Svm.Runtime.keccak256Lit) &&
      e.getAppArgs.size ≥ 1 then
    match strip e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s) => some (.keccak256Lit s)
    | _ => none
  else if (endsWith e ".accKeyWord" || isConstNamed e ``ProofForge.Svm.Runtime.accKeyWord) &&
      e.getAppArgs.size ≥ 2 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit word) =>
      let a := acc.toNat
      let w := word.toNat
      if Svm.Ops.accInRange a && w ≤ 3 then some (.accKeyWord a w) else none
    | _, _ => none
  else if (endsWith e ".accOwnerWord" || isConstNamed e ``ProofForge.Svm.Runtime.accOwnerWord) &&
      e.getAppArgs.size ≥ 2 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit word) =>
      let a := acc.toNat
      let w := word.toNat
      if Svm.Ops.accInRange a && w ≤ 3 then some (.accOwnerWord a w) else none
    | _, _ => none
  else if endsWith e ".fifoCancelQuoteReleased" ||
      isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelQuoteReleased then
    some (.fifoCancelResult .quoteReleased)
  else if endsWith e ".fifoCancelBaseReleased" ||
      isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelBaseReleased then
    some (.fifoCancelResult .baseReleased)
  else if endsWith e ".fifoCancelEventCount" ||
      isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelEventCount then
    some (.fifoCancelResult .eventCount)
  else if (endsWith e ".accDataWord" || isConstNamed e ``ProofForge.Svm.Runtime.accDataWord) &&
      e.getAppArgs.size ≥ 2 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit word) =>
      let a := acc.toNat
      let w := word.toNat
      if Svm.Ops.accInRange a && Svm.Ops.dataWordInRange w then
        some (.accDataWord a w)
      else none
    | _, _ => none
  else if (endsWith e ".memoryCompare" ||
      isConstNamed e ``ProofForge.Svm.Runtime.memoryCompare) && e.getAppArgs.size ≥ 5 then
    let args := e.getAppArgs
    match asStaticLit env fuel args[args.size - 5]!,
        asStaticLit env fuel args[args.size - 4]!,
        asStaticLit env fuel args[args.size - 3]!,
        asStaticLit env fuel args[args.size - 2]!,
        asStaticLit env fuel args[args.size - 1]! with
    | some (.lit leftAccount), some (.lit leftOffset), some (.lit rightAccount),
        some (.lit rightOffset), some (.lit length) =>
      let query : Svm.Memory.Query := .compare
        { account := leftAccount.toNat, offsetBytes := leftOffset.toNat,
          lengthBytes := length.toNat }
        { account := rightAccount.toNat, offsetBytes := rightOffset.toNat,
          lengthBytes := length.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.memory query))) #[])
      else none
    | _, _, _, _, _ => none
  else if (endsWith e ".transientVecLength" ||
      isConstNamed e ``ProofForge.Svm.Runtime.transientVecLength) && e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit capacity) =>
      let query : Svm.TransientVec.Query := .length { capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.transientVec query))) #[])
      else none
    | _ => none
  else if (endsWith e ".transientBytesLength" ||
      isConstNamed e ``ProofForge.Svm.Runtime.transientBytesLength) && e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit capacity) =>
      let query : Svm.TransientBytes.Query := .length { capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.transientBytes query))) #[])
      else none
    | _ => none
  else if (endsWith e ".remainingComputeUnits" ||
      isConstNamed e ``ProofForge.Svm.Runtime.remainingComputeUnits) && e.getAppArgs.isEmpty then
    some (.ext (.svm (.component (.telemetry .remainingComputeUnits))) #[])
  else if (endsWith e ".stackHeight" ||
      isConstNamed e ``ProofForge.Svm.Runtime.stackHeight) && e.getAppArgs.isEmpty then
    some (.ext (.svm (.component (.telemetry .stackHeight))) #[])
  else if (endsWith e ".transientVecGet" ||
      isConstNamed e ``ProofForge.Svm.Runtime.transientVecGet) && e.getAppArgs.size ≥ 2 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit capacity), some index =>
      let query : Svm.TransientVec.Query := .get { capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.transientVec query))) #[index])
      else none
    | _, _ => none
  else if (endsWith e ".transientVecPop" ||
      isConstNamed e ``ProofForge.Svm.Runtime.transientVecPop) && e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit capacity) =>
      let query : Svm.TransientVec.Query := .pop { capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.transientVec query))) #[])
      else none
    | _ => none
  else if (endsWith e ".transientBytesGet" ||
      isConstNamed e ``ProofForge.Svm.Runtime.transientBytesGet) && e.getAppArgs.size ≥ 2 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit capacity), some index =>
      let query : Svm.TransientBytes.Query := .get { capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.transientBytes query))) #[index])
      else none
    | _, _ => none
  else if (endsWith e ".transientBytesPop" ||
      isConstNamed e ``ProofForge.Svm.Runtime.transientBytesPop) && e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit capacity) =>
      let query : Svm.TransientBytes.Query := .pop { capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.transientBytes query))) #[])
      else none
    | _ => none
  else if (endsWith e ".accDataWordAt" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataWordAt) && e.getAppArgs.size ≥ 5 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit baseWord), some (.lit strideWords),
        some (.lit capacity), some index =>
      let a := acc.toNat
      let b := baseWord.toNat
      let s := strideWords.toNat
      let c := capacity.toNat
      if Svm.Ops.accInRange a && Svm.Ops.indexedDataWordsInRange b s c then
        some (.accDataWordAt a b s c index)
      else none
    | _, _, _, _, _ => none
  else if (endsWith e ".accDataWordAtOneBased" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataWordAtOneBased) &&
      e.getAppArgs.size ≥ 5 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit baseWord), some (.lit strideWords),
        some (.lit capacity), some index =>
      let query := Svm.AccountStorage.Query.readWordOneBased acc.toNat baseWord.toNat
        strideWords.toNat capacity.toNat
      if query.wellFormed then
        some (.accDataWordAtOneBased acc.toNat baseWord.toNat strideWords.toNat
          capacity.toNat index)
      else none
    | _, _, _, _, _ => none
  else if (endsWith e ".viewKeyWord" ||
      isConstNamed e ``ProofForge.Svm.Runtime.viewKeyWord) && e.getAppArgs.size ≥ 4 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some (.lit word), some index =>
      let query := Svm.AccountView.Query.header
        { base := base.toNat, capacity := capacity.toNat } (.key word.toNat)
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _, _ => none
  else if (endsWith e ".viewDataWord" ||
      isConstNamed e ``ProofForge.Svm.Runtime.viewDataWord) && e.getAppArgs.size ≥ 4 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some (.lit word), some index =>
      let query := Svm.AccountView.Query.dataWord
        { base := base.toNat, capacity := capacity.toNat } word.toNat
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _, _ => none
  else if (endsWith e ".viewOwnerIsSelf" ||
      isConstNamed e ``ProofForge.Svm.Runtime.viewOwnerIsSelf) && e.getAppArgs.size ≥ 3 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some index =>
      let query := Svm.AccountView.Query.ownerIsSelf
        { base := base.toNat, capacity := capacity.toNat }
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _ => none
  else if (endsWith e ".viewLamports" || isConstNamed e ``ProofForge.Svm.Runtime.viewLamports) &&
      e.getAppArgs.size ≥ 3 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some index =>
      let query := Svm.AccountView.Query.header
        { base := base.toNat, capacity := capacity.toNat } .lamports
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _ => none
  else if (endsWith e ".viewDataLen" || isConstNamed e ``ProofForge.Svm.Runtime.viewDataLen) &&
      e.getAppArgs.size ≥ 3 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some index =>
      let query := Svm.AccountView.Query.header
        { base := base.toNat, capacity := capacity.toNat } .dataLen
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _ => none
  else if (endsWith e ".viewIsSigner" || isConstNamed e ``ProofForge.Svm.Runtime.viewIsSigner) &&
      e.getAppArgs.size ≥ 3 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some index =>
      let query := Svm.AccountView.Query.header
        { base := base.toNat, capacity := capacity.toNat } .isSigner
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _ => none
  else if (endsWith e ".viewIsWritable" || isConstNamed e ``ProofForge.Svm.Runtime.viewIsWritable) &&
      e.getAppArgs.size ≥ 3 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit base), some (.lit capacity), some index =>
      let query := Svm.AccountView.Query.header
        { base := base.toNat, capacity := capacity.toNat } .isWritable
      if query.wellFormed then
        some (.ext (.svm (.component (.accountView query))) #[index])
      else none
    | _, _, _ => none
  else if (endsWith e ".accDataRbTreeKey4Find" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeKey4Find) &&
      e.getAppArgs.size ≥ 11 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 11]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 10]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 9]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 8]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 7]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 6]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit rootWord), some (.lit linksBaseWord),
        some (.lit parentBaseWord), some (.lit keyBaseWord), some (.lit strideWords),
        some (.lit capacity), some key0, some key1, some key2, some key3 =>
      let query := Svm.AccountStorage.Query.key4FindOneBased acc.toNat rootWord.toNat
        linksBaseWord.toNat parentBaseWord.toNat keyBaseWord.toNat strideWords.toNat
        capacity.toNat
      if query.wellFormed then
        some (.accDataRbTreeKey4Find acc.toNat rootWord.toNat linksBaseWord.toNat
          parentBaseWord.toNat keyBaseWord.toNat strideWords.toNat capacity.toNat
          key0 key1 key2 key3)
      else none
    | _, _, _, _, _, _, _, _, _, _, _ => none
  else if (endsWith e ".accDataRbTreeOrderFind" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeOrderFind) &&
      e.getAppArgs.size ≥ 11 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 11]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 10]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 9]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 8]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 7]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 6]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit rootWord), some (.lit linksBaseWord),
        some (.lit parentBaseWord), some (.lit keyBaseWord), some (.lit sequenceBaseWord),
        some (.lit strideWords), some (.lit capacity), some (.lit bid),
        some price, some sequence =>
      let query := Svm.AccountStorage.Query.fifoFindOneBased acc.toNat rootWord.toNat
        linksBaseWord.toNat parentBaseWord.toNat keyBaseWord.toNat sequenceBaseWord.toNat
        strideWords.toNat capacity.toNat (bid == 1)
      if (bid == 0 || bid == 1) && query.wellFormed then
        some (.accDataRbTreeOrderFind acc.toNat rootWord.toNat linksBaseWord.toNat
          parentBaseWord.toNat keyBaseWord.toNat sequenceBaseWord.toNat strideWords.toNat
          capacity.toNat (bid == 1) price sequence)
      else none
    | _, _, _, _, _, _, _, _, _, _, _ => none
  else if (endsWith e ".accDataRbTreeOrderCursor" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeOrderCursor) &&
      e.getAppArgs.size ≥ 12 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 12]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 11]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 10]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 9]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 8]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 7]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 6]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit rootWord), some (.lit linksBaseWord),
        some (.lit parentBaseWord), some (.lit keyBaseWord), some (.lit sequenceBaseWord),
        some (.lit strideWords), some (.lit capacity), some (.lit bid),
        some hasCursor, some price, some sequence =>
      let query := Svm.AccountStorage.Query.fifoCursorOneBased acc.toNat rootWord.toNat
        linksBaseWord.toNat parentBaseWord.toNat keyBaseWord.toNat sequenceBaseWord.toNat
        strideWords.toNat capacity.toNat (bid == 1)
      if (bid == 0 || bid == 1) && query.wellFormed then
        some (.accDataRbTreeOrderCursor acc.toNat rootWord.toNat linksBaseWord.toNat
          parentBaseWord.toNat keyBaseWord.toNat sequenceBaseWord.toNat strideWords.toNat
          capacity.toNat (bid == 1) hasCursor price sequence)
      else none
    | _, _, _, _, _, _, _, _, _, _, _, _ => none
  else if (endsWith e ".accDataParentPathValid" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataParentPathValid) &&
      e.getAppArgs.size ≥ 9 then
    match asLit fuel e.getAppArgs[e.getAppArgs.size - 9]!,
        asLit fuel e.getAppArgs[e.getAppArgs.size - 8]!,
        asLit fuel e.getAppArgs[e.getAppArgs.size - 7]!,
        asLit fuel e.getAppArgs[e.getAppArgs.size - 6]!,
        asLit fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asLit fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit linksBaseWord), some (.lit parentBaseWord),
        some (.lit strideWords), some (.lit capacity), some (.lit maxDepth),
        some index, some root, some bumpIndex =>
      let a := acc.toNat
      let l := linksBaseWord.toNat
      let p := parentBaseWord.toNat
      let s := strideWords.toNat
      let c := capacity.toNat
      let d := maxDepth.toNat
      if Svm.Ops.accInRange a && Svm.Ops.parentPathWordsInRange l p s c d then
        some (.accDataParentPathValid a l p s c d index root bumpIndex)
      else none
    | _, _, _, _, _, _, _, _, _ => none
  else if (endsWith e ".accDataRbTreeValid" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeValid) &&
      e.getAppArgs.size ≥ 12 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 12]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 11]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 10]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 9]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 8]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 7]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 6]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit linksBaseWord), some (.lit parentBaseWord),
        some (.lit keyBaseWord), some (.lit sequenceBaseWord), some (.lit strideWords),
        some (.lit capacity), some (.lit bid), some root, some size, some bumpIndex,
        some freeListHead =>
      let a := acc.toNat
      let l := linksBaseWord.toNat
      let p := parentBaseWord.toNat
      let k := keyBaseWord.toNat
      let q := sequenceBaseWord.toNat
      let s := strideWords.toNat
      let c := capacity.toNat
      if Svm.Ops.accInRange a &&
          Svm.Ops.rbTreeWordsInRange l p k q s c && (bid == 0 || bid == 1) then
        some (.accDataRbTreeValid a l p k q s c (bid == 1)
          root size bumpIndex freeListHead)
      else none
    | _, _, _, _, _, _, _, _, _, _, _, _ => none
  else if (endsWith e ".accDataRbTreeKey4Valid" ||
      isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeKey4Valid) &&
      e.getAppArgs.size ≥ 10 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 10]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 9]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 8]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 7]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 6]!,
        asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 5]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 4]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 3]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc), some (.lit linksBaseWord), some (.lit parentBaseWord),
        some (.lit keyBaseWord), some (.lit strideWords), some (.lit capacity),
        some root, some size, some bumpIndex, some freeListHead =>
      let a := acc.toNat
      let l := linksBaseWord.toNat
      let p := parentBaseWord.toNat
      let k := keyBaseWord.toNat
      let s := strideWords.toNat
      let c := capacity.toNat
      if Svm.Ops.accInRange a && Svm.Ops.rbTreeKey4WordsInRange l p k s c then
        some (.accDataRbTreeKey4Valid a l p k s c
          root size bumpIndex freeListHead)
      else none
    | _, _, _, _, _, _, _, _, _, _ => none
  else if (endsWith e ".checkPda" || isConstNamed e ``ProofForge.Svm.Runtime.checkPda) &&
      e.getAppArgs.size ≥ 2 then
    match strip e.getAppArgs[e.getAppArgs.size - 2]!,
        asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | .lit (.strVal s), some bump =>
      if s.isEmpty then none else some (.checkPda s bump)
    | _, _ => none
  else if (endsWith e ".rentExemption" ||
      isConstNamed e ``ProofForge.Svm.Runtime.rentExemption) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit n) => some (.ext (.svm (.component (.sysvar (.rentExemption n)))) #[])
    | _ => none
  else if (endsWith e ".accLamports" || isConstNamed e ``ProofForge.Svm.Runtime.accLamports) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.accLamportsN a) else none
    | _ => none
  else if (endsWith e ".accDataLen" || isConstNamed e ``ProofForge.Svm.Runtime.accDataLen) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.accDataLenN a) else none
    | _ => none
  else if (endsWith e ".isSigner" || isConstNamed e ``ProofForge.Svm.Runtime.isSigner) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.isSignerN a) else none
    | _ => none
  else if (endsWith e ".isWritable" || isConstNamed e ``ProofForge.Svm.Runtime.isWritable) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.isWritableN a) else none
    | _ => none
  else if (endsWith e ".isExecutable" || isConstNamed e ``ProofForge.Svm.Runtime.isExecutable) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.isExecutableN a) else none
    | _ => none
  else if (endsWith e ".signerKey" || isConstNamed e ``ProofForge.Svm.Runtime.signerKey) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.signerKeyN a) else none
    | _ => none
  else if (endsWith e ".ownerIsSelf" || isConstNamed e ``ProofForge.Svm.Runtime.ownerIsSelf) &&
      e.getAppArgs.size ≥ 1 then
    match asStaticLit env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.lit acc) =>
      let a := acc.toNat
      if Svm.Ops.accInRange a then some (.ownerIsSelf a) else none
    | _ => none
  else if let some leaf := uint256ProjLeaf n then
    let args := e.getAppArgs
    if args.isEmpty then none
    else
      let rawBase := args[args.size - 1]!
      let baseE := unfoldUserHelpers env 8 rawBase
      let limb := uint256LimbLit leaf
      let binaryQuery? : Option Evm.WideWord.Query :=
        if isConstNamed baseE ``ProofForge.Evm.Runtime.evmAdd256 ||
            endsWith baseE ".evmAdd256" then some (.arith256 0 limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmSub256 ||
            endsWith baseE ".evmSub256" then some (.arith256 1 limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmMul256 ||
            endsWith baseE ".evmMul256" then some (.arith256 2 limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmAnd256 ||
            endsWith baseE ".evmAnd256" then some (.bitwise256 .and limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmOr256 ||
            endsWith baseE ".evmOr256" then some (.bitwise256 .or limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmXor256 ||
            endsWith baseE ".evmXor256" then some (.bitwise256 .xor limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmDiv256 ||
            endsWith baseE ".evmDiv256" then some (.checkedDivMod256 .quotient limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmMod256 ||
            endsWith baseE ".evmMod256" then some (.checkedDivMod256 .remainder limb.toNat)
        else none
      let unaryQuery? : Option Evm.WideWord.Query :=
        if isConstNamed baseE ``ProofForge.Evm.Runtime.evmNot256 ||
            endsWith baseE ".evmNot256" then some (.not256 limb.toNat)
        else none
      let shiftQuery? : Option Evm.WideWord.Query :=
        if isConstNamed baseE ``ProofForge.Evm.Runtime.evmShl256 ||
            endsWith baseE ".evmShl256" then some (.shift256 .left limb.toNat)
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmShr256 ||
            endsWith baseE ".evmShr256" then some (.shift256 .right limb.toNat)
        else none
      let limbConst : String → Name
        | "w0" => ``ProofForge.Core.Value.UInt256.w0
        | "w1" => ``ProofForge.Core.Value.UInt256.w1
        | "w2" => ``ProofForge.Core.Value.UInt256.w2
        | _ => ``ProofForge.Core.Value.UInt256.w3
      let limbVal (base : Expr) (name : String) : Option Ops.Val :=
        asVal env fuel (mkApp (mkConst (limbConst name)) base)
      let wordVals (base : Expr) : Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val) := do
        let w0 ← limbVal base "w0"
        let w1 ← limbVal base "w1"
        let w2 ← limbVal base "w2"
        let w3 ← limbVal base "w3"
        some (w0, w1, w2, w3)
      match binaryQuery?, unaryQuery?, shiftQuery? with
      | some query, _, _ =>
        let bargs := baseE.getAppArgs
        if bargs.size < 2 then none
        else
          let aE := bargs[bargs.size - 2]!
          let bE := bargs[bargs.size - 1]!
          match wordVals aE, wordVals bE with
          | some (a0, a1, a2, a3), some (b0, b1, b2, b3) =>
            some (.ext (.evm (.component (.wideWord query))) #[a0, a1, a2, a3, b0, b1, b2, b3])
          | _, _ => none
      | none, some query, _ =>
        let bargs := baseE.getAppArgs
        if bargs.isEmpty then none
        else
          match wordVals bargs[bargs.size - 1]! with
          | some (a0, a1, a2, a3) =>
            some (.ext (.evm (.component (.wideWord query))) #[a0, a1, a2, a3])
          | none => none
      | none, none, some query =>
        let bargs := baseE.getAppArgs
        if bargs.size < 2 then none
        else
          let aE := bargs[bargs.size - 2]!
          let amountE := bargs[bargs.size - 1]!
          match wordVals aE, asVal env fuel amountE with
          | some (a0, a1, a2, a3), some amount =>
            some (.ext (.evm (.component (.wideWord query))) #[a0, a1, a2, a3, amount])
          | _, _ => none
      | none, none, none =>
        if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.attachedDeposit128 then
          if leaf == "w0" then some Ops.Val.nearAttachedDepositW0
          else if leaf == "w1" then some Ops.Val.nearAttachedDepositW1
          else none
        else if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.accountBalance128 then
          if leaf == "w0" then some Ops.Val.nearAccountBalanceW0
          else if leaf == "w1" then some Ops.Val.nearAccountBalanceW1
          else none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmMapGetAddr256 ||
            endsWith baseE ".evmMapGetAddr256" then
          let gargs := baseE.getAppArgs
          if gargs.size < 2 then none
          else
            let base := (asEvmMapBaseLit env fuel gargs[gargs.size - 2]! <|>
              asVal env fuel gargs[gargs.size - 2]!).map foldClosedU64
            let key := gargs[gargs.size - 1]!
            let k0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) key)
            let k1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) key)
            let k2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) key)
            match base, k0, k1, k2 with
            | some b, some a0, some a1, some a2 =>
              some (.ext (.evm (.component (.hashedMap (.getAddr256 limb.toNat)))) #[b, a0, a1, a2])
            | _, _, _, _ => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmMapGetPair256 ||
            endsWith baseE ".evmMapGetPair256" then
          let gargs := baseE.getAppArgs
          if gargs.size < 3 then none
          else
            let base := (asEvmMapBaseLit env fuel gargs[gargs.size - 3]! <|>
              asVal env fuel gargs[gargs.size - 3]!).map foldClosedU64
            let owner := gargs[gargs.size - 2]!
            let spender := gargs[gargs.size - 1]!
            let ow0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) owner)
            let ow1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) owner)
            let ow2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) owner)
            let sw0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) spender)
            let sw1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) spender)
            let sw2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) spender)
            match base, ow0, ow1, ow2, sw0, sw1, sw2 with
            | some b, some a0, some a1, some a2, some b0, some b1, some b2 =>
              some (.ext (.evm (.component (.hashedMap (.getPair256 limb.toNat)))) #[b, a0, a1, a2, b0, b1, b2])
            | _, _, _, _, _, _, _ => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmTokenBalanceOfSelf ||
            endsWith baseE ".evmTokenBalanceOfSelf" then
          let gargs := baseE.getAppArgs
          if gargs.isEmpty then none
          else
            let token := gargs[gargs.size - 1]!
            let t0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) token)
            let t1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) token)
            let t2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) token)
            match t0, t1, t2 with
            | some a0, some a1, some a2 =>
              some (.ext (.evm (.component (.closedCall (.balance256 limb.toNat)))) #[a0, a1, a2])
            | _, _, _ => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmTokenAllowanceOf ||
            endsWith baseE ".evmTokenAllowanceOf" then
          let gargs := baseE.getAppArgs
          if gargs.size < 3 then none
          else
            let token := gargs[gargs.size - 3]!
            let owner := gargs[gargs.size - 2]!
            let spender := gargs[gargs.size - 1]!
            let t0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) token)
            let t1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) token)
            let t2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) token)
            let o0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) owner)
            let o1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) owner)
            let o2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) owner)
            let s0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) spender)
            let s1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) spender)
            let s2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) spender)
            match t0, t1, t2, o0, o1, o2, s0, s1, s2 with
            | some a0, some a1, some a2, some b0, some b1, some b2, some c0, some c1, some c2 =>
              some (.ext (.evm (.component (.closedCall (.allowance256 limb.toNat))))
                #[a0, a1, a2, b0, b1, b2, c0, c1, c2])
            | _, _, _, _, _, _, _, _, _ => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmCallValue256 ||
            endsWith baseE ".evmCallValue256" then
          some (.ext (.evm (.callValue256 limb.toNat)) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmSelfBalance256 ||
            endsWith baseE ".evmSelfBalance256" then
          some (.ext (.evm (.selfBalance256 limb.toNat)) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmGasLeft256 ||
            endsWith baseE ".evmGasLeft256" then
          some (.ext (.evm (.component (.environment (.gasLeft256 limb.toNat)))) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmBaseFee256 ||
            endsWith baseE ".evmBaseFee256" then
          some (.ext (.evm (.component (.environment (.baseFee256 limb.toNat)))) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmPrevRandao256 ||
            endsWith baseE ".evmPrevRandao256" then
          some (.ext (.evm (.component (.environment (.prevRandao256 limb.toNat)))) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmGasLimit256 ||
            endsWith baseE ".evmGasLimit256" then
          some (.ext (.evm (.component (.environment (.gasLimit256 limb.toNat)))) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmGasPrice256 ||
            endsWith baseE ".evmGasPrice256" then
          some (.ext (.evm (.component (.environment (.gasPrice256 limb.toNat)))) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmBlobBaseFee256 ||
            endsWith baseE ".evmBlobBaseFee256" then
          some (.ext (.evm (.component (.environment (.blobBaseFee256 limb.toNat)))) #[])
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmBlobHash32 ||
            endsWith baseE ".evmBlobHash32" then
          let args := baseE.getAppArgs
          if args.isEmpty then none
          else
            match asVal env fuel args[args.size - 1]! with
            | some index =>
                some (.ext (.evm (.component (.environment (.blobHash32 limb.toNat)))) #[index])
            | none => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmSelector4 ||
            endsWith baseE ".evmSelector4" then
          if limb == 0 then some (.ext (.evm (.component (.environment .selector4))) #[])
          else none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmBalance256 ||
            endsWith baseE ".evmBalance256" then
          let args := baseE.getAppArgs
          if args.isEmpty then none
          else
            let address := args[args.size - 1]!
            let a0 := asVal env fuel
              (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) address)
            let a1 := asVal env fuel
              (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) address)
            let a2 := asVal env fuel
              (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) address)
            match a0, a1, a2 with
            | some w0, some w1, some w2 =>
                some (.ext (.evm (.component (.environment (.balance256 limb.toNat))))
                  #[w0, w1, w2])
            | _, _, _ => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmCodeHash32 ||
            endsWith baseE ".evmCodeHash32" then
          let args := baseE.getAppArgs
          if args.isEmpty then none
          else
            let address := args[args.size - 1]!
            let a0 := asVal env fuel
              (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) address)
            let a1 := asVal env fuel
              (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) address)
            let a2 := asVal env fuel
              (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) address)
            match a0, a1, a2 with
            | some w0, some w1, some w2 =>
                some (.ext (.evm (.component (.environment (.codeHash32 limb.toNat))))
                  #[w0, w1, w2])
            | _, _, _ => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmBlockHash256 ||
            endsWith baseE ".evmBlockHash256" then
          let args := baseE.getAppArgs
          if args.isEmpty then none
          else
            match asVal env fuel args[args.size - 1]! with
            | some number =>
                some (.ext (.evm (.component (.environment (.blockHash256 limb.toNat))))
                  #[number])
            | none => none
        else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmDomainSeparator ||
            endsWith baseE ".evmDomainSeparator" then
          some (.ext (.evm (.domainSep256 limb.toNat)) #[])
        else
          let projected := mkApp (mkConst (limbConst leaf)) baseE
          match reduceCtorProjection? env projected with
          | some reduced => asVal env fuel reduced
          | none =>
            match asVal env fuel baseE with
            | some b => some (flattenField b leaf)
            | none =>
              match strip baseE with
              | .bvar i => some (flattenField (.arg i) leaf)
              | _ => none
  else if let some leaf := nearAccountIdProjLeaf n then
    let args := e.getAppArgs
    if args.isEmpty then none
    else
      let baseE := unfoldUserHelpers env 8 args[args.size - 1]!
      if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.predecessorAccountId ||
          endsWith baseE ".predecessorAccountId" then
        some (match leaf with
          | "length" => .nearPredecessorLen
          | "w0" => .nearPredecessor
          | "w1" => .nearPredecessorW1 | "w2" => .nearPredecessorW2
          | "w3" => .nearPredecessorW3 | "w4" => .nearPredecessorW4
          | "w5" => .nearPredecessorW5 | "w6" => .nearPredecessorW6
          | _ => .nearPredecessorW7)
      else if isConstNamed baseE ``ProofForge.Wasm.Near.Runtime.selfAccountId ||
          endsWith baseE ".selfAccountId" then
        some (match leaf with
          | "length" => .nearCurrentAccountIdLen
          | "w0" => .nearCurrentAccountId
          | "w1" => .nearCurrentAccountIdW1 | "w2" => .nearCurrentAccountIdW2
          | "w3" => .nearCurrentAccountIdW3 | "w4" => .nearCurrentAccountIdW4
          | "w5" => .nearCurrentAccountIdW5 | "w6" => .nearCurrentAccountIdW6
          | _ => .nearCurrentAccountIdW7)
      else
        match asVal env fuel baseE with
        | some b => some (flattenField b leaf)
        | none =>
          match strip baseE with
          | .bvar i => some (flattenField (.arg i) leaf)
          | _ => none
  else if let some leaf := addr20ProjLeaf n then
    let args := e.getAppArgs
    if args.isEmpty then none
    else
      let baseE := unfoldUserHelpers env 8 args[args.size - 1]!
      if isConstNamed baseE ``ProofForge.Evm.Runtime.evmCaller20 ||
          endsWith baseE ".evmCaller20" then
        some (match leaf with
          | "w0" => .evmCallerW0 | "w1" => .evmCallerW1 | _ => .evmCallerW2)
      else if isConstNamed baseE ``ProofForge.Wasm.Xrpl.Runtime.xrplCaller20 ||
          endsWith baseE ".xrplCaller20" then
        some (match leaf with
          | "w0" => .xrplCallerW0 | "w1" => .xrplCallerW1 | _ => .xrplCallerW2)
      else if (isConstNamed baseE ``ProofForge.Wasm.Xrpl.Runtime.xrplAccountLit ||
          endsWith baseE ".xrplAccountLit") && baseE.getAppArgs.size ≥ 1 then
        match strip baseE.getAppArgs[baseE.getAppArgs.size - 1]! with
        | .lit (.strVal s) =>
          some (match leaf with
            | "w0" => .xrplAccountLitW0 s | "w1" => .xrplAccountLitW1 s | _ => .xrplAccountLitW2 s)
        | _ => none
      else if isConstNamed baseE ``ProofForge.Wasm.Xrpl.Runtime.xrplSelf20 ||
          endsWith baseE ".xrplSelf20" then
        some (match leaf with
          | "w0" => .xrplSelfW0 | "w1" => .xrplSelfW1 | _ => .xrplSelfW2)
      else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmSelf20 ||
          endsWith baseE ".evmSelf20" then
        some (match leaf with
          | "w0" => .evmSelfW0 | "w1" => .evmSelfW1 | _ => .evmSelfW2)
      else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmCoinbase20 ||
          endsWith baseE ".evmCoinbase20" then
        some (.ext (.evm (.component (.environment (.coinbase20
          (if leaf == "w0" then 0 else if leaf == "w1" then 1 else 2))))) #[])
      else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmOrigin20 ||
          endsWith baseE ".evmOrigin20" then
        some (.ext (.evm (.component (.environment (.origin20
          (if leaf == "w0" then 0 else if leaf == "w1" then 1 else 2))))) #[])
      else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmImm20b ||
          endsWith baseE ".evmImm20b" then
        some (match leaf with
          | "w0" => .evmImmX0 | "w1" => .evmImmX1 | _ => .evmImmX2)
      else if isConstNamed baseE ``ProofForge.Evm.Runtime.evmImm20 ||
          endsWith baseE ".evmImm20" then
        some (match leaf with
          | "w0" => .evmImmW0 | "w1" => .evmImmW1 | _ => .evmImmW2)
      else
        match asVal env fuel baseE with
        | some b => some (flattenField b leaf)
        | none =>
          match strip baseE with
          | .bvar i => some (flattenField (.arg i) leaf)
          | _ => none
  else if endsWith e ".evmCaller20" || isConstNamed e ``ProofForge.Evm.Runtime.evmCaller20 then
    none
  else if endsWith e ".xrplCaller20" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCaller20 then
    none
  else if endsWith e ".xrplAccountLit" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplAccountLit then
    none
  else if endsWith e ".xrplSelf20" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplSelf20 then
    none
  else if endsWith e ".evmSelf20" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelf20 then
    none
  else if endsWith e ".evmCoinbase20" || isConstNamed e ``ProofForge.Evm.Runtime.evmCoinbase20 then
    none
  else if endsWith e ".evmOrigin20" || isConstNamed e ``ProofForge.Evm.Runtime.evmOrigin20 then
    none
  else if endsWith e ".evmImm20b" || isConstNamed e ``ProofForge.Evm.Runtime.evmImm20b then
    none
  else if endsWith e ".evmImm20" || isConstNamed e ``ProofForge.Evm.Runtime.evmImm20 then
    none
  else if endsWith e ".evmMapGetAddr" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetAddr then
    let args := e.getAppArgs
    if args.size < 2 then none
    else
      let base := (asEvmMapBaseLit env fuel args[args.size - 2]! <|>
        asVal env fuel args[args.size - 2]!).map foldClosedU64
      let k0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) args[args.size - 1]!)
      let k1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) args[args.size - 1]!)
      let k2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) args[args.size - 1]!)
      match base, k0, k1, k2 with
      | some b, some a0, some a1, some a2 => some (.mapGetAddr b a0 a1 a2)
      | _, _, _, _ => none
  else if endsWith e ".evmMapGetPair" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetPair then
    let args := e.getAppArgs
    if args.size < 3 then none
    else
      let base := (asEvmMapBaseLit env fuel args[args.size - 3]! <|>
        asVal env fuel args[args.size - 3]!).map foldClosedU64
      let owner := args[args.size - 2]!
      let spender := args[args.size - 1]!
      let ow0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) owner)
      let ow1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) owner)
      let ow2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) owner)
      let sw0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) spender)
      let sw1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) spender)
      let sw2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) spender)
      match base, ow0, ow1, ow2, sw0, sw1, sw2 with
      | some b, some a0, some a1, some a2, some b0, some b1, some b2 =>
        some (.mapGetPair b a0 a1 a2 b0 b1 b2)
      | _, _, _, _, _, _, _ => none
  else if endsWith e ".evmGe256" || isConstNamed e ``ProofForge.Evm.Runtime.evmGe256 ||
      endsWith e ".evmEq256" || isConstNamed e ``ProofForge.Evm.Runtime.evmEq256 ||
      endsWith e ".evmLt256" || isConstNamed e ``ProofForge.Evm.Runtime.evmLt256 ||
      endsWith e ".evmLe256" || isConstNamed e ``ProofForge.Evm.Runtime.evmLe256 ||
      endsWith e ".evmGt256" || isConstNamed e ``ProofForge.Evm.Runtime.evmGt256 then
    let args := e.getAppArgs
    if args.size < 2 then none
    else
      let query : Evm.WideWord.Query :=
        if endsWith e ".evmEq256" || isConstNamed e ``ProofForge.Evm.Runtime.evmEq256 then
          .compare256 .eq
        else if endsWith e ".evmLt256" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmLt256 then
          .compare256 .lt
        else if endsWith e ".evmLe256" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmLe256 then
          .compare256 .le
        else if endsWith e ".evmGt256" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmGt256 then
          .compare256 .gt
        else
          .ge256
      let aE := args[args.size - 2]!
      let bE := args[args.size - 1]!
      let limbConst : String → Name
        | "w0" => ``ProofForge.Core.Value.UInt256.w0
        | "w1" => ``ProofForge.Core.Value.UInt256.w1
        | "w2" => ``ProofForge.Core.Value.UInt256.w2
        | _ => ``ProofForge.Core.Value.UInt256.w3
      let limbVal (base : Expr) (name : String) : Option Ops.Val :=
        asVal env fuel (mkApp (mkConst (limbConst name)) base)
      match limbVal aE "w0", limbVal aE "w1", limbVal aE "w2", limbVal aE "w3",
          limbVal bE "w0", limbVal bE "w1", limbVal bE "w2", limbVal bE "w3" with
      | some a0, some a1, some a2, some a3, some b0, some b1, some b2, some b3 =>
        some (.ext (.evm (.component (.wideWord query))) #[a0, a1, a2, a3, b0, b1, b2, b3])
      | _, _, _, _, _, _, _, _ => none
  else if endsWith e ".evmEq20" || isConstNamed e ``ProofForge.Evm.Runtime.evmEq20 then
    let args := e.getAppArgs
    if args.size < 2 then none
    else
      let aE := unfoldUserHelpers env 8 args[args.size - 2]!
      let bE := unfoldUserHelpers env 8 args[args.size - 1]!
      let limbA (name : Name) : Option Ops.Val :=
        asVal env fuel (mkApp (mkConst name) aE)
      let limbB (name : Name) : Option Ops.Val :=
        asVal env fuel (mkApp (mkConst name) bE)
      match limbA ``ProofForge.Evm.Runtime.Addr20.w0,
          limbA ``ProofForge.Evm.Runtime.Addr20.w1,
          limbA ``ProofForge.Evm.Runtime.Addr20.w2,
          limbB ``ProofForge.Evm.Runtime.Addr20.w0,
          limbB ``ProofForge.Evm.Runtime.Addr20.w1,
          limbB ``ProofForge.Evm.Runtime.Addr20.w2 with
      | some a0, some a1, some a2, some b0, some b1, some b2 =>
        some (.ext (.evm (.component (.wideWord .eq20))) #[a0, a1, a2, b0, b1, b2])
      | _, _, _, _, _, _ => none
  else if endsWith e ".evmMapGetU64" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetU64 then
    let args := e.getAppArgs
    let get (n : Nat) : Ops.Val :=
      if args.size ≥ n + 1 then (asVal env fuel args[args.size - 1 - n]!).getD (.arg n)
      else .arg n
    let base :=
      if args.size ≥ 2 then
        foldClosedU64 <| (asEvmMapBaseLit env fuel args[args.size - 2]!).getD (get 1)
      else .arg 1
    some (.mapGetU64 base (get 0))
  else if user && field.contains "." && e.getAppArgs.size ≥ 1 then
    let proj :=
      match field.splitOn "." with
      | [] => field
      | parts => parts.getLast!
    if proj == "mk" || proj == "ok" || proj == "error" ||
        proj.startsWith "_proof" || proj == "rfl" ||
        (field.startsWith "ProofForge.Svm.Runtime." ||
          field.startsWith "ProofForge.Evm.Runtime.") then none
    else if match env.find? n with
        | some (.ctorInfo _) => true
        | some (.inductInfo _) => true
        | _ => false then none
    else
      -- 整个 Vector 投影本身不是叶。下标 / 元素字段再展开。
      let skipVector :=
        match env.find? n with
        | some info =>
          info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
        | none => false
      if skipVector then none
      else
        match asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
        | some b =>
          let leaf := if looksLikeOptionProj env n then s!"{proj}_tag" else proj
          -- `s.nodes[0]!.value`：基是 `nodes_0`，叶是 `value`。
          some (flattenField b leaf)
        | none =>
          match e.getAppArgs[e.getAppArgs.size - 1]! with
          | .bvar i =>
            let leaf := if looksLikeOptionProj env n then s!"{proj}_tag" else proj
            some (flattenField (.arg i) leaf)
          | _ => none
  else if (isConstNamed e ``UInt8.toUInt64 || isConstNamed e ``UInt64.toUInt8 ||
      isConstNamed e ``UInt16.toUInt64 || isConstNamed e ``UInt64.toUInt16 ||
      isConstNamed e ``UInt32.toUInt64 || isConstNamed e ``UInt64.toUInt32 ||
      isConstNamed e ``UInt64.toNat || isConstNamed e ``UInt64.ofNat) &&
      e.getAppArgs.size ≥ 1 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!
    else if (isConstNamed e ``HAdd.hAdd || endsWith e ".hAdd") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.addU64 l r)
    | _, _ => none
    else if (isConstNamed e ``Nat.sub ||
        (isConstNamed e ``HSub.hSub && e.getAppArgs.size ≥ 3 &&
          isConstNamed e.getAppArgs[0]! ``Nat &&
          isConstNamed e.getAppArgs[1]! ``Nat &&
          isConstNamed e.getAppArgs[2]! ``Nat)) && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.select .ge l r (.subU64 l r) (.lit 0))
    | _, _ => none
    else if (isConstNamed e ``HSub.hSub || endsWith e ".hSub") &&
        e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.subU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HMul.hMul || endsWith e ".hMul") &&
        e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.mulU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HDiv.hDiv || endsWith e ".hDiv" ||
        isConstNamed e ``UInt64.div) && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.divU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HMod.hMod || endsWith e ".hMod" ||
        isConstNamed e ``UInt64.mod) && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.modU64 l r)
    | _, _ => none
    else if (isConstNamed e ``HAnd.hAnd || endsWith e ".hAnd") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.bitAnd l r)
    | _, _ => none
  else if (isConstNamed e ``HOr.hOr || endsWith e ".hOr") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.bitOr l r)
    | _, _ => none
  else if (isConstNamed e ``HXor.hXor || endsWith e ".hXor") && e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.bitXor l r)
    | _, _ => none
  else if (isConstNamed e ``Complement.complement || endsWith e ".complement") &&
      e.getAppArgs.size ≥ 1 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some v => some (.bitNot v)
    | none => none
  else if (isConstNamed e ``HShiftLeft.hShiftLeft || endsWith e ".hShiftLeft") &&
      e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.shiftL l r)
    | _, _ => none
  else if (isConstNamed e ``HShiftRight.hShiftRight || endsWith e ".hShiftRight") &&
      e.getAppArgs.size ≥ 2 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 2]!,
          asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some l, some r => some (.shiftR l r)
    | _, _ => none
  else if (isConstNamed e ``Option.isSome || endsWith e ".isSome") && e.getAppArgs.size ≥ 1 then
    match asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]! with
    | some (.field b n) =>
      if n.endsWith "_tag" then some (.field b n)
      else some (.field b s!"{n}_tag")
    | some b => some (.field b s!"slot_tag")
    | none => none
  else if endsWith e ".clockSlot" || isConstNamed e ``ProofForge.Svm.Runtime.clockSlot then
    some (.ext (.svm (.component (.sysvar (.clock .slot)))) #[])
  else if endsWith e ".clockEpoch" || isConstNamed e ``ProofForge.Svm.Runtime.clockEpoch then
    some (.ext (.svm (.component (.sysvar (.clock .epoch)))) #[])
  else if endsWith e ".clockLeaderScheduleEpoch" ||
      isConstNamed e ``ProofForge.Svm.Runtime.clockLeaderScheduleEpoch then
    some (.ext (.svm (.component (.sysvar (.clock .leaderScheduleEpoch)))) #[])
  else if endsWith e ".unixTime" || isConstNamed e ``ProofForge.Svm.Runtime.unixTime then
    some (.ext (.svm (.component (.sysvar (.clock .unixTimestamp)))) #[])
  else if endsWith e ".slotsPerEpoch" || isConstNamed e ``ProofForge.Svm.Runtime.slotsPerEpoch then
    some (.ext (.svm (.component (.sysvar (.epochSchedule .slotsPerEpoch)))) #[])
  else if endsWith e ".epochScheduleLeaderScheduleSlotOffset" ||
      isConstNamed e ``ProofForge.Svm.Runtime.epochScheduleLeaderScheduleSlotOffset then
    some (.ext (.svm (.component (.sysvar (.epochSchedule .leaderScheduleSlotOffset)))) #[])
  else if endsWith e ".epochScheduleWarmup" ||
      isConstNamed e ``ProofForge.Svm.Runtime.epochScheduleWarmup then
    some (.ext (.svm (.component (.sysvar (.epochSchedule .warmup)))) #[])
  else if endsWith e ".epochScheduleFirstNormalEpoch" ||
      isConstNamed e ``ProofForge.Svm.Runtime.epochScheduleFirstNormalEpoch then
    some (.ext (.svm (.component (.sysvar (.epochSchedule .firstNormalEpoch)))) #[])
  else if endsWith e ".epochScheduleFirstNormalSlot" ||
      isConstNamed e ``ProofForge.Svm.Runtime.epochScheduleFirstNormalSlot then
    some (.ext (.svm (.component (.sysvar (.epochSchedule .firstNormalSlot)))) #[])
  else if endsWith e ".cpiReturn" || isConstNamed e ``ProofForge.Svm.Runtime.cpiReturn then
    some .cpiReturn
  else if endsWith e ".signerKey0" || isConstNamed e ``ProofForge.Svm.Runtime.signerKey0 then
    some .signerKey0
  else if endsWith e ".evmCodeSize20" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmCodeSize20 then
    let args := e.getAppArgs
    if args.isEmpty then none
    else
      let address := args[args.size - 1]!
      let a0 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) address)
      let a1 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) address)
      let a2 := asVal env fuel (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) address)
      match a0, a1, a2 with
      | some w0, some w1, some w2 =>
          some (.ext (.evm (.component (.environment .codeSize20))) #[w0, w1, w2])
      | _, _, _ => none
  else if endsWith e ".evmCalldataSize" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmCalldataSize then
    some (.ext (.evm (.component (.environment .calldataSize))) #[])
  else if let some leaf := nearRuntimeLeaf? e then
    some leaf
  else if endsWith e ".evmCaller" || isConstNamed e ``ProofForge.Evm.Runtime.evmCaller then
    some .evmCaller
  else if endsWith e ".evmBlockNumber" || isConstNamed e ``ProofForge.Evm.Runtime.evmBlockNumber then
    some .evmBlockNumber
  else if endsWith e ".evmTimestamp" || isConstNamed e ``ProofForge.Evm.Runtime.evmTimestamp then
    some .evmTimestamp
  else if endsWith e ".evmChainId" || isConstNamed e ``ProofForge.Evm.Runtime.evmChainId then
    some .evmChainId
  else if endsWith e ".evmSelf" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelf then
    some .evmSelf
  else if endsWith e ".evmCallValue" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallValue then
    some .evmCallValue
  else if endsWith e ".evmSelfBalance" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfBalance then
    some .evmSelfBalance
  else if endsWith e ".evmCallerW0" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallerW0 then
    some .evmCallerW0
  else if endsWith e ".evmCallerW1" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallerW1 then
    some .evmCallerW1
  else if endsWith e ".evmCallerW2" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallerW2 then
    some .evmCallerW2
  else if endsWith e ".xrplCallerW0" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerW0 then
    some .xrplCallerW0
  else if endsWith e ".xrplCallerW1" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerW1 then
    some .xrplCallerW1
  else if endsWith e ".xrplCallerW2" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerW2 then
    some .xrplCallerW2
  else if endsWith e ".xrplSelfW0" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplSelfW0 then
    some .xrplSelfW0
  else if endsWith e ".xrplSelfW1" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplSelfW1 then
    some .xrplSelfW1
  else if endsWith e ".xrplSelfW2" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplSelfW2 then
    some .xrplSelfW2
  else if endsWith e ".xrplLedgerSqn" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplLedgerSqn then
    some .xrplLedgerSqn
  else if endsWith e ".xrplParentTime" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplParentTime then
    some .xrplParentTime
  else if endsWith e ".xrplParentHashW0" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplParentHashW0 then
    some .xrplParentHashW0
  else if endsWith e ".xrplBaseFee" || isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplBaseFee then
    some .xrplBaseFee
  else if endsWith e ".xrplCallerBalanceDrops" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerBalanceDrops then
    some .xrplCallerBalanceDrops
  else if endsWith e ".xrplCallerSequence" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerSequence then
    some .xrplCallerSequence
  else if endsWith e ".xrplCallerFlags" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerFlags then
    some .xrplCallerFlags
  else if endsWith e ".xrplCallerOwnerCount" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplCallerOwnerCount then
    some .xrplCallerOwnerCount
  else if endsWith e ".xrplTxSequence" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplTxSequence then
    some .xrplTxSequence
  else if endsWith e ".xrplTxFeeDrops" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplTxFeeDrops then
    some .xrplTxFeeDrops
  else if endsWith e ".xrplTxFlags" ||
      isConstNamed e ``ProofForge.Wasm.Xrpl.Runtime.xrplTxFlags then
    some .xrplTxFlags
  else if endsWith e ".evmSelfW0" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfW0 then
    some .evmSelfW0
  else if endsWith e ".evmSelfW1" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfW1 then
    some .evmSelfW1
  else if endsWith e ".evmSelfW2" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfW2 then
    some .evmSelfW2
  else if endsWith e ".evmImmU64" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmU64 then
    some .evmImmU64
  else if endsWith e ".evmImmU64b" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmU64b then
    some .evmImmU64b
  else if endsWith e ".evmImmW0" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmW0 then
    some .evmImmW0
  else if endsWith e ".evmImmW1" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmW1 then
    some .evmImmW1
  else if endsWith e ".evmImmW2" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmW2 then
    some .evmImmW2
  else if endsWith e ".evmImmX0" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmX0 then
    some .evmImmX0
  else if endsWith e ".evmImmX1" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmX1 then
    some .evmImmX1
  else if endsWith e ".evmImmX2" || isConstNamed e ``ProofForge.Evm.Runtime.evmImmX2 then
    some .evmImmX2
  else if endsWith e ".accLamports0" || isConstNamed e ``ProofForge.Svm.Runtime.accLamports0 then
    some .accLamports0
  else if endsWith e ".accOwner0" || isConstNamed e ``ProofForge.Svm.Runtime.accOwner0 then
    some .accOwner0
  else if endsWith e ".accDataLen0" || isConstNamed e ``ProofForge.Svm.Runtime.accDataLen0 then
    some .accDataLen0
  else if endsWith e ".accN" || isConstNamed e ``ProofForge.Svm.Runtime.accN then
    some .accN
  else if endsWith e ".isSigner0" || isConstNamed e ``ProofForge.Svm.Runtime.isSigner0 then
    some .isSigner0
  else if endsWith e ".isWritable0" || isConstNamed e ``ProofForge.Svm.Runtime.isWritable0 then
    some .isWritable0
  else if endsWith e ".isExecutable0" || isConstNamed e ``ProofForge.Svm.Runtime.isExecutable0 then
    some .isExecutable0
  else if endsWith e ".accLamports1" || isConstNamed e ``ProofForge.Svm.Runtime.accLamports1 then
    some .accLamports1
  else if endsWith e ".accOwner1" || isConstNamed e ``ProofForge.Svm.Runtime.accOwner1 then
    some .accOwner1
  else if endsWith e ".accDataLen1" || isConstNamed e ``ProofForge.Svm.Runtime.accDataLen1 then
    some .accDataLen1
  else if endsWith e ".isSigner1" || isConstNamed e ``ProofForge.Svm.Runtime.isSigner1 then
    some .isSigner1
  else if endsWith e ".isWritable1" || isConstNamed e ``ProofForge.Svm.Runtime.isWritable1 then
    some .isWritable1
  else if endsWith e ".isExecutable1" || isConstNamed e ``ProofForge.Svm.Runtime.isExecutable1 then
    some .isExecutable1
  else if (endsWith e ".systemTransfer" ||
      isConstNamed e ``ProofForge.Svm.Runtime.systemTransfer) && e.getAppArgs.size ≥ 1 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!
  else if endsWith e ".invokeAcc1" || isConstNamed e ``ProofForge.Svm.Runtime.invokeAcc1 ||
      endsWith e ".invoke" || isConstNamed e ``ProofForge.Svm.Runtime.invoke ||
      endsWith e ".invokeSigned" || isConstNamed e ``ProofForge.Svm.Runtime.invokeSigned then
    some (.lit 0)
  else if ((endsWith e ".evmDeposit" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmDeposit) ||
      (endsWith e ".evmDeposit256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmDeposit256) ||
      (endsWith e ".evmLogTipped" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLogTipped) ||
      (endsWith e ".evmLogIncremented" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLogIncremented) ||
      (endsWith e ".evmLogTransfer" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLogTransfer) ||
      (endsWith e ".evmLogApproval" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLogApproval) ||
      (endsWith e ".evmLogTransfer256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLogTransfer256) ||
      (endsWith e ".evmLogApproval256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLogApproval256) ||
      (endsWith e ".evmSendEth" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmSendEth) ||
      (endsWith e ".evmSendEth256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmSendEth256) ||
      (endsWith e ".evmMapGetU64" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetU64) ||
      (endsWith e ".evmMapSetU64" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMapSetU64) ||
      (endsWith e ".evmMapGetAddr" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetAddr) ||
      (endsWith e ".evmMapSetAddr" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMapSetAddr) ||
      (endsWith e ".evmMapGetPair" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetPair) ||
      (endsWith e ".evmMapSetPair" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMapSetPair) ||
      (endsWith e ".evmTokenTransfer" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmTokenTransfer) ||
      (endsWith e ".evmTokenApprove" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmTokenApprove) ||
      (endsWith e ".evmTokenTransferFrom" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmTokenTransferFrom) ||
      (endsWith e ".evmTokenBalanceOfSelf" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmTokenBalanceOfSelf) ||
      (endsWith e ".evmTokenAllowanceOf" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmTokenAllowanceOf) ||
      (endsWith e ".evmWethDeposit" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmWethDeposit) ||
      (endsWith e ".evmWethWithdraw" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmWethWithdraw) ||
      (endsWith e ".evmSwapExact2" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmSwapExact2) ||
      (endsWith e ".evmSwapExact3" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmSwapExact3) ||
      (endsWith e ".evmTokenPermit" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmTokenPermit) ||
      (endsWith e ".evmPermit" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmPermit)) &&
      e.getAppArgs.size ≥ 1 then
      if endsWith e ".evmMapGetU64" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetU64 then
      let args := e.getAppArgs
      let get (n : Nat) : Ops.Val :=
        if args.size ≥ n + 1 then (asVal env fuel args[args.size - 1 - n]!).getD (.arg n)
        else .arg n
      some (.mapGetU64 (get 1) (get 0))
      else if endsWith e ".evmMapGetAddr" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetAddr then
      let args := e.getAppArgs
      let get (n : Nat) : Ops.Val :=
        if args.size ≥ n + 1 then (asVal env fuel args[args.size - 1 - n]!).getD (.arg n)
        else .arg n
      some (.mapGetAddr (get 3) (get 2) (get 1) (get 0))
      else if endsWith e ".evmMapGetPair" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetPair then
      let args := e.getAppArgs
      let get (n : Nat) : Ops.Val :=
        if args.size ≥ n + 1 then (asVal env fuel args[args.size - 1 - n]!).getD (.arg n)
        else .arg n
      some (.mapGetPair (get 6) (get 5) (get 4) (get 3) (get 2) (get 1) (get 0))
      else if endsWith e ".evmLogTransfer256" ||
          isConstNamed e ``ProofForge.Evm.Runtime.evmLogTransfer256 ||
          endsWith e ".evmLogApproval256" ||
          isConstNamed e ``ProofForge.Evm.Runtime.evmLogApproval256 then
      -- Event stubs use the amount's low limb as their source-level carrier. Preserve that value
      -- when a reusable SDK combinator sequences the effect into a wider result expression.
      let projected := mkApp (mkConst ``ProofForge.Core.Value.UInt256.w0)
        e.getAppArgs[e.getAppArgs.size - 1]!
      asVal env fuel projected
      else
      asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!
      else if isConstNamed e ``Bool.true || endsWith e ".true" then
      some (.lit 1)
  else if isConstNamed e ``Bool.false || endsWith e ".false" then
    some (.lit 0)
  else if user && e.getAppArgs.isEmpty then
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo c) =>
        match enumCtorIndex env c.induct ctor with
        | some i => some (.lit (UInt64.ofNat i))
        | none => none
      | _ => none
    | none => none
  else if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0)
  else if (isConstNamed e ``Option.some || endsWith e ".some") && e.getAppArgs.size ≥ 1 then
    asVal env fuel e.getAppArgs[e.getAppArgs.size - 1]!
  else if (isConstNamed e ``GetElem.getElem || isConstNamed e ``GetElem?.getElem! ||
      isConstNamed e ``Vector.get ||
      endsWith e ".getElem" || endsWith e ".getElem!" || endsWith e ".get") &&
      e.getAppArgs.size ≥ 2 then
    let args := e.getAppArgs
    -- Do not recursively search proof/type arguments for an index: their local binders
    -- are not source values. The collection/index positions are fixed by GetElem.
    let collIndex? : Option (Expr × Expr) :=
      if isConstNamed e ``GetElem.getElem || endsWith e ".getElem" then
        if h : args.size ≥ 3 then some (args[args.size - 3], args[args.size - 2])
        else none
      else if h : args.size ≥ 2 then
        some (args[args.size - 2], args[args.size - 1])
      else none
    let rec findState (fuel : Nat) (e : Expr) : Option Ops.Val :=
      match fuel with
      | 0 => none
      | fuel + 1 =>
        match strip e with
        | .bvar j => some (.arg j)
        | e =>
          if isConstNamed e ``methodArgRef && e.getAppArgs.size ≥ 1 then
            match asLit fuel e.getAppArgs[e.getAppArgs.size - 1]! with
            | some (.lit i) => some (.local (methodArgLocalBase + i.toNat))
            | _ => none
          else e.getAppArgs.findSome? (findState fuel)
    match collIndex?.bind fun pair => (asVal env fuel pair.2).map (pair.1, ·) with
    | some (collection, .lit n) =>
      let i := n.toNat
      let baseField :=
        match asVal env fuel collection with
        | some (.field _ fname) => some fname
        | _ => none
      match findState fuel collection, baseField with
      | some base, some fname =>
        let suf := s!"_{i}"
        let baseName :=
          if fname.endsWith suf then fname.dropEnd suf.length |>.copy else fname
        some (.field base s!"{baseName}_{i}")
      | some base, none =>
        match vectorBaseName env 8 collection with
        | some fname => some (.field base s!"{fname}_{i}")
        | none =>
            if isConstNamed collection ``methodArgRef then some (.field base s!"_{i}")
            else none
      | _, _ => none
    | some (collection, idx) =>
      let lits := args.filterMap (asLit fuel)
      let len :=
        if h : lits.size > 0 then
          match lits[0] with
          | .lit n => n.toNat
          | _ => 0
        else 0
      match findState fuel collection, vectorBaseName env 8 collection with
      | some base, some fname => some (.indexGet base fname idx len)
      | _, _ => none
    | none => none

  else if e.getAppArgs.isEmpty then
    match env.find? n with
    | some (.defnInfo info) =>
      if info.type.consumeMData.getAppFn.constName? == some ``UInt64 then
        match asVal env fuel info.value with
        | some value =>
            match staticUInt64? value with
            | some literal => some (.lit literal)
            | none => some value
        | none => none
      else none
    | _ => none
  else none
end
private def val (env : Environment) (e : Expr) : Option Ops.Val :=
  -- Bounded tree algorithms naturally compose several parent/child projections. Their elaborated
  -- `GetElem`/`toNat` wrappers are deeper than ordinary scalar expressions, but still finite.
  asVal env 32 e

private def addr20Leaves (env : Environment) (e : Expr) : Ops.Val × Ops.Val × Ops.Val :=
  let e := unfoldUserHelpers env 8 e
  if isConstNamed e ``ProofForge.Evm.Runtime.evmCaller20 || endsWith e ".evmCaller20" then
    (.evmCallerW0, .evmCallerW1, .evmCallerW2)
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmSelf20 || endsWith e ".evmSelf20" then
    (.evmSelfW0, .evmSelfW1, .evmSelfW2)
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmCoinbase20 || endsWith e ".evmCoinbase20" then
    (.ext (.evm (.component (.environment (.coinbase20 0)))) #[],
      .ext (.evm (.component (.environment (.coinbase20 1)))) #[],
      .ext (.evm (.component (.environment (.coinbase20 2)))) #[])
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmOrigin20 || endsWith e ".evmOrigin20" then
    (.ext (.evm (.component (.environment (.origin20 0)))) #[],
      .ext (.evm (.component (.environment (.origin20 1)))) #[],
      .ext (.evm (.component (.environment (.origin20 2)))) #[])
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmImm20b || endsWith e ".evmImm20b" then
    (.evmImmX0, .evmImmX1, .evmImmX2)
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmImm20 || endsWith e ".evmImm20" then
    (.evmImmW0, .evmImmW1, .evmImmW2)
  else
    let w0 := val env (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w0) e)
    let w1 := val env (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w1) e)
    let w2 := val env (mkApp (mkConst ``ProofForge.Evm.Runtime.Addr20.w2) e)
    match w0, w1, w2 with
    | some a, some b, some c => (a, b, c)
    | _, _, _ =>
      match val env e with
      | some v => (flattenField v "w0", flattenField v "w1", flattenField v "w2")
      | none => (.field (.arg 0) "w0", .field (.arg 0) "w1", .field (.arg 0) "w2")

private def addr20CtorFields (env : Environment) (e : Expr) : Option (Array Expr) :=
  let e := peelLets (strip e)
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    match env.find? n with
    | some (.ctorInfo c) =>
      if c.induct == addr20Name && e.getAppArgs.size ≥ 3 then
        some (e.getAppArgs.extract (e.getAppArgs.size - 3) e.getAppArgs.size)
      else none
    | _ => none

private def uint256CtorFields (env : Environment) (e : Expr) : Option (Array Expr) :=
  let e := peelLets (strip e)
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    match env.find? n with
    | some (.ctorInfo c) =>
      if (c.induct == uint256Name || c.induct == fixedBytesName) && e.getAppArgs.size ≥ 4 then
        some (e.getAppArgs.extract (e.getAppArgs.size - 4) e.getAppArgs.size)
      else none
    | _ => none

private def uint256Leaves (env : Environment) (e : Expr) :
    Ops.Val × Ops.Val × Ops.Val × Ops.Val :=
  let e := unfoldUserHelpers env 8 e
  let projConst : String → Name
    | "w0" => ``ProofForge.Core.Value.UInt256.w0
    | "w1" => ``ProofForge.Core.Value.UInt256.w1
    | "w2" => ``ProofForge.Core.Value.UInt256.w2
    | _ => ``ProofForge.Core.Value.UInt256.w3
  let proj (name : String) : Ops.Val :=
    (val env (mkApp (mkConst (projConst name)) e)).getD (flattenField (.arg 0) name)
  match uint256CtorFields env e with
  | some fields =>
    let leaf (i : Nat) : Ops.Val := (val env fields[i]!).getD (proj s!"w{i}")
    (leaf 0, leaf 1, leaf 2, leaf 3)
  | none =>
    if isConstNamed e ``ProofForge.Evm.Runtime.evmAdd256 || endsWith e ".evmAdd256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmSub256 || endsWith e ".evmSub256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmMul256 || endsWith e ".evmMul256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmAnd256 || endsWith e ".evmAnd256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmOr256 || endsWith e ".evmOr256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmXor256 || endsWith e ".evmXor256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmNot256 || endsWith e ".evmNot256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmShl256 || endsWith e ".evmShl256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmShr256 || endsWith e ".evmShr256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmDiv256 || endsWith e ".evmDiv256" ||
        isConstNamed e ``ProofForge.Evm.Runtime.evmMod256 || endsWith e ".evmMod256" then
      (proj "w0", proj "w1", proj "w2", proj "w3")
    else
      match val env e with
      | some v =>
        (flattenField v "w0", flattenField v "w1", flattenField v "w2", flattenField v "w3")
      | none => (proj "w0", proj "w1", proj "w2", proj "w3")

private def bytes32Leaves (env : Environment) (e : Expr) :
    Ops.Val × Ops.Val × Ops.Val × Ops.Val :=
  let projConst : String → Name
    | "w0" => ``ProofForge.Core.Value.FixedBytes.w0
    | "w1" => ``ProofForge.Core.Value.FixedBytes.w1
    | "w2" => ``ProofForge.Core.Value.FixedBytes.w2
    | _ => ``ProofForge.Core.Value.FixedBytes.w3
  let proj (name : String) : Ops.Val :=
    (val env (mkApp (mkConst (projConst name)) e)).getD (flattenField (.arg 0) name)
  match uint256CtorFields env e with
  | some fields =>
    let leaf (i : Nat) : Ops.Val := (val env fields[i]!).getD (proj s!"w{i}")
    (leaf 0, leaf 1, leaf 2, leaf 3)
  | none =>
    match val env e with
    | some v => (flattenField v "w0", flattenField v "w1", flattenField v "w2", flattenField v "w3")
    | none => (proj "w0", proj "w1", proj "w2", proj "w3")

/-- Decode a scalar binding through pure explicitly-inline facade layers before substituting it.
This preserves shared target reads without increasing the global value-decoder fuel or recognizing
the facade's namespace. -/
private partial def valNodeCount : Ops.Val → Nat
  | .arg _ | .local _ | .lit _ | .loopIx => 1
  | .field base _ | .bitNot base => 1 + valNodeCount base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      1 + valNodeCount lhs + valNodeCount rhs
  | .indexGet base _ index _ _ => 1 + valNodeCount base + valNodeCount index
  | .select _ lhs rhs thn els =>
      1 + valNodeCount lhs + valNodeCount rhs + valNodeCount thn + valNodeCount els
  | .ext _ operands =>
      1 + operands.foldl (init := 0) fun total operand => total + valNodeCount operand

private partial def readsMutableNearResult : Ops.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => readsMutableNearResult base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs | .addU64 lhs rhs | .subU64 lhs rhs
  | .mulU64 lhs rhs | .divU64 lhs rhs | .modU64 lhs rhs =>
      readsMutableNearResult lhs || readsMutableNearResult rhs
  | .indexGet base _ index _ _ =>
      readsMutableNearResult base || readsMutableNearResult index
  | .select _ lhs rhs thn els =>
      readsMutableNearResult lhs || readsMutableNearResult rhs ||
        readsMutableNearResult thn || readsMutableNearResult els
  | .ext (.near (.storageResultStatus _)) _
  | .ext (.near (.storageResultLength _)) _
  | .ext (.near (.storageResultFits _)) _
  | .ext (.near (.storageResultByte _)) _
  | .ext (.near (.promiseResultStatus _)) _
  | .ext (.near (.promiseResultLength _)) _
  | .ext (.near (.promiseResultFits _)) _
  | .ext (.near (.promiseResultByte _)) _
  | .ext (.near (.promiseResultBorshUInt64D _)) _ => true
  | .ext _ operands => operands.any readsMutableNearResult

/-- Materialize scalar source values whose substitution would duplicate bounded control flow or
re-evaluate a target read after a later effect. -/
private def shouldMaterializeLocal (_type : Expr) (value : Ops.Val) : Bool :=
  match value with
  | .field .. | .indexGet .. | .select .. | .ext .. => true
  | value => readsMutableNearResult value || valNodeCount value ≥ 1024

private def localScalarValue? (env : Environment) (fuel : Nat) (value : Expr) : Option Ops.Val :=
  let rec go (fuel : Nat) (value : Expr) : Option Ops.Val :=
    let value := substLets 64 value
    asVal env 64 value <|>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        if let some reduced := reducePureInlineMatch? env value then
          go fuel' reduced
        else if let some (helper, unfolded) := unfoldUserHelper env value then
          if inlineHelperPreservesUserType env helper then none else go fuel' unfolded
        else
          none
  go fuel value

private def asUInt64VariantCtor (env : Environment) (e : Expr) :
    Option (UInt64 × Array Ops.Val × Nat) := do
  let ctorName ← e.getAppFn.constName?
  let .ctorInfo ctor ← env.find? ctorName | none
  let payloadWidth ← uint64VariantPayloadWidth? env ctor.induct
  let index ← enumCtorIndex env ctor.induct ctorName
  let args := e.getAppArgs
  if args.size < ctor.numFields then none else pure ()
  let mut payloads : Array Ops.Val := #[]
  for offset in [:ctor.numFields] do
    let payloadExpr ← args[args.size - ctor.numFields + offset]?
    let payload ← val env payloadExpr
    payloads := payloads.push payload
  return (UInt64.ofNat index, payloads, payloadWidth)

private def asSubFromMax (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HSub.hSub then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]! >>= staticUInt64? with
      | some max => if max == ~~~(0 : UInt64) then val env args[args.size - 1]! else none
      | none => none
    else none
  else none

/-- `x ≤ u64Max - y`  →  checked add x y。单独的 `x ≤ u64Max` 不是 add。 -/
private def asCheckedAddGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]!, asSubFromMax env args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def asDivFromMax (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HDiv.hDiv then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]! >>= staticUInt64? with
      | some max => if max == ~~~(0 : UInt64) then val env args[args.size - 1]! else none
      | none => none
    else none
  else none

/-- `x ≤ u64Max / y`  →  checked mul x y -/
private def asCheckedMulGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]!, asDivFromMax env args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def binArgs (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none

private def looksAddr20Expr (env : Environment) (e : Expr) : Bool :=
  isConstNamed e ``ProofForge.Evm.Runtime.evmCaller20 || endsWith e ".evmCaller20" ||
    isConstNamed e ``ProofForge.Evm.Runtime.evmSelf20 || endsWith e ".evmSelf20" ||
    isConstNamed e ``ProofForge.Evm.Runtime.evmCoinbase20 || endsWith e ".evmCoinbase20" ||
    isConstNamed e ``ProofForge.Evm.Runtime.evmOrigin20 || endsWith e ".evmOrigin20" ||
    (addr20CtorFields env e).isSome ||
    (match e.getAppFn.constName? with
      | some n =>
        match env.find? n with
        | some info =>
          (resultType 16 info.type).consumeMData.getAppFn.constName? == some addr20Name
        | none => false
      | none => false)

private def asCmpCoreWithFuel (env : Environment) (fuel : Nat) (e : Expr) :
    Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Eq || isConstNamed e ``BEq.beq then
    match binArgs e with
    | some (l, r) =>
      if looksAddr20Expr env l || looksAddr20Expr env r then none
      else
        match asVal env fuel l, asVal env fuel r with
        | some lv, some rv => some (.eq, lv, rv)
        | _, _ => none
    | none => none
  else if isConstNamed e ``Ne || isConstNamed e ``bne then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.ne, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LT.lt then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.lt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LE.le then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.le, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GT.gt then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.gt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GE.ge || endsWith e ".ge" || endsWith e ".hGe" then
    match binArgs e with
    | some (l, r) =>
      match asVal env fuel l, asVal env fuel r with
      | some lv, some rv => some (.ge, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmGe256 || endsWith e ".evmGe256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmEq256 || endsWith e ".evmEq256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLt256 || endsWith e ".evmLt256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmLe256 || endsWith e ".evmLe256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmGt256 || endsWith e ".evmGt256" then
    match asVal env fuel e with
    | some v => some (.ne, v, .lit 0)
    | none => none
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmEq20 || endsWith e ".evmEq20" then
    match asVal env fuel e with
    | some v => some (.ne, v, .lit 0)
    | none => none
  else none

private def asCmpCore (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  asCmpCoreWithFuel env 32 e

private def asCmp (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Not then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      match asCmpCore env args[args.size - 1]! with
      | some (.eq, l, r) => some (.ne, l, r)
      | some (.ne, l, r) => some (.eq, l, r)
      | _ => none
    else none
  else
    match asCmpCore env e with
    | some t => some t
    | none =>
      if isConstNamed e ``Eq then
        match binArgs e with
        | some (l, r) =>
          let l := strip l
          let r := strip r
          let trueR := isConstNamed r ``Bool.true || endsWith r ".true"
          let noneR := isConstNamed r ``Option.none || endsWith r ".none"
          let noneL := isConstNamed l ``Option.none || endsWith l ".none"
          if trueR && (isConstNamed l ``Option.isSome || endsWith l ".isSome") then
            match val env l with
            | some (.field b n) =>
              let tag := if n.endsWith "_tag" then n else s!"{n}_tag"
              some (.ne, .field b tag, .lit 0)
            | some b => some (.ne, .field b "slot_tag", .lit 0)
            | none => some (.ne, .field (.arg 0) "slot_tag", .lit 0)
          else if noneR then
            match val env l with
            | some lv => some (.eq, lv, .lit 0)
            | none => none
          else if noneL then
            match val env r with
            | some rv => some (.eq, rv, .lit 0)
            | none => none
          else none
        | none => none
      else if isConstNamed e ``Option.isSome || endsWith e ".isSome" then
        let args := e.getAppArgs
        if args.size ≥ 1 then
          match val env args[args.size - 1]! with
          | some (.field b n) =>
            let tag := if n.endsWith "_tag" then n else s!"{n}_tag"
            some (.ne, .field b tag, .lit 0)
          | some b => some (.ne, .field b "slot_tag", .lit 0)
          | none => none
        else none
      else none

/-- Normalize pure Boolean syntax to a 0/1 value so compound guards do not duplicate branches. -/
private def asBoolVal (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      asBoolVal env fuel' (body.instantiate1 value)
    else
    let args := e.getAppArgs
    let last? := if h : args.size > 0 then some args[args.size - 1] else none
    if isConstNamed e ``Bool.true then some (.lit 1)
    else if isConstNamed e ``Bool.false then some (.lit 0)
    else if isConstNamed e ``Bool.or && args.size ≥ 2 then
      match asBoolVal env fuel' args[args.size - 2]!, asBoolVal env fuel' args[args.size - 1]! with
      | some lhs, some rhs => some (.bitOr lhs rhs)
      | _, _ => none
    else if isConstNamed e ``Bool.and && args.size ≥ 2 then
      match asBoolVal env fuel' args[args.size - 2]!, asBoolVal env fuel' args[args.size - 1]! with
      | some lhs, some rhs => some (.bitAnd lhs rhs)
      | _, _ => none
    else if isConstNamed e ``Bool.not then
      last?.bind fun value =>
        (asBoolVal env fuel' value).map fun v => .select .eq v (.lit 0) (.lit 1) (.lit 0)
    else if (isConstNamed e ``ite || isConstNamed e ``dite) && args.size ≥ 4 then
      let peelProofLam (value : Expr) : Expr :=
        match strip value with
        | .lam _ _ body _ => body.lowerLooseBVars 1 1
        | value => value
      match asBoolVal env fuel' args[args.size - 4]!,
          asBoolVal env fuel' (peelProofLam args[args.size - 2]!),
          asBoolVal env fuel' (peelProofLam args[args.size - 1]!) with
      | some cond, some thn, some els => some (.select .ne cond (.lit 0) thn els)
      | _, _, _ => none
    else if isConstNamed e ``Decidable.decide && args.size ≥ 2 then
      asBoolVal env fuel' args[args.size - 2]!
    else if isConstNamed e ``Eq && args.size ≥ 2 then
      let lhs := strip args[args.size - 2]!
      let rhs := strip args[args.size - 1]!
      if isConstNamed rhs ``Bool.true then asBoolVal env fuel' lhs
      else if isConstNamed lhs ``Bool.true then asBoolVal env fuel' rhs
      else if isConstNamed rhs ``Bool.false then
        (asBoolVal env fuel' lhs).map fun v => .select .eq v (.lit 0) (.lit 1) (.lit 0)
      else if isConstNamed lhs ``Bool.false then
        (asBoolVal env fuel' rhs).map fun v => .select .eq v (.lit 0) (.lit 1) (.lit 0)
      else
        (asCmp env e).map fun (cmp, lhs, rhs) => .select cmp lhs rhs (.lit 1) (.lit 0)
    else
      match asCmp env e with
      | some (cmp, lhs, rhs) => some (.select cmp lhs rhs (.lit 1) (.lit 0))
      | none =>
        match unfoldUserHelper env e with
        | some (_, unfolded) => asBoolVal env fuel' unfolded
        | none => none

private def asCondition (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  -- Bounded tree guards can contain several nested projected lookups. Keep ordinary value
  -- decoding conservative, but let an explicit control-flow boundary finish that finite tree.
  asCmp env e <|> asCmpCoreWithFuel env 128 e <|>
    (asBoolVal env 64 e).map fun value => (.ne, value, .lit 0)

/-- `x ≥ y` / `y ≤ x`  →  checked sub x y。`x ≤ lit` 是上界（255 / u64Max），不是 sub。 -/
private def asCheckedSubGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  match asCmp env e with
  | some (.le, _, .lit _) => none
  | some (.le, rhs, lhs) => some (lhs, rhs)
  | some (.ge, lhs, rhs) => some (lhs, rhs)
  | _ => none

/-- `den ≠ 0` 才是除法守卫。两边都是字面量的 `0 ≠ 1` 不算。 -/
private def asNeZero (env : Environment) (e : Expr) : Option Ops.Val :=
  match asCmp env e with
  | some (.ne, .lit _, .lit _) => none
  | some (.ne, v, .lit 0) => some v
  | some (.ne, .lit 0, v) => some v
  | _ => none

private def asEqZero (env : Environment) (e : Expr) : Option Ops.Val :=
  match asCmp env e with
  | some (.eq, v, .lit 0) => some v
  | some (.eq, .lit 0, v) => some v
  | _ => none

/-- 多字段 `State.mk a b …`：init 用第一个显式参数；checked 更新用最后一个。 -/
private def asStateMk (env : Environment) (e : Expr) (preferLast := false) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Prod.mk || endsWith e ".Prod.mk" then none
  else if (uint256CtorFields env e).isSome then none
  else if endsWith e ".State.mk" || endsWith e ".mk" then
    let args := e.getAppArgs
    if args.size = 0 then none
    else if preferLast then val env args[args.size - 1]!
    else
      match args.findSome? (val env) with
      | some v => some v
      | none => val env args[args.size - 1]!
  else none

private def asOptionPayload (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0)
  else if isConstNamed e ``Option.some || endsWith e ".some" then
    let args := e.getAppArgs
    if args.size ≥ 1 then val env args[args.size - 1]! else none
  else
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo c) =>
        if isOptionLikeInductive env c.induct || isEnumLeaf env c.induct then
          match enumCtorIndex env c.induct ctor with
          | some 0 => some (.lit 0)
          | some _ =>
            if c.numFields == 0 then some (.lit 1)
            else if e.getAppArgs.size ≥ 1 then val env e.getAppArgs[e.getAppArgs.size - 1]!
            else none
          | none => none
        else none
      | _ => none
    | none => none

/-- Preserve the constructor discriminant when an Option-like value becomes storage leaves. -/
private def asOptionStorage (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0, .lit 0)
  else if isConstNamed e ``Option.some || endsWith e ".some" then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      (val env args[args.size - 1]!).map fun payload => (.lit 1, payload)
    else none
  else
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo info) =>
        if isOptionLikeInductive env info.induct then
          match enumCtorIndex env info.induct ctor with
          | some 0 => some (.lit 0, .lit 0)
          | some _ =>
            if info.numFields == 0 then some (.lit 1, .lit 1)
            else if e.getAppArgs.size ≥ 1 then
              (val env e.getAppArgs[e.getAppArgs.size - 1]!).map fun payload =>
                (.lit 1, payload)
            else none
          | none => none
        else none
      | _ => none
    | none => none

/-- Unwrap only sequencing carriers around a returned Option. `peelControl` intentionally erases
`Option.some` for payload-oriented consumers, so fixed result framing must inspect it first. -/
private def asConstructedOptionResult (env : Environment) : Nat → Expr →
    Option (Ops.Val × Ops.Val)
  | 0, e => asOptionStorage env e
  | fuel' + 1, e =>
      let e := peelLets (strip e)
      if (isConstNamed e ``Pure.pure || endsWith e ".pure" ||
          isConstNamed e ``ForInStep.done || endsWith e ".done") &&
          e.getAppArgs.size ≥ 1 then
        asConstructedOptionResult env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
      else
        asOptionStorage env e

/-- `#v[a, b, …]` = `Vector.mk (List.toArray (a :: b :: []))`。 -/
private def collectListVals (env : Environment) (fuel : Nat) (e : Expr) : Array Ops.Val :=
  match fuel with
  | 0 => #[]
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.nil || endsWith e ".nil" then
      #[]
    else if isConstNamed e ``List.cons || endsWith e ".cons" then
      let args := e.getAppArgs
      if args.size ≥ 2 then
        let head := args[args.size - 2]!
        let tail := args[args.size - 1]!
        match val env head with
        | some v => #[v] ++ collectListVals env fuel' tail
        | none => collectListVals env fuel' tail
      else #[]
    else if isConstNamed e ``List.toArray || endsWith e ".toArray" then
      let args := e.getAppArgs
      if args.size ≥ 1 then collectListVals env fuel' args[args.size - 1]! else #[]
    else
      match val env e with
      | some v => #[v]
      | none => #[]

private def findListVals (env : Environment) (fuel : Nat) (e : Expr) : Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.cons || endsWith e ".cons" then
      some (collectListVals env 16 e)
    else
      e.getAppArgs.findSome? (findListVals env fuel')

private def asVectorLits (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Vector.mk || endsWith e "Vector.mk" then
    match findListVals env 16 e with
    | some vs => if vs.isEmpty then none else some vs
    | none => none
  else none

/-- A constructed bounded boundary value already has the target-neutral fixed frame expected by
the codec adapters: one length followed by every compile-time-capacity slot. Keep this recognition
separate from ordinary user structures because these compiler-owned polymorphic carriers are not
persistent state and their capacity parameter is erased after extraction. -/
private def asBoundedCtorFields (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let e := substLets 32 (strip e)
  let ctor ← e.getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  unless info.induct == boundedVecName || info.induct == boundedBytesName ||
      info.induct == boundedStringName do none
  let args := e.getAppArgs
  unless args.size ≥ 2 do none
  let length ← val env args[args.size - 2]!
  let values ← asVectorLits env args[args.size - 1]!
  return #[length] ++ values

/-- A reusable compiler-owned `@[pf_boundary]` value is source data, not persistent State.
Unfold only explicitly bounded helpers to its constructor and expose every scalar field through
the ordinary fixed return frame. Schema validation and target codecs still decide whether that
frame is admissible and how it is serialized. -/
private def asRegisteredBoundaryCtorFields (env : Environment) (e : Expr) :
    Option (Array Ops.Val) := do
  let e := substLets 32 (strip (unfoldUserHelpers env 16 e))
  let ctor ← e.getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  unless Attr.isBoundary env info.induct do none
  let args := e.getAppArgs
  unless info.numFields ≤ args.size do none
  let fields := args.extract (args.size - info.numFields) args.size
  let values ← fields.mapM (val env)
  unless values.size == info.numFields do none
  return values

/-- `xs.set i v`：只抽出被改的那一叶。 -/
private def asVectorSet (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isVectorSet e then
    let args := e.getAppArgs
    -- 只认编译期常量下标。运行时下标走 `asIndexSet`。
    -- `Vector.set.{u} α n xs i v h` 里 `n` 是长度，不能当 index。
    let idx? : Option Nat :=
      Id.run do
        let mut seenLen := false
        for a in args do
          match asLit 8 a with
          | some (.lit n) =>
            if !seenLen then
              seenLen := true
            else
              return some n.toNat
          | _ => pure ()
        return none
    -- `Vector.set xs i v h`：值在字面量下标之后。
    -- 嵌套 `Node.mk` 时取被改的那一叶（preferLast）。
    let payload :=
      Id.run do
        let mut seenIdx := false
        for a in args do
          match asLit 8 a with
          | some (.lit _) =>
            seenIdx := true
          | _ =>
            if seenIdx then
              -- `{ s.nodes[0]! with value := v }` 展开成 `have __src := …; Node.mk …`。
              let a := peelLets (strip a)
              match asStateMk env a true with
              | some v => return some (true, v)
              | none =>
                match val env a with
                | some v => return some (false, v)
                | none => pure ()
        return none
    match idx?, payload, vectorBaseName env 16 e with
    | some i, some (true, v), some n => some (.field v s!"{n}_{i}_value")
    | some i, some (false, v), some n => some (.field v s!"{n}_{i}")
    | _, _, _ => none
  else none

/-- `State.mk` 每个字段一个值。`Option` 展开成 tag + payload；`Vector` 展开成各叶。 -/
private def asIndexSets (env : Environment) (e0 : Expr) : Option (Array Ops.Op) :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ => go fuel' value <|> go fuel' body
      | .lam _ _ body _ => go fuel' body
      | _ =>
        if isConstNamed e ``Except.ok && e.getAppArgs.size ≥ 1 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 2]!
        else if isVectorSet e then
          some e
        else
          e.getAppArgs.findSome? (go fuel')
  match go 8 e0 with
  | none => none
  | some e =>
  if isVectorSet e then
    let args := e.getAppArgs
    let lits := args.filterMap (asLit 8)
    let len :=
      if h : lits.size > 0 then
        match lits[0] with
        | .lit n => n.toNat
        | _ => 0
      else 0
    -- `Vector.set α n xs i v h`：最后四项固定为 xs、下标、新元素、证明。
    -- 不要扫描证明参数；其中的局部 binder 不是源程序的动态下标。
    let parsed :=
      Id.run do
        if h : args.size ≥ 4 then
          let idx? := val env args[args.size - 3]
          let payload := substLets 8 (peelLets (strip args[args.size - 2]))
          let isCtor :=
            match payload.getAppFn.constName? with
            | some n =>
              match env.find? n with
              | some (.ctorInfo _) => true
              | _ => false
            | none => false
          if isCtor || isIteExpr payload then return (false, idx?, some payload, none)
          else return (false, idx?, none, val env payload)
        else
          return (false, none, none, none)
    let rec changedLeaves (selfIdx : Option Ops.Val) (fuel : Nat) (e : Expr) :
        Array (String × Ops.Val) :=
      match fuel with
      | 0 => #[]
      | fuel' + 1 =>
        let e := substLets 16 (strip e)
        match e.getAppFn.constName? with
        | some n =>
          match env.find? n with
          | some (.ctorInfo c) =>
            if isUserType env c.induct && isStructure env c.induct then
              let names := getStructureFields env c.induct
              let args := e.getAppArgs
              let nF := names.size
              if nF == 0 || args.size < nF then #[]
              else
                -- `{ src with left := a, parent := b }`：叶来自别的节点 / 别的字段就算改了。
                -- `y.parent := x.parent` 两边都叫 parent，不能只看字段名。
                Id.run do
                  let mut acc : Array (String × Ops.Val) := #[]
                  for i in [0:nF] do
                    if h : i < nF ∧ i < args.size then
                      let fname := names[i].toString
                      let arg := substLets 8 (strip args[args.size - nF + i])
                      let looksSame :=
                        match val env arg with
                        | some (.field (.arg _) n) =>
                          n == fname || n.endsWith ("_" ++ fname)
                        | some (.field (.indexGet _ _ i _ _) leaf) =>
                          -- 同一下标上的同一逻辑叶才算没改。
                          (leaf == fname || leaf.endsWith ("_" ++ fname)) &&
                            (match selfIdx with
                             | some j => i == j
                             | none => true)
                        | _ => false
                      unless looksSame do
                        match val env arg with
                        | some v => acc := acc.push (fname, v)
                        | none => pure ()
                  return acc
            else
              e.getAppArgs.foldl (init := #[]) fun a x =>
                a ++ changedLeaves selfIdx fuel' x
          | _ => e.getAppArgs.foldl (init := #[]) fun a x =>
              a ++ changedLeaves selfIdx fuel' x
        | none => e.getAppArgs.foldl (init := #[]) fun a x =>
            a ++ changedLeaves selfIdx fuel' x
    match parsed with
    | (true, _, _, _) => none
    | (false, some idx, some payloadE, _) =>
      match idx with
      | .lit _ => none
      | _ =>
        match vectorBaseName env 16 e with
        | none => none
        | some name =>
          let payloadOps (payload : Expr) : Array Ops.Op :=
            match asUInt64VariantCtor env payload with
            | some (tag, payloads, payloadWidth) => Id.run do
              let mut ops : Array Ops.Op := #[.indexSetLeaf name idx (.lit tag) len "tag"]
              for offset in [:payloadWidth] do
                ops := ops.push (.indexSetLeaf name idx
                  (payloads[offset]?.getD (.lit 0)) len s!"p{offset}")
              return ops
            | none =>
              let leaves := changedLeaves (some idx) 8 payload
              let leaves :=
                if leaves.isEmpty then
                  match val env payload with
                  | some v => #[("", v)]
                  | none => #[]
                else leaves
              leaves.map fun p => (.indexSetLeaf name idx p.2 len p.1 : Ops.Op)
          if isIteExpr payloadE then
            let args := payloadE.getAppArgs
            let peelProofLam (branch : Expr) : Expr :=
              match strip branch with
              | .lam _ _ body _ => substLets 16 (body.lowerLooseBVars 1 1)
              | branch => substLets 16 branch
            if args.size < 2 then none
            else
              match args.findSome? (asCondition env) with
              | none => none
              | some (cmp, lhs, rhs) =>
                let thn := payloadOps (peelProofLam args[args.size - 2]!)
                let els := payloadOps (peelProofLam args[args.size - 1]!)
                if thn.isEmpty && els.isEmpty then none else some #[.ite cmp lhs rhs thn els]
          else
            let ops := payloadOps payloadE
            if ops.isEmpty then none else some ops
    | (false, some idx, none, some payload) =>
      match idx with
      | .lit _ => none
      | _ =>
        match vectorBaseName env 16 e with
        | some name => some #[.indexSetLeaf name idx payload len]
        | none => none
    | _ => none
  else none

private def asIndexSet (env : Environment) (e0 : Expr) : Option Ops.Op :=
  match asIndexSets env e0 with
  | some ops => ops[0]?
  | none => none

def peelForalls (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      match strip e with
      | .forallE _ _ body _ => go fuel' body
      | e => e
  go 32 e

def fieldTypeExpr (env : Environment) (structName fieldName : Name) : Option Expr :=
  match getProjFnForField? env structName fieldName with
  | none => none
  | some proj =>
    match env.find? proj with
    | none => none
    | some info => some (peelForalls info.type)

private partial def collectListExprs (fuel : Nat) (e : Expr) : Option (Array Expr) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.nil || endsWith e ".nil" then
      some #[]
    else if isConstNamed e ``List.cons || endsWith e ".cons" then
      let args := e.getAppArgs
      if args.size < 2 then none
      else do
        let tail ← collectListExprs fuel' args[args.size - 1]!
        return #[args[args.size - 2]!] ++ tail
    else if isConstNamed e ``List.toArray || endsWith e ".toArray" then
      let args := e.getAppArgs
      if args.isEmpty then none else collectListExprs fuel' args[args.size - 1]!
    else
      e.getAppArgs.findSome? (collectListExprs fuel')

private def vectorElements (e : Expr) : Option (Array Expr) :=
  let e := strip e
  if isConstNamed e ``Vector.mk || endsWith e "Vector.mk" then
    collectListExprs 32 e
  else none

private def unfoldNullaryValue? (env : Environment) (e : Expr) : Option Expr :=
  let e := strip e
  if !e.getAppArgs.isEmpty then none
  else do
    let name ← e.getAppFn.constName?
    -- Keep `@[irreducible]` runtime leaves (caller/self/ledger) as named constants.
    -- Unfolding them here would turn `xrplCallerW0` into the host stub `0`.
    if Lean.getReducibilityStatusCore env name == .irreducible then none
    else
      let .defnInfo info ← env.find? name | none
      return info.value

/-- Explicit source fields of one user-defined structure constructor. -/
private def userCtorFields (env : Environment) (e : Expr) : Option (Array Expr) :=
  let e := peelLets (strip e)
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    match env.find? n with
    | some (.ctorInfo c) =>
      if isUserType env c.induct && isStructure env c.induct then
        let args := e.getAppArgs
        if args.size ≥ c.numFields then
          some (args.extract (args.size - c.numFields) args.size)
        else none
      else none
    | _ => none

/-- Flatten an initializer from its source type, producing exactly one value per schema leaf. -/
private partial def flattenInitValue (env : Environment) (fuel : Nat) (ty e : Expr) :
    Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := substLets 32 (strip e)
    match unfoldNullaryValue? env e with
    | some body => flattenInitValue env fuel' ty body
    | none =>
      let ty := strip ty
      let tyName? := ty.getAppFn.constName?
      if tyName? == some ``UInt64 || tyName? == some ``UInt32 ||
          tyName? == some ``UInt16 || tyName? == some ``UInt8 then
        (val env e).map (#[·])
      else if tyName? == some addr20Name then
        let (w0, w1, w2) := addr20Leaves env e
        some #[w0, w1, w2]
      else if isUInt256Type ty then
        let (w0, w1, w2, w3) := uint256Leaves env e
        some #[w0, w1, w2, w3]
      else if tyName? == some ``Bool then
        if isConstNamed e ``Bool.true || endsWith e ".true" then some #[.lit 1]
        else if isConstNamed e ``Bool.false || endsWith e ".false" then some #[.lit 0]
        else (val env e).map (#[·])
      else if tyName? == some ``Option then
        (asOptionStorage env e).map fun (tag, payload) => #[tag, payload]
      else if tyName? == some ``Vector then
        let tyArgs := ty.getAppArgs
        if tyArgs.size < 2 then none
        else
          match asLit 8 tyArgs[tyArgs.size - 1]!, vectorElements e with
          | some (.lit length), some elements =>
            if elements.size != length.toNat then none
            else Id.run do
              let mut values : Array Ops.Val := #[]
              for h : i in [:elements.size] do
                let some item := flattenInitValue env fuel' tyArgs[tyArgs.size - 2]! elements[i]
                  | return none
                values := values ++ item
              return some values
          | _, _ => none
      else if let some tyName := tyName? then
        if isEnumLeaf env tyName then
          match e.getAppFn.constName? with
          | some ctor => (enumCtorIndex env tyName ctor).map fun index => #[.lit (UInt64.ofNat index)]
          | none => none
        else if isUInt64Newtype env tyName then
          (val env e).map (#[·])
        else if isOptionLikeInductive env tyName then
          (asOptionStorage env e).map fun (tag, payload) => #[tag, payload]
        else if let some payloadWidth := uint64VariantPayloadWidth? env tyName then
          match asUInt64VariantCtor env e with
          | none => none
          | some (tag, payloads, _) =>
            Id.run do
              let mut values := #[.lit tag]
              for index in [:payloadWidth] do
                values := values.push (payloads[index]?.getD (.lit 0))
              return some values
        else if isUserName env tyName && isStructure env tyName then
          match userCtorFields env e with
          | none => none
          | some fields =>
            let names := getStructureFields env tyName
            if fields.size != names.size then none
            else Id.run do
              let mut values : Array Ops.Val := #[]
              for h : i in [:fields.size] do
                let some fieldTy := fieldTypeExpr env tyName names[i]! | return none
                let some fieldValues := flattenInitValue env fuel' fieldTy fields[i] | return none
                values := values ++ fieldValues
              return some values
        else none
      else none

private def asStateFields (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let fields ← userCtorFields env (substLets 32 e)
  let ctor ← (substLets 32 e).getAppFn.constName?
  let .ctorInfo info ← env.find? ctor | none
  if info.induct == addr20Name || info.induct == uint128Name ||
      info.induct == uint256Name || info.induct == fixedBytesName then none else pure ()
  let names := getStructureFields env info.induct
  if fields.size != names.size then none else pure ()
  let mut values : Array Ops.Val := #[]
  for h : i in [:fields.size] do
    let fieldTy ← fieldTypeExpr env info.induct names[i]!
    let fieldValues ← flattenInitValue env 32 fieldTy fields[i]
    values := values ++ fieldValues
  return values

private def looksUnchangedField (v : Ops.Val) (leaf : String) : Bool :=
  match v with
  | .field _ n =>
    n == leaf || n.endsWith ("_" ++ leaf) || leaf.endsWith ("_" ++ n)
  | _ => false

/-- Wide aggregate leaves must preserve their complete parent path. A bare child name is not
enough to prove identity: assigning `candidate.w0` to `ownership_w0` remains a write even though
both paths end in `w0`. Scalar nested-state normalization retains its broader historical rule. -/
private def looksUnchangedWideLeaf (v : Ops.Val) (leaf : String) : Bool :=
  match v with
  | .field _ n => n == leaf || n.endsWith ("_" ++ leaf)
  | _ => false

/-- 把一个值摊成账户叶。`Vector.set` / 嵌套 `with` 只展开被改的那些。 -/
private partial def flattenLeaves (env : Environment) (base : String) (e : Expr)
    (appliedBases : Array Expr := #[]) : Array (String × Ops.Val) :=
  let e := peelLets (strip e)
  if isVectorSet e then
    let args := e.getAppArgs
    -- `Vector.set α n xs i v h`：第一个字面量是长度，第二个是下标。
    -- 长度之后的第一个非字面量是旧向量，两下标之后才是新元素。
    let parsed :=
      Id.run do
        let mut nLits : Nat := 0
        let mut xs? : Option Expr := none
        let mut idx? : Option Nat := none
        let mut payload? : Option Expr := none
        for a in args do
          if endsWith a "._proof_1" || endsWith a "._proof_2" || endsWith a ".rfl" then
            pure ()
          else
            match asLit 8 a with
            | some (.lit n) =>
              if nLits == 0 then
                nLits := 1
              else if nLits == 1 then
                nLits := 2
                idx? := some n.toNat
              else
                pure ()
            | some _ =>
              pure ()
            | none =>
              if nLits == 1 && xs?.isNone then
                xs? := some (peelLets (strip a))
              else if nLits ≥ 2 && payload?.isNone then
                payload? := some (peelLets (strip a))
        return (idx?, xs?, payload?)
    match parsed with
    | (some i, xs?, some payload) =>
      let pre := if base.isEmpty then s!"{i}" else s!"{base}_{i}"
      let here := flattenLeaves env pre payload appliedBases
      let here :=
        if here.isEmpty then
          match val env payload with
          | some v => #[(pre, v)]
          | none => #[]
        else here
      let prev :=
        match xs? with
        | some xs => flattenLeaves env base xs appliedBases
        | none => #[]
      prev ++ here
    | _ => #[]
  else if let some fields := addr20CtorFields env e then
    Id.run do
      let mut acc : Array (String × Ops.Val) := #[]
      let names := #["w0", "w1", "w2"]
      for i in [0:3] do
        if h : i < fields.size then
          let fname := names[i]!
          let child := if base.isEmpty then fname else s!"{base}_{fname}"
          match val env fields[i] with
          | some v => acc := acc.push (child, v)
          | none => pure ()
      acc
  else if let some fields := userCtorFields env e then
    match e.getAppFn.constName? with
    | none => #[]
    | some n =>
      match env.find? n with
      | some (.ctorInfo c) =>
        let names := getStructureFields env c.induct
        Id.run do
          let mut acc : Array (String × Ops.Val) := #[]
          for i in [0:fields.size] do
            if h : i < names.size ∧ i < fields.size then
              let fname := names[i].toString
              let child := if base.isEmpty then fname else s!"{base}_{fname}"
              let arg := fields[i]
              let inheritedFromAppliedBase :=
                match (peelLets (strip arg)).getAppFn.constName? with
                | some projection =>
                  match env.getProjectionFnInfo? projection with
                  | some info =>
                    let args := (peelLets (strip arg)).getAppArgs
                    info.ctorName == n && info.i == i &&
                      (args[args.size - 1]?.map appliedBases.contains).getD false
                  | none => false
                | none => false
              -- A payload constructor is one typed variant field, not a nested scalar
              -- expression whose first argument can stand in for the whole field.
              -- `{ { s with locked := e } with seats := xs.set … }.locked` elaborates as a
              -- projection of the inner constructor; reduce that projection before treating
              -- the field as an inherited `s.locked` leaf.
              let nestedArg := (reduceCtorProjection? env (peelLets (strip arg))).getD arg
              let nested :=
                if (asUInt64VariantCtor env arg).isSome || (asOptionStorage env arg).isSome then #[]
                else flattenLeaves env child nestedArg appliedBases
              let isVectorField :=
                match env.find? (c.induct.str fname) with
                | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
                | none => false
              -- Inner transitions represented by `appliedBases` were already lowered. A direct
              -- projection only inherits that field; reducing it through the constructor would
              -- replay a transition rather than describe an outer write.
              let fieldTy? := fieldTypeExpr env c.induct names[i]
              let isAddr20Field :=
                match fieldTy? with
                | some ty => isAddr20Type ty
                | none => false
              let isUInt256Field :=
                match fieldTy? with
                | some ty => isUInt256Type ty
                | none => false
              if inheritedFromAppliedBase then
                pure ()
              else if isAddr20Field then
                let (w0, w1, w2) := addr20Leaves env nestedArg
                let l0 := s!"{child}_w0"
                let l1 := s!"{child}_w1"
                let l2 := s!"{child}_w2"
                unless looksUnchangedWideLeaf w0 l0 do acc := acc.push (l0, w0)
                unless looksUnchangedWideLeaf w1 l1 do acc := acc.push (l1, w1)
                unless looksUnchangedWideLeaf w2 l2 do acc := acc.push (l2, w2)
              else if isUInt256Field then
                let (w0, w1, w2, w3) := uint256Leaves env nestedArg
                let l0 := s!"{child}_w0"
                let l1 := s!"{child}_w1"
                let l2 := s!"{child}_w2"
                let l3 := s!"{child}_w3"
                unless looksUnchangedWideLeaf w0 l0 do acc := acc.push (l0, w0)
                unless looksUnchangedWideLeaf w1 l1 do acc := acc.push (l1, w1)
                unless looksUnchangedWideLeaf w2 l2 do acc := acc.push (l2, w2)
                unless looksUnchangedWideLeaf w3 l3 do acc := acc.push (l3, w3)
              else if !nested.isEmpty then
                acc := acc ++ nested.filter fun p => !looksUnchangedField p.2 p.1
              else if isVectorField then
                -- A runtime-indexed vector is represented only by typed indexSet writes.
                -- Its root projection is not a scalar account leaf.
                pure ()
              else
                match asUInt64VariantCtor env arg with
                | some (tag, payloads, payloadWidth) =>
                  acc := acc.push (s!"{child}_tag", .lit tag)
                  for index in [:payloadWidth] do
                    acc := acc.push
                      (s!"{child}_p{index}", payloads[index]?.getD (.lit 0))
                | none =>
                  match asOptionStorage env arg with
                  | some (tag, payload) =>
                    acc := acc.push (s!"{child}_tag", tag) |>.push (s!"{child}_p0", payload)
                  | none =>
                    -- Record-update fields can close over bounded tree walks (Phoenix
                    -- `oldSize` / `maxBookAddress`). The ordinary scalar decoder fuel is
                    -- too low and used to drop those aggregate stores silently.
                    match val env nestedArg <|> asVal env 128 nestedArg <|>
                        localScalarValue? env 128 nestedArg with
                    | some v =>
                      unless looksUnchangedField v child || looksUnchangedField v fname do
                        acc := acc.push (child, v)
                    | none =>
                      if isConstNamed nestedArg ``Bool.true || endsWith nestedArg ".true" then
                        acc := acc.push (child, .lit 1)
                      else if isConstNamed nestedArg ``Bool.false || endsWith nestedArg ".false" then
                        acc := acc.push (child, .lit 0)
                      else
                        match nestedArg.getAppFn.constName? with
                        | some ctor =>
                          match env.find? ctor with
                          | some (.ctorInfo info) =>
                            -- A payload variant must be flattened into its typed tag/payload
                            -- leaves. Falling back to the constructor index would create a raw
                            -- store for the non-leaf parent and silently discard its payload.
                            if (uint64VariantPayloadWidth? env info.induct).isNone then
                              match enumCtorIndex env info.induct ctor with
                              | some k => acc := acc.push (child, .lit (UInt64.ofNat k))
                              | none => pure ()
                          | _ => pure ()
                        | none =>
                          match asLit 8 nestedArg with
                          | some v => acc := acc.push (child, v)
                          | none => pure ()
          acc
      | _ => #[]
  else
    match val env e with
    | some v =>
      if base.isEmpty || looksUnchangedField v base then #[] else #[(base, v)]
    | none => #[]

/-- Flatten a statically shaped scalar result. Products are protocol tuples, not heap containers:
each leaf must already lower to one target-neutral scalar value. -/
private def scalarResultValues (env : Environment) (fuel : Nat) (e : Expr) :
    Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then do
      let args := e.getAppArgs
      let left ← scalarResultValues env fuel' args[args.size - 2]!
      let right ← scalarResultValues env fuel' args[args.size - 1]!
      return left ++ right
    else
      (asBoolVal env fuel e <|> val env e).map (#[·])

/-- Keep the historical scalar `okState` shorthand, but spell multi-leaf effectful results as the
existing sequence of scalar returns. CFG lowering already joins that sequence into `returnU64s`. -/
private def effectfulResultOps (env : Environment) (e : Expr) : Option (Array Ops.Op) := do
  let values ← scalarResultValues env 16 e
  if values.size == 1 then
    return #[.okState values[0]!]
  else if values.size > 1 then
    return values.map fun value => .returnU64 value
  else
    none

/-- `Except.ok (State.mk …, ret)`：按叶 diff，改了几个槽就写几条。 -/
private def asStoreFields (env : Environment) (e : Expr)
    (includeSingle : Bool := false) : Option (Array Ops.Op) :=
  -- Preserve the RHS of `let next := ...` before peeling the state constructor. Dropping a used
  -- scalar binder turns `next` into an unrelated outer `.arg` and silently stores the wrong value.
  let e := peelControl 8 (substUInt64Lets 64 (dropUnusedHeadLets 32 e))
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk && pair.getAppArgs.size ≥ 2 then
        let st := pair.getAppArgs[pair.getAppArgs.size - 2]!
        let ret := pair.getAppArgs[pair.getAppArgs.size - 1]!
        let vectorBase := vectorBaseName env 32 st
        let leaves := (flattenLeaves env "" st).filter fun p => some p.1 != vectorBase
        let explicitSingle := includeSingle || containsUInt64NewtypeCtor env 16 st
        if leaves.isEmpty || (!explicitSingle && leaves.size == 1) then none
        else
          let stores := leaves.map fun p => (.storeField p.1 p.2 : Ops.Op)
          match effectfulResultOps env ret with
          | some returns => some (stores ++ returns)
          | none => some stores
      else none
    else none
  else none

private def asOkStateCore (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk then
        let pargs := pair.getAppArgs
        if pargs.size ≥ 2 then
          let st := pargs[pargs.size - 2]!
          let boolLit :=
            (strip st).getAppArgs.findSome? fun a =>
              if isConstNamed a ``Bool.true || endsWith a ".true" then some (.lit 1)
              else if isConstNamed a ``Bool.false || endsWith a ".false" then some (.lit 0)
              else none
          match boolLit with
          | some v => some v
          | none =>
          match asOptionPayload env st with
          | some v => some v
          | none =>
            -- `{ s with nodes := s.nodes.set i { … with value := v } }`
            -- 展开成 `State.mk s.root s.size (Vector.set …)`。`val` 会先吃到
            -- `s.root`，必须先认嵌套 Vector.set，否则 dest 落到错误槽。
            match asVectorSet env (strip st) <|>
                (strip st).getAppArgs.findSome? (asVectorSet env) with
            | some v => some v
            | none =>
            match val env st with
            | some (.clockSlot) => some .clockSlot
            | some (.nearBlockIndex) => some .nearBlockIndex
            | some (.nearBlockTimestamp) => some .nearBlockTimestamp
            | some (.nearPredecessor) => some .nearPredecessor
            | some (.nearPredecessorLen) => some .nearPredecessorLen
            | some (.nearPredecessorW1) => some .nearPredecessorW1
            | some (.nearPredecessorW2) => some .nearPredecessorW2
            | some (.nearPredecessorW3) => some .nearPredecessorW3
            | some (.nearPredecessorW4) => some .nearPredecessorW4
            | some (.nearPredecessorW5) => some .nearPredecessorW5
            | some (.nearPredecessorW6) => some .nearPredecessorW6
            | some (.nearPredecessorW7) => some .nearPredecessorW7
            | some (.nearAttachedDeposit) => some .nearAttachedDeposit
            | some (.nearAccountBalance) => some .nearAccountBalance
            | some (.nearCurrentAccountId) => some .nearCurrentAccountId
            | some (.nearCurrentAccountIdLen) => some .nearCurrentAccountIdLen
            | some (.nearCurrentAccountIdW1) => some .nearCurrentAccountIdW1
            | some (.nearCurrentAccountIdW2) => some .nearCurrentAccountIdW2
            | some (.nearCurrentAccountIdW3) => some .nearCurrentAccountIdW3
            | some (.nearCurrentAccountIdW4) => some .nearCurrentAccountIdW4
            | some (.nearCurrentAccountIdW5) => some .nearCurrentAccountIdW5
            | some (.nearCurrentAccountIdW6) => some .nearCurrentAccountIdW6
            | some (.nearCurrentAccountIdW7) => some .nearCurrentAccountIdW7
            | some (.clockEpoch) => some .clockEpoch
            | some (.unixTime) => some .unixTime
            | some (.slotsPerEpoch) => some .slotsPerEpoch
            | some (.cpiReturn) => some .cpiReturn
            | some (.signerKey0) => some .signerKey0
            | some (.accLamports0) => some .accLamports0
            | some (.accOwner0) => some .accOwner0
            | some (.accDataLen0) => some .accDataLen0
            | some (.accN) => some .accN
            | some (.isSigner0) => some .isSigner0
            | some (.isWritable0) => some .isWritable0
            | some (.isExecutable0) => some .isExecutable0
            | some (.accLamports1) => some .accLamports1
            | some (.accOwner1) => some .accOwner1
            | some (.accDataLen1) => some .accDataLen1
            | some (.isSigner1) => some .isSigner1
            | some (.isWritable1) => some .isWritable1
            | some (.isExecutable1) => some .isExecutable1
            | some (.findPda s) => some (.findPda s)
            | some (.checkPda s b) => some (.checkPda s b)
            | some (.rentExemption n) => some (.rentExemption n)
            | some (.sha256Lit s) => some (.sha256Lit s)
            | some (.keccak256Lit s) => some (.keccak256Lit s)
            | some (.byteSwap64 word) => some (.byteSwap64 word)
            | some (.accKeyWord a w) => some (.accKeyWord a w)
            | some (.accOwnerWord a w) => some (.accOwnerWord a w)
            | some (.accDataWord a w) => some (.accDataWord a w)
            | some (.accDataWordAt a b s c i) => some (.accDataWordAt a b s c i)
            | some (.ext (.svm (.component query)) operands) =>
                some (.ext (.svm (.component query)) operands)
            | some (.accLamportsN a) => some (.accLamportsN a)
            | some (.accDataLenN a) => some (.accDataLenN a)
            | some (.isSignerN a) => some (.isSignerN a)
            | some (.isWritableN a) => some (.isWritableN a)
            | some (.isExecutableN a) => some (.isExecutableN a)
            | some (.signerKeyN a) => some (.signerKeyN a)
            | some (.ownerIsSelf a) => some (.ownerIsSelf a)
            | some v =>
              if Ops.hasEvmLeaf #[.returnU64 v] || Ops.hasXrplLeaf #[.returnU64 v] ||
                  Ops.isLangLeaf v then some v else none
            | _ =>
              match asVectorSet env (strip st) <|>
                  (strip st).getAppArgs.findSome? (asVectorSet env) with
              | some v => some v
              | none =>
                match asStateMk env st true with
                | some v => some v
                | none =>
                  let args := (strip st).getAppArgs
                  args.findSome? (asOptionPayload env) <|> asStateMk env st true
        else none
      else asStateMk env pair true
    else none
  else none

private def asOkState (env : Environment) (e : Expr) : Option Ops.Val :=
  match asOkStateCore env e with
  | result@(some (.field _ field)) =>
      let projectionScalar? := e.getUsedConstantsAsSet.toList.findSome? fun name =>
        if Core.IR.lastName name.toString != field || (env.getProjectionFnInfo? name).isNone then none
        else (env.find? name).map fun info => isScalarResult env info.type
      -- A structure/variant projection cannot be the scalar result of a mutating method. Let the
      -- full state decoder handle that branch instead of selecting an arbitrary constructor field.
      if projectionScalar? == some false then none else result
  | result => result

/-- Scalar `Except.ok` is an intermediate value producer, not a state commit. -/
private def asOkScalar (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let payload := strip args[args.size - 1]
      if isConstNamed payload ``Prod.mk then none else val env payload
    else none
  else none

/-- `.ok (s, value)` with the original state is a successful no-op, not an implicit write. The
result may be one scalar or a statically bounded product of scalar leaves. -/
private def asOkNoop (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let pair := strip args[args.size - 1]
      if isConstNamed pair ``Prod.mk then
        let pairArgs := pair.getAppArgs
        if h : pairArgs.size ≥ 2 then
          match strip pairArgs[pairArgs.size - 2] with
          | .bvar _ => scalarResultValues env 16 pairArgs[pairArgs.size - 1]
          | state =>
            if isConstNamed state ``methodArgRef then
              scalarResultValues env 16 pairArgs[pairArgs.size - 1]
            else
              let reconstructedFromOneBinder :=
                match userCtorFields env state with
                | some fields =>
                    !fields.isEmpty && fields.all fun value =>
                      let args := (strip value).getAppArgs
                      if h : args.size > 0 then
                        match strip args[args.size - 1] with
                        | .bvar _ => true
                        | _ => false
                      else false
                | none => false
              if reconstructedFromOneBinder then
                scalarResultValues env 16 pairArgs[pairArgs.size - 1]
              else none
        else none
      else none
    else none
  else none

private inductive DecodedError where
  | notError
  | overflow
  | named (name : String)
  | typed (frame : Core.Ops.ErrorFrame Ops.Val)
  | unsupported (reason : String)

/-- Preserve direct parameterized source-error constructors as one target-neutral fixed frame.
The first safe slice accepts one through four explicitly named UInt64 fields. Unsupported payloads
must not silently degrade to selector-only errors. -/
private def decodeErrorCtor (env : Environment) (e : Expr) : DecodedError :=
  let e := peelControl 8 e
  if isConstNamed e ``Except.error then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let applied := strip args[args.size - 1]
      match applied.getAppFn.constName? with
      | none => .notError
      | some ctorName =>
        let name := Core.IR.lastName ctorName.toString
        match env.find? ctorName with
        | some (.ctorInfo ctor) =>
          if ctor.numFields == 0 then
            if name == "overflow" then .overflow else .named name
          else if name == "overflow" then
            .unsupported "overflow error constructor cannot carry fields"
          else if ctor.numFields > 4 then
            .unsupported "parameterized source error supports at most four UInt64 fields"
          else
            match env.find? ctor.induct with
            | some (.inductInfo info) =>
              if info.numParams != 0 || info.numIndices != 0 || info.isRec then
                .unsupported "parameterized source error must be a nonrecursive monomorphic enum"
              else if applied.getAppArgs.size < ctor.numFields then
                .unsupported "parameterized source error lost constructor fields"
              else Id.run do
                let mut type := ctor.type
                let mut errorArgs : Array (Core.Ops.ErrorArg Ops.Val) := #[]
                let mut names : Array String := #[]
                for fieldIndex in [:ctor.numFields] do
                  let .forallE fieldName domain body binderInfo := strip type
                    | return .unsupported "parameterized source error lost field metadata"
                  if fieldName.isAnonymous || binderInfo != .default then
                    return .unsupported "parameterized source error fields must be explicitly named"
                  if domain.consumeMData.getAppFn.constName? != some ``UInt64 then
                    return .unsupported "parameterized source error currently supports only UInt64 fields"
                  let fieldName := fieldName.toString
                  if fieldName.isEmpty || names.contains fieldName then
                    return .unsupported "parameterized source error field names must be unique"
                  let some fieldExpr := applied.getAppArgs[applied.getAppArgs.size - ctor.numFields + fieldIndex]?
                    | return .unsupported "parameterized source error lost field value"
                  let some value := val env fieldExpr
                    | return .unsupported "parameterized source error field is not a scalar value"
                  names := names.push fieldName
                  errorArgs := errorArgs.push { name := fieldName, type := .uint64, parts := #[value] }
                  type := body
                let frame : Core.Ops.ErrorFrame Ops.Val := { constructor := name, args := errorArgs }
                if frame.wellFormed (·.wellFormed IR.ValKind.arity) then .typed frame
                else .unsupported "parameterized source error frame is malformed"
            | _ => .unsupported "parameterized source error has no enum metadata"
        | _ => if name == "overflow" then .overflow else .named name
    else .notError
  else .notError

private def isErrorOverflow (e : Expr) : Bool :=
  let e := peelControl 8 e
  if isConstNamed e ``Except.error then
    let args := e.getAppArgs
    if h : args.size > 0 then
      endsWith (strip args[args.size - 1]) ".overflow"
    else false
  else false

private def returnStatesOf (vs : Array Ops.Val) : Array Ops.Op :=
  vs.map fun value => .returnState value

private def isRuntimeName (n : Name) (suf : String) : Bool :=
  n == (`ProofForge.Svm.Runtime).append suf.toName ||
    n == (`ProofForge.Evm.Runtime).append suf.toName ||
    n.toString.endsWith s!".{suf}"

private def mentionsRuntime (env : Environment) (e : Expr) (suf : String) : Bool :=
  let suf := if suf.front == '.' then String.ofList (suf.toList.drop 1) else suf
  let rec mentions (fuel : Nat) (e : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      e.getUsedConstantsAsSet.toList.any fun name =>
        isRuntimeName name suf ||
          (Attr.isInline env name &&
            match env.find? name with
            | some (.defnInfo info) => mentions fuel' info.value
            | _ => false)
  mentions 8 e

/-- Runtime CPI wrappers are unfolded by namespace, not by an ever-growing list of recipe names.
Marked source facades may add one or more compiler-erased naming layers; inspect only their
definitions so an unmarked application helper cannot become an implicit extraction boundary. -/
private def mentionsSvmRuntime (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      e.getUsedConstantsAsSet.toList.any fun name =>
        name.toString.startsWith "ProofForge.Svm.Runtime." ||
          (Attr.isInline env name &&
            match env.find? name with
            | some (.defnInfo info) => mentionsSvmRuntime env fuel info.value
            | _ => false)

private def natOfVal : Ops.Val → Option Nat
  | .lit n => some n.toNat
  | _ => none

private partial def staticNatTerm? (env : Environment) (fuel : Nat) (e : Expr) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := substLets fuel' (strip e)
      if let some value := natLiteral? e then
        some value
      else if let some reduced := reduceCtorProjectionFuel? env fuel' e then
        staticNatTerm? env fuel' reduced
      else
        match unfoldUserHelper env e with
        | some (_, unfolded) => staticNatTerm? env fuel' (substLets fuel' unfolded)
        | none => none

private def staticNatVal? (env : Environment) (e : Expr) : Option Nat :=
  staticNatTerm? env 64 e <|> (val env e >>= natOfVal) <|> do
    let .lit value ← asStaticLit env 64 e | none
    some value.toNat

private partial def staticString? (env : Environment) (fuel : Nat) (e : Expr) : Option String :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := substLets fuel' (strip e)
      match e with
      | .lit (.strVal value) => some value
      | _ =>
          if let some reduced := reduceCtorProjectionFuel? env fuel' e then
            staticString? env fuel' reduced
          else if let some (helper, unfolded) := unfoldUserHelper env e then
            if inlineHelperPreservesUserType env helper then none
            else staticString? env fuel' (substLets fuel' unfolded)
          else none

private def asBoolLit (e : Expr) : Option Bool :=
  if isConstNamed e ``Bool.true || endsWith e ".true" then some true
  else if isConstNamed e ``Bool.false || endsWith e ".false" then some false
  else none

/-- Decode the closed `Cpi.TokenTlv.Policy` source vocabulary. -/
private def asAccountDataPolicy (e : Expr) :
    Option (Option ProofForge.Svm.Cpi.TokenTlv.Policy) :=
  if isConstNamed e ``Option.none || endsWith e ".none" then
    some none
  else if (isConstNamed e ``Option.some || endsWith e ".some") && e.getAppArgs.size ≥ 1 then
    let p := strip e.getAppArgs[e.getAppArgs.size - 1]!
    if (isConstNamed p ``ProofForge.Svm.Cpi.TokenTlv.Policy.token2022Base ||
        endsWith p ".token2022Base") && p.getAppArgs.size ≥ 1 then
      let k := strip p.getAppArgs[p.getAppArgs.size - 1]!
      if isConstNamed k ``ProofForge.Svm.Cpi.TokenTlv.BaseKind.mint || endsWith k ".mint" then
        some (some (.token2022Base .mint))
      else if isConstNamed k ``ProofForge.Svm.Cpi.TokenTlv.BaseKind.account ||
          endsWith k ".account" then
        some (some (.token2022Base .account))
      else none
    else none
  else none

/-- A statically shaped `CpiMeta`, including its optional exact account-data length or typed
account-data policy. -/
private def asCpiMeta (env : Environment) (e : Expr) : Option Ops.CpiMeta :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.CpiMeta.mk || endsWith e ".mk" then
    let args := e.getAppArgs
    if args.size ≥ 5 then
      let lenExpr := strip args[args.size - 2]!
      let expectedDataLen : Option (Option Nat) :=
        if isConstNamed lenExpr ``Option.none || endsWith lenExpr ".none" then
          some none
        else if (isConstNamed lenExpr ``Option.some || endsWith lenExpr ".some") &&
            lenExpr.getAppArgs.size ≥ 1 then
          (natOfVal <$> val env lenExpr.getAppArgs[lenExpr.getAppArgs.size - 1]!)
        else none
      let accountData := asAccountDataPolicy (strip args[args.size - 1]!)
      match val env args[args.size - 5]!, asBoolLit args[args.size - 4]!,
          asBoolLit args[args.size - 3]!, expectedDataLen, accountData with
      | some accV, some signer, some writable, some expectedDataLen, some accountData =>
        match natOfVal accV with
        | some acc => some { acc, signer, writable, expectedDataLen, accountData }
        | none => none
      | _, _, _, _, _ => none
    else none
  else none

private def asCpiWord (env : Environment) (e : Expr) : Option Ops.CpiWord :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u8le || endsWith e ".u8le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! with
      | some value => some (.u8le value)
      | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u16le || endsWith e ".u16le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! with
      | some value => some (.u16le value)
      | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u32le || endsWith e ".u32le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! with
      | some value => some (.u32le value)
      | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u64le || endsWith e ".u64le" then
    if e.getAppArgs.size ≥ 1 then
      let value := e.getAppArgs[e.getAppArgs.size - 1]!
      match val env value with
      | some v => some (.u64le v)
      | none =>
          match staticNatVal? env value with
          | some n => some (.u64le (.lit (UInt64.ofNat n)))
          | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.selfEntry then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]! >>= natOfVal, strip args[args.size - 1]! with
      | some tag, .lit (.strVal authoritySeed) =>
          some (.selfEntry (UInt64.ofNat tag) authoritySeed)
      | _, _ => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.ascii || endsWith e ".ascii" then
    if e.getAppArgs.size ≥ 1 then
      match e.getAppArgs[e.getAppArgs.size - 1]! with
      | .lit (.strVal s) => some (.ascii s)
      | _ => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.programId || endsWith e ".programId" then
    some .programId
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.accKey || endsWith e ".accKey" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! >>= natOfVal with
      | some i => some (.accKey i)
      | none => none
    else none
  else none

/-- `#[a, b, …]` 展开成 `Array.mk [a, b, …]` / `List.cons`。 -/
private def asArrayElems (e : Expr) : Option (Array Expr) :=
  let rec fromList (fuel : Nat) (e : Expr) (acc : Array Expr) : Option (Array Expr) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``List.nil then some acc
      else if isConstNamed e ``List.cons && e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        fromList fuel' args[args.size - 1]! (acc.push args[args.size - 2]!)
      else none
  let e := strip e
  -- Keep a bounded decoder for compile-time payloads while allowing realistic event records.
  if isConstNamed e ``Array.mk && e.getAppArgs.size ≥ 1 then
    fromList 256 e.getAppArgs[e.getAppArgs.size - 1]! #[]
  else if isConstNamed e ``List.toArray && e.getAppArgs.size ≥ 1 then
    fromList 256 e.getAppArgs[e.getAppArgs.size - 1]! #[]
  else if isConstNamed e ``Array.empty || endsWith e ".empty" then
    some #[]
  else none

private def decodeMetasData (env : Environment) (metaE dataE : Expr) :
    Option (Array Ops.CpiMeta × Array Ops.CpiWord) :=
  match asArrayElems metaE, asArrayElems dataE with
  | some metaEs, some dataEs =>
    Id.run do
      let mut metas : Array Ops.CpiMeta := #[]
      for me in metaEs do
        match asCpiMeta env me with
        | none => return none
        | some m => metas := metas.push m
      let mut data : Array Ops.CpiWord := #[]
      for de in dataEs do
        match asCpiWord env de with
        | none => return none
        | some w => data := data.push w
      some (metas, data)
  | _, _ => none

private def asAsciiLit (e : Expr) : Option String :=
  match strip e with
  | .lit (.strVal s) => if s.isEmpty then none else some s
  | _ => none

private def asBatchRecorderWord : Ops.CpiWord → Option (Svm.BatchRecorder.Word Ops.Val)
  | .u8le value => some (.u8le value)
  | .u16le value => some (.u16le value)
  | .u32le value => some (.u32le value)
  | .u64le value => some (.u64le value)
  | .ascii value => some (.ascii value)
  | .programId => some .programId
  | .accKey account => some (.accountKey account)
  | .selfEntry .. => none

private def decodeBatchRecorderWords (env : Environment) (e : Expr) :
    Option (Array (Svm.BatchRecorder.Word Ops.Val)) := do
  let expressions ← asArrayElems e
  let mut words := #[]
  for expression in expressions do
    let word ← asCpiWord env expression >>= asBatchRecorderWord
    words := words.push word
  return words

private def decodeBatchRecorderConfig (env : Environment)
    (logAccountE selfEntryTagE authoritySeedE maxBytesE headerBytesE countOffsetE
      maxRecordsE : Expr) : Option Svm.BatchRecorder.Config := do
  let logAccount ← staticNatVal? env logAccountE
  let selfEntryTag ← staticNatVal? env selfEntryTagE
  let authoritySeed ← staticString? env 64 authoritySeedE
  let maxBytes ← staticNatVal? env maxBytesE
  let headerBytes ← staticNatVal? env headerBytesE
  let countOffset ← staticNatVal? env countOffsetE
  let maxRecords ← staticNatVal? env maxRecordsE
  return { logAccount, selfEntryTag, authoritySeed, maxBytes, headerBytes, countOffset, maxRecords }

private def decodeBatchRecorderCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.batchRecorderBegin ||
      endsWith e ".batchRecorderBegin" then
    if args.size < 9 then none else do
      let config ← decodeBatchRecorderConfig env
        args[args.size - 9]! args[args.size - 8]! args[args.size - 7]!
        args[args.size - 6]! args[args.size - 5]! args[args.size - 4]! args[args.size - 3]!
      let header ← decodeBatchRecorderWords env args[args.size - 2]!
      let bump ← val env args[args.size - 1]!
      return .batchRecorder (.begin config header bump)
  else if isConstNamed e ``ProofForge.Svm.Runtime.batchRecorderAppend ||
      endsWith e ".batchRecorderAppend" then
    if args.size < 9 then none else do
      let config ← decodeBatchRecorderConfig env
        args[args.size - 9]! args[args.size - 8]! args[args.size - 7]!
        args[args.size - 6]! args[args.size - 5]! args[args.size - 4]! args[args.size - 3]!
      let enabled ← val env args[args.size - 2]!
      let record ← decodeBatchRecorderWords env args[args.size - 1]!
      return .batchRecorder (.append config enabled record)
  else if isConstNamed e ``ProofForge.Svm.Runtime.batchRecorderFinish ||
      endsWith e ".batchRecorderFinish" then
    if args.size < 7 then none else do
      let config ← decodeBatchRecorderConfig env
        args[args.size - 7]! args[args.size - 6]! args[args.size - 5]!
        args[args.size - 4]! args[args.size - 3]! args[args.size - 2]! args[args.size - 1]!
      return .batchRecorder (.finish config)
  else none

private def decodeFifoCancelCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelBegin ||
      endsWith e ".fifoCancelBegin" then
    some (.fifoCancel .begin)
  else if isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelFinish ||
      endsWith e ".fifoCancelFinish" then
    some (.fifoCancel .finish)
  else if isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelSide ||
      endsWith e ".fifoCancelSide" then
    if args.size < 25 then none else do
      let marketAccount ← staticNatVal? env args[args.size - 25]!
      let rootWord ← staticNatVal? env args[args.size - 24]!
      let linksWord ← staticNatVal? env args[args.size - 23]!
      let parentWord ← staticNatVal? env args[args.size - 22]!
      let priceWord ← staticNatVal? env args[args.size - 21]!
      let sequenceWord ← staticNatVal? env args[args.size - 20]!
      let ownerWord ← staticNatVal? env args[args.size - 19]!
      let sizeWord ← staticNatVal? env args[args.size - 18]!
      let lockedWord ← staticNatVal? env args[args.size - 17]!
      let freeWord ← staticNatVal? env args[args.size - 16]!
      let orderStride ← staticNatVal? env args[args.size - 15]!
      let orderCapacity ← staticNatVal? env args[args.size - 14]!
      let traderStride ← staticNatVal? env args[args.size - 13]!
      let traderCapacity ← staticNatVal? env args[args.size - 12]!
      let bid ← staticNatVal? env args[args.size - 11]!
      let baseLotsPerBaseUnitWord ← staticNatVal? env args[args.size - 10]!
      let tickSizeWord ← staticNatVal? env args[args.size - 9]!
      let recorder ← decodeBatchRecorderConfig env
        args[args.size - 8]! args[args.size - 7]! args[args.size - 6]!
        args[args.size - 5]! args[args.size - 4]! args[args.size - 3]! args[args.size - 2]!
      let traderIndex ← val env args[args.size - 1]!
      if bid != 0 && bid != 1 then none else
      let bid := bid == 1
      let access : Svm.AccountStorage.Access :=
        { writable := true, currentProgramOwned := true }
      let field (baseWord strideWords capacity : Nat) : Svm.AccountStorage.Field :=
        { region :=
            { account := marketAccount, baseWord, strideWords, capacity
              indexBase := .one, access } }
      let config : Svm.FifoCancel.Config :=
        { map := .fifoOneBased marketAccount rootWord linksWord parentWord priceWord sequenceWord
            orderStride orderCapacity bid
          owner := field ownerWord orderStride orderCapacity
          size := field sizeWord orderStride orderCapacity
          locked := field lockedWord traderStride traderCapacity
          free := field freeWord traderStride traderCapacity
          collateral := if bid then .quote baseLotsPerBaseUnitWord tickSizeWord else .base
          recorder }
      if config.wellFormed then some (.fifoCancel (.cancelSide config traderIndex)) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.fifoCancelUpToSide ||
      endsWith e ".fifoCancelUpToSide" then
    if args.size < 29 then none else do
      let marketAccount ← staticNatVal? env args[args.size - 29]!
      let rootWord ← staticNatVal? env args[args.size - 28]!
      let linksWord ← staticNatVal? env args[args.size - 27]!
      let parentWord ← staticNatVal? env args[args.size - 26]!
      let priceWord ← staticNatVal? env args[args.size - 25]!
      let sequenceWord ← staticNatVal? env args[args.size - 24]!
      let ownerWord ← staticNatVal? env args[args.size - 23]!
      let sizeWord ← staticNatVal? env args[args.size - 22]!
      let lockedWord ← staticNatVal? env args[args.size - 21]!
      let freeWord ← staticNatVal? env args[args.size - 20]!
      let orderStride ← staticNatVal? env args[args.size - 19]!
      let orderCapacity ← staticNatVal? env args[args.size - 18]!
      let traderStride ← staticNatVal? env args[args.size - 17]!
      let traderCapacity ← staticNatVal? env args[args.size - 16]!
      let bid ← staticNatVal? env args[args.size - 15]!
      let baseLotsPerBaseUnitWord ← staticNatVal? env args[args.size - 14]!
      let tickSizeWord ← staticNatVal? env args[args.size - 13]!
      let recorder ← decodeBatchRecorderConfig env
        args[args.size - 12]! args[args.size - 11]! args[args.size - 10]!
        args[args.size - 9]! args[args.size - 8]! args[args.size - 7]! args[args.size - 6]!
      let traderIndex ← val env args[args.size - 5]!
      let tickLimit ← val env args[args.size - 4]!
      let searchLimit ← val env args[args.size - 3]!
      let cancelLimit ← val env args[args.size - 2]!
      let claimImmediately ← staticNatVal? env args[args.size - 1]!
      if (bid != 0 && bid != 1) || (claimImmediately != 0 && claimImmediately != 1) then none else
      let bid := bid == 1
      let access : Svm.AccountStorage.Access :=
        { writable := true, currentProgramOwned := true }
      let field (baseWord strideWords capacity : Nat) : Svm.AccountStorage.Field :=
        { region :=
            { account := marketAccount, baseWord, strideWords, capacity
              indexBase := .one, access } }
      let config : Svm.FifoCancel.Config :=
        { map := .fifoOneBased marketAccount rootWord linksWord parentWord priceWord sequenceWord
            orderStride orderCapacity bid
          owner := field ownerWord orderStride orderCapacity
          size := field sizeWord orderStride orderCapacity
          locked := field lockedWord traderStride traderCapacity
          free := field freeWord traderStride traderCapacity
          collateral := if bid then .quote baseLotsPerBaseUnitWord tickSizeWord else .base
          recorder }
      if config.wellFormed then
        some (.fifoCancel (.cancelUpTo config traderIndex tickLimit searchLimit cancelLimit
          (claimImmediately == 1)))
      else none
  else none

private def decodeMemorySpan (account offset length : Nat) : Option Svm.Memory.Span := do
  let span : Svm.Memory.Span := { account, offsetBytes := offset, lengthBytes := length }
  if span.wellFormed then some span else none

private def decodeMemoryCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.memoryCopy || endsWith e ".memoryCopy" then
    if args.size < 5 then none else do
      let destinationAccount ← staticNatVal? env args[args.size - 5]!
      let destinationOffset ← staticNatVal? env args[args.size - 4]!
      let sourceAccount ← staticNatVal? env args[args.size - 3]!
      let sourceOffset ← staticNatVal? env args[args.size - 2]!
      let length ← staticNatVal? env args[args.size - 1]!
      let destination ← decodeMemorySpan destinationAccount destinationOffset length
      let source ← decodeMemorySpan sourceAccount sourceOffset length
      let call : Svm.Memory.Call Ops.Val := .copyNonoverlapping destination source
      if call.wellFormed (fun _ => true) then some (.memory call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.memoryMove || endsWith e ".memoryMove" then
    if args.size < 5 then none else do
      let destinationAccount ← staticNatVal? env args[args.size - 5]!
      let destinationOffset ← staticNatVal? env args[args.size - 4]!
      let sourceAccount ← staticNatVal? env args[args.size - 3]!
      let sourceOffset ← staticNatVal? env args[args.size - 2]!
      let length ← staticNatVal? env args[args.size - 1]!
      let destination ← decodeMemorySpan destinationAccount destinationOffset length
      let source ← decodeMemorySpan sourceAccount sourceOffset length
      let call : Svm.Memory.Call Ops.Val := .move destination source
      if call.wellFormed (fun _ => true) then some (.memory call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.memorySet || endsWith e ".memorySet" then
    if args.size < 4 then none else do
      let destinationAccount ← staticNatVal? env args[args.size - 4]!
      let destinationOffset ← staticNatVal? env args[args.size - 3]!
      let length ← staticNatVal? env args[args.size - 2]!
      let byte ← val env args[args.size - 1]!
      let destination ← decodeMemorySpan destinationAccount destinationOffset length
      let call : Svm.Memory.Call Ops.Val := .set destination byte
      if call.wellFormed (fun _ => true) then
        some (.memory call)
      else none
  else none

private def decodeTransientVecConfig (env : Environment) (capacity : Expr) :
    Option Svm.TransientVec.Config := do
  let capacity ← staticNatVal? env capacity
  let config : Svm.TransientVec.Config := { capacity }
  if config.wellFormed then some config else none

private def decodeTransientVecCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.transientVecBegin ||
      endsWith e ".transientVecBegin" then
    if args.size < 1 then none else do
      let config ← decodeTransientVecConfig env args[args.size - 1]!
      return .transientVec (.begin config)
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientVecPush ||
      endsWith e ".transientVecPush" then
    if args.size < 2 then none else do
      let config ← decodeTransientVecConfig env args[args.size - 2]!
      let value ← val env args[args.size - 1]!
      let call : Svm.TransientVec.Call Ops.Val := .push config value
      if call.wellFormed (fun _ => true) then some (.transientVec call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientVecSet ||
      endsWith e ".transientVecSet" then
    if args.size < 3 then none else do
      let config ← decodeTransientVecConfig env args[args.size - 3]!
      let index ← val env args[args.size - 2]!
      let value ← val env args[args.size - 1]!
      let call : Svm.TransientVec.Call Ops.Val := .set config index value
      if call.wellFormed (fun _ => true) then some (.transientVec call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientVecTruncate ||
      endsWith e ".transientVecTruncate" then
    if args.size < 2 then none else do
      let config ← decodeTransientVecConfig env args[args.size - 2]!
      let newLength ← val env args[args.size - 1]!
      let call : Svm.TransientVec.Call Ops.Val := .truncate config newLength
      if call.wellFormed (fun _ => true) then some (.transientVec call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientVecClear ||
      endsWith e ".transientVecClear" then
    if args.size < 1 then none else do
      let config ← decodeTransientVecConfig env args[args.size - 1]!
      return .transientVec (.clear config)
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientVecFinish ||
      endsWith e ".transientVecFinish" then
    if args.size < 1 then none else do
      let config ← decodeTransientVecConfig env args[args.size - 1]!
      return .transientVec (.finish config)
  else none

private def decodeTransientBytesConfig (env : Environment) (capacity : Expr) :
    Option Svm.TransientBytes.Config := do
  let capacity ← staticNatVal? env capacity
  let config : Svm.TransientBytes.Config := { capacity }
  if config.wellFormed then some config else none

private def decodeTransientBytesCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesBegin ||
      endsWith e ".transientBytesBegin" then
    if args.size < 1 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 1]!
      return .transientBytes (.begin config)
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesPush ||
      endsWith e ".transientBytesPush" then
    if args.size < 2 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 2]!
      let byte ← val env args[args.size - 1]!
      let call : Svm.TransientBytes.Call Ops.Val := .push config byte
      if call.wellFormed (fun _ => true) then some (.transientBytes call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesAppendLe64 ||
      endsWith e ".transientBytesAppendLe64" then
    if args.size < 2 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 2]!
      let value ← val env args[args.size - 1]!
      let call : Svm.TransientBytes.Call Ops.Val := .appendLe64 config value
      if call.wellFormed (fun _ => true) then some (.transientBytes call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesSet ||
      endsWith e ".transientBytesSet" then
    if args.size < 3 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 3]!
      let index ← val env args[args.size - 2]!
      let byte ← val env args[args.size - 1]!
      let call : Svm.TransientBytes.Call Ops.Val := .set config index byte
      if call.wellFormed (fun _ => true) then some (.transientBytes call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesTruncate ||
      endsWith e ".transientBytesTruncate" then
    if args.size < 2 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 2]!
      let newLength ← val env args[args.size - 1]!
      let call : Svm.TransientBytes.Call Ops.Val := .truncate config newLength
      if call.wellFormed (fun _ => true) then some (.transientBytes call) else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesClear ||
      endsWith e ".transientBytesClear" then
    if args.size < 1 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 1]!
      return .transientBytes (.clear config)
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesLogData ||
      endsWith e ".transientBytesLogData" then
    if args.size < 1 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 1]!
      return .transientBytes (.logData config)
  else if isConstNamed e ``ProofForge.Svm.Runtime.transientBytesFinish ||
      endsWith e ".transientBytesFinish" then
    if args.size < 1 then none else do
      let config ← decodeTransientBytesConfig env args[args.size - 1]!
      return .transientBytes (.finish config)
  else none

private def decodeTelemetryCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if (isConstNamed e ``ProofForge.Svm.Runtime.logComputeUnits ||
      endsWith e ".logComputeUnits") && args.isEmpty then
    some (.telemetry .logComputeUnits)
  else if (isConstNamed e ``ProofForge.Svm.Runtime.log64 || endsWith e ".log64") &&
      args.size == 5 then do
    let first ← val env args[args.size - 5]!
    let second ← val env args[args.size - 4]!
    let third ← val env args[args.size - 3]!
    let fourth ← val env args[args.size - 2]!
    let fifth ← val env args[args.size - 1]!
    let call : Svm.Telemetry.Call Ops.Val := .log64 first second third fourth fifth
    if call.wellFormed (fun _ => true) then some (.telemetry call) else none
  else none

private def decodeLamportsCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.transferLamports ||
      endsWith e ".transferLamports" then
    if args.size < 3 then none else do
      let source ← staticNatVal? env args[args.size - 3]!
      let destination ← staticNatVal? env args[args.size - 2]!
      let amount ← val env args[args.size - 1]!
      let call : Svm.Lamports.Call Ops.Val := .transfer source destination amount
      if call.wellFormed (fun _ => true) Svm.Ops.maxTxAccountLocks then
        some (.lamports call)
      else none
  else none

private def decodeAccountDataCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let e := strip e
  let args := e.getAppArgs
  if isConstNamed e ``ProofForge.Svm.Runtime.resizeAccountData ||
      endsWith e ".resizeAccountData" then
    if args.size < 2 then none else do
      let account ← staticNatVal? env args[args.size - 2]!
      let newLength ← val env args[args.size - 1]!
      let call : Svm.AccountData.Call Ops.Val := .resize account newLength
      if call.wellFormed (fun _ => true) Svm.Ops.maxTxAccountLocks then
        some (.accountData call)
      else none
  else none

private def decodeComponentCall (env : Environment) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  decodeBatchRecorderCall env e <|> decodeFifoCancelCall env e <|> decodeMemoryCall env e <|>
    decodeTransientVecCall env e <|> decodeTransientBytesCall env e <|> decodeTelemetryCall env e <|>
    decodeLamportsCall env e <|> decodeAccountDataCall env e

private def mentionsFifoCancelSource (e : Expr) : Bool :=
  e.getUsedConstantsAsSet.toList.any fun name =>
    name.toString.startsWith "ProofForge.Svm.FifoCancel.Source."

private def isFifoCancelSourceHelper (env : Environment) (name : Name) : Bool :=
  name.toString.startsWith "ProofForge.Svm.FifoCancel.Source." ||
    Attr.isInline env name &&
      match env.find? name with
      | some (.defnInfo helper) => mentionsFifoCancelSource helper.value
      | _ => false

private def normalizeFifoCancelEffect (env : Environment) (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      let e := substLets 64 e
      if let some (helper, unfolded) := unfoldUserHelper env e then
        if !isFifoCancelSourceHelper env helper || inlineHelperPreservesUserType env helper then e
        else go fuel' unfolded
      else if let some reduced := reducePureInlineMatch? env e then
        go fuel' reduced
      else e
  go 24 e

/-- Find a bounded component call through ordinary source wrappers without exposing concrete
component constructors to the generic extraction IR. -/
private def findComponentCall (env : Environment) (fuel : Nat) (e : Expr) :
    Option (Svm.Component.Call Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Svm.Component.Call Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := normalizeFifoCancelEffect env e
      match decodeComponentCall env e with
      | some call => some call
      | none =>
        let unfolded :=
          match e.getAppFn.constName? with
          | none => none
          | some name =>
            if name.getRoot != `ProofForge && !Attr.isInline env name then none
            else
              match env.find? name with
              | some (.defnInfo info) =>
                  if e.getAppArgs.isEmpty then some info.value
                  else some (info.value.beta e.getAppArgs)
              | _ => none
        match unfolded with
        | some body => go fuel' body
        | none =>
          match e with
          | .letE _ _ value body _ => go fuel' value <|> go fuel' body
          | .lam _ _ body _ => go fuel' body
          | .app fn arg => go fuel' fn <|> go fuel' arg
          | _ => none
  go fuel e

private abbrev DecodedInvoke :=
  Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Array Ops.PdaSeed × Option Ops.Val

private abbrev DecodedAccDataWordSetAt :=
  Svm.AccountStorage.IndexBase × Nat × Nat × Nat × Nat × Ops.Val × Ops.Val

private abbrev DecodedAccDataRbTreeKey4Insert :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Ops.Val × Ops.Val × Ops.Val × Ops.Val

private abbrev DecodedAccDataRbTreeKey4Remove := DecodedAccDataRbTreeKey4Insert

private abbrev DecodedAccDataRbTreeTraderDeposit :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Ops.Val × Ops.Val × Ops.Val × Ops.Val ×
    Ops.Val × Ops.Val

private abbrev DecodedAccDataRbTreeOrderInsert :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool ×
    Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val

private abbrev DecodedAccDataRbTreeOrderRemove :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool × Ops.Val × Ops.Val

private abbrev DecodedAccDataRbTreeOrderSetWordOrRemove :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool ×
    Ops.Val × Ops.Val × Ops.Val × Ops.Val

/-- Extracted static program, metas, data, non-bump signer seeds, and optional bump. -/
private def decodeInvokeArgs (env : Environment) (e : Expr) :
    Option DecodedInvoke :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.invokeSignedSeeds ||
      endsWith e ".invokeSignedSeeds" then
    let args := e.getAppArgs
    if args.size < 5 then none
    else
      match val env args[args.size - 5]!,
          decodeMetasData env args[args.size - 4]! args[args.size - 3]!,
          asPdaSeeds args[args.size - 2]!,
          val env args[args.size - 1]! with
      | some progV, some (metas, data), some seeds, some bump =>
        match natOfVal progV with
        | some prog => some (prog, metas, data, seeds, some bump)
        | none => none
      | _, _, _, _ => none
  else if isConstNamed e ``ProofForge.Svm.Runtime.invokeSigned || endsWith e ".invokeSigned" then
    let args := e.getAppArgs
    if args.size < 5 then none
    else
      match val env args[args.size - 5]!,
          decodeMetasData env args[args.size - 4]! args[args.size - 3]!,
          asAsciiLit args[args.size - 2]!,
          val env args[args.size - 1]! with
      | some progV, some (metas, data), some seed, some bump =>
        match natOfVal progV with
        | some prog => some (prog, metas, data, #[.ascii seed], some bump)
        | none => none
      | _, _, _, _ => none
  else if isConstNamed e ``ProofForge.Svm.Runtime.invoke || endsWith e ".invoke" then
    let args := e.getAppArgs
    if args.size < 3 then none
    else
      match val env args[args.size - 3]!,
          decodeMetasData env args[args.size - 2]! args[args.size - 1]! with
      | some progV, some (metas, data) =>
        match natOfVal progV with
        | some prog => some (prog, metas, data, #[], none)
        | none => none
      | _, _ => none
  else none

/-- 体里任意深度的编译期 `invoke`。包装会 unfold 成这条。 -/
private def findInvoke (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedInvoke :=
  let rec go (fuel : Nat) (e : Expr) : Option DecodedInvoke :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      match decodeInvokeArgs env e with
      | some inv => some inv
      | none =>
        -- 非 irreducible 的 Runtime 包装展开成 invoke。
        let unfolded :=
          match e.getAppFn.constName? with
          | none => none
          | some n =>
            if n.getRoot != `ProofForge then none
            else
              match env.find? n with
              | some (.defnInfo info) =>
                -- 空参包装（invokeAcc1）直接取体；有参包装 β 展开。
                if e.getAppArgs.isEmpty then some info.value
                else some (info.value.beta e.getAppArgs)
              | _ => none
        match unfolded with
        | some u => go fuel' u
        | none =>
          match e with
          | .letE _ _ value body _ => go fuel' value <|> go fuel' body
          | .lam _ _ body _ => go fuel' body
          | .app f a => go fuel' f <|> go fuel' a
          | _ => none
  if mentionsSvmRuntime env 8 e then
    go fuel e
  else none

/-- Normalize an ignored storage effect through any pure marked facade. The decoder below still
requires a known account-storage runtime intrinsic with fully static geometry, so Queue/Map
wrappers can compose without a namespace whitelist while unrelated and stateful helpers remain
fail closed. -/
private def normalizeStorageEffect (env : Environment) (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      let e := substLets 64 e
      if let some (helper, unfolded) := unfoldUserHelper env e then
        if inlineHelperPreservesUserType env helper then e else go fuel' unfolded
      else if let some reduced := reducePureInlineMatch? env e then
        go fuel' reduced
      else e
  go 64 e

private def decodeAccDataWordSetAt (env : Environment) (e : Expr) :
    Option DecodedAccDataWordSetAt :=
  let e := strip e
  let indexBase : Option Svm.AccountStorage.IndexBase :=
    if isConstNamed e ``ProofForge.Svm.Runtime.accDataWordSetAtOneBased then some .one
    else if isConstNamed e ``ProofForge.Svm.Runtime.accDataWordSetAt then some .zero
    else none
  if indexBase.isSome && e.getAppArgs.size ≥ 6 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 6]!,
        staticNatVal? env args[args.size - 5]!,
        staticNatVal? env args[args.size - 4]!,
        staticNatVal? env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some baseWord, some strideWords, some capacity, some index, some value =>
        some (indexBase.get!, acc, baseWord, strideWords, capacity, index, value)
    | _, _, _, _, _, _ => none
  else
    none

private def findAccDataWordSetAt (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataWordSetAt :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataWordSetAt env e with
      | some write => some write
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataWordSetAt env fuel' value <|> findAccDataWordSetAt env fuel' body
          | .lam _ _ body _ => findAccDataWordSetAt env fuel' body
          | .app fn arg =>
              findAccDataWordSetAt env fuel' fn <|> findAccDataWordSetAt env fuel' arg
          | _ => none

private def decodeAccDataRbTreeKey4Insert (env : Environment) (e : Expr) :
    Option DecodedAccDataRbTreeKey4Insert :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeKey4Insert &&
      e.getAppArgs.size ≥ 11 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 11]!,
        staticNatVal? env args[args.size - 10]!,
        staticNatVal? env args[args.size - 9]!,
        staticNatVal? env args[args.size - 8]!,
        staticNatVal? env args[args.size - 7]!,
        staticNatVal? env args[args.size - 6]!,
        staticNatVal? env args[args.size - 5]!,
        val env args[args.size - 4]!, val env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some rootWord, some linksBaseWord, some parentBaseWord, some keyBaseWord,
        some strideWords, some capacity, some key0, some key1, some key2, some key3 =>
        some (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, strideWords,
          capacity, key0, key1, key2, key3)
    | _, _, _, _, _, _, _, _, _, _, _ => none
  else
    none

private def findAccDataRbTreeKey4Insert (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataRbTreeKey4Insert :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataRbTreeKey4Insert env e with
      | some insert => some insert
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataRbTreeKey4Insert env fuel' value <|>
                findAccDataRbTreeKey4Insert env fuel' body
          | .lam _ _ body _ => findAccDataRbTreeKey4Insert env fuel' body
          | .app fn arg =>
              findAccDataRbTreeKey4Insert env fuel' fn <|>
                findAccDataRbTreeKey4Insert env fuel' arg
          | _ => none

private def decodeAccDataRbTreeKey4Remove (env : Environment) (e : Expr) :
    Option DecodedAccDataRbTreeKey4Remove :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeKey4Remove &&
      e.getAppArgs.size ≥ 11 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 11]!,
        staticNatVal? env args[args.size - 10]!,
        staticNatVal? env args[args.size - 9]!,
        staticNatVal? env args[args.size - 8]!,
        staticNatVal? env args[args.size - 7]!,
        staticNatVal? env args[args.size - 6]!,
        staticNatVal? env args[args.size - 5]!,
        val env args[args.size - 4]!, val env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some rootWord, some linksBaseWord, some parentBaseWord, some keyBaseWord,
        some strideWords, some capacity, some key0, some key1, some key2, some key3 =>
        some (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, strideWords,
          capacity, key0, key1, key2, key3)
    | _, _, _, _, _, _, _, _, _, _, _ => none
  else
    none

private def findAccDataRbTreeKey4Remove (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataRbTreeKey4Remove :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataRbTreeKey4Remove env e with
      | some remove => some remove
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataRbTreeKey4Remove env fuel' value <|>
                findAccDataRbTreeKey4Remove env fuel' body
          | .lam _ _ body _ => findAccDataRbTreeKey4Remove env fuel' body
          | .app fn arg =>
              findAccDataRbTreeKey4Remove env fuel' fn <|>
                findAccDataRbTreeKey4Remove env fuel' arg
          | _ => none

private def decodeAccDataRbTreeTraderDeposit (env : Environment) (e : Expr) :
    Option DecodedAccDataRbTreeTraderDeposit :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeTraderDeposit &&
      e.getAppArgs.size ≥ 13 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 13]!,
        staticNatVal? env args[args.size - 12]!,
        staticNatVal? env args[args.size - 11]!,
        staticNatVal? env args[args.size - 10]!,
        staticNatVal? env args[args.size - 9]!,
        staticNatVal? env args[args.size - 8]!,
        staticNatVal? env args[args.size - 7]!,
        val env args[args.size - 6]!, val env args[args.size - 5]!,
        val env args[args.size - 4]!, val env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some rootWord, some linksBaseWord, some parentBaseWord, some keyBaseWord,
        some strideWords, some capacity, some key0, some key1, some key2, some key3,
        some quoteLots, some baseLots =>
        some (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, strideWords,
          capacity, key0, key1, key2, key3, quoteLots, baseLots)
    | _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  else
    none

private def findAccDataRbTreeTraderDeposit (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataRbTreeTraderDeposit :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataRbTreeTraderDeposit env e with
      | some deposit => some deposit
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataRbTreeTraderDeposit env fuel' value <|>
                findAccDataRbTreeTraderDeposit env fuel' body
          | .lam _ _ body _ => findAccDataRbTreeTraderDeposit env fuel' body
          | .app fn arg =>
              findAccDataRbTreeTraderDeposit env fuel' fn <|>
                findAccDataRbTreeTraderDeposit env fuel' arg
          | _ => none

private def decodeAccDataRbTreeOrderInsert (env : Environment) (e : Expr) :
    Option DecodedAccDataRbTreeOrderInsert :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeOrderInsert &&
      e.getAppArgs.size ≥ 15 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 15]!,
        staticNatVal? env args[args.size - 14]!,
        staticNatVal? env args[args.size - 13]!,
        staticNatVal? env args[args.size - 12]!,
        staticNatVal? env args[args.size - 11]!,
        staticNatVal? env args[args.size - 10]!,
        staticNatVal? env args[args.size - 9]!,
        staticNatVal? env args[args.size - 8]!,
        staticNatVal? env args[args.size - 7]!,
        val env args[args.size - 6]!, val env args[args.size - 5]!,
        val env args[args.size - 4]!, val env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some rootWord, some linksBaseWord, some parentBaseWord, some keyBaseWord,
        some sequenceBaseWord, some strideWords, some capacity, some bid, some price,
        some sequence, some traderIndex, some numBaseLots, some lastValidSlot,
        some lastValidUnixTimestamp =>
        if bid == 0 || bid == 1 then
          some (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, sequenceBaseWord,
            strideWords, capacity, bid == 1, price, sequence, traderIndex, numBaseLots,
            lastValidSlot, lastValidUnixTimestamp)
        else none
    | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  else
    none

private def findAccDataRbTreeOrderInsert (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataRbTreeOrderInsert :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataRbTreeOrderInsert env e with
      | some insert => some insert
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataRbTreeOrderInsert env fuel' value <|>
                findAccDataRbTreeOrderInsert env fuel' body
          | .lam _ _ body _ => findAccDataRbTreeOrderInsert env fuel' body
          | .app fn arg =>
              findAccDataRbTreeOrderInsert env fuel' fn <|>
                findAccDataRbTreeOrderInsert env fuel' arg
          | _ => none

private def decodeAccDataRbTreeOrderRemove (env : Environment) (e : Expr) :
    Option DecodedAccDataRbTreeOrderRemove :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeOrderRemove &&
      e.getAppArgs.size ≥ 11 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 11]!,
        staticNatVal? env args[args.size - 10]!,
        staticNatVal? env args[args.size - 9]!,
        staticNatVal? env args[args.size - 8]!,
        staticNatVal? env args[args.size - 7]!,
        staticNatVal? env args[args.size - 6]!,
        staticNatVal? env args[args.size - 5]!,
        staticNatVal? env args[args.size - 4]!,
        staticNatVal? env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some rootWord, some linksBaseWord, some parentBaseWord, some keyBaseWord,
        some sequenceBaseWord, some strideWords, some capacity, some bid, some price,
        some sequence =>
        if bid == 0 || bid == 1 then
          some (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, sequenceBaseWord,
            strideWords, capacity, bid == 1, price, sequence)
        else none
    | _, _, _, _, _, _, _, _, _, _, _ => none
  else
    none

private def findAccDataRbTreeOrderRemove (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataRbTreeOrderRemove :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataRbTreeOrderRemove env e with
      | some remove => some remove
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataRbTreeOrderRemove env fuel' value <|>
                findAccDataRbTreeOrderRemove env fuel' body
          | .lam _ _ body _ => findAccDataRbTreeOrderRemove env fuel' body
          | .app fn arg =>
              findAccDataRbTreeOrderRemove env fuel' fn <|>
                findAccDataRbTreeOrderRemove env fuel' arg
          | _ => none

private def decodeAccDataRbTreeOrderSetWordOrRemove (env : Environment) (e : Expr) :
    Option DecodedAccDataRbTreeOrderSetWordOrRemove :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.accDataRbTreeOrderSetWordOrRemove &&
      e.getAppArgs.size ≥ 14 then
    let args := e.getAppArgs
    match staticNatVal? env args[args.size - 14]!,
        staticNatVal? env args[args.size - 13]!,
        staticNatVal? env args[args.size - 12]!,
        staticNatVal? env args[args.size - 11]!,
        staticNatVal? env args[args.size - 10]!,
        staticNatVal? env args[args.size - 9]!,
        staticNatVal? env args[args.size - 8]!,
        staticNatVal? env args[args.size - 7]!,
        staticNatVal? env args[args.size - 6]!,
        staticNatVal? env args[args.size - 5]!,
        val env args[args.size - 4]!, val env args[args.size - 3]!,
        val env args[args.size - 2]!, val env args[args.size - 1]! with
    | some acc, some rootWord, some linksBaseWord, some parentBaseWord, some keyBaseWord,
        some sequenceBaseWord, some valueBaseWord, some strideWords, some capacity, some bid,
        some price, some sequence, some index, some value =>
        if bid == 0 || bid == 1 then
          some (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, sequenceBaseWord,
            valueBaseWord, strideWords, capacity, bid == 1, price, sequence, index, value)
        else none
    | _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  else
    none

private def findAccDataRbTreeOrderSetWordOrRemove (env : Environment) (fuel : Nat) (e : Expr) :
    Option DecodedAccDataRbTreeOrderSetWordOrRemove :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
      let e := normalizeStorageEffect env e
      match decodeAccDataRbTreeOrderSetWordOrRemove env e with
      | some update => some update
      | none =>
          match e.consumeMData with
          | .letE _ _ value body _ =>
              findAccDataRbTreeOrderSetWordOrRemove env fuel' value <|>
                findAccDataRbTreeOrderSetWordOrRemove env fuel' body
          | .lam _ _ body _ => findAccDataRbTreeOrderSetWordOrRemove env fuel' body
          | .app fn arg =>
              findAccDataRbTreeOrderSetWordOrRemove env fuel' fn <|>
                findAccDataRbTreeOrderSetWordOrRemove env fuel' arg
          | _ => none

/-- Distinguish an absent SVM component effect from one whose static shape or dynamic value failed
to decode. Such a call must fail extraction rather than disappear. -/
def mentionsSvmEffect (env : Environment) (fuel : Nat) (e : Expr) : Bool :=
  let constants := e.getUsedConstantsAsSet
  if constants.contains ``ProofForge.Svm.Runtime.accDataWordSetAt ||
      constants.contains ``ProofForge.Svm.Runtime.accDataWordSetAtOneBased ||
      constants.contains ``ProofForge.Svm.Runtime.accDataRbTreeKey4Insert ||
      constants.contains ``ProofForge.Svm.Runtime.accDataRbTreeKey4Remove ||
      constants.contains ``ProofForge.Svm.Runtime.accDataRbTreeTraderDeposit ||
      constants.contains ``ProofForge.Svm.Runtime.accDataRbTreeOrderInsert ||
      constants.contains ``ProofForge.Svm.Runtime.accDataRbTreeOrderRemove ||
      constants.contains ``ProofForge.Svm.Runtime.accDataRbTreeOrderSetWordOrRemove ||
      constants.contains ``ProofForge.Svm.Runtime.batchRecorderBegin ||
      constants.contains ``ProofForge.Svm.Runtime.batchRecorderAppend ||
      constants.contains ``ProofForge.Svm.Runtime.batchRecorderFinish ||
      constants.contains ``ProofForge.Svm.Runtime.fifoCancelBegin ||
      constants.contains ``ProofForge.Svm.Runtime.fifoCancelSide ||
      constants.contains ``ProofForge.Svm.Runtime.fifoCancelUpToSide ||
      constants.contains ``ProofForge.Svm.Runtime.fifoCancelFinish ||
      constants.contains ``ProofForge.Svm.Runtime.memoryCopy ||
      constants.contains ``ProofForge.Svm.Runtime.memoryMove ||
      constants.contains ``ProofForge.Svm.Runtime.memorySet ||
      constants.contains ``ProofForge.Svm.Runtime.transientVecBegin ||
      constants.contains ``ProofForge.Svm.Runtime.transientVecPush ||
      constants.contains ``ProofForge.Svm.Runtime.transientVecSet ||
      constants.contains ``ProofForge.Svm.Runtime.transientVecTruncate ||
      constants.contains ``ProofForge.Svm.Runtime.transientVecClear ||
      constants.contains ``ProofForge.Svm.Runtime.transientVecFinish ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesBegin ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesPush ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesAppendLe64 ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesSet ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesTruncate ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesClear ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesLogData ||
      constants.contains ``ProofForge.Svm.Runtime.transientBytesFinish ||
      constants.contains ``ProofForge.Svm.Runtime.transferLamports ||
      constants.contains ``ProofForge.Svm.Runtime.resizeAccountData then true
  else
    match fuel with
    | 0 => false
    | fuel' + 1 =>
        if let some reduced := reducePureInlineMatch? env e then
          -- A match over a static SDK descriptor selects one applied branch at extraction time.
          -- Reduce it before the generic lambda rule so effects in that selected branch are not
          -- mistaken for deferred continuation effects.
          mentionsSvmEffect env fuel' reduced
        else
          match unfoldUserHelper env e with
          | some (_, unfolded) => mentionsSvmEffect env fuel' unfolded
          | none =>
              match e.consumeMData with
              | .letE _ _ value body _ =>
                  mentionsSvmEffect env fuel' value || mentionsSvmEffect env fuel' body
              -- A lambda is a deferred continuation, not an effect at its definition site. Applied
              -- lambdas are beta-reduced by `decodeExpr` before effect discovery.
              | .lam .. => false
              | .app fn arg =>
                  mentionsSvmEffect env fuel' fn || mentionsSvmEffect env fuel' arg
              | _ => false

/-- Collect consecutive ignored CPI results without collapsing the final state transition. Every
ignored call needs explicit sequencing: recursive invoke search would otherwise retain the CPI
but silently discard a following state write. -/
private def leadingInvokes (env : Environment) (e : Expr) : Array DecodedInvoke × Expr :=
  let rec go (fuel : Nat) (e : Expr) (invokes : Array DecodedInvoke) :
      Array DecodedInvoke × Expr :=
    match fuel with
    | 0 => (invokes, e)
    | fuel' + 1 =>
      match strip e with
      | .letE _ _ value body _ =>
          if body.hasLooseBVar 0 then
            -- Preserve effect order while substituting a compile-time seed recipe used by a
            -- later signed CPI. Other dependent lets retain the established lowering path.
            match asPdaSeeds value with
            | some _ => go fuel' (body.instantiate1 value) invokes
            | none => (invokes, e)
          else
            match findInvoke env 16 value with
            | some invoke => go fuel' (body.instantiate1 value) (invokes.push invoke)
            | none => (invokes, e)
      | _ => (invokes, e)
  go 16 e #[]

private def substLetsPreservingInvokes (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE n ty value body nd =>
      let scalarBinding := ty.consumeMData.getAppFn.constName? == some ``UInt64
      let value := substLetsPreservingInvokes env fuel' value
      let body := substLetsPreservingInvokes env fuel' body
      let structuredState :=
        (ty.consumeMData.getAppFn.constName?.map (isUserType env)).getD false &&
          ((unfoldUserHelper env value).isSome || (userCtorFields env value).isSome ||
            isIteExpr value)
      if (findInvoke env 16 value).isSome || (findComponentCall env 16 value).isSome ||
          mentionsSvmEffect env 16 value || structuredState || scalarBinding then
        .letE n ty value body nd
      else substLetsPreservingInvokes env fuel' (body.instantiate1 value)
    | .lam n ty body bi => .lam n ty (substLetsPreservingInvokes env fuel' body) bi
    | .app _ _ =>
      let rec goApp (n : Nat) (e : Expr) : Expr :=
        match n, strip e with
        | n + 1, .app f a => .app (goApp n f) (substLetsPreservingInvokes env fuel' a)
        | _, e => substLetsPreservingInvokes env fuel' e
      goApp 32 e
    | e => e

private def invokeOps
    (inv : DecodedInvoke)
    (ret : Ops.Val) : Array Ops.Op :=
  let (prog, metas, data, seeds, bump) := inv
  #[.invoke prog metas data seeds bump, .returnU64 ret]

private def invokeOp (inv : DecodedInvoke) : Ops.Op :=
  let (prog, metas, data, seeds, bump) := inv
  .invoke prog metas data seeds bump

private def accDataWordSetAtOp (write : DecodedAccDataWordSetAt) : Ops.Op :=
  let (indexBase, acc, baseWord, strideWords, capacity, index, value) := write
  match indexBase with
  | .zero => .accDataWordSetAt acc baseWord strideWords capacity index value
  | .one => .accDataWordSetAtOneBased acc baseWord strideWords capacity index value

private def accDataRbTreeKey4InsertOp (insert : DecodedAccDataRbTreeKey4Insert) : Ops.Op :=
  let (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, strideWords,
    capacity, key0, key1, key2, key3) := insert
  .accDataRbTreeKey4Insert acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords
    capacity key0 key1 key2 key3

private def accDataRbTreeKey4RemoveOp (remove : DecodedAccDataRbTreeKey4Remove) : Ops.Op :=
  let (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, strideWords,
    capacity, key0, key1, key2, key3) := remove
  .accDataRbTreeKey4Remove acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords
    capacity key0 key1 key2 key3

private def accDataRbTreeTraderDepositOp
    (deposit : DecodedAccDataRbTreeTraderDeposit) : Ops.Op :=
  let (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, strideWords,
    capacity, key0, key1, key2, key3, quoteLots, baseLots) := deposit
  .accDataRbTreeTraderDeposit acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords
    capacity key0 key1 key2 key3 quoteLots baseLots

private def accDataRbTreeOrderInsertOp (insert : DecodedAccDataRbTreeOrderInsert) : Ops.Op :=
  let (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, sequenceBaseWord,
    strideWords, capacity, bid, price, sequence, traderIndex, numBaseLots, lastValidSlot,
    lastValidUnixTimestamp) := insert
  .accDataRbTreeOrderInsert acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord
    strideWords capacity bid price sequence traderIndex numBaseLots lastValidSlot
    lastValidUnixTimestamp

private def accDataRbTreeOrderRemoveOp (remove : DecodedAccDataRbTreeOrderRemove) : Ops.Op :=
  let (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, sequenceBaseWord,
    strideWords, capacity, bid, price, sequence) := remove
  .accDataRbTreeOrderRemove acc rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord
    strideWords capacity bid price sequence

private def accDataRbTreeOrderSetWordOrRemoveOp
    (update : DecodedAccDataRbTreeOrderSetWordOrRemove) : Ops.Op :=
  let (acc, rootWord, linksBaseWord, parentBaseWord, keyBaseWord, sequenceBaseWord,
    valueBaseWord, strideWords, capacity, bid, price, sequence, index, value) := update
  .accDataRbTreeOrderSetWordOrRemove acc rootWord linksBaseWord parentBaseWord keyBaseWord
    sequenceBaseWord valueBaseWord strideWords capacity bid price sequence index value

/-- Whether the first marked helper layer owns effectful runtime control/sequencing that recursive
primitive discovery must not erase. Static descriptor wrappers and matcher projections can keep
the historical direct discovery path; an `if` around effects or two effectful sides of a `let`
must be unfolded by `decodeExpr` as a whole. Nested helper layers are deliberately not unfolded
here, so one-use facade delegates do not become a new extraction boundary. -/
private def inlineOwnsSvmEffectStructure (env : Environment) (e : Expr) : Bool :=
  let rec go (fuel : Nat) (e : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ =>
          (mentionsSvmEffect env 16 value && mentionsSvmEffect env 16 body) ||
            go fuel' value || go fuel' body
      | .lam .. => false
      | .app fn arg =>
          let isBranch := isConstNamed e ``ite || isConstNamed e ``dite
          (isBranch && mentionsSvmEffect env 16 e) || go fuel' fn || go fuel' arg
      | _ => false
  match unfoldUserHelper env e with
  | some (_, unfolded) => go 32 unfolded
  | none => false

/-- Preserve consecutive ignored SVM effects before decoding their state/return continuation.
The final flag reports an external-account write that was present but could not be decoded. -/
private def leadingSvmEffects (env : Environment) (e : Expr) : Array Ops.Op × Expr × Bool :=
  let rec go (fuel : Nat) (e : Expr) (effects : Array Ops.Op) : Array Ops.Op × Expr × Bool :=
    match fuel with
    | 0 => (effects, e, false)
    | fuel' + 1 =>
      match strip e with
      | .letE _ ty value body _ =>
          if body.hasLooseBVar 0 then
            match asPdaSeeds value with
            | some _ => go fuel' (body.instantiate1 value) effects
            | none =>
                -- A dependent scalar effect is a producer, not a malformed ignored write.
                -- `decodeExpr` lowers its terminal into a lexical local before decoding `body`.
                -- Keep malformed detection for unsupported dependent non-scalar effects.
                let scalarBinding := ty.consumeMData.getAppFn.constName? == some ``UInt64
                (effects, e, !scalarBinding && mentionsSvmEffect env 16 value)
          else
            -- A marked SDK combinator may sequence multiple component effects or own runtime
            -- branch-local effects. Do not let recursive component discovery select only one
            -- nested call and erase siblings/control flow; simple facade delegates keep the
            -- established direct primitive path.
            if inlineOwnsSvmEffectStructure env value then
              (effects, e, false)
            else
              match findComponentCall env 16 value, findInvoke env 16 value,
                  findAccDataWordSetAt env 16 value,
                  findAccDataRbTreeKey4Insert env 16 value,
                  findAccDataRbTreeKey4Remove env 16 value,
                  findAccDataRbTreeTraderDeposit env 16 value,
                  findAccDataRbTreeOrderInsert env 16 value,
                  findAccDataRbTreeOrderRemove env 16 value,
                  findAccDataRbTreeOrderSetWordOrRemove env 16 value with
              | some call, _, _, _, _, _, _, _, _ =>
                  go fuel' (body.instantiate1 value) (effects.push (.component call))
              | none, some invoke, _, _, _, _, _, _, _ =>
                  go fuel' (body.instantiate1 value) (effects.push (invokeOp invoke))
              | none, none, some write, _, _, _, _, _, _ =>
                  go fuel' (body.instantiate1 value) (effects.push (accDataWordSetAtOp write))
              | none, none, none, some insert, _, _, _, _, _ =>
                  go fuel' (body.instantiate1 value)
                    (effects.push (accDataRbTreeKey4InsertOp insert))
              | none, none, none, none, some remove, _, _, _, _ =>
                  go fuel' (body.instantiate1 value)
                    (effects.push (accDataRbTreeKey4RemoveOp remove))
              | none, none, none, none, none, some deposit, _, _, _ =>
                  go fuel' (body.instantiate1 value)
                    (effects.push (accDataRbTreeTraderDepositOp deposit))
              | none, none, none, none, none, none, some insert, _, _ =>
                  go fuel' (body.instantiate1 value)
                    (effects.push (accDataRbTreeOrderInsertOp insert))
              | none, none, none, none, none, none, none, some remove, _ =>
                  go fuel' (body.instantiate1 value)
                    (effects.push (accDataRbTreeOrderRemoveOp remove))
              | none, none, none, none, none, none, none, none, some update =>
                  go fuel' (body.instantiate1 value)
                    (effects.push (accDataRbTreeOrderSetWordOrRemoveOp update))
              | none, none, none, none, none, none, none, none, none =>
                  (effects, e, mentionsSvmEffect env 16 value)
      | _ => (effects, e, false)
  go 32 e #[]

/-- `.ok (state, ret)` 的第二元。找不到就 none。 -/
private def findOkRet (env : Environment) (e : Expr) : Option Ops.Val :=
  let rec go (fuel : Nat) (e : Expr) : Option Ops.Val :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``Except.ok && e.getAppArgs.size ≥ 1 then
        let pair := strip e.getAppArgs[e.getAppArgs.size - 1]!
        if isConstNamed pair ``Prod.mk && pair.getAppArgs.size ≥ 2 then
          let ret := pair.getAppArgs[pair.getAppArgs.size - 1]!
          -- Constant evaluation of Runtime stubs must not turn a consumed CPI result into zero.
          if mentionsRuntime env ret "invoke" || mentionsRuntime env ret "invokeSigned" then none
          else val env ret
        else none
      else
        match e with
        | .letE _ _ value body _ => go fuel' (body.instantiate1 value)
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

private def invokeRet
    (env : Environment) (e : Expr)
    (inv : DecodedInvoke) :
    Except String Ops.Val :=
  let validAsciiSeedLength (length : Ops.Val) (seed : String) : Bool :=
    match length with
    | .lit encoded =>
        encoded.toNat == seed.length &&
          ProofForge.Svm.Seed.Ascii.wellFormed seed
    | _ => false
  let seededResult (length : Ops.Val) (seed : String) (result : Ops.Val) : Except String Ops.Val :=
    if validAsciiSeedLength length seed then .ok result
    else .error "extract/unsupported: System seed must be 1-32 ASCII bytes with matching length"
  if let some ret := findOkRet env e then
    .ok ret
  else match inv with
  | (2, _, #[.u32le (.lit 2), .u64le amount], #[], none) => .ok amount
  | (2, _, #[.u32le (.lit 0), .u64le amount, .u64le _, .programId], #[], none) => .ok amount
  | (2, _, #[.u32le (.lit 0), .u64le amount, .u64le _, .programId], #[.ascii _], some _) =>
      .ok amount
  | (1, _, #[.u32le (.lit 1), .programId], #[], none) => .ok (.lit 0)
  | (1, _, #[.u32le (.lit 8), .u64le space], #[], none) => .ok space
  | (2, _, #[.u32le (.lit 9), .accKey 0, .u64le length, .ascii seed, .u64le space,
      .programId], #[], none) => seededResult length seed space
  | (2, _, #[.u32le (.lit 3), .accKey 0, .u64le length, .ascii seed, .u64le lamports,
      .u64le _, .programId], #[], none) => seededResult length seed lamports
  | (2, _, #[.u32le (.lit 10), .accKey 0, .u64le length, .ascii seed, .programId], #[], none) =>
      seededResult length seed (.lit 0)
  | (3, _, #[.u32le (.lit 11), .u64le lamports, .u64le length, .ascii seed,
      .programId], #[], none) => seededResult length seed lamports
  | (2, _, #[.u8le (.lit 20), .u8le (.lit 6), .accKey 0, .u8le (.lit 0)], #[], none) => .ok (.lit 0)
  | (2, _, #[.u8le (.lit 17)], #[], none) => .ok (.lit 0)
  -- Statically indexed classic/Token-2022 TransferChecked wrappers return their modeled amount;
  -- the token program may occupy any authenticated external account index.
  | (_, _, #[.u8le (.lit 12), .u64le amount, .u8le _], #[], none) => .ok amount
  | (_, _, #[.u8le (.lit 12), .u64le amount, .u8le _], _, some _) => .ok amount
  | (_, _, #[.u8le (.lit 3), .u64le amount], #[], none) => .ok amount
  | (_, _, #[.u8le (.lit 3), .u64le amount], _, some _) => .ok amount
  | (3, _, #[.u8le (.lit 14), .u64le amount, .u8le _], #[], none) => .ok amount
  | (3, _, #[.u8le (.lit 15), .u64le amount, .u8le _], #[], none) => .ok amount
  | (3, _, #[.u8le (.lit 18), .accKey 0], #[], none) => .ok (.lit 0)
  | (3, _, #[.u8le (.lit 9)], #[], none) => .ok (.lit 0)
  | (4, _, #[.u8le (.lit 13), .u64le amount, .u8le _], #[], none) => .ok amount
  | (3, _, #[.u8le (.lit 10)], #[], none) => .ok (.lit 0)
  | (3, _, #[.u8le (.lit 11)], #[], none) => .ok (.lit 0)
  | (3, _, #[.u8le (.lit 6), .u8le (.lit 0), .u8le (.lit 1), .accKey 2], #[], none) => .ok (.lit 0)
  | (3, _, #[.u8le (.lit 5)], #[], none) => .ok (.lit 0)
  | (2, _, #[.u8le (.lit 21)], #[], none) => .ok .cpiReturn
  | (1, _, #[.ascii memo], #[], none) =>
      if ProofForge.Svm.Memo.Ascii.wellFormed memo then .ok (.lit 0)
      else .error "extract/unsupported: Memo payload must be at most 512 ASCII bytes"
  | (6, _, #[.u8le (.lit 1)], #[], none) => .ok (.lit 0)
  | (programIx, _, data, _, _) =>
      match data[0]? with
      | some (ProofForge.Svm.Ops.CpiWord.selfEntry ..) => .ok (.lit 0)
      | _ => .error s!"extract/unsupported: unknown CPI return semantics for program {programIx}"

private def invokeOpsWithRet
    (env : Environment) (e : Expr)
    (inv : DecodedInvoke) :
    Except String (Array Ops.Op) := do
  return invokeOps inv (← invokeRet env e inv)

private def forRangeEnd (env : Environment) (e : Expr) : Option Nat :=
  let rec rangeEnd (fuel : Nat) (e : Expr) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if endsWith e ".mk" || e.getAppFn.constName?.isSome then
        let rargs := e.getAppArgs
        if rargs.size ≥ 2 then
          match asStaticLit env 16 rargs[1]! with
          | some (.lit n) => some n.toNat
          | _ => rargs.findSome? (rangeEnd fuel')
        else rargs.findSome? (rangeEnd fuel')
      else e.getAppArgs.findSome? (rangeEnd fuel')
  rangeEnd 8 e

/-- `forAccum` / `forBody`：下标位的 `.arg` 是循环变量。不要改 payload。 -/
private partial def rewriteLoopIx : Ops.Val → Ops.Val
  | .indexGet b n i k off => .indexGet b n (rewriteLoopIx i) k off
  -- State-loop callbacks expose the mutable accumulator and index as their two innermost
  -- binders. Depending on zeta/proof reduction, the scalar index is decoded as either one;
  -- captured method parameters remain at indices ≥ 2 and are normalized later.
  | .arg 0 | .arg 1 => .loopIx
  | .field b n => .field (rewriteLoopIx b) n
  | .bitAnd l r => .bitAnd (rewriteLoopIx l) (rewriteLoopIx r)
  | .bitOr l r => .bitOr (rewriteLoopIx l) (rewriteLoopIx r)
  | .bitXor l r => .bitXor (rewriteLoopIx l) (rewriteLoopIx r)
  | .bitNot v => .bitNot (rewriteLoopIx v)
  | .shiftL l r => .shiftL (rewriteLoopIx l) (rewriteLoopIx r)
  | .shiftR l r => .shiftR (rewriteLoopIx l) (rewriteLoopIx r)
  | .select c l r t f =>
      .select c (rewriteLoopIx l) (rewriteLoopIx r) (rewriteLoopIx t) (rewriteLoopIx f)
  | .addU64 l r => .addU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .subU64 l r => .subU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .mulU64 l r => .mulU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .divU64 l r => .divU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .modU64 l r => .modU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .ext kind operands => .ext kind (operands.map rewriteLoopIx)
  | v => v

private partial def rewriteLoopOp : Ops.Op → Ops.Op
  | .letLocal i v => .letLocal i (rewriteLoopIx v)
  | .joinLocal i => .joinLocal i
  | .setLocal i v => .setLocal i (rewriteLoopIx v)
  | .checkedAddU64 l r => .checkedAddU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedSubU64 l r => .checkedSubU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedMulU64 l r => .checkedMulU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedDivU64 l r => .checkedDivU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .checkedModU64 l r => .checkedModU64 (rewriteLoopIx l) (rewriteLoopIx r)
  | .ite c l r t f =>
      .ite c (rewriteLoopIx l) (rewriteLoopIx r)
        (t.map rewriteLoopOp) (f.map rewriteLoopOp)
  | .invoke prog metas data seed bump =>
      .invoke prog metas (data.map (·.map rewriteLoopIx)) seed (bump.map rewriteLoopIx)
  | .indexSetLeaf n i v k leaf =>
      .indexSetLeaf n (rewriteLoopIx i) (rewriteLoopIx v) k leaf
  | .indexSet n i v k off =>
      .indexSet n (rewriteLoopIx i) (rewriteLoopIx v) k off
  | .storeField n v => .storeField n (rewriteLoopIx v)
  | .okState v => .okState (rewriteLoopIx v)
  | .returnU64 v => .returnU64 (rewriteLoopIx v)
  | .returnState _ => .errorOverflow
  | .forAccum n v resultLocal => .forAccum n (rewriteLoopIx v) resultLocal
  | .forBody n body => .forBody n (body.map rewriteLoopOp)
  | op => op

/--
普通 accumulator / early-return 循环沿用原来的 callback 归一化：账户参数落到
`.arg 0`，动态索引就是 `loopIx`，而 `indexSet` payload 仍是外层方法参数。
State-carrying loop 不能用这条宽松规则，继续走上面的精确 binder 重写。
-/
private partial def rewritePlainLoopIx : Ops.Val → Ops.Val
  | .indexGet b n i k off =>
      let b' := match b with | .arg _ => .arg 0 | _ => rewritePlainLoopIx b
      let i' := match i with | .lit _ => i | _ => .loopIx
      .indexGet b' n i' k off
  | .field b n => .field (rewritePlainLoopIx b) n
  | .bitAnd l r => .bitAnd (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .bitOr l r => .bitOr (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .bitXor l r => .bitXor (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .bitNot x => .bitNot (rewritePlainLoopIx x)
  | .shiftL l r => .shiftL (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .shiftR l r => .shiftR (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .select c l r t f =>
      .select c (rewritePlainLoopIx l) (rewritePlainLoopIx r)
        (rewritePlainLoopIx t) (rewritePlainLoopIx f)
  | .addU64 l r => .addU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .subU64 l r => .subU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .mulU64 l r => .mulU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .divU64 l r => .divU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .modU64 l r => .modU64 (rewritePlainLoopIx l) (rewritePlainLoopIx r)
  | .ext kind operands => .ext kind (operands.map rewritePlainLoopIx)
  | v => v

private partial def rewritePlainLoopOp (op : Ops.Op) : Ops.Op :=
  let rv := rewritePlainLoopIx
  match op with
  | .letLocal i v => .letLocal i (rv v)
  | .joinLocal i => .joinLocal i
  | .setLocal i v => .setLocal i (rv v)
  | .checkedAddU64 l r => .checkedAddU64 (rv l) (rv r)
  | .checkedSubU64 l r => .checkedSubU64 (rv l) (rv r)
  | .checkedMulU64 l r => .checkedMulU64 (rv l) (rv r)
  | .checkedDivU64 l r => .checkedDivU64 (rv l) (rv r)
  | .checkedModU64 l r => .checkedModU64 (rv l) (rv r)
  | .ite c l r t f =>
      let l' := match l with | .arg _ => .loopIx | _ => rv l
      let r' := match r with | .arg _ => .loopIx | _ => rv r
      .ite c l' r' (t.map rewritePlainLoopOp) (f.map rewritePlainLoopOp)
  | .invoke prog metas data seed bump =>
      .invoke prog metas (data.map (·.map rv)) seed (bump.map rv)
  | .indexSetLeaf n i v k leaf =>
      let i' := match i with | .lit _ => i | _ => .loopIx
      let v' := match v with | .arg _ => .arg 0 | _ => v
      .indexSetLeaf n i' v' k leaf
  | .indexSet n i v k off =>
      let i' := match i with | .lit _ => i | _ => .loopIx
      let v' := match v with | .arg _ => .arg 0 | _ => v
      .indexSet n i' v' k off
  | .storeField n v => .storeField n v
  | .okState v => .okState (match v with | .arg _ => .arg 0 | _ => v)
  | .returnU64 v => .returnU64 (rv v)
  | .returnState _ => .errorOverflow
  | .forAccum n v resultLocal => .forAccum n (rv v) resultLocal
  | .forBody n body => .forBody n (body.map rewritePlainLoopOp)
  | op => op

private def findForIn (env : Environment) (e : Expr) : Option (Nat × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Nat × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then
        let args := e.getAppArgs
        let n? := args.findSome? (forRangeEnd env)
        let rec findAdd (fuel : Nat) (e : Expr) : Option Ops.Val :=
          match fuel with
          | 0 => none
          | fuel' + 1 =>
            let e := strip e
            if isConstNamed e ``HAdd.hAdd && e.getAppArgs.size ≥ 2 then
              (asVal env 8 e.getAppArgs[e.getAppArgs.size - 1]!).map rewritePlainLoopIx
            else
              match e with
              | .lam _ _ body _ => findAdd fuel' body
              | .letE _ _ value body _ => findAdd fuel' value <|> findAdd fuel' body
              | _ => e.getAppArgs.findSome? (findAdd fuel')
        let addend? := args.findSome? (findAdd 16)
        match n?, addend? with
        | some n, some v =>
          if n = 0 || n > 64 then none else some (n, v)
        | _, _ => none
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

/-- `for i in [:n]` 里 `ForInStep.done` 提前返回。累加仍走 `findForIn`。 -/
private def findForBodyExpr (env : Environment) (e : Expr) : Option (Nat × Expr) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Nat × Expr) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then
        if (findForIn env e).isSome then none
        else
          let args := e.getAppArgs
          let n? := args.findSome? (forRangeEnd env)
          -- `forIn xs init (fun i r => body)`：最后一个 λ 是循环体。
          let rec lastLam (fuel : Nat) (e : Expr) : Option Expr :=
            match fuel with
            | 0 => none
            | fuel' + 1 =>
              match strip e with
              | .lam _ _ body _ =>
                match strip body with
                | .lam _ _ body2 _ => some (peelLets body2)
                | _ => some (peelLets body)
              | .letE _ _ _ body _ => lastLam fuel' body
              | e => e.getAppArgs.findSome? (lastLam fuel')
          let bodyE? :=
            if args.size > 0 then lastLam 8 args[args.size - 1]! else none
          match n?, bodyE? with
          | some n, some bodyE =>
            if n = 0 || n > 64 then none else some (n, bodyE)
          | _, _ => none
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

/-- Conservatively detect a structured State binding before zeta reduction erases its sharing. -/
def containsStructuredStateLet (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      match strip e with
      | .letE _ type value body _ =>
          let userStructure :=
            (type.consumeMData.getAppFn.constName?.map (isUserType env)).getD false
          (userStructure && (isIteExpr value || (unfoldUserHelper env value).isSome)) ||
            containsStructuredStateLet env fuel value || containsStructuredStateLet env fuel body
      | .lam _ _ body _ => containsStructuredStateLet env fuel body
      | .app fn arg =>
          containsStructuredStateLet env fuel fn || containsStructuredStateLet env fuel arg
      | _ => false

/-- Detect a marked State transition below surrounding control/record syntax. -/
private def containsInlineStateTransition (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      let e := strip e
      let here :=
        match unfoldUserHelper env e with
        | some (name, _) => inlineHelperPreservesUserType env name
        | none => false
      here || match e with
        | .letE _ _ value body _ =>
            containsInlineStateTransition env fuel value ||
              containsInlineStateTransition env fuel body
        | .lam _ _ body _ => containsInlineStateTransition env fuel body
        | .app fn arg =>
            containsInlineStateTransition env fuel fn ||
              containsInlineStateTransition env fuel arg
        | _ => false

/--
`do let mut st := s; for ... do st := ...; k st` 的 loop body 与 continuation。
真正是否为 state-carrying loop 由 body 解码出的显式 store 判定；普通 early-return
`forBody` 继续走旧路径。
-/
private def findForStateExpr (env : Environment) (e : Expr) :
    Option (Nat × Expr × Expr × Expr) :=
  let rec findForExpr (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then some e
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ =>
          findForExpr fuel' value <|> findForExpr fuel' (body.instantiate1 value)
        | .lam _ _ body _ => findForExpr fuel' body
        | _ => e.getAppArgs.findSome? (findForExpr fuel')
  let loopParts? := do
    let forExpr ← findForExpr 32 e
    let n ← forExpr.getAppArgs.findSome? (forRangeEnd env)
    let rec lastLam (fuel : Nat) (e : Expr) : Option Expr :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        match strip e with
        | .lam _ _ body _ =>
          match strip body with
          | .lam _ _ body2 _ => some (substLetsPreservingInvokes env 128 body2)
          | _ => some (substLetsPreservingInvokes env 128 body)
        | .letE _ _ _ body _ => lastLam fuel' body
        | e => e.getAppArgs.findSome? (lastLam fuel')
    let args := forExpr.getAppArgs
    if args.size < 2 then none else
    let initial := args[args.size - 2]!
    let body ← if h : args.size > 0 then lastLam 16 args[args.size - 1] else none
    if n = 0 || n > 64 then none else some (n, initial, body)
  let rec findContinuation (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then
          findContinuation fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if isConstNamed e ``ite || isConstNamed e ``dite then none
      else
        match e with
        | .letE _ _ value body _ => findContinuation fuel' (body.instantiate1 value)
        | _ =>
          if e.getAppFn.constName? == some ``Bind.bind || endsWith e ".bind" then
            let args := e.getAppArgs
            if args.any fun a => (findForExpr 16 a).isSome then
              match args.findRev? fun a => match strip a with | .lam .. => true | _ => false with
              | some continuation =>
                match strip continuation with
                | .lam _ _ continuationBody _ =>
                  if containsStructuredStateLet env 2048 continuationBody ||
                      containsInlineStateTransition env 2048 continuationBody then
                    some (strip continuationBody)
                  else
                    some (peelControl 16
                      (substLetsPreservingInvokes env 128 continuationBody))
                | _ => none
              | none => none
            else args.findSome? (findContinuation fuel')
          else
            e.getAppArgs.findSome? (findContinuation fuel')
  match loopParts?, findContinuation 32 e with
  | some (n, initial, bodyE), some continuation => some (n, initial, bodyE, continuation)
  | _, _ => none

/-- Flatten the right-nested `MProd` generated by two or more `let mut UInt64` bindings. The
constructor's explicit type arguments keep this gate restricted to scalar `UInt64` leaves. -/
private def scalarFrameLeaves (e : Expr) : Option (Array Expr) :=
  let rec go (fuel : Nat) (value : Expr) : Option (Array Expr) := do
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let value := strip value
      if !isConstNamed value ``MProd.mk then none else
      let args := value.getAppArgs
      if h : args.size ≥ 4 then
        let decodeLeaf (type value : Expr) : Option (Array Expr) :=
          if type.consumeMData.getAppFn.constName? == some ``UInt64 then
            some #[value]
          else if type.consumeMData.getAppFn.constName? == some ``MProd then
            go fuel' value
          else
            none
        let left ← decodeLeaf args[args.size - 4] args[args.size - 2]
        let right ← decodeLeaf args[args.size - 3] args[args.size - 1]
        return left ++ right
      else
        none
  go 32 e

/-- Rebuild an `MProd` frame with extractor local markers while preserving its exact nested shape. -/
private def scalarFrameLocalShape (e : Expr) (base : Nat) : Option Expr := do
  let leaves ← scalarFrameLeaves e
  let rec go (fuel : Nat) (value : Expr) (index : Nat) : Expr × Nat :=
    match fuel with
    | 0 => (value, index)
    | fuel' + 1 =>
      let value := strip value
      if isConstNamed value ``MProd.mk && value.getAppArgs.size ≥ 4 then
        let args := value.getAppArgs
        let (left, index) := go fuel' args[args.size - 2]! index
        let (right, index) := go fuel' args[args.size - 1]! index
        let headArgs := args.extract 0 (args.size - 2)
        (mkAppN value.getAppFn (headArgs ++ #[left, right]), index)
      else
        (mkApp (mkConst ``localRef) (mkNatLit (base + index)), index + 1)
  let (shape, count) := go 32 e 0
  if count == leaves.size then some shape else none

/-- Elaboration flattens a final `MProd` pattern into one continuation lambda per scalar leaf.
Apply that branch directly after replacing the loop result with local markers. -/
private def reduceScalarFrameContinuation? (env : Environment) (e frame : Expr) : Option Expr := do
  let leaves ← scalarFrameLeaves frame
  let e := strip e
  let matcherName ← e.getAppFn.constName?
  let matcher ← Lean.Meta.getMatcherInfoCore? env matcherName
  if matcher.numDiscrs != 1 then none else pure ()
  let args := e.getAppArgs
  let discr ← args[matcher.getFirstDiscrPos]?
  if strip discr != strip frame then none else pure ()
  let branch ← args[matcher.getFirstAltPos]?
  if (peelLams branch).1 != leaves.size then none else
    some (branch.beta leaves)

/-- Mark every scalar-frame yield with its target-local base. The marker is private extraction
syntax, not a source SDK primitive or a target opcode. -/
private def markScalarFrameYields (base : Nat) (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      let raw := strip e
      if (isConstNamed raw ``ForInStep.yield || endsWith raw ".yield") &&
          raw.getAppArgs.size ≥ 2 then
        let args := raw.getAppArgs
        let type := args[args.size - 2]!
        let value := go fuel' args[args.size - 1]!
        let marked := mkApp3 (mkConst ``scalarFrameYield) type (mkNatLit base) value
        mkAppN raw.getAppFn (args.extract 0 (args.size - 1) |>.push marked)
      else
        match raw with
        | .app fn arg => .app (go fuel' fn) (go fuel' arg)
        | .lam name type body info => .lam name (go fuel' type) (go fuel' body) info
        | .forallE name type body info => .forallE name (go fuel' type) (go fuel' body) info
        | .letE name type value body nondep =>
            .letE name (go fuel' type) (go fuel' value) (go fuel' body) nondep
        | .mdata data body => .mdata data (go fuel' body)
        | .proj type index value => .proj type index (go fuel' value)
        | e => e
  go 128 e

/-- 收集 `xs.set … .set …` 整条链。先外层（旧向量），后内层（新写）。
一次 `set` 可以改多叶（`left` + `parent`）。 -/
private def collectIndexSets (env : Environment) (e : Expr)
    (deduplicate : Bool := false) (appliedBases : Array Expr := #[]) : Array Ops.Op :=
  let rec go (fuel : Nat) (e : Expr) (state : Array Expr × Array Ops.Op) :
      Array Expr × Array Ops.Op :=
    match fuel with
    | 0 => state
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ => go fuel' (body.instantiate1 value) state
      | .lam _ _ body _ => go fuel' body state
      | _ =>
        if isConstNamed e ``Except.ok && e.getAppArgs.size ≥ 1 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 1]! state
        else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 2]! state
        else if isVectorSet e then
          -- `Vector.set α n xs i v h`：只沿 xs 追溯旧写。payload/下标里的
          -- vector reads 不是写；共享 record projections 也会重复引用同一个 set node。
          if deduplicate && state.1.contains e then state else
            let args := e.getAppArgs
            let state :=
              if h : args.size ≥ 4 then go fuel' args[args.size - 4] state else state
            match asIndexSets env e with
            | some ops =>
                let seen := if deduplicate then state.1.push e else state.1
                (seen, state.2 ++ ops)
            | none => state
        else
          let inheritedFromAppliedBase :=
            match e.getAppFn.constName? with
            | some projection =>
              match env.getProjectionFnInfo? projection with
              | some _ =>
                let args := e.getAppArgs
                (args[args.size - 1]?.map appliedBases.contains).getD false
              | none => false
            | none => false
          if inheritedFromAppliedBase then state
          else e.getAppArgs.foldl (init := state) fun state arg => go fuel' arg state
  (go 16 e (#[], #[])).2

private def findIndexSet (env : Environment) (e : Expr) : Option Ops.Op :=
  (collectIndexSets env e)[0]?

private def nthFromEnd (args : Array Expr) (n : Nat) : Option Expr :=
  if args.size ≥ n + 1 then some args[args.size - 1 - n]! else none

private def valAtEnd (env : Environment) (args : Array Expr) (n : Nat) : Ops.Val :=
  match nthFromEnd args n with
  | some e => (val env e).getD (.arg n)
  | none => .arg n

/-- EVM hashed-map namespaces are compile-time storage descriptors. Reduce their closed Nat
geometry without changing ordinary source arithmetic or another target's canonical IR. -/
private def mapBaseAtEnd (env : Environment) (args : Array Expr) (n : Nat) : Ops.Val :=
  match nthFromEnd args n with
  | some e => foldClosedU64 <| (asEvmMapBaseLit env 64 e <|> val env e).getD (.arg n)
  | none => .arg n

private def opOfRuntimeApp (env : Environment) (app : Expr) : Option Ops.Op :=
  let args := app.getAppArgs
  if isConstNamed app ``ProofForge.Evm.Runtime.evmDeposit || endsWith app ".evmDeposit" then
    some (.evmDeposit (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmDeposit256 || endsWith app ".evmDeposit256" then
    match nthFromEnd args 0 with
    | some amt =>
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmDeposit256 a0 a1 a2 a3)
    | none => some (.evmDeposit256 (.arg 0) (.arg 1) (.arg 2) (.arg 3))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSendEth || endsWith app ".evmSendEth" then
    let amt := valAtEnd env args 0
    match nthFromEnd args 1 with
    | some dst =>
      let (w0, w1, w2) := addr20Leaves env dst
      some (.evmSendEth w0 w1 w2 amt)
    | none => some (.evmSendEth (.arg 0) (.arg 1) (.arg 2) amt)
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSendEth256 || endsWith app ".evmSendEth256" then
    match nthFromEnd args 1, nthFromEnd args 0 with
    | some dst, some amt =>
      let (w0, w1, w2) := addr20Leaves env dst
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmSendEth256 w0 w1 w2 a0 a1 a2 a3)
    | _, _ => some (.evmSendEth256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogTipped || endsWith app ".evmLogTipped" then
    some (.evmLog "Tipped" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogIncremented ||
      endsWith app ".evmLogIncremented" then
    some (.evmLog "Incremented" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogTransfer ||
      endsWith app ".evmLogTransfer" then
    some (.evmLog "Transfer" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogApproval ||
      endsWith app ".evmLogApproval" then
    some (.evmLog "Approval" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogTransfer256 ||
      endsWith app ".evmLogTransfer256" then
    match nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some src, some dest, some amt =>
      let (f0, f1, f2) := addr20Leaves env src
      let (t0, t1, t2) := addr20Leaves env dest
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmLogTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3)
    | _, _, _ =>
      some (.evmLogTransfer256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogApproval256 ||
      endsWith app ".evmLogApproval256" then
    match nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some owner, some spender, some amt =>
      let (o0, o1, o2) := addr20Leaves env owner
      let (s0, s1, s2) := addr20Leaves env spender
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmLogApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3)
    | _, _, _ =>
      some (.evmLogApproval256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmRevertInsufficient ||
      endsWith app ".evmRevertInsufficient" then
    match nthFromEnd args 1, nthFromEnd args 0 with
    | some haveAmt, some wantAmt =>
      let (h0, h1, h2, h3) := uint256Leaves env haveAmt
      let (w0, w1, w2, w3) := uint256Leaves env wantAmt
      some (.evmRevertInsufficient h0 h1 h2 h3 w0 w1 w2 w3)
    | _, _ =>
      some (.evmRevertInsufficient (.arg 0) (.arg 1) (.arg 2) (.arg 3)
        (.arg 4) (.arg 5) (.arg 6) (.arg 7))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmRevertUnauthorized ||
      endsWith app ".evmRevertUnauthorized" then
    match nthFromEnd args 0 with
    | some who =>
      let (w0, w1, w2) := addr20Leaves env who
      some (.evmRevertUnauthorized w0 w1 w2)
    | none => some (.evmRevertUnauthorized (.arg 0) (.arg 1) (.arg 2))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmRevertZeroAddress ||
      endsWith app ".evmRevertZeroAddress" then
    some .evmRevertZeroAddress
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmRevertPaused ||
      endsWith app ".evmRevertPaused" then
    some .evmRevertPaused
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmRevertCapExceeded ||
      endsWith app ".evmRevertCapExceeded" then
    some .evmRevertCapExceeded
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmReceive || endsWith app ".evmReceive" then
    some .evmReceive
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmStoreStaticU64 ||
      endsWith app ".evmStoreStaticU64" then
    match nthFromEnd args 1 with
    | some field =>
      some (.evmStoreStaticU64 ((staticString? env 64 field).getD "") (valAtEnd env args 0))
    | none => some (.evmStoreStaticU64 "" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetU64 || endsWith app ".evmMapSetU64" then
    some (.mapSetU64 (mapBaseAtEnd env args 2) (valAtEnd env args 1) (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetAddr || endsWith app ".evmMapSetAddr" then
    let val := valAtEnd env args 0
    let base := mapBaseAtEnd env args 2
    match nthFromEnd args 1 with
    | some key =>
      let (w0, w1, w2) := addr20Leaves env key
      some (.mapSetAddr base w0 w1 w2 val)
    | none => some (.mapSetAddr base (.arg 1) (.arg 2) (.arg 3) val)
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetPair || endsWith app ".evmMapSetPair" then
    let val := valAtEnd env args 0
    let base := mapBaseAtEnd env args 3
    match nthFromEnd args 2, nthFromEnd args 1 with
    | some owner, some spender =>
      let (o0, o1, o2) := addr20Leaves env owner
      let (s0, s1, s2) := addr20Leaves env spender
      some (.mapSetPair base o0 o1 o2 s0 s1 s2 val)
    | _, _ => some (.mapSetPair base (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6) val)
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetAddr256 ||
      endsWith app ".evmMapSetAddr256" then
    match nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some _base, some key, some val =>
      let (w0, w1, w2) := addr20Leaves env key
      let (v0, v1, v2, v3) := uint256Leaves env val
      some (.mapSetAddr256 (mapBaseAtEnd env args 2) w0 w1 w2 v0 v1 v2 v3)
    | _, _, _ =>
      some (.mapSetAddr256 (mapBaseAtEnd env args 2) (.arg 1) (.arg 2) (.arg 3)
        (.arg 4) (.arg 5) (.arg 6) (.arg 7))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetPair256 ||
      endsWith app ".evmMapSetPair256" then
    match nthFromEnd args 3, nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some _base, some owner, some spender, some val =>
      let (o0, o1, o2) := addr20Leaves env owner
      let (s0, s1, s2) := addr20Leaves env spender
      let (v0, v1, v2, v3) := uint256Leaves env val
      some (.mapSetPair256 (mapBaseAtEnd env args 3) o0 o1 o2 s0 s1 s2 v0 v1 v2 v3)
    | _, _, _, _ =>
      some (.mapSetPair256 (mapBaseAtEnd env args 3) (.arg 1) (.arg 2) (.arg 3)
        (.arg 4) (.arg 5) (.arg 6) (.arg 7) (.arg 8) (.arg 9) (.arg 10))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenTransfer ||
      endsWith app ".evmTokenTransfer" then
    match nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some token, some dest, some amt =>
      let (t0, t1, t2) := addr20Leaves env token
      let (d0, d1, d2) := addr20Leaves env dest
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmTokenTransfer256 t0 t1 t2 d0 d1 d2 a0 a1 a2 a3)
    | _, _, _ =>
      some (.evmTokenTransfer256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenApprove ||
      endsWith app ".evmTokenApprove" then
    match nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some token, some spender, some amt =>
      let (t0, t1, t2) := addr20Leaves env token
      let (s0, s1, s2) := addr20Leaves env spender
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmTokenApprove256 t0 t1 t2 s0 s1 s2 a0 a1 a2 a3)
    | _, _, _ =>
      some (.evmTokenApprove256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenTransferFrom ||
      endsWith app ".evmTokenTransferFrom" then
    match nthFromEnd args 3, nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some token, some owner, some dest, some amt =>
      let (t0, t1, t2) := addr20Leaves env token
      let (o0, o1, o2) := addr20Leaves env owner
      let (d0, d1, d2) := addr20Leaves env dest
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmTokenTransferFrom256 t0 t1 t2 o0 o1 o2 d0 d1 d2 a0 a1 a2 a3)
    | _, _, _, _ =>
      some (.evmTokenTransferFrom256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9) (.arg 10) (.arg 11) (.arg 12))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmWethDeposit ||
      endsWith app ".evmWethDeposit" then
    match nthFromEnd args 1, nthFromEnd args 0 with
    | some weth, some amt =>
      let (t0, t1, t2) := addr20Leaves env weth
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmWethDeposit256 t0 t1 t2 a0 a1 a2 a3)
    | _, _ =>
      some (.evmWethDeposit256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmWethWithdraw ||
      endsWith app ".evmWethWithdraw" then
    match nthFromEnd args 1, nthFromEnd args 0 with
    | some weth, some amt =>
      let (t0, t1, t2) := addr20Leaves env weth
      let (a0, a1, a2, a3) := uint256Leaves env amt
      some (.evmWethWithdraw256 t0 t1 t2 a0 a1 a2 a3)
    | _, _ =>
      some (.evmWethWithdraw256 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSwapExact2 ||
      endsWith app ".evmSwapExact2" then
    match nthFromEnd args 4, nthFromEnd args 3, nthFromEnd args 2,
        nthFromEnd args 1, nthFromEnd args 0 with
    | some router, some tokenA, some tokenB, some amtIn, some minOut =>
      let (r0, r1, r2) := addr20Leaves env router
      let (a0, a1, a2) := addr20Leaves env tokenA
      let (b0, b1, b2) := addr20Leaves env tokenB
      let (i0, i1, i2, i3) := uint256Leaves env amtIn
      let (m0, m1, m2, m3) := uint256Leaves env minOut
      some (.evmSwapExact2 r0 r1 r2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3)
    | _, _, _, _, _ =>
      some (.evmSwapExact2 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9) (.arg 10) (.arg 11) (.arg 12)
        (.arg 13) (.arg 14) (.arg 15) (.arg 16))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSwapExact3 ||
      endsWith app ".evmSwapExact3" then
    match nthFromEnd args 5, nthFromEnd args 4, nthFromEnd args 3,
        nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some router, some tokenA, some tokenB, some tokenC, some amtIn, some minOut =>
      let (r0, r1, r2) := addr20Leaves env router
      let (a0, a1, a2) := addr20Leaves env tokenA
      let (b0, b1, b2) := addr20Leaves env tokenB
      let (c0, c1, c2) := addr20Leaves env tokenC
      let (i0, i1, i2, i3) := uint256Leaves env amtIn
      let (m0, m1, m2, m3) := uint256Leaves env minOut
      some (.evmSwapExact3 r0 r1 r2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3)
    | _, _, _, _, _, _ =>
      some (.evmSwapExact3 (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9) (.arg 10) (.arg 11) (.arg 12)
        (.arg 13) (.arg 14) (.arg 15) (.arg 16) (.arg 17) (.arg 18) (.arg 19))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenPermit ||
      endsWith app ".evmTokenPermit" then
    match nthFromEnd args 7, nthFromEnd args 6, nthFromEnd args 5, nthFromEnd args 4,
        nthFromEnd args 3, nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some token, some owner, some spender, some value, some deadline, some _v, some r, some s =>
      let (t0, t1, t2) := addr20Leaves env token
      let (o0, o1, o2) := addr20Leaves env owner
      let (s0, s1, s2) := addr20Leaves env spender
      let (v0, v1, v2, v3) := uint256Leaves env value
      let (d0, d1, d2, d3) := uint256Leaves env deadline
      let vv := valAtEnd env args 2
      let (r0, r1, r2, r3) := bytes32Leaves env r
      let (z0, z1, z2, z3) := bytes32Leaves env s
      some (.evmTokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3
        vv r0 r1 r2 r3 z0 z1 z2 z3)
    | _, _, _, _, _, _, _, _ =>
      some (.evmTokenPermit (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9) (.arg 10) (.arg 11) (.arg 12)
        (.arg 13) (.arg 14) (.arg 15) (.arg 16) (.arg 17) (.arg 18) (.arg 19)
        (.arg 20) (.arg 21) (.arg 22) (.arg 23) (.arg 24) (.arg 25))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmPermit ||
      endsWith app ".evmPermit" then
    match nthFromEnd args 6, nthFromEnd args 5, nthFromEnd args 4,
        nthFromEnd args 3, nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
    | some owner, some spender, some value, some deadline, some _v, some r, some s =>
      let (o0, o1, o2) := addr20Leaves env owner
      let (s0, s1, s2) := addr20Leaves env spender
      let (v0, v1, v2, v3) := uint256Leaves env value
      let (d0, d1, d2, d3) := uint256Leaves env deadline
      let vv := valAtEnd env args 2
      let (r0, r1, r2, r3) := bytes32Leaves env r
      let (z0, z1, z2, z3) := bytes32Leaves env s
      some (.evmPermit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3)
    | _, _, _, _, _, _, _ =>
      some (.evmPermit (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5)
        (.arg 6) (.arg 7) (.arg 8) (.arg 9) (.arg 10) (.arg 11) (.arg 12)
        (.arg 13) (.arg 14) (.arg 15) (.arg 16) (.arg 17) (.arg 18) (.arg 19)
        (.arg 20) (.arg 21) (.arg 22))
  else none

/-- Collect EVM effect leaves by unfolding source facades into `ProofForge.Evm.Runtime`
stubs. New closed recipes register in `opOfRuntimeApp`; this walker does not grow a name
table. -/
private def collectEvmEffectOps (env : Environment) (e : Expr) : Array Ops.Op :=
  let rec walk (fuel : Nat) (e : Expr) (acc : Array Ops.Op) : Array Ops.Op :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let e := e.consumeMData
      match opOfRuntimeApp env e with
      | some op => acc.push op
      | none =>
        if let some (_, unfolded) := unfoldUserHelper env e then
          walk fuel' unfolded acc
        else
          match e with
          | .letE _ _ value body _ =>
            walk fuel' (body.instantiate1 value) (walk fuel' value acc)
          | .lam _ _ body _ => walk fuel' body acc
          | .app f a => walk fuel' a (walk fuel' f acc)
          | _ => acc
  walk 24 e #[]

/-- Statement-level EVM queries. 256-bit reads expand to four limb returns; scalar map
gets remain as component Calls so the emitter does not grow a parallel family. New query
recipes register here; `decodeEvmEffect` does not grow a finder table. Env opcodes stay
top-level ValKind and are not collected. -/
private def queryOfRuntimeApp (env : Environment) (app : Expr) : Option (Array Ops.Op) :=
  let args := app.getAppArgs
  if isConstNamed app ``ProofForge.Evm.Runtime.evmMapGetU64 || endsWith app ".evmMapGetU64" then
    let b := mapBaseAtEnd env args 1
    let k := valAtEnd env args 0
    some #[.mapGetU64 b k, .returnU64 k]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapGetAddr || endsWith app ".evmMapGetAddr" then
    let base := mapBaseAtEnd env args 1
    match nthFromEnd args 0 with
    | some key =>
      let (w0, w1, w2) := addr20Leaves env key
      some #[.mapGetAddr base w0 w1 w2, .returnU64 w0]
    | none => some #[.mapGetAddr base (.arg 1) (.arg 2) (.arg 3), .returnU64 (.arg 1)]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapGetPair || endsWith app ".evmMapGetPair" then
    let base := mapBaseAtEnd env args 2
    match nthFromEnd args 1, nthFromEnd args 0 with
    | some owner, some spender =>
      let (o0, o1, o2) := addr20Leaves env owner
      let (s0, s1, s2) := addr20Leaves env spender
      some #[.mapGetPair base o0 o1 o2 s0 s1 s2, .returnU64 o0]
    | _, _ =>
      some #[.mapGetPair base (.arg 1) (.arg 2) (.arg 3) (.arg 4) (.arg 5) (.arg 6),
        .returnU64 (.arg 1)]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapGetAddr256 ||
      endsWith app ".evmMapGetAddr256" then
    let base := mapBaseAtEnd env args 1
    let (w0, w1, w2) :=
      match nthFromEnd args 0 with
      | some key => addr20Leaves env key
      | none => (.arg 1, .arg 2, .arg 3)
    some #[
      .returnU64 (.ext (.evm (.component (.hashedMap (.getAddr256 0)))) #[base, w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.hashedMap (.getAddr256 1)))) #[base, w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.hashedMap (.getAddr256 2)))) #[base, w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.hashedMap (.getAddr256 3)))) #[base, w0, w1, w2])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapGetPair256 ||
      endsWith app ".evmMapGetPair256" then
    let base := mapBaseAtEnd env args 2
    let (o0, o1, o2, s0, s1, s2) :=
      match nthFromEnd args 1, nthFromEnd args 0 with
      | some owner, some spender =>
        let (o0, o1, o2) := addr20Leaves env owner
        let (s0, s1, s2) := addr20Leaves env spender
        (o0, o1, o2, s0, s1, s2)
      | _, _ => (.arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6)
    some #[
      .returnU64 (.ext (.evm (.component (.hashedMap (.getPair256 0)))) #[base, o0, o1, o2, s0, s1, s2]),
      .returnU64 (.ext (.evm (.component (.hashedMap (.getPair256 1)))) #[base, o0, o1, o2, s0, s1, s2]),
      .returnU64 (.ext (.evm (.component (.hashedMap (.getPair256 2)))) #[base, o0, o1, o2, s0, s1, s2]),
      .returnU64 (.ext (.evm (.component (.hashedMap (.getPair256 3)))) #[base, o0, o1, o2, s0, s1, s2])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenBalanceOfSelf ||
      endsWith app ".evmTokenBalanceOfSelf" then
    let (t0, t1, t2) :=
      match nthFromEnd args 0 with
      | some token => addr20Leaves env token
      | none => (.arg 0, .arg 1, .arg 2)
    some #[
      .returnU64 (.ext (.evm (.component (.closedCall (.balance256 0)))) #[t0, t1, t2]),
      .returnU64 (.ext (.evm (.component (.closedCall (.balance256 1)))) #[t0, t1, t2]),
      .returnU64 (.ext (.evm (.component (.closedCall (.balance256 2)))) #[t0, t1, t2]),
      .returnU64 (.ext (.evm (.component (.closedCall (.balance256 3)))) #[t0, t1, t2])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenAllowanceOf ||
      endsWith app ".evmTokenAllowanceOf" then
    let (t0, t1, t2, o0, o1, o2, s0, s1, s2) :=
      match nthFromEnd args 2, nthFromEnd args 1, nthFromEnd args 0 with
      | some token, some owner, some spender =>
        let (t0, t1, t2) := addr20Leaves env token
        let (o0, o1, o2) := addr20Leaves env owner
        let (s0, s1, s2) := addr20Leaves env spender
        (t0, t1, t2, o0, o1, o2, s0, s1, s2)
      | _, _, _ =>
        (.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6, .arg 7, .arg 8)
    some #[
      .returnU64 (.ext (.evm (.component (.closedCall (.allowance256 0))))
        #[t0, t1, t2, o0, o1, o2, s0, s1, s2]),
      .returnU64 (.ext (.evm (.component (.closedCall (.allowance256 1))))
        #[t0, t1, t2, o0, o1, o2, s0, s1, s2]),
      .returnU64 (.ext (.evm (.component (.closedCall (.allowance256 2))))
        #[t0, t1, t2, o0, o1, o2, s0, s1, s2]),
      .returnU64 (.ext (.evm (.component (.closedCall (.allowance256 3))))
        #[t0, t1, t2, o0, o1, o2, s0, s1, s2])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmCallValue256 ||
      endsWith app ".evmCallValue256" then
    some #[
      .returnU64 (.ext (.evm (.callValue256 0)) #[]),
      .returnU64 (.ext (.evm (.callValue256 1)) #[]),
      .returnU64 (.ext (.evm (.callValue256 2)) #[]),
      .returnU64 (.ext (.evm (.callValue256 3)) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSelfBalance256 ||
      endsWith app ".evmSelfBalance256" then
    some #[
      .returnU64 (.ext (.evm (.selfBalance256 0)) #[]),
      .returnU64 (.ext (.evm (.selfBalance256 1)) #[]),
      .returnU64 (.ext (.evm (.selfBalance256 2)) #[]),
      .returnU64 (.ext (.evm (.selfBalance256 3)) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmGasLeft256 ||
      endsWith app ".evmGasLeft256" then
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.gasLeft256 0)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasLeft256 1)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasLeft256 2)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasLeft256 3)))) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmBaseFee256 ||
      endsWith app ".evmBaseFee256" then
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.baseFee256 0)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.baseFee256 1)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.baseFee256 2)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.baseFee256 3)))) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmPrevRandao256 ||
      endsWith app ".evmPrevRandao256" then
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.prevRandao256 0)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.prevRandao256 1)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.prevRandao256 2)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.prevRandao256 3)))) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmGasLimit256 ||
      endsWith app ".evmGasLimit256" then
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.gasLimit256 0)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasLimit256 1)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasLimit256 2)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasLimit256 3)))) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmGasPrice256 ||
      endsWith app ".evmGasPrice256" then
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.gasPrice256 0)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasPrice256 1)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasPrice256 2)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.gasPrice256 3)))) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmBlobBaseFee256 ||
      endsWith app ".evmBlobBaseFee256" then
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.blobBaseFee256 0)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.blobBaseFee256 1)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.blobBaseFee256 2)))) #[]),
      .returnU64 (.ext (.evm (.component (.environment (.blobBaseFee256 3)))) #[])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmBlobHash32 ||
      endsWith app ".evmBlobHash32" then
    let index := valAtEnd env args 0
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.blobHash32 0)))) #[index]),
      .returnU64 (.ext (.evm (.component (.environment (.blobHash32 1)))) #[index]),
      .returnU64 (.ext (.evm (.component (.environment (.blobHash32 2)))) #[index]),
      .returnU64 (.ext (.evm (.component (.environment (.blobHash32 3)))) #[index])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSelector4 ||
      endsWith app ".evmSelector4" then
    some #[.returnU64 (.ext (.evm (.component (.environment .selector4))) #[])]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmCalldataSize ||
      endsWith app ".evmCalldataSize" then
    some #[.returnU64 (.ext (.evm (.component (.environment .calldataSize))) #[])]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmBlockHash256 ||
      endsWith app ".evmBlockHash256" then
    let number := valAtEnd env args 0
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.blockHash256 0)))) #[number]),
      .returnU64 (.ext (.evm (.component (.environment (.blockHash256 1)))) #[number]),
      .returnU64 (.ext (.evm (.component (.environment (.blockHash256 2)))) #[number]),
      .returnU64 (.ext (.evm (.component (.environment (.blockHash256 3)))) #[number])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmBalance256 ||
      endsWith app ".evmBalance256" then
    let (w0, w1, w2) :=
      match nthFromEnd args 0 with
      | some address => addr20Leaves env address
      | none => (.arg 0, .arg 1, .arg 2)
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.balance256 0)))) #[w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.environment (.balance256 1)))) #[w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.environment (.balance256 2)))) #[w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.environment (.balance256 3)))) #[w0, w1, w2])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmCodeHash32 ||
      endsWith app ".evmCodeHash32" then
    let (w0, w1, w2) :=
      match nthFromEnd args 0 with
      | some address => addr20Leaves env address
      | none => (.arg 0, .arg 1, .arg 2)
    some #[
      .returnU64 (.ext (.evm (.component (.environment (.codeHash32 0)))) #[w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.environment (.codeHash32 1)))) #[w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.environment (.codeHash32 2)))) #[w0, w1, w2]),
      .returnU64 (.ext (.evm (.component (.environment (.codeHash32 3)))) #[w0, w1, w2])
    ]
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmDomainSeparator ||
      endsWith app ".evmDomainSeparator" then
    some #[
      .returnU64 (.ext (.evm (.domainSep256 0)) #[]),
      .returnU64 (.ext (.evm (.domainSep256 1)) #[]),
      .returnU64 (.ext (.evm (.domainSep256 2)) #[]),
      .returnU64 (.ext (.evm (.domainSep256 3)) #[])
    ]
  else none

private def collectEvmQueryOps (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  let rec walk (fuel : Nat) (e : Expr) : Option (Array Ops.Op) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      match queryOfRuntimeApp env e with
      | some ops => some ops
      | none =>
        if let some (_, unfolded) := unfoldUserHelper env e then
          walk fuel' unfolded
        else
          match e with
          | .letE _ _ value body _ =>
            walk fuel' value <|> walk fuel' (body.instantiate1 value)
          | .lam _ _ body _ => walk fuel' body
          | .app f a => walk fuel' f <|> walk fuel' a
          | _ => none
  walk 24 e

private def retOfEvmOps (ops : Array Ops.Op) : Ops.Val :=
  match ops.back? with
  | some (.evmDeposit v) => v
  | some (.evmDeposit256 a0 _ _ _) => a0
  | some (.evmSendEth _ _ _ v) => v
  | some (.evmSendEth256 _ _ _ a0 _ _ _) => a0
  | some (.evmLog _ v) => v
  | some (.evmLogTransfer256 _ _ _ _ _ _ a0 _ _ _) => a0
  | some (.evmLogApproval256 _ _ _ _ _ _ a0 _ _ _) => a0
  | some (.evmRevertInsufficient h0 _ _ _ _ _ _ _) => h0
  | some (.evmRevertUnauthorized w0 _ _) => w0
  | some .evmRevertZeroAddress => .lit 0
  | some .evmRevertPaused => .lit 0
  | some .evmRevertCapExceeded => .lit 0
  | some .evmReceive => .lit 0
  | some (.evmStoreStaticU64 _ value) => value
  | some (.mapSetU64 _ _ v) => v
  | some (.mapSetAddr _ _ _ _ v) => v
  | some (.mapSetPair _ _ _ _ _ _ _ v) => v
  | some (.mapSetAddr256 _ _ _ _ v0 _ _ _) => v0
  | some (.mapSetPair256 _ _ _ _ _ _ _ v0 _ _ _) => v0
  | some (.evmTokenTransfer _ _ _ _ _ _ v) => v
  | some (.evmTokenTransfer256 _ _ _ _ _ _ a0 _ _ _) => a0
  | some (.evmTokenApprove256 _ _ _ _ _ _ a0 _ _ _) => a0
  | some (.evmTokenTransferFrom256 _ _ _ _ _ _ _ _ _ a0 _ _ _) => a0
  | some (.evmWethDeposit256 _ _ _ a0 _ _ _) => a0
  | some (.evmWethWithdraw256 _ _ _ a0 _ _ _) => a0
  | some (.evmSwapExact2 _ _ _ _ _ _ _ _ _ i0 _ _ _ _ _ _ _) => i0
  | some (.evmSwapExact3 _ _ _ _ _ _ _ _ _ _ _ _ i0 _ _ _ _ _ _ _) => i0
  | some (.evmPermit _ _ _ _ _ _ v0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => v0
  | some (.evmTokenPermit _ _ _ _ _ _ _ _ _ v0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) => v0
  | _ => .arg 0

private def decodeEvmEffect (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  let writes := collectEvmEffectOps env e
  if writes.size ≥ 1 then
    some (writes.push (.returnU64 ((findOkRet env e).getD (retOfEvmOps writes))))
  else
    collectEvmQueryOps env e

/-- Flatten one logical bounded byte value into `length, byte₀ … byteₙ₋₁`. Constructors already
carry literal leaves; a parameter or local root is projected so the target input binder can later
rewrite it to canonical scalar locals. -/
private def normalizeBoundedParameterFrame (capacity : Nat) (values : Array Ops.Val) :
    Array Ops.Val := Id.run do
  unless values.size == capacity + 1 do return values
  let .field _ "length" := values[0]! | return values
  let mut normalized : Array Ops.Val := #[values[0]!]
  for position in [0:capacity] do
    match values[position + 1]! with
    | .indexGet base "values" (.local index) length elementOffset =>
        unless index == position && (length == 0 || length == capacity) &&
            elementOffset == 0 do
          return values
        normalized := normalized.push
          (.indexGet base "values" (.lit (UInt64.ofNat position)) capacity 0)
    | _ => return values
  return normalized

private def boundedStorageFrame? (env : Environment) (capacity : Nat) (e : Expr) :
    Option (Array Ops.Val) := do
  let e := substLets 32 (strip (unfoldUserHelpers env 8 e))
  if let some values := asBoundedCtorFields env e then
    if values.size == capacity + 1 then
      return normalizeBoundedParameterFrame capacity values
    else none
  let root ← val env e
  let mut values : Array Ops.Val := #[.field root "length"]
  for index in [0:capacity] do
    values := values.push (.indexGet root "values" (.lit (UInt64.ofNat index)) capacity 0)
  return values

private def nearAccountIdFrame? (env : Environment) (e : Expr) : Option (Array Ops.Val) := do
  let length ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.length) e)
  let w0 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w0) e)
  let w1 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w1) e)
  let w2 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w2) e)
  let w3 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w3) e)
  let w4 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w4) e)
  let w5 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w5) e)
  let w6 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w6) e)
  let w7 ← val env (mkApp (mkConst ``ProofForge.Wasm.Near.Runtime.AccountId.w7) e)
  return #[length, w0, w1, w2, w3, w4, w5, w6, w7]

/-- Preserve source lets that sequence NEAR effects before generic zeta reduction. Otherwise an
ignored UInt64 sequencing result would erase the host/log or guest-memory mutation before
`decodeExpr` can turn it into a typed effect. -/
partial def mentionsNearEffect (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      e.getUsedConstantsAsSet.toList.any fun name =>
        name == ``ProofForge.Wasm.Near.Runtime.logUtf8 ||
        name == ``ProofForge.Wasm.Near.Runtime.logUtf8Bounded ||
        name == ``ProofForge.Wasm.Near.Runtime.nep297StringData ||
        name == ``ProofForge.Wasm.Near.Runtime.nep141FtMint ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallDetached ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAndThenReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseTransferDetached ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseTransferReturned ||
        name == ``ProofForge.Wasm.Near.Runtime.promiseResultRead ||
        name == ``ProofForge.Wasm.Near.Runtime.transientBuffer64Begin ||
        name == ``ProofForge.Wasm.Near.Runtime.transientBuffer64Set ||
        name == ``ProofForge.Wasm.Near.Runtime.transientBuffer64Finish ||
        name == ``ProofForge.Wasm.Near.Runtime.storageRead ||
        name == ``ProofForge.Wasm.Near.Runtime.storageWrite ||
        name == ``ProofForge.Wasm.Near.Runtime.storageRemove ||
        name == ``ProofForge.Wasm.Near.Runtime.storageHasKey ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callDetached ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.callAndThenReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.transferDetached ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.transferReturned ||
        name == ``ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.read ||
        name == ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.begin ||
        name == ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.set ||
        name == ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.finish ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.read ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.write ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.remove ||
        name == ``ProofForge.Wasm.Near.Sdk.Storage.ResultBuffer.hasKey ||
        (Attr.isInline env name &&
          match env.find? name with
          | some (.defnInfo info) => mentionsNearEffect env fuel info.value
          | _ => false)

/-- NEAR logging and invocation-memory mutations stay effects so CFG rewrites cannot duplicate,
discard, or reorder them as pure scalar expressions. Buffer capacities remain compile-time. -/
private def decodeNearEffect (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  let rec find (fuel : Nat) (e : Expr) : Option Ops.Op :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``ProofForge.Wasm.Near.Runtime.logUtf8 then
        (e.getAppArgs.back? >>= staticString? env 64).map Ops.Op.nearLogUtf8
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.logUtf8Bounded &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 2]! with
        | some capacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
              (boundedStorageFrame? env capacity args[args.size - 1]!).map fun message =>
                .nearLogUtf8Bounded capacity message
            else none
        | none => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep297StringData &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 5]!,
            staticString? env 64 args[args.size - 4]!,
            staticString? env 64 args[args.size - 3]!,
            staticString? env 64 args[args.size - 2]! with
        | some capacity, some standard, some version, some event =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
              (boundedStorageFrame? env capacity args[args.size - 1]!).map fun data =>
                .nearNep297StringData standard version event capacity data
            else none
        | _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.nep141FtMint &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        let owner := args[args.size - 2]!
        let amount := args[args.size - 1]!
        match nearAccountIdFrame? env owner,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some owner, some amountLo, some amountHi =>
            some (.nearNep141FtMint owner amountLo amountHi)
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferReturned) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        let amount := args[args.size - 1]!
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.transferReturned
        match staticString? env 64 args[args.size - 2]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) amount),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) amount) with
        | some receiver, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver then
              some (if returned then
                .nearPromiseTransferReturned receiver amountLo amountHi
              else
                .nearPromiseTransferDetached receiver amountLo amountHi)
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferReturned) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseTransferReturned
        match staticString? env 64 args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some receiver, some amountLo, some amountHi =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver then
              some (if returned then
                .nearPromiseTransferReturned receiver amountLo amountHi
              else
                .nearPromiseTransferDetached receiver amountLo amountHi)
            else none
        | _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callThenReturned &&
          e.getAppArgs.size ≥ 11 then
        let args := e.getAppArgs
        let childDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 11]!,
            staticNatVal? env args[args.size - 10]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) childDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) childDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some childArgsCapacity, some callbackArgsCapacity,
            some receiver, some childMethod, some callbackMethod,
            some childDepositLo, some childDepositHi, some childGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid childMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid childArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env childArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some childArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallThenReturned receiver childMethod callbackMethod
                    childArgsCapacity callbackArgsCapacity childArguments callbackArguments
                    childDepositLo childDepositHi childGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callAndThenReturned &&
          e.getAppArgs.size ≥ 17 then
        let args := e.getAppArgs
        let leftDeposit := args[args.size - 11]!
        let rightDeposit := args[args.size - 6]!
        let callbackDeposit := args[args.size - 2]!
        match staticNatVal? env args[args.size - 17]!,
            staticNatVal? env args[args.size - 16]!,
            staticNatVal? env args[args.size - 15]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            staticString? env 64 args[args.size - 9]!,
            staticString? env 64 args[args.size - 8]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) leftDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) leftDeposit),
            val env args[args.size - 10]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) rightDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) rightDeposit),
            val env args[args.size - 5]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) callbackDeposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) callbackDeposit),
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some rightArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some rightReceiver, some rightMethod,
            some callbackMethod, some leftDepositLo, some leftDepositHi, some leftGas,
            some rightDepositLo, some rightDepositHi, some rightGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 7]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 3]! with
              | some leftArguments, some rightArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAndThenReturned
                    leftReceiver leftMethod rightReceiver rightMethod callbackMethod
                    leftArgsCapacity rightArgsCapacity callbackArgsCapacity
                    leftArguments rightArguments callbackArguments
                    leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callReturned) &&
          e.getAppArgs.size ≥ 6 then
        let args := e.getAppArgs
        let deposit := args[args.size - 2]!
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.callReturned
        match staticNatVal? env args[args.size - 6]!,
            staticString? env 64 args[args.size - 5]!,
            staticString? env 64 args[args.size - 4]!,
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w0) deposit),
            val env (mkApp (mkConst ``ProofForge.Core.Value.UInt128.w1) deposit),
            val env args[args.size - 1]! with
        | some argsCapacity, some receiver, some method, some depositLo, some depositHi, some gas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid method &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid argsCapacity then
              (boundedStorageFrame? env argsCapacity args[args.size - 3]!).map fun arguments =>
                if returned then
                  .nearPromiseFunctionCallReturned receiver method argsCapacity arguments
                    depositLo depositHi gas
                else
                  .nearPromiseFunctionCallDetached receiver method argsCapacity arguments
                    depositLo depositHi gas
            else none
        | _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallDetached ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned) &&
          e.getAppArgs.size ≥ 7 then
        let args := e.getAppArgs
        let returned := isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallReturned
        match staticNatVal? env args[args.size - 7]!,
            staticString? env 64 args[args.size - 6]!,
            staticString? env 64 args[args.size - 5]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some argsCapacity, some receiver, some method, some depositLo, some depositHi, some gas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid method &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid argsCapacity then
              (boundedStorageFrame? env argsCapacity args[args.size - 4]!).map fun arguments =>
                if returned then
                  .nearPromiseFunctionCallReturned receiver method argsCapacity arguments
                    depositLo depositHi gas
                else
                  .nearPromiseFunctionCallDetached receiver method argsCapacity arguments
                    depositLo depositHi gas
            else none
        | _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallThenReturned &&
          e.getAppArgs.size ≥ 13 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 13]!,
            staticNatVal? env args[args.size - 12]!,
            staticString? env 64 args[args.size - 11]!,
            staticString? env 64 args[args.size - 10]!,
            staticString? env 64 args[args.size - 9]!,
            val env args[args.size - 6]!, val env args[args.size - 5]!,
            val env args[args.size - 4]!, val env args[args.size - 3]!,
            val env args[args.size - 2]!, val env args[args.size - 1]! with
        | some childArgsCapacity, some callbackArgsCapacity,
            some receiver, some childMethod, some callbackMethod,
            some childDepositLo, some childDepositHi, some childGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid receiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid childMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid childArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env childArgsCapacity args[args.size - 8]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 7]! with
              | some childArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallThenReturned receiver childMethod callbackMethod
                    childArgsCapacity callbackArgsCapacity childArguments callbackArguments
                    childDepositLo childDepositHi childGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseFunctionCallAndThenReturned &&
          e.getAppArgs.size ≥ 20 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 20]!,
            staticNatVal? env args[args.size - 19]!,
            staticNatVal? env args[args.size - 18]!,
            staticString? env 64 args[args.size - 17]!,
            staticString? env 64 args[args.size - 16]!,
            staticString? env 64 args[args.size - 15]!,
            staticString? env 64 args[args.size - 14]!,
            staticString? env 64 args[args.size - 13]!,
            val env args[args.size - 9]!, val env args[args.size - 8]!,
            val env args[args.size - 7]!, val env args[args.size - 6]!,
            val env args[args.size - 5]!, val env args[args.size - 4]!,
            val env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some leftArgsCapacity, some rightArgsCapacity, some callbackArgsCapacity,
            some leftReceiver, some leftMethod, some rightReceiver, some rightMethod,
            some callbackMethod, some leftDepositLo, some leftDepositHi, some leftGas,
            some rightDepositLo, some rightDepositHi, some rightGas,
            some callbackDepositLo, some callbackDepositHi, some callbackGas =>
            if ProofForge.Wasm.Near.Codec.accountIdLiteralValid leftReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid leftMethod &&
                ProofForge.Wasm.Near.Codec.accountIdLiteralValid rightReceiver &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid rightMethod &&
                ProofForge.Wasm.Near.Codec.promiseMethodLiteralValid callbackMethod &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid leftArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid rightArgsCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid callbackArgsCapacity then
              match boundedStorageFrame? env leftArgsCapacity args[args.size - 12]!,
                  boundedStorageFrame? env rightArgsCapacity args[args.size - 11]!,
                  boundedStorageFrame? env callbackArgsCapacity args[args.size - 10]! with
              | some leftArguments, some rightArguments, some callbackArguments =>
                  some (.nearPromiseFunctionCallAndThenReturned
                    leftReceiver leftMethod rightReceiver rightMethod callbackMethod
                    leftArgsCapacity rightArgsCapacity callbackArgsCapacity
                    leftArguments rightArguments callbackArguments
                    leftDepositLo leftDepositHi leftGas rightDepositLo rightDepositHi rightGas
                    callbackDepositLo callbackDepositHi callbackGas)
              | _, _, _ => none
            else none
        | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.promiseResultRead ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Promises.ResultBuffer.read) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 2]!, val env args[args.size - 1]! with
        | some capacity, some index =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid capacity then
              some (.nearPromiseResultRead capacity index)
            else none
        | _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Begin ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.begin) &&
          e.getAppArgs.size ≥ 1 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 1]! with
        | some capacity =>
            if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity then
              some (.nearTransientBuffer64Begin capacity)
            else none
        | none => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Set ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.set) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!, val env args[args.size - 2]!,
            val env args[args.size - 1]! with
        | some capacity, some index, some value =>
            if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity then
              some (.nearTransientBuffer64Set capacity index value)
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.transientBuffer64Finish ||
          isConstNamed e ``ProofForge.Wasm.Near.Sdk.Transient.Buffer64.finish) &&
          e.getAppArgs.size ≥ 1 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 1]! with
        | some capacity =>
            if ProofForge.Wasm.Near.Memory.buffer64CapacityValid capacity then
              some (.nearTransientBuffer64Finish capacity)
            else none
        | none => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageRead &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!,
            staticNatVal? env args[args.size - 2]! with
        | some resultCapacity, some keyCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid keyCapacity then
              (boundedStorageFrame? env keyCapacity args[args.size - 1]!).map fun key =>
                .nearStorageRead resultCapacity keyCapacity key
            else none
        | _, _ => none
      else if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageWrite &&
          e.getAppArgs.size ≥ 5 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 5]!,
            staticNatVal? env args[args.size - 4]!,
            staticNatVal? env args[args.size - 3]! with
        | some resultCapacity, some keyCapacity, some valueCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid keyCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid valueCapacity then
              match boundedStorageFrame? env keyCapacity args[args.size - 2]!,
                  boundedStorageFrame? env valueCapacity args[args.size - 1]! with
              | some key, some value =>
                  some (.nearStorageWrite resultCapacity keyCapacity valueCapacity key value)
              | _, _ => none
            else none
        | _, _, _ => none
      else if (isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageRemove ||
          isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageHasKey) &&
          e.getAppArgs.size ≥ 3 then
        let args := e.getAppArgs
        match staticNatVal? env args[args.size - 3]!,
            staticNatVal? env args[args.size - 2]! with
        | some resultCapacity, some keyCapacity =>
            if ProofForge.Wasm.Near.Codec.storageCapacityValid resultCapacity &&
                ProofForge.Wasm.Near.Codec.storageCapacityValid keyCapacity then
              (boundedStorageFrame? env keyCapacity args[args.size - 1]!).map fun key =>
                if isConstNamed e ``ProofForge.Wasm.Near.Runtime.storageRemove then
                  .nearStorageRemove resultCapacity keyCapacity key
                else
                  .nearStorageHasKey resultCapacity keyCapacity key
            else none
        | _, _ => none
      else
        match unfoldUserHelper env e with
        | some (_, unfolded) => find fuel' unfolded
        | none => none
  match find 8 e with
  | some effect => some #[effect, .returnU64 (.lit 0)]
  | none => none

/-- A vector root is not a scalar slot. Mixed static/dynamic writeback can see an inline
helper's vector parameter as a changed structure field; discard that synthetic root store. -/
private def dropVectorRootStores (dynamic stores : Array Ops.Op) : Array Ops.Op :=
  let vectorNames := dynamic.filterMap fun
    | .indexSetLeaf name _ _ _ _ | .indexSet name _ _ _ _ => some name
    | _ => none
  stores.filter fun
    | .storeField name _ => !vectorNames.contains name
    | _ => true

private def qualifyStatePrefix (statePrefix name : String) : String :=
  if statePrefix.isEmpty || name == statePrefix || name.startsWith (statePrefix ++ "_") then name
  else s!"{statePrefix}_{name}"

private def qualifyDynamicStateOp (statePrefix : String) : Ops.Op → Ops.Op
  | .indexSetLeaf name index value len leaf =>
      .indexSetLeaf (qualifyStatePrefix statePrefix name) index value len leaf
  | .indexSet name index value len elemOff =>
      .indexSet (qualifyStatePrefix statePrefix name) index value len elemOff
  | op => op

private def qualifyNestedStateName (statePrefix : String) (fieldNames : Array String)
    (name : String) : String :=
  if statePrefix.isEmpty || name == statePrefix || name.startsWith (statePrefix ++ "_") then name
  else if fieldNames.any fun field => name == field || name.startsWith (field ++ "_") then
    s!"{statePrefix}_{name}"
  else name

private partial def qualifyNestedStateVal (statePrefix : String) (fieldNames : Array String) :
    Ops.Val → Ops.Val
  | .arg i => .arg i
  | .local i => .local i
  | .field base name =>
      .field (qualifyNestedStateVal statePrefix fieldNames base)
        (qualifyNestedStateName statePrefix fieldNames name)
  | .lit value => .lit value
  | .bitAnd lhs rhs => .bitAnd (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .bitOr lhs rhs => .bitOr (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .bitXor lhs rhs => .bitXor (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .bitNot value => .bitNot (qualifyNestedStateVal statePrefix fieldNames value)
  | .shiftL lhs rhs => .shiftL (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .shiftR lhs rhs => .shiftR (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .indexGet base name index len elemOff =>
      .indexGet (qualifyNestedStateVal statePrefix fieldNames base)
        (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames index) len elemOff
  | .loopIx => .loopIx
  | .select cmp lhs rhs thn els =>
      .select cmp (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
        (qualifyNestedStateVal statePrefix fieldNames thn)
        (qualifyNestedStateVal statePrefix fieldNames els)
  | .addU64 lhs rhs => .addU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .subU64 lhs rhs => .subU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .mulU64 lhs rhs => .mulU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .divU64 lhs rhs => .divU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .modU64 lhs rhs => .modU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
      (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .ext kind operands =>
      .ext kind (operands.map (qualifyNestedStateVal statePrefix fieldNames))

private partial def qualifyNestedStateOp (statePrefix : String) (fieldNames : Array String) :
    Ops.Op → Ops.Op
  | .letLocal i value => .letLocal i (qualifyNestedStateVal statePrefix fieldNames value)
  | .joinLocal i => .joinLocal i
  | .setLocal i value => .setLocal i (qualifyNestedStateVal statePrefix fieldNames value)
  | .checkedAddU64 lhs rhs =>
      .checkedAddU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedSubU64 lhs rhs =>
      .checkedSubU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedMulU64 lhs rhs =>
      .checkedMulU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedDivU64 lhs rhs =>
      .checkedDivU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .checkedModU64 lhs rhs =>
      .checkedModU64 (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
  | .ite cmp lhs rhs thn els =>
      .ite cmp (qualifyNestedStateVal statePrefix fieldNames lhs)
        (qualifyNestedStateVal statePrefix fieldNames rhs)
        (thn.map (qualifyNestedStateOp statePrefix fieldNames))
        (els.map (qualifyNestedStateOp statePrefix fieldNames))
  | .forAccum n value resultLocal =>
      .forAccum n (qualifyNestedStateVal statePrefix fieldNames value) resultLocal
  | .forBody n body => .forBody n (body.map (qualifyNestedStateOp statePrefix fieldNames))
  | .indexSetLeaf name index value len leaf =>
      .indexSetLeaf (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames index)
        (qualifyNestedStateVal statePrefix fieldNames value) len leaf
  | .indexSet name index value len elemOff =>
      .indexSet (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames index)
        (qualifyNestedStateVal statePrefix fieldNames value) len elemOff
  | .storeField name value =>
      .storeField (qualifyNestedStateName statePrefix fieldNames name)
        (qualifyNestedStateVal statePrefix fieldNames value)
  | .okState value => .okState (qualifyNestedStateVal statePrefix fieldNames value)
  | .returnU64 value => .returnU64 (qualifyNestedStateVal statePrefix fieldNames value)
  | .returnState value => .returnState (qualifyNestedStateVal statePrefix fieldNames value)
  | op => op

/-- A nested state helper's success value is consumed by the enclosing record update. Its writes
remain observable, but its state terminal must not be interpreted as a root-schema commit. -/
private partial def dropNestedStateTerminals (ops : Array Ops.Op) : Array Ops.Op :=
  ops.filterMap fun op =>
    match op with
    | .okState _ | .returnState _ => none
    | .ite cmp lhs rhs thn els =>
        some (.ite cmp lhs rhs (dropNestedStateTerminals thn) (dropNestedStateTerminals els))
    | .forBody n body => some (.forBody n (dropNestedStateTerminals body))
    | op => some op

/-- Once a nested transition has been lowered, the enclosing record's projection of that
structure is inheritance, not a scalar write. Keep later scalar/vector continuation effects while
removing only the impossible whole-structure store. -/
private partial def dropNestedRootStores (statePrefix : String)
    (ops : Array Ops.Op) : Array Ops.Op :=
  ops.filterMap fun op =>
    match op with
    | .storeField name _ => if name == statePrefix then none else some op
    | .ite cmp lhs rhs thn els =>
        some (.ite cmp lhs rhs (dropNestedRootStores statePrefix thn)
          (dropNestedRootStores statePrefix els))
    | .forBody n body => some (.forBody n (dropNestedRootStores statePrefix body))
    | op => some op

/-- Zeta-reduce syntax-only aliases at the head of an expression.
Compiler intrinsics and loops stay explicit so later effect/control decoding still sees them. -/
def zetaPureHeadLets (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE _ _ value body _ =>
        let effectful :=
          (findInvoke env 16 value).isSome || mentionsSvmEffect env 16 value ||
            (decodeNearEffect env value).isSome || (decodeEvmEffect env value).isSome ||
            (findForIn env value).isSome || (findForBodyExpr env value).isSome
        -- A scalar captured before a CPI must remain a local: substituting its state-field read
        -- through the call can move that read after a later state write.
        let bodyHasInvoke := (findInvoke env 16 body).isSome
        let directAlias := match strip body with | .bvar 0 => true | _ => false
        if effectful || bodyHasInvoke || (!directAlias && !isIteExpr body) then e
        else zetaPureHeadLets env fuel' (body.instantiate1 value)
    | e => e

private def findYieldPayload (e : Expr) : Option Expr :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``ForInStep.yield || endsWith e ".yield" then
        if e.getAppArgs.size ≥ 1 then
          -- The payload remains under the yielded state/control binder. Keep accumulator 0,
          -- and lower the loop index plus outer method arguments back to callback scope.
          some (e.getAppArgs[e.getAppArgs.size - 1]!.lowerLooseBVars 1 1)
        else none
      else
        match e with
        | .letE _ _ value body _ => go fuel' body <|> go fuel' value
        -- Yield can sit under a dependent branch proof lambda. Dropping that binder without
        -- lowering would turn the loop index and outer arguments into unrelated `.arg`s.
        | .lam _ _ body _ => go fuel' (body.lowerLooseBVars 1 1)
        | _ => e.getAppArgs.findSome? (go fuel')
  go 32 e

/--
Lean composes consecutive mutable-state assignments as a record update whose unchanged
fields project from the previous expression. When that base is a `pf_inline` State helper,
preserve the helper transition before lowering the outer update. This is target-neutral
structured-state normalization; backends only see the resulting stores.
-/
private def findProjectedInlineBase (env : Environment) (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    let args := e.getAppArgs
    let projectedBase? :=
      match e.getAppFn.constName? with
      | some name =>
        match env.getProjectionFnInfo? name with
        | some _ =>
          if h : args.size > 0 then
            let base := args[args.size - 1]
            match unfoldUserHelper env base with
            | some (helper, _) =>
              if inlineHelperPreservesUserType env helper then some base else none
            | none => none
          else none
        | none => none
      | none => none
    projectedBase? <|> args.findSome? (findProjectedInlineBase env fuel')

/-- Collect the inline State expressions inherited through record projections. Once such an
expression has been lowered, later wrappers may still contain several projections of the same
result; retaining every applied ancestor prevents those transitions from being emitted again. -/
private def projectedInlineBases (env : Environment) (fuel : Nat) (e : Expr) : Array Expr :=
  let rec go (fuel : Nat) (e : Expr) (acc : Array Expr) : Array Expr :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let e := strip e
      let args := e.getAppArgs
      let acc :=
        match e.getAppFn.constName? with
        | some name =>
          match env.getProjectionFnInfo? name with
          | some _ =>
            match args[args.size - 1]? with
            | some base =>
              match unfoldUserHelper env base with
              | some (helper, _) =>
                if inlineHelperPreservesUserType env helper && !acc.contains base then acc.push base
                else acc
              | none => acc
            | none => acc
          | none => acc
        | none => acc
      args.foldl (init := acc) fun acc arg => go fuel' arg acc
  go fuel e #[]

private def addAppliedBases (current extra : Array Expr) : Array Expr :=
  extra.foldl (init := current) fun result base =>
    if result.contains base then result else result.push base

/-- Find the mutable source underneath a composed State expression. -/
private def inlineStateSource (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      inlineStateSource env fuel' (body.instantiate1 value)
    else if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 2 then
      let args := e.getAppArgs
      let branch := args[args.size - 2]!
      let branch :=
        match strip branch with
        | .lam _ _ body _ => body.lowerLooseBVars 1 1
        | branch => branch
      inlineStateSource env fuel' branch
    else if (unfoldUserHelper env e).isSome then
      let args := e.getAppArgs
      if h : args.size > 0 then inlineStateSource env fuel' args[0] else e
    else
      let structureSource? :=
        match e.getAppFn.constName?, userCtorFields env e with
        | some ctor, some fields => Id.run do
          for h : i in [:fields.size] do
            let field := fields[i]
            if let some projection := (strip field).getAppFn.constName? then
              if let some info := env.getProjectionFnInfo? projection then
                let args := (strip field).getAppArgs
                if info.ctorName == ctor && info.i == i then
                  if h : args.size > 0 then return some args[args.size - 1]
          return none
        | _, _ => none
      let directProjectionBase? :=
        match e.getAppFn.constName? with
        | some name =>
          if !isUserName env name then none else match env.getProjectionFnInfo? name with
          | some _ =>
            let args := e.getAppArgs
            if h : args.size > 0 then some args[args.size - 1] else none
          | none => none
        | none => none
      match structureSource? <|> directProjectionBase? with
      | some base => inlineStateSource env fuel' base
      | none => e

private def isStateTransitionValue (env : Environment) : Nat → Bool → Expr → Bool
  | 0, _, _ => false
  | fuel + 1, underControl, e =>
      let e := strip e
      match e with
      | .letE _ _ value body _ =>
          isStateTransitionValue env fuel underControl (body.instantiate1 value)
      | _ =>
        if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 2 then
          let args := e.getAppArgs
          let peelProofLam (branch : Expr) : Expr :=
            match strip branch with
            | .lam _ _ body _ => body.lowerLooseBVars 1 1
            | branch => branch
          isStateTransitionValue env fuel true (peelProofLam args[args.size - 2]!) ||
            isStateTransitionValue env fuel true (peelProofLam args[args.size - 1]!)
        else
          match unfoldUserHelper env e with
          | some (name, _) => inlineHelperPreservesUserType env name
          | none =>
            match e.getAppFn.constName? with
            | some name =>
              match env.find? name with
              | some (.ctorInfo ctor) =>
                  underControl && isUserType env ctor.induct && isStructure env ctor.induct
              | _ => false
            | none => false

/-- Sequential decoding is needed when substitution would duplicate dynamic structure writes or
erase a conditional State constructor behind later projections. Straight-line scalar-only helpers
retain the established zeta-normalized Core shape. Follow marked helpers recursively so wrappers
around `Vector.set` remain generic. -/
private def stateTransitionNeedsSequencing (env : Environment) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
      let e := strip e
      if isIteExpr e || !(collectIndexSets env e).isEmpty then true
      else
        match e with
        | .letE _ _ value body _ =>
            stateTransitionNeedsSequencing env fuel value ||
              stateTransitionNeedsSequencing env fuel body
        | .lam _ _ body _ => stateTransitionNeedsSequencing env fuel body
        | _ =>
          match unfoldUserHelper env e with
          | some (_, unfolded) => stateTransitionNeedsSequencing env fuel unfolded
          | none => e.getAppArgs.any (stateTransitionNeedsSequencing env fuel)

/-- Follow structure-preserving helpers to their source value without erasing a nested projection.
For a helper over `s.askBook`, the root-state source is `s` but the type-correct substitution source
is `s.askBook`; sequential nested lowering needs both facts. -/
private def inlineTypedStateSource (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    let e := strip e
    if let .letE _ _ value body _ := e then
      inlineTypedStateSource env fuel' (body.instantiate1 value)
    else if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 2 then
      let args := e.getAppArgs
      let branch := args[args.size - 2]!
      let branch :=
        match strip branch with
        | .lam _ _ body _ => body.lowerLooseBVars 1 1
        | branch => branch
      inlineTypedStateSource env fuel' branch
    else if (unfoldUserHelper env e).isSome then
      let args := e.getAppArgs
      if h : args.size > 0 then inlineTypedStateSource env fuel' args[0] else e
    else
      let structureSource? :=
        match e.getAppFn.constName?, userCtorFields env e with
        | some ctor, some fields => Id.run do
          for h : i in [:fields.size] do
            let field := fields[i]
            if let some projection := (strip field).getAppFn.constName? then
              if let some info := env.getProjectionFnInfo? projection then
                let args := (strip field).getAppArgs
                if info.ctorName == ctor && info.i == i then
                  if h : args.size > 0 then return some args[args.size - 1]
          return none
        | _, _ => none
      match structureSource? with
      | some source => inlineTypedStateSource env fuel' source
      | none => e

/--
A let-bound user structure rooted at a method state argument is a sequential State transition,
not a pure value alias. Decoding it before the continuation avoids substituting an ever-growing
record expression through every later projection. Nested structures have a separate typed-source
path below; this boundary owns only transitions of the declared root state type.
-/
private def sequentialStateSource? (env : Environment) (type value : Expr)
    (stateType? : Option Name := none) : Option Expr := do
  let typeName ← type.consumeMData.getAppFn.constName?
  if !isUserType env typeName then none else
  if stateType?.any (· != typeName) then none else
  let value := strip value
  let source := inlineStateSource env 64 value
  if source == value then none else
  let directRecordUpdate :=
    match value.getAppFn.constName?, userCtorFields env value with
    | some ctor, some _ =>
        match env.find? ctor with
        | some (.ctorInfo info) => info.induct == typeName
        | _ => false
    | _, _ => false
  if !directRecordUpdate && !isStateTransitionValue env 64 false value then none else
  if !stateTransitionNeedsSequencing env 64 value then none else
  match strip source with
  | .bvar _ => some source
  | source =>
      if isConstNamed source ``methodArgRef || isConstNamed source ``localRef then
        some source
      else none

private structure NestedStateTransition where
  transition : Expr
  typedSource : Expr
  nestedType : Name
  fieldPrefix : String
  /-- Composed outer state, its mutable source, and the outer state type. -/
  outerOwner? : Option (Expr × Expr × Name) := none

private structure NestedStateNormalization where
  prior : Array Ops.Op
  transition : Expr
  typedSource : Expr
  outerState : Expr

/-- Find a structure-valued field transition embedded directly in an outer record update. Lean's
zeta reduction commonly turns `let book := update s.book; { s with book }` into exactly this shape.
Lowering the nested transition first prevents every leaf projection from independently expanding
the same helper, while retaining a target-neutral flattened field prefix. -/
private def nestedSequentialTransition? (env : Environment) (state : Expr)
    (statePrefix : String) : Option NestedStateTransition := Id.run do
  let state := strip state
  let some fields := userCtorFields env state | return none
  let some ctor := state.getAppFn.constName? | return none
  let some (.ctorInfo info) := env.find? ctor | return none
  let names := getStructureFields env info.induct
  for h : i in [:fields.size] do
    if i < names.size then
      let some fieldType := fieldTypeExpr env info.induct names[i]! | continue
      let some fieldTypeName := fieldType.consumeMData.getAppFn.constName? | continue
      if fieldTypeName != info.induct && isUserType env fieldTypeName &&
          isStructure env fieldTypeName then
        let transition := strip fields[i]
        if isStateTransitionValue env 64 false transition &&
            stateTransitionNeedsSequencing env 64 transition then
          let typedSource := inlineTypedStateSource env 64 transition
          if typedSource != transition then
            let fieldName := names[i]!.toString
            let pathPrefix :=
              if statePrefix.isEmpty then fieldName else s!"{statePrefix}_{fieldName}"
            let outerOwner? :=
              match typedSource.getAppFn.constName? with
              | some projection =>
                match env.getProjectionFnInfo? projection with
                | some projectionInfo =>
                  let args := typedSource.getAppArgs
                  if h : args.size > 0 then
                    let owner := args[args.size - 1]
                    let root := inlineStateSource env 64 owner
                    if owner == root then none else
                    match env.find? projectionInfo.ctorName with
                    | some (.ctorInfo ownerCtor) => some (owner, root, ownerCtor.induct)
                    | _ => none
                  else none
                | none => none
              | none => none
            return some {
              transition := transition
              typedSource := typedSource
              nestedType := fieldTypeName
              fieldPrefix := pathPrefix
              outerOwner? := outerOwner?
            }
  return none

private def stateNamesAlias (left right : String) : Bool :=
  left == right || left.startsWith (right ++ "_") || right.startsWith (left ++ "_")

private partial def valReadsWritten (written : Array String) : Ops.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base name => written.any (stateNamesAlias name) || valReadsWritten written base
  | .indexGet base name index _ _ =>
      written.any (stateNamesAlias name) ||
        valReadsWritten written base || valReadsWritten written index
  | .bitNot value => valReadsWritten written value
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valReadsWritten written lhs || valReadsWritten written rhs
  | .select _ lhs rhs thn els =>
      valReadsWritten written lhs || valReadsWritten written rhs ||
        valReadsWritten written thn || valReadsWritten written els
  | .ext _ operands => operands.any (valReadsWritten written)

/-- A target query whose observation can change after an EVM storage write or external call.
The component effect summary, rather than a container-specific pattern, owns this distinction. -/
private partial def valReadsMutableEvmState : Ops.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => valReadsMutableEvmState base
  | .indexGet base _ index _ _ =>
      valReadsMutableEvmState base || valReadsMutableEvmState index
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valReadsMutableEvmState lhs || valReadsMutableEvmState rhs
  | .select _ lhs rhs thn els =>
      valReadsMutableEvmState lhs || valReadsMutableEvmState rhs ||
        valReadsMutableEvmState thn || valReadsMutableEvmState els
  | .ext (.evm (.component query)) operands =>
      let effects := query.effects
      effects.readsStorage || effects.externalCall || operands.any valReadsMutableEvmState
  | .ext _ operands => operands.any valReadsMutableEvmState

/-- Whether an EVM effect can invalidate a mutable target query that appears in a later ordinary
State store. Logs and pure reads do not force snapshots; storage writes and external calls do. -/
private partial def evmEffectsInvalidateQueries (ops : Array Ops.Op) : Bool :=
  ops.any fun op =>
    match op with
    | .ext (.evm (.component call)) =>
        let effects := call.effects
        effects.writesStorage || effects.externalCall
    | .ite _ _ _ thn els =>
        evmEffectsInvalidateQueries thn || evmEffectsInvalidateQueries els
    | .forBody _ body => evmEffectsInvalidateQueries body
    | _ => false

private structure SnapshotState where
  written : Array String := #[]
  bindings : Array (Ops.Val × Nat) := #[]
  prelude : Array Ops.Op := #[]

private def SnapshotState.snapshot (base : Nat) (state : SnapshotState)
    (value : Ops.Val) : SnapshotState × Ops.Val :=
  match state.bindings.find? (·.1 == value) with
  | some (_, localIx) => (state, .local localIx)
  | none =>
    let localIx := base + state.bindings.size
    ({ state with
        bindings := state.bindings.push (value, localIx)
        prelude := state.prelude.push (.letLocal localIx value) },
      .local localIx)

/-- Lower one simultaneous State update while collecting every required pre-write snapshot.
`snapshotMutableEvm` additionally freezes target queries before an effect head that can invalidate
them; this keeps that target sequencing concern out of SDK containers and ordinary State lowering. -/
private def snapshotStateOps (base : Nat) (ops : Array Ops.Op)
    (snapshotMutableEvm : Bool := false) : SnapshotState × Array Ops.Op := Id.run do
  let mut state : SnapshotState := {}
  let mut body : Array Ops.Op := #[]
  let needsSnapshot (state : SnapshotState) (value : Ops.Val) : Bool :=
    valReadsWritten state.written value ||
      (snapshotMutableEvm && valReadsMutableEvmState value)
  for op in ops do
    match op with
    | .indexSetLeaf name index value len leaf =>
      let (next, index) :=
        if needsSnapshot state index then state.snapshot base index else (state, index)
      state := next
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := { next with written := next.written.push name }
      body := body.push (.indexSetLeaf name index value len leaf)
    | .indexSet name index value len offset =>
      let (next, index) :=
        if needsSnapshot state index then state.snapshot base index else (state, index)
      state := next
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := { next with written := next.written.push name }
      body := body.push (.indexSet name index value len offset)
    | .storeField name value =>
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := { next with written := next.written.push name }
      body := body.push (.storeField name value)
    | .okState value =>
      let (next, value) :=
        if needsSnapshot state value then state.snapshot base value else (state, value)
      state := next
      body := body.push (.okState value)
    | op => body := body.push op
  return (state, body)

/--
Lean record-update RHS expressions all observe the pre-update value. Keep flat write Ops, but
snapshot only expressions that a preceding write in this same source update would invalidate.
-/
private def snapshotStateUpdate (base : Nat) (ops : Array Ops.Op) : Array Ops.Op :=
  let (state, body) := snapshotStateOps base ops
  state.prelude ++ body

private def decodeYieldState (env : Environment) (fuel localDepth : Nat) (state : Expr)
    (appliedBases : Array Expr := #[]) (stateType? : Option Name := none)
    (statePrefix : String := "") (deepScalars : Bool := false) :
    Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: inline state depth"
  | fuel' + 1 =>
    let raw := strip state
    let sequential? : Option (Expr × Expr × Expr) :=
      match raw with
      | .letE _ type value body _ =>
          (sequentialStateSource? env type value stateType?).map fun source =>
            (value, source, body)
      | _ => none
    let ordinaryLet? : Option (Expr × Expr × Expr) :=
      match raw with
      | .letE _ type value body _ => some (type, value, body)
      | _ => none
    match sequential?, ordinaryLet? with
    | some (value, source, body), _ =>
      match decodeYieldState env fuel' localDepth value appliedBases stateType? statePrefix deepScalars,
          decodeYieldState env fuel' localDepth (body.instantiate1 source) appliedBases
            stateType? statePrefix deepScalars with
      | .ok prior, .ok continuation => .ok (prior ++ continuation)
      | .error reason, _ =>
          .error s!"extract/unsupported: sequential inline state binding: {reason}"
      | _, .error reason => .error reason
    | none, some (type, value, body) =>
      let scalarType := type.consumeMData.getAppFn.constName?
      if scalarType == some ``UInt64 then
        match localScalarValue? env (if deepScalars then 128 else 32) value with
        | some localValue =>
          if shouldMaterializeLocal type localValue then
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            match decodeYieldState env fuel' (localDepth + 1)
                (body.instantiate1 marker) appliedBases stateType? statePrefix deepScalars with
            | .ok continuation => .ok (#[.letLocal localDepth localValue] ++ continuation)
            | .error reason => .error reason
          else
            decodeYieldState env fuel' localDepth (body.instantiate1 value) appliedBases stateType?
              statePrefix deepScalars
        | none =>
            decodeYieldState env fuel' localDepth (body.instantiate1 value) appliedBases stateType?
              statePrefix deepScalars
      else
        decodeYieldState env fuel' localDepth (body.instantiate1 value) appliedBases stateType?
          statePrefix deepScalars
    | none, none =>
      let state0 := raw
      let appliedBases := addAppliedBases #[] <|
        appliedBases.map fun base => strip (substLets 256 base)
      if appliedBases.contains state0 then
        .ok #[]
      else if let some (name, unfolded) := unfoldUserHelper env state0 then do
        let args := state0.getAppArgs
        let (prior, normalized, bodyAppliedBases) ←
          if h : args.size > 0 then
            let base := args[0]
            let source :=
              if statePrefix.isEmpty then inlineStateSource env 64 base
              else inlineTypedStateSource env 64 base
            if source == base then
              .ok (#[], unfolded, appliedBases)
            else do
              let prior ← decodeYieldState env fuel' localDepth base appliedBases stateType?
                statePrefix deepScalars
              let normalized := unfolded.replace fun e => if e == base then some source else none
              let bodyAppliedBases := addAppliedBases appliedBases #[base]
              let bodyAppliedBases :=
                addAppliedBases bodyAppliedBases (projectedInlineBases env 64 base)
              .ok (prior, normalized, bodyAppliedBases)
          else
            .ok (#[], unfolded, appliedBases)
        match decodeYieldState env fuel' localDepth normalized bodyAppliedBases stateType?
            statePrefix deepScalars with
        | .ok ops => .ok (prior ++ ops)
        | .error reason => .error s!"extract/unsupported: inline state {name}: {reason}"
      else if (isConstNamed state0 ``ite || isConstNamed state0 ``dite) &&
          state0.getAppArgs.size ≥ 2 then
        let args := state0.getAppArgs
        let peelProofLam (e : Expr) : Expr :=
          match strip e with
          | .lam _ _ body _ => body.lowerLooseBVars 1 1
          | e => e
        let thn := peelProofLam args[args.size - 2]!
        let els := peelProofLam args[args.size - 1]!
        match args.findSome? (asCondition env),
            decodeYieldState env fuel' localDepth thn appliedBases stateType? statePrefix deepScalars,
            decodeYieldState env fuel' localDepth els appliedBases stateType? statePrefix deepScalars with
        | some (cmp, lhs, rhs), .ok thnOps, .ok elsOps =>
          .ok #[.ite cmp lhs rhs thnOps elsOps]
        | none, _, _ =>
          .error s!"extract/unsupported: inline state condition: {args[args.size - 4]!}"
        | _, .error reason, _ => .error s!"extract/unsupported: inline state then: {reason}"
        | _, _, .error reason => .error s!"extract/unsupported: inline state else: {reason}"
      else if let some nested := nestedSequentialTransition? env state0 statePrefix then do
        let normalized : NestedStateNormalization ←
          match nested.outerOwner? with
          | none => .ok (NestedStateNormalization.mk #[] nested.transition
              nested.typedSource state0)
          | some (owner, root, ownerType) => do
            let prior ← decodeYieldState env fuel' localDepth owner appliedBases
              (some ownerType) "" deepScalars
            -- The composed owner may itself contain the nested transition whose result is also
            -- referenced by a scalar argument of the later helper (for example an allocated
            -- address read from a just-pruned tree). That transition has already run as part of
            -- `prior`; rewrite the exact same-typed value to its normalized projection as well.
            let appliedNested? := nestedSequentialTransition? env owner ""
            let rewriteApplied (e : Expr) : Expr :=
              let e := e.replace fun candidate => if candidate == owner then some root else none
              match appliedNested? with
              | none => e
              | some applied =>
                let source := applied.typedSource.replace fun candidate =>
                  if candidate == owner then some root else none
                let appliedSourceVal := val env applied.typedSource
                e.replace fun candidate =>
                  let candidateSource := inlineTypedStateSource env 64 candidate
                  let sameTypedSource := candidateSource == applied.typedSource ||
                    (appliedSourceVal.isSome && val env candidateSource == appliedSourceVal)
                  if candidate == applied.transition || (sameTypedSource &&
                      isStateTransitionValue env 64 false candidate) then
                    some source
                  else none
            let transition :=
              rewriteApplied nested.transition
            let typedSource :=
              rewriteApplied nested.typedSource
            let outerState := state0.replace fun e => if e == owner then some root else none
            .ok (NestedStateNormalization.mk prior transition typedSource outerState)
        let nestedOps ←
          match decodeYieldState env fuel' localDepth normalized.transition appliedBases
              (some nested.nestedType) nested.fieldPrefix deepScalars with
          | .ok ops =>
              let fieldNames := (getStructureFields env nested.nestedType).map (·.toString)
              .ok (dropNestedStateTerminals
                (ops.map (qualifyNestedStateOp nested.fieldPrefix fieldNames)))
          | .error reason =>
              .error s!"extract/unsupported: nested sequential state field: {reason}"
        let continuationState :=
          normalized.outerState.replace fun e =>
            if e == normalized.transition then some normalized.typedSource else none
        match decodeYieldState env fuel' localDepth continuationState appliedBases stateType?
            statePrefix deepScalars with
        | .ok continuation =>
            .ok (dropNestedRootStores nested.fieldPrefix
              (normalized.prior ++ nestedOps ++ continuation))
        | .error reason => .error reason
      else do
        let priorBase? := findProjectedInlineBase env 64 state0
        let prior ←
          match priorBase? with
          | none => .ok #[]
          | some base =>
            if appliedBases.contains base then .ok #[] else match unfoldUserHelper env base with
            | some (name, _) =>
              -- Keep the helper application intact here. Its normal decode path sequences the
              -- state argument before β-expanded scalar lets; decoding the body directly would
              -- read the pre-transition state and duplicate those lets through every projection.
              match decodeYieldState env fuel' localDepth base appliedBases stateType?
                  statePrefix deepScalars with
              | .ok ops => .ok ops
              | .error reason =>
                .error s!"extract/unsupported: projected inline state {name}: {reason}"
            | none => .error "extract/unsupported: projected inline state"
        -- The prior transition has now run. Rewrite outer projections of its result back to
        -- the helper's source state expression; state-loop normalization interprets those
        -- projections against the current mutable state, preserving the sequential semantics.
        let outerState :=
          match priorBase? with
          | none => state0
          | some base =>
            let args := base.getAppArgs
            if h : args.size > 0 then
              let sourceState := args[0]
              state0.replace fun e => if e == base then some sourceState else none
            else state0
        let outerAppliedBases :=
          match priorBase? with
          | some base =>
            let bases := addAppliedBases appliedBases #[base]
            addAppliedBases bases (projectedInlineBases env 64 base)
          | none => appliedBases
        let dynamic := (collectIndexSets env outerState (deduplicate := true)
          (appliedBases := outerAppliedBases)).map (qualifyDynamicStateOp statePrefix)
        let static := (flattenLeaves env statePrefix outerState outerAppliedBases).map fun p =>
          (.storeField p.1 p.2 : Ops.Op)
        let update := snapshotStateUpdate localDepth
          (dynamic ++ dropVectorRootStores dynamic static)
        .ok (prior ++ update)

/-- Lower one marked `MProd` yield as a simultaneous scalar-frame update. Every right-hand side is
snapshotted before any frame slot changes, so later assignments cannot observe an earlier write. -/
private def scalarFrameYieldOps (env : Environment) (state : Expr) :
    Option (Except String (Array Ops.Op)) :=
  let state := strip state
  if !isConstNamed state ``scalarFrameYield then none else
  some do
    let args := state.getAppArgs
    if args.size < 2 then
      throw "extract/unsupported: scalar frame yield marker"
    let base ←
      match asLit 8 args[args.size - 2]! with
      | some (.lit base) => .ok base.toNat
      | _ => .error "extract/unsupported: scalar frame local base"
    let leaves ←
      match scalarFrameLeaves args[args.size - 1]! with
      | some leaves => .ok leaves
      | none => .error "extract/unsupported: scalar frame yield shape"
    if leaves.size < 2 then
      throw "extract/unsupported: scalar frame requires multiple UInt64 values"
    let values ← leaves.mapM fun leaf =>
      match val env leaf with
      | some value => .ok value
      | none => .error "extract/unsupported: scalar frame yield value"
    let mut ops : Array Ops.Op := #[]
    for index in [:values.size] do
      ops := ops.push (.letLocal (base + values.size + index) values[index]!)
    for index in [:values.size] do
      ops := ops.push (.setLocal (base + index) (.local (base + values.size + index)))
    return ops

/-- State loop 的 `yield newState` 只写账户并继续，不生成 commit/exit。 -/
private def asYieldStores (env : Environment) (e : Expr) (localDepth : Nat)
    (stateType? : Option Name := none) (deepScalars : Bool := false) :
    Option (Except String (Array Ops.Op)) :=
  match findYieldPayload e with
  | none => none
  | some state =>
      scalarFrameYieldOps env state <|>
        some (decodeYieldState env 128 localDepth state (stateType? := stateType?)
          (deepScalars := deepScalars))

/-- An inline State helper used as the state component of `.ok (state, ret)` still owns a real
transition. Decode that transition before returning the pair's explicit scalar result. -/
private def asInlineStateSuccess (env : Environment) (e : Expr) (localDepth : Nat)
    (stateType? : Option Name := none) (deepScalars : Bool := false) :
    Option (Except String (Array Ops.Op)) :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if !isConstNamed e ``Except.ok || e.getAppArgs.size < 1 then none else
  let pair := strip e.getAppArgs[e.getAppArgs.size - 1]!
  if !isConstNamed pair ``Prod.mk || pair.getAppArgs.size < 2 then none else
  let args := pair.getAppArgs
  let state := args[args.size - 2]!
  let result := args[args.size - 1]!
  if (unfoldUserHelper env state).isNone then none else
  some do
    let returns ←
      match effectfulResultOps env result with
      | some returns => .ok returns
      | none => .error "extract/unsupported: inline state success result"
    let stores ← decodeYieldState env 128 localDepth state (stateType? := stateType?)
      (deepScalars := deepScalars)
    return stores ++ returns

/-- State-leaf stores that accompany an Evm effect sequence in the same success transition:
dynamic fixed-vector writes plus the complete leaf diff. Effect-bearing leaf values stay in the
op list only (a carrier field's runtime put must not also become a store), synthetic vector
roots are dropped, and unchanged leaves never reach this filter because the leaf diff omits
them. This keeps one success branch's literal `State` update and its runtime effects coherent
instead of silently erasing the non-wide half of the transition. `mergeEvmStores` snapshots any
mutable target queries in these stores before an invalidating effect head, then emits the effects
before the final State writes. -/
private def evmEffectStores (env : Environment) (e : Expr) :
    Array Ops.Op :=
  let dynamic := collectIndexSets env e (deduplicate := true)
  let staticStores :=
    match asStoreFields env e true with
    | some stores => stores.filterMap fun
        | .storeField name value =>
            if Ops.hasEvmLeaf #[.returnU64 value] then none
            else some (.storeField name value)
        | _ => none
    | none => #[]
  dynamic ++ dropVectorRootStores dynamic staticStores

/-- Evm effect sequences keep their own op list; the same success branch's state-leaf stores
rejoin right before the trailing result instead of being discarded for lacking a wide leaf name.
Any State-store operand that reads mutable EVM state is evaluated into a lexical local before a
storage-writing/external-call effect can change that observation. -/
private def mergeEvmStores (localDepth : Nat) (evmOps stores : Array Ops.Op) : Array Ops.Op :=
  let evmHead :=
    if evmOps.back?.any (fun | .returnU64 _ => true | _ => false) then evmOps.pop else evmOps
  if stores.isEmpty then evmOps
  else
    let (snapshot, stores) :=
      snapshotStateOps localDepth stores (evmEffectsInvalidateQueries evmHead)
    let tail : Array Ops.Op :=
      match evmOps.back? with
      | some op@(.returnU64 _) => #[op]
      | _ => #[]
    snapshot.prelude ++ evmHead ++ stores ++ tail

private def decodePlain (env : Environment) (e : Expr) (stateful : Bool)
    (localDepth : Nat) (stateType? : Option Name := none) (deepScalars : Bool := false) :
    Except String (Array Ops.Op) :=
  -- A direct update of one field in a multi-field State is still a complete state transition.
  -- Historically only branch/loop callers requested single-leaf stores, forcing source programs
  -- to wrap ordinary updates in an artificial always-true comparison. Keep the one-field-state
  -- shorthand below, but decode one changed leaf explicitly when the declared State has siblings.
  let includeSingleStore := stateful || stateType?.any fun stateType =>
    (getStructureFields env stateType).size > 1
  -- 必须在 peelLets 之前找效应：剥掉 `have sent := …` 后调用就没了。
  if let some call := findComponentCall env 16 e then
    .ok #[.component call, .returnU64 (.lit 0)]
  else if let some inv := findInvoke env 16 e then
    invokeOpsWithRet env e inv
  else if let some ops := decodeNearEffect env e then
    .ok ops
  else if let some ops := decodeEvmEffect env e then
    .ok (mergeEvmStores localDepth ops (evmEffectStores env e))
  else if let some (n, addend) := findForIn env e then
    .ok #[.forAccum n addend localDepth, .returnU64 (.local localDepth)]
  else if let some result := asYieldStores env e localDepth stateType? deepScalars then
    result
  else if let some result := asInlineStateSuccess env e localDepth stateType? deepScalars then
    result
  else
  -- Record updates repeat one shared constructor through every unchanged projection. Emit each
  -- exact Vector.set node once; separate branch/set expressions remain distinct.
  let isets := collectIndexSets env e (deduplicate := true)
  if isets.size ≥ 1 then
    match asStoreFields env e true with
    | some stores =>
      .ok (snapshotStateUpdate localDepth (isets ++ dropVectorRootStores isets stores))
    | none =>
      match isets[isets.size - 1]! with
      | .indexSetLeaf _ _ v _ _ | .indexSet _ _ v _ _ =>
        -- `.ok ({ state with xs := xs.set i value }, ret)` returns its explicit second
        -- component, which need not be `value`. Loop yields have no public return and keep
        -- the written value as their internal fallback.
        let ret := if isForInStep e then v else (findOkRet env e).getD v
        .ok (snapshotStateUpdate localDepth (isets.push (.okState ret)))
      | _ => .ok isets
  else if let some op := findIndexSet env e then
    match op with
    | .indexSetLeaf _ _ v _ _ | .indexSet _ _ v _ _ =>
      let ret := if isForInStep e then v else (findOkRet env e).getD v
      .ok (snapshotStateUpdate localDepth #[op, .okState ret])
    | _ => .ok #[op]
  else
  let optionResult? := asConstructedOptionResult env 8 e
  let decodedError := decodeErrorCtor env e
  let e := peelControl 8 e
  if let .overflow := decodedError then
    .ok #[.errorOverflow]
  else if let .named name := decodedError then
    .ok #[.errorNamed name]
  else if let .typed frame := decodedError then
    .ok #[.errorTyped frame]
  else if let .unsupported reason := decodedError then
    .error s!"extract/unsupported: {reason}"
  else if let some (tag, payload) := optionResult? then
    -- A constructed Option is already a fixed logical frame. Target codecs retain ownership of
    -- the tag width and wire layout; extraction only preserves both source leaves through joins.
    .ok #[.returnU64 tag, .returnU64 payload]
  else if let some values := asOkNoop env e then
    if stateful && values.size == 1 then
      .ok #[.okState values[0]!]
    else
      .ok (values.map fun value => .returnU64 value)
  else if let some ops := asStoreFields env e includeSingleStore then
    .ok (snapshotStateUpdate localDepth ops)
  else if let some v := asOkState env e then
    .ok #[.okState v]
  else if let some v := asOkScalar env e then
    .ok #[.okState v]
  else if let some vs := asBoundedCtorFields env e then
    .ok (returnStatesOf vs)
  else if let some vs := asRegisteredBoundaryCtorFields env e then
    .ok (vs.map fun value => .returnU64 value)
  else if let some vs := asStateFields env e then
    .ok (returnStatesOf vs)
  else if let some v := asStateMk env e then
    .ok #[.returnState v]
  else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
    match val env e.getAppArgs[e.getAppArgs.size - 2]!,
          val env e.getAppArgs[e.getAppArgs.size - 1]! with
    | some a, some b => .ok #[.returnU64 a, .returnU64 b]
    | _, _ => .error "extract/unsupported: pair return"
  else if (match e.getAppFn.constName? with
      | some name =>
        match env.find? name with
        | some info => isBytes32Type (resultType 16 info.type)
        | none => false
      | none => false) then
    let (w0, w1, w2, w3) := bytes32Leaves env (unfoldUserHelpers env 8 e)
    .ok #[.returnU64 w0, .returnU64 w1, .returnU64 w2, .returnU64 w3]
  else if isConstNamed e ``ProofForge.Evm.Runtime.evmCaller20 || endsWith e ".evmCaller20" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmSelf20 || endsWith e ".evmSelf20" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmCoinbase20 || endsWith e ".evmCoinbase20" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmOrigin20 || endsWith e ".evmOrigin20" ||
      (addr20CtorFields env e).isSome ||
      (match e.getAppFn.constName? with
        | some n =>
          match env.find? n with
          | some info =>
            (resultType 16 info.type).consumeMData.getAppFn.constName? == some addr20Name
          | none => false
        | none => false) then
    let (w0, w1, w2) := addr20Leaves env e
    .ok #[.returnU64 w0, .returnU64 w1, .returnU64 w2]
  else if (uint256CtorFields env e).isSome ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmAdd256 || endsWith e ".evmAdd256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmSub256 || endsWith e ".evmSub256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMul256 || endsWith e ".evmMul256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmAnd256 || endsWith e ".evmAnd256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmOr256 || endsWith e ".evmOr256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmXor256 || endsWith e ".evmXor256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmNot256 || endsWith e ".evmNot256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmShl256 || endsWith e ".evmShl256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmShr256 || endsWith e ".evmShr256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmDiv256 || endsWith e ".evmDiv256" ||
      isConstNamed e ``ProofForge.Evm.Runtime.evmMod256 || endsWith e ".evmMod256" ||
      (match unfoldUserHelper env e with
        | some (_, unfolded) => (uint256CtorFields env unfolded).isSome
        | none => false) ||
      (match e.getAppFn.constName? with
        | some n =>
          match env.find? n with
          | some info => isUInt256Type (resultType 16 info.type)
          | none => false
        | none => false) then
    let (w0, w1, w2, w3) := uint256Leaves env e
    .ok #[.returnU64 w0, .returnU64 w1, .returnU64 w2, .returnU64 w3]
  else if let some leaf := nearRuntimeLeaf? e then
    .ok #[.returnU64 leaf]
  else if let some v := val env e then
    match v with
    | .field _ _ => .ok #[.returnU64 v]
    | .arg _ => .ok #[.returnU64 v]
    | .local _ => .ok #[.returnU64 v]
    | .lit _ => .ok #[.returnU64 v]
    | .clockSlot | .clockEpoch | .unixTime | .slotsPerEpoch | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
    | .accN | .isSigner0 | .isWritable0 | .isExecutable0
    | .accLamports1 | .accOwner1 | .accDataLen1
    | .isSigner1 | .isWritable1 | .isExecutable1 | .findPda _
    | .checkPda _ _ | .rentExemption _ | .cpiReturn | .sha256Lit _ | .keccak256Lit _
    | .byteSwap64 _
    | .accKeyWord _ _ | .accOwnerWord _ _ | .accDataWord _ _ | .accDataWordAt ..
    | .ext (.svm (.component _)) _
    | .nearBlockIndex | .nearBlockTimestamp | .nearPredecessor
    | .nearPredecessorLen
    | .nearPredecessorW1 | .nearPredecessorW2 | .nearPredecessorW3 | .nearPredecessorW4
    | .nearPredecessorW5 | .nearPredecessorW6 | .nearPredecessorW7
    | .nearAttachedDeposit | .nearAttachedDepositW0 | .nearAttachedDepositW1
    | .nearAccountBalance | .nearAccountBalanceW0 | .nearAccountBalanceW1
    | .nearCurrentAccountId
    | .nearCurrentAccountIdLen
    | .nearCurrentAccountIdW1 | .nearCurrentAccountIdW2 | .nearCurrentAccountIdW3
    | .nearCurrentAccountIdW4 | .nearCurrentAccountIdW5 | .nearCurrentAccountIdW6
    | .nearCurrentAccountIdW7
    | .nearTransientBuffer64Get _ _
    | .nearStorageResultStatus _ | .nearStorageResultLength _ | .nearStorageResultFits _
    | .nearStorageResultByte _ _
    | .accLamportsN _ | .accDataLenN _ | .isSignerN _ | .isWritableN _ | .isExecutableN _
    | .signerKeyN _ | .ownerIsSelf _ | .findPdaSeeds _ | .checkPdaSeeds _ _ =>
        .ok #[.returnU64 v]
    | .indexGet .. => .ok #[.returnU64 v]
    | .addU64 .. | .subU64 .. | .mulU64 .. | .divU64 .. | .modU64 .. =>
        .ok #[.returnU64 v]
    | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. =>
        .ok #[.returnU64 v]
    | v =>
      if Ops.hasEvmLeaf #[.returnU64 v] || Ops.hasXrplLeaf #[.returnU64 v] ||
          Ops.isLangLeaf v then .ok #[.returnU64 v]
      else .error "extract/unsupported: body"
  else
    .error "extract/unsupported: body"

private def findBy (args : Array Expr) (p : Expr → Bool) : Option Expr :=
  args.find? p

private def lastNamedBin (env : Environment) (want : Name) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Ops.Val × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e want then
        match binArgs e with
        | some (l, r) =>
          match val env l, val env r with
          | some lv, some rv => some (lv, rv)
          | _, _ => none
        | none => none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | _ => e.getAppArgs.findSome? (go fuel')
  go 16 e

/--
Turn the terminal successes of a scalar `Except` producer into assignments to one join slot.
Checked arithmetic already branches to the enclosing error exit, so operations after a terminal
success are unreachable and must not be copied into the joined path.
-/
private partial def lowerBindProducer (slot : Nat) (ops : Array Ops.Op) :
    Option (Array Ops.Op × Bool × Bool) := Id.run do
  let mut lowered := #[]
  let mut hadSuccess := false
  for op in ops do
    match op with
    | .okState value | .returnU64 value =>
        return some (lowered.push (.setLocal slot value), true, true)
    | .errorOverflow | .errorNamed _ =>
        return some (lowered.push op, hadSuccess, true)
    | .ite cmp lhs rhs thn els =>
        let some (thn', thnSuccess, thnTerminates) := lowerBindProducer slot thn
          | return none
        let some (els', elsSuccess, elsTerminates) := lowerBindProducer slot els
          | return none
        lowered := lowered.push (.ite cmp lhs rhs thn' els')
        hadSuccess := hadSuccess || thnSuccess || elsSuccess
        if thnTerminates && elsTerminates then
          return some (lowered, hadSuccess, true)
    | .letLocal .. | .joinLocal .. | .setLocal ..
    | .checkedAddU64 .. | .checkedSubU64 .. | .checkedMulU64 ..
    | .checkedDivU64 .. | .checkedModU64 .. | .forAccum .. =>
        lowered := lowered.push op
    | .forBody bound body =>
        let some (body', bodySuccess, bodyTerminates) := lowerBindProducer slot body
          | return none
        if bodySuccess || bodyTerminates then return none
        lowered := lowered.push (.forBody bound body')
    | .ext _ =>
        -- Target effects can precede a scalar success just like checked arithmetic. Preserve
        -- them in order; their own backend contracts fail closed before the join continuation.
        lowered := lowered.push op
    | _ => return none
  return some (lowered, hadSuccess, false)

/-- The return of an ignored scalar helper is not a method return. Keep its branch structure and
effects, but splice the caller's continuation after every successful helper path. -/
private partial def dropIgnoredScalarTerminals (ops : Array Ops.Op) : Array Ops.Op :=
  ops.filterMap fun op =>
    match op with
    | .returnU64 _ | .okState _ => none
    | .ite cmp lhs rhs thn els =>
        some (.ite cmp lhs rhs (dropIgnoredScalarTerminals thn) (dropIgnoredScalarTerminals els))
    | .forBody n body => some (.forBody n (dropIgnoredScalarTerminals body))
    | op => some op

/-- A bind enclosing a loop belongs to the surrounding monadic control flow and must be decoded
before loop discovery. Binds inside the callback body are part of that iteration and do not hide
the state loop itself. -/
private def loopUnderBind (fuel : Nat) (e : Expr) (underBind : Bool := false) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    let e := strip e
    if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then underBind
    else if isConstNamed e ``Bind.bind || endsWith e ".bind" then
      let args := e.getAppArgs
      if h : args.size ≥ 2 then
        let producer := args[args.size - 2]
        let continuation := args[args.size - 1]
        -- `forIn ... >>= continuation` is the loop's own sequencing bind. A loop in the
        -- producer is therefore not hidden by this bind. Decode that producer first even when
        -- its continuation contains another sequential loop; the recursive continuation decode
        -- will then own the later loop. If the producer has no loop, a continuation loop remains
        -- hidden under this bind and must wait for normal bind lowering.
        let producerOwnsLoop := producer.getUsedConstantsAsSet.toList.any fun name =>
          name == ``ForIn.forIn || name.toString.endsWith ".forIn"
        if producerOwnsLoop then loopUnderBind fuel' producer underBind
        else loopUnderBind fuel' producer underBind || loopUnderBind fuel' continuation true
      else
        args.any (loopUnderBind fuel' · true)
    else
      e.getAppArgs.any (loopUnderBind fuel' · underBind)

/-- A scalar let whose producer owns bounded control/effects needs one join local before its caller
can compare or transform the result. Ordinary scalar lets remain eligible for direct substitution. -/
private def isSequencedScalarProducer (env : Environment) (type value : Expr) : Bool :=
  type.consumeMData.getAppFn.constName? == some ``UInt64 &&
    (mentionsSvmEffect env 16 value || (findForIn env value).isSome ||
      (findForBodyExpr env value).isSome)

/-- Find one effect-free UInt64 helper below a pure expression wrapper whose bounded control must
be evaluated before the enclosing comparison/arithmetic expression. Never cross a control
boundary: branch arms and bind continuations retain their original evaluation order. Effectful
producers require an explicit source `let`, so replacing a repeated pure subtree cannot coalesce
effects. -/
private def nestedSequencedScalarHelper? (env : Environment) (e : Expr) : Option Expr :=
  let rec visit (fuel : Nat) (candidate : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let candidate := candidate.consumeMData
      let head := strip candidate
      if isConstNamed head ``ite || isConstNamed head ``dite ||
          isConstNamed head ``Bind.bind || endsWith head ".bind" then
        none
      else
        match unfoldUserHelper env candidate with
        | some (name, unfolded) =>
            match env.find? name with
            | some (.defnInfo info) =>
                if (resultType 16 info.type).consumeMData.getAppFn.constName? == some ``UInt64 &&
                    !mentionsSvmEffect env 16 unfolded && (decodeEvmEffect env unfolded).isNone &&
                    ((findForIn env unfolded).isSome || (findForBodyExpr env unfolded).isSome) then
                  some candidate
                else
                  candidate.getAppArgs.findSome? (visit fuel')
            | _ => candidate.getAppArgs.findSome? (visit fuel')
        | none => candidate.getAppArgs.findSome? (visit fuel')
  e.getAppArgs.findSome? (visit 16)

def decodeExpr (env : Environment) (fuel : Nat) (e : Expr)
    (stateful : Bool := false) (preserveLocals : Bool := false)
    (localDepth : Nat := 0) (stateType? : Option Name := none)
    (deepScalars : Bool := false) :
    Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: ite depth"
  | fuel' + 1 => Id.run do
    -- Do-notation over a branch-selected inline helper can leave a head beta redex after the bind
    -- result is replaced by a lexical marker. Normalize that language-level composition before
    -- looking for effects or control flow; this keeps helper composition out of target Ops/Emit.
    let e := e.headBeta
    let e := (reducePureInlineMatch? env e).getD e
    let (effects, continuation, malformedWrite) := leadingSvmEffects env e
    if malformedWrite then
      return .error "extract/unsupported: external account write operands"
    if !effects.isEmpty then
      match decodeExpr env fuel' continuation (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars) with
      | .ok decodedOps =>
          let continuationOps :=
            if Ops.hasStoreField decodedOps || Ops.hasIndexSet decodedOps then decodedOps
            else (asStoreFields env continuation true).getD decodedOps
          return .ok (effects ++ continuationOps)
      | .error reason =>
          return .error s!"extract/unsupported: SVM effect sequence continuation: {reason}"
    let stripped := strip e
    if isConstNamed stripped ``Id.run then
      if let some guarded := guardedRunBody? 64 stripped then
        return decodeExpr env fuel' guarded (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars)
    match strip e with
    | .letE _ ty value body _ =>
      let ignoredInlineEffect :=
        if body.hasLooseBVar 0 then false
        else
          (decodeNearEffect env value).isSome ||
            match unfoldUserHelper env value with
            | some (_, unfolded) =>
                mentionsSvmRuntime env 8 unfolded || (findInvoke env 64 unfolded).isSome ||
                  mentionsSvmEffect env 64 unfolded || mentionsNearEffect env 64 unfolded
            | none => false
      if ignoredInlineEffect then
        match decodeExpr env fuel' value (preserveLocals := preserveLocals)
              (localDepth := localDepth) (stateType? := stateType?)
              (deepScalars := deepScalars),
            decodeExpr env fuel' (body.instantiate1 value) (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars) with
        | .ok helperOps, .ok continuationOps =>
            return .ok (dropIgnoredScalarTerminals helperOps ++ continuationOps)
        | .error reason, _ =>
            return .error s!"extract/unsupported: inline effect helper: {reason}"
        | _, .error reason => return .error reason
      let effectful :=
        (findInvoke env 16 value).isSome || mentionsSvmEffect env 16 value ||
          mentionsNearEffect env 16 value || (decodeNearEffect env value).isSome ||
          (decodeEvmEffect env value).isSome ||
          (findForIn env value).isSome || (findForBodyExpr env value).isSome
      let scalarControlProducer := isSequencedScalarProducer env ty value
      if scalarControlProducer then
        match decodeExpr env fuel' value (preserveLocals := preserveLocals)
            (localDepth := localDepth + 1) (stateType? := stateType?)
            (deepScalars := deepScalars) with
        | .error reason =>
            return .error s!"extract/unsupported: scalar control producer: {reason}"
        | .ok producerOps =>
          match lowerBindProducer localDepth producerOps with
          | some (joinedProducer, true, true) =>
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            match decodeExpr env fuel' (body.instantiate1 marker) (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok continuationOps =>
                return .ok (#[.joinLocal localDepth] ++ joinedProducer ++ continuationOps)
            | .error reason =>
                return .error s!"extract/unsupported: scalar control continuation: {reason}"
          | _ =>
              return .error "extract/unsupported: scalar control producer has no value"
      else if !effectful then
        if let some source := sequentialStateSource? env ty value stateType? then
          match decodeYieldState env 128 localDepth value (stateType? := stateType?)
              (statePrefix := "") (deepScalars := deepScalars),
              decodeExpr env fuel' (body.instantiate1 source) (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars) with
          | .ok prior, .ok continuation => return .ok (prior ++ continuation)
          | .error reason, _ =>
            return .error s!"extract/unsupported: sequential state binding: {reason}"
          | _, .error reason => return .error reason
        else if ty.consumeMData.getAppFn.constName? == some ``UInt64 then
          match localScalarValue? env (if deepScalars then 128 else 32) value with
          | some localValue =>
            if preserveLocals && shouldMaterializeLocal ty localValue then
              let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
              match decodeExpr env fuel' (body.instantiate1 marker)
                  (stateful := stateful) (preserveLocals := preserveLocals)
                  (localDepth := localDepth + 1) (stateType? := stateType?)
                  (deepScalars := deepScalars) with
              | .ok ops => return .ok (#[.letLocal localDepth localValue] ++ ops)
              | .error reason => return .error reason
            else
              return decodeExpr env fuel' (body.instantiate1 value)
                (stateful := stateful) (preserveLocals := preserveLocals)
                (localDepth := localDepth) (stateType? := stateType?)
                (deepScalars := deepScalars)
          | _ =>
            return decodeExpr env fuel' (body.instantiate1 value)
              (stateful := stateful) (preserveLocals := preserveLocals)
              (localDepth := localDepth) (stateType? := stateType?)
              (deepScalars := deepScalars)
        else
          return decodeExpr env fuel' (body.instantiate1 value)
            (stateful := stateful) (preserveLocals := preserveLocals)
            (localDepth := localDepth) (stateType? := stateType?)
            (deepScalars := deepScalars)
    | _ => pure ()
    if let some producer := nestedSequencedScalarHelper? env e then
      match decodeExpr env fuel' producer (preserveLocals := preserveLocals)
          (localDepth := localDepth + 1) (stateType? := stateType?)
          (deepScalars := deepScalars) with
      | .error reason =>
          return .error s!"extract/unsupported: nested scalar control producer: {reason}"
      | .ok producerOps =>
        match lowerBindProducer localDepth producerOps with
        | some (joinedProducer, true, true) =>
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            let continuation := e.replace fun candidate =>
              if candidate == producer then some marker else none
            match decodeExpr env fuel' continuation (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok continuationOps =>
                return .ok (#[.joinLocal localDepth] ++ joinedProducer ++ continuationOps)
            | .error reason =>
                return .error s!"extract/unsupported: nested scalar control continuation: {reason}"
        | _ =>
            return .error "extract/unsupported: nested scalar control producer has no value"
    -- Branch decoders normalize their arms independently. Zeta-reducing the entire branch here
    -- duplicates let-bound State transitions into every projection before the sequential-state
    -- boundary can consume them, making composed record updates exponential.
    let structured := strip e
    let fullySubstituted :=
      if isConstNamed structured ``ite || isConstNamed structured ``dite then e
      else substLets 256 e
    let controlled := peelControl 16 fullySubstituted
    let e :=
      if (unfoldUserHelper env fullySubstituted).isSome then fullySubstituted
      else if (unfoldUserHelper env controlled).isSome then controlled
      else e
    let e0 := strip e
    if (isConstNamed e0 ``Bind.bind || endsWith e0 ".bind") && e0.getAppArgs.size ≥ 2 then
      let args := e0.getAppArgs
      let producer := args[args.size - 2]!
      let continuation := args[args.size - 1]!
      match strip continuation with
      | .lam _ ty body _ =>
        if isScalarResult env ty then
          match decodeExpr env fuel' producer (preserveLocals := preserveLocals)
              (localDepth := localDepth + 1) (stateType? := stateType?)
              (deepScalars := deepScalars) with
          | .error reason =>
              return .error s!"extract/unsupported: bind producer: {reason}"
          | .ok producerOps =>
            match lowerBindProducer localDepth producerOps with
            | some (joinedProducer, true, true) =>
              let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
              match decodeExpr env fuel' (body.instantiate1 marker) (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok continuationOps =>
                  return .ok (#[.joinLocal localDepth] ++ joinedProducer ++ continuationOps)
              | .error reason =>
                  return .error s!"extract/unsupported: bind continuation: {reason}"
            | _ =>
                return .error "extract/unsupported: bind producer is not a scalar control value"
        else
          pure ()
      | _ => pure ()
    let scalarLoop? : Option (Except String (Array Ops.Op)) :=
      match if loopUnderBind 64 e then none else findForStateExpr env e with
      | none => none
      | some (n, initial, bodyE, continuation) =>
        match scalarFrameLeaves initial with
        | none => none
        | some leaves =>
          if leaves.size < 2 || isForInDone bodyE then none else some do
            let frame ←
              match scalarFrameLocalShape initial localDepth with
              | some frame => .ok frame
              | none => .error "extract/unsupported: scalar frame local shape"
            let initialValues ← leaves.mapM fun leaf =>
              match val env leaf with
              | some value => .ok value
              | none => .error "extract/unsupported: scalar frame initial value"
            let body := markScalarFrameYields localDepth (bodyE.instantiate1 frame)
            let bodyOps ←
              match decodeExpr env fuel' body (stateful := true) (preserveLocals := true)
                  (localDepth := localDepth + 2 * leaves.size) (stateType? := stateType?)
                  (deepScalars := n > 4) with
              | .ok ops => .ok ops
              | .error reason =>
                  .error s!"extract/unsupported: scalar frame body: {reason}"
            let continuation := continuation.instantiate1 frame
            let continuation :=
              (reduceScalarFrameContinuation? env continuation frame).getD continuation
            let continuationOps ←
              match decodeExpr env fuel' continuation (stateful := true)
                  (preserveLocals := preserveLocals)
                  (localDepth := localDepth + 2 * leaves.size) (stateType? := stateType?)
                  (deepScalars := n > 4) with
              | .ok ops => .ok ops
              | .error reason =>
                  .error s!"extract/unsupported: scalar frame continuation: {reason}"
            let initialOps := initialValues.mapIdx fun index value =>
              (.letLocal (localDepth + index) value : Ops.Op)
            return initialOps ++ #[.forBody n (bodyOps.map rewriteLoopOp)] ++ continuationOps
    if let some result := scalarLoop? then
      return result
    let stateLoop? : Option (Except String (Array Ops.Op)) :=
      -- State-loop callbacks capture scalar outer lets by value, while their mutable state binder
      -- must remain visible so `findForStateExpr` can distinguish them from ordinary loops.
      match if loopUnderBind 64 e then none else findForStateExpr env e with
      | none => none
      | some (n, initial, bodyE, continuation) =>
        if isForInDone bodyE then none else
        match decodeYieldState env 128 localDepth initial (stateType? := stateType?),
            decodeExpr env fuel' bodyE (stateful := true)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := n > 4) with
        | .error reason, _ =>
            some (.error s!"extract/unsupported: state loop initial value: {reason}")
        | _, .error reason => some (.error s!"extract/unsupported: state loop body: {reason}")
        | .ok initialOps, .ok bodyOps =>
          if Ops.hasStoreField bodyOps || Ops.hasIndexSet bodyOps then
            match decodeExpr env fuel' continuation (stateful := true)
                (preserveLocals := preserveLocals)
                (localDepth := localDepth) (stateType? := stateType?)
                (deepScalars := n > 4) with
            | .error reason =>
              some (.error s!"extract/unsupported: state loop continuation: {reason}")
            | .ok continuationOps =>
              some (.ok (initialOps ++ #[.forBody n (bodyOps.map rewriteLoopOp)] ++
                continuationOps))
          else none
    if let some result := stateLoop? then
      return result
    else if (isConstNamed e0 ``ite || isConstNamed e0 ``dite) && e0.getAppArgs.size ≥ 5 then
      -- 已经是比较 / dite，不要再往下搜 forIn（循环体自己就是 ite）。
      pure ()
    else if let some (name, unfolded) := unfoldUserHelper env e then
      -- A marked helper owns its control flow. Expose that control flow before recursive
      -- component/CPI discovery, which must never select a nested effect and erase an enclosing
      -- branch (notably a checked wide-value view helper).
      match decodeExpr env fuel' (substIteLets 256 unfolded) (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars) with
      | .ok ops => return .ok ops
      | .error reason => return .error s!"extract/unsupported: inline {name}: {reason}"
    else if let some write := decodeAccDataWordSetAt env (normalizeStorageEffect env e) then
      -- `accDataWordSetAt*` returns its stored value at the source boundary. Keep that return
      -- contract available to reusable POD/container facades without adding another operation.
      let (_, _, _, _, _, _, value) := write
      return .ok #[accDataWordSetAtOp write, .returnU64 value]
    else if let some call := findComponentCall env 16 e then
      return .ok #[.component call, .returnU64 (.lit 0)]
    else if let some inv := findInvoke env 16 e then
      return invokeOpsWithRet env e inv
    else if let some ops := decodeNearEffect env e then
      return .ok ops
    else if let some ops := decodeEvmEffect env e then
      return .ok (mergeEvmStores localDepth ops (evmEffectStores env e))
    else if let some (n, addend) := findForIn env e then
      return .ok #[.forAccum n addend localDepth, .returnU64 (.local localDepth)]
    else if let some (n, bodyE) := findForBodyExpr env e then
      match decodeExpr env fuel' bodyE (preserveLocals := preserveLocals)
          (localDepth := localDepth) (stateType? := stateType?)
          (deepScalars := deepScalars) with
      | .ok ops => return .ok #[.forBody n (ops.map rewritePlainLoopOp), .errorOverflow]
      | .error r => return .error r
    let e := strip e
    if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 5 then
      let args := e.getAppArgs
      let rec peelProofLam (fuel : Nat) (lower : Bool) (e : Expr) : Expr :=
        match fuel with
        | 0 => e
        | fuel' + 1 =>
          match strip e with
          -- 先代入 `have __src`，再降 proof λ。反过来会把 `h` 叠到 `__src` 上。
          | .lam _ _ body _ =>
            let body := substIteLets 16 body
            let body := if lower then body.lowerLooseBVars 1 1 else body
            peelProofLam fuel' lower body
          | e => e
      -- 不在这里 peelLets：`let debit := evmMapSetAddr …` 必须留给 decodeEvmEffect。
      -- 只代 then / else：入口代整个 ite 会把 `have y` 塞进 `y ≠ 0`，asCmp 认不出。
      let tRaw := args[args.size - 2]!
      let fRaw := args[args.size - 1]!
      let lower :=
        stateful ||
          (!(collectIndexSets env tRaw).isEmpty &&
            !isForInStep tRaw && !isForInStep fRaw)
      let t := peelProofLam 4 lower tRaw
      let f := peelProofLam 4 stateful fRaw
      -- Preserve lexical scalar reads in an effectful arm so its recursive decoder can
      -- materialize them before a later account write, component call, or CPI consumes them.
      -- Substituting here would embed the read into the effect operand and could re-read mutated
      -- storage; it also prevents reusable storage-query facades from composing with components.
      -- NEAR effects need the same treatment: zeta-reducing an ignored raw-storage result here
      -- would silently erase the host mutation before the arm is decoded.
      let t :=
        if containsStructuredStateLet env 64 t || mentionsSvmEffect env 64 t ||
            mentionsNearEffect env 64 t then t
        else substIteLets 64 t
      let f :=
        if containsStructuredStateLet env 64 f || mentionsSvmEffect env 64 f ||
            mentionsNearEffect env 64 f then f
        else substIteLets 64 f
      let checkedSubMatches (candidate : Expr) : Bool :=
        match asCheckedSubGuard env candidate with
        | none => false
        | some (guardLhs, guardRhs) =>
          let directResult :=
            match strip t with
            | .letE _ _ value _ _ => val env value
            | _ => asOkState env t
          let directMatch :=
            match directResult with
            | some (.subU64 bodyLhs bodyRhs) =>
                guardLhs == bodyLhs && guardRhs == bodyRhs
            | _ => false
          let nestedMatch :=
            match lastNamedBin env ``HSub.hSub t with
            | some (bodyLhs, bodyRhs) =>
                guardLhs == bodyLhs && guardRhs == bodyRhs
            | none => false
          directMatch || nestedMatch
      let rec hasNestedIte (fuel : Nat) (e : Expr) : Bool :=
        match fuel with
        | 0 => false
        | fuel' + 1 =>
          let e := strip e
          if isConstNamed e ``ite || isConstNamed e ``dite then true
          else
            match e with
            | .letE _ _ value body _ =>
                hasNestedIte fuel' value || hasNestedIte fuel' body
            | .lam _ _ body _ => hasNestedIte fuel' body
            | .app fn arg => hasNestedIte fuel' fn || hasNestedIte fuel' arg
            | _ => false
      -- A recursive invoke search must not erase an intervening branch or a sequence of ignored
      -- invokes followed by a state transition. `decodeExpr` owns the latter so it can preserve
      -- every effect and the continuation.
      let (leading, invokeContinuation) := leadingInvokes env t
      let sequencedState := !leading.isEmpty &&
        (containsStructuredStateLet env 2048 invokeContinuation ||
          containsInlineStateTransition env 2048 invokeContinuation)
      let directInvoke :=
        if hasNestedIte 64 t || sequencedState then none
        else findInvoke env 8 t
      if isErrorOverflow f && !isForInYield f then
        if let some condE := findBy args (fun a =>
            (asCmp env a).isSome &&
              (asCheckedAddGuard env a).isNone &&
              (asCheckedMulGuard env a).isNone &&
              !checkedSubMatches a &&
              -- 真支再套 ite 时，`y ≠ 0` 是比较，不是除法守卫。
              ((asNeZero env a).isNone ||
                isConstNamed (peelLets (strip t)) ``ite ||
                  isConstNamed (peelLets (strip t)) ``dite)) then
          let decodedThen := decodeExpr env fuel' t (stateful := stateful)
            (preserveLocals := preserveLocals) (localDepth := localDepth)
            (stateType? := stateType?) (deepScalars := deepScalars)
          let structuredThen := containsStructuredStateLet env 2048 t ||
            containsInlineStateTransition env 2048 t
          if let .ok thn := decodedThen then
            let rec hasAccDataWrite (fuel : Nat) (ops : Array Ops.Op) : Bool :=
              match fuel with
              | 0 => false
              | fuel' + 1 => ops.any fun op =>
                  match op with
                  | .ext (.svm (.component call)) => !call.effects.writes.isEmpty
                  | .ite _ _ _ nestedThen nestedElse =>
                      hasAccDataWrite fuel' nestedThen || hasAccDataWrite fuel' nestedElse
                  | .forBody _ body => hasAccDataWrite fuel' body
                  | _ => false
            -- A decoded external-account write is the branch's observable effect. Prefer the
            -- recursively decoded sequence over `asStoreFields`, which only sees the final state
            -- value and would otherwise erase ignored writes preceding `.ok`.
            if hasAccDataWrite 8 thn then
              match asCmp env condE with
              | some (cmp, lv, rv) =>
                  return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | none => pure ()
            let rec hasNearEffect (fuel : Nat) (ops : Array Ops.Op) : Bool :=
              match fuel with
              | 0 => false
              | fuel' + 1 => ops.any fun op =>
                  match op with
                  | .ext (.near _) => true
                  | .ite _ _ _ nestedThen nestedElse =>
                      hasNearEffect fuel' nestedThen || hasNearEffect fuel' nestedElse
                  | .forBody _ body => hasNearEffect fuel' body
                  | _ => false
            -- A state-producing arm may also contain an ignored NEAR storage/log/memory result.
            -- Prefer the recursively decoded sequence over `asStoreFields`; the latter sees only
            -- the final state constructor and would silently discard the preceding host effect.
            if hasNearEffect 8 thn then
              match asCmp env condE with
              | some (cmp, lv, rv) =>
                  return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | none => pure ()
            let rec invokeCount (fuel : Nat) (ops : Array Ops.Op) : Nat :=
              match fuel with
              | 0 => 0
              | fuel' + 1 => ops.foldl (init := 0) fun count op =>
                  count + match op with
                  | .invoke .. => 1
                  | .ite _ _ _ nestedThen nestedElse =>
                      invokeCount fuel' nestedThen + invokeCount fuel' nestedElse
                  | .forBody _ body => invokeCount fuel' body
                  | _ => 0
            if 1 < invokeCount 8 thn then
              match asCmp env condE with
              | some (.ne, .lit 0, .lit 1) | some (.ne, .lit 1, .lit 0) =>
                  return .ok thn
              | some (cmp, lv, rv) =>
                  return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | none => pure ()
            if thn.any fun | .letLocal .. => true | _ => false then
              match asCmp env condE with
              | some (cmp, lv, rv) =>
                return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | none => pure ()
          match asCmp env condE, directInvoke, decodeEvmEffect env t, asIndexSet env t,
              asStoreFields env t true, asOkState env t, decodedThen with
          | some (.ne, .lit 0, .lit 1), some inv, _, _, _, _, _ =>
            return invokeOpsWithRet env t inv
          | some (.ne, .lit 1, .lit 0), some inv, _, _, _, _, _ =>
            return invokeOpsWithRet env t inv
          | some (cmp, lv, rv), some inv, _, _, _, _, _ =>
            match invokeOpsWithRet env t inv with
            | .ok ops => return .ok #[.ite cmp lv rv ops #[.errorOverflow]]
            | .error reason => return .error reason
          | some (cmp, lv, rv), none, some evmOps, _, _, _, _ =>
            let ops := mergeEvmStores localDepth evmOps (evmEffectStores env t)
            return .ok #[.ite cmp lv rv ops #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, some iset, _, _, _ =>
            if structuredThen || hasNestedIte 64 t then
              match decodeExpr env fuel' t (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok thn => return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | .error r => return .error r
            else
              let isets := collectIndexSets env t
              let ops := if isets.size ≥ 1 then isets else #[iset]
              match asStoreFields env t true with
              | some stores =>
                return .ok #[.ite cmp lv rv
                  (ops ++ dropVectorRootStores ops stores) #[.errorOverflow]]
              | none =>
                match ops[ops.size - 1]! with
                | .indexSetLeaf _ _ v _ _ | .indexSet _ _ v _ _ =>
                  -- 多叶 set 的返回值是 `.ok (_, y)`。循环体不要用 findOkRet。
                  let ret :=
                    if isForInStep t then v else (findOkRet env t).getD v
                  return .ok #[.ite cmp lv rv (ops.push (.okState ret)) #[.errorOverflow]]
                | _ => return .ok #[.ite cmp lv rv ops #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, some stores, _, _ =>
            return .ok #[.ite cmp lv rv (snapshotStateUpdate localDepth stores) #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, none, some v, _ =>
            return .ok #[.ite cmp lv rv #[.okState v] #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, none, none, .ok thn =>
            match decodeExpr env fuel' f (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok els => return .ok #[.ite cmp lv rv thn els]
            | .error _ => return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
          | some _, none, none, none, none, none, .error reason =>
            return .error s!"extract/unsupported: comparison continuation: {reason}"
          | _, _, _, _, _, _, _ => return .error "extract/unsupported: ite then/cmp"
        else if let some condE := findBy args (fun a => (asCheckedAddGuard env a).isSome) then
          match asCheckedAddGuard env condE, directInvoke, decodeEvmEffect env t,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars), asStoreFields env t,
              asOkState env t with
          | some (lhs, rhs), some inv, _, _, some stores, _ =>
            return .ok (#[.checkedAddU64 lhs rhs, invokeOp inv] ++ stores)
          | some _, none, some evmOps, _, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv evmOps #[.errorOverflow]]
          | some (lhs, rhs), none, none, .ok thn, _, _ =>
            -- then 支可以再套比较 / CPI。先做 checked-add，再跑内层。
            -- 内层若只是 okState，仍压成旧的三连。
            match thn.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedAddU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedAddU64 lhs rhs] ++ thn)
          | some (lhs, rhs), none, none, .error _, some stores, _ =>
            return .ok (#[.checkedAddU64 lhs rhs] ++ stores)
          | some (lhs, rhs), none, none, .error _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedAddU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, none, none, .error reason, none, none =>
            return .error s!"extract/unsupported: checked-add continuation: {reason}"
          | _, _, _, _, _, _ => return .error "extract/unsupported: ite then/add"
        else if let some condE := findBy args (fun a =>
            (asCheckedMulGuard env a).isSome && (collectIndexSets env t).isEmpty) then
          match asCheckedMulGuard env condE,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars),
              asStoreFields env t, asOkState env t with
          | some (lhs, rhs), _, some stores, _ =>
            match stores.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedMulU64 lhs rhs] ++ stores ++ #[.errorOverflow])
          | some (lhs, rhs), .ok thn, none, _ =>
            match thn.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedMulU64 lhs rhs] ++ thn ++ #[.errorOverflow])
          | some (lhs, rhs), .error _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, .error reason, none, none =>
            return .error s!"extract/unsupported: checked-mul continuation: {reason}"
          | _, _, _, _ => return .error "extract/unsupported: ite then/mul"
        else if let some condE := findBy args (fun a =>
            checkedSubMatches a && (collectIndexSets env t).isEmpty) then
          match asCheckedSubGuard env condE, directInvoke, decodeEvmEffect env t,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars),
              decodeExpr env fuel' f (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars), asStoreFields env t,
              asOkState env t with
          | some _, some inv, _, _, _, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            match invokeOpsWithRet env t inv with
            | .ok ops => return .ok #[.ite cmp lv rv ops #[.errorOverflow]]
            | .error reason => return .error reason
          | some _, none, some evmOps, _, _, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv evmOps #[.errorOverflow]]
          | some (lhs, rhs), none, none, _, .ok #[.errorOverflow], _, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedSubU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, none, none, .ok thn, .ok els, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv thn els]
          | some (lhs, rhs), none, none, _, _, some stores, _ =>
            return .ok (#[.checkedSubU64 lhs rhs] ++ stores)
          | some (lhs, rhs), none, none, _, _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedSubU64 lhs rhs, .okState dest, .errorOverflow]
          | _, _, _, _, _, _, _ => return .error "extract/unsupported: ite then/sub"
        else if let some condE := findBy args (fun a =>
            (asNeZero env a).isSome && (collectIndexSets env t).isEmpty) then
          match asNeZero env condE with
          | none => return .error "extract/unsupported: ite then"
          | some den =>
            let v := (asOkState env t).getD (.arg 0)
            let fallback := (.field (.arg 1) "value", den)
            if (lastNamedBin env ``HMod.hMod t).isSome then
              let (lhs, rhs) := (lastNamedBin env ``HMod.hMod t).getD fallback
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else if (lastNamedBin env ``UInt64.mod t).isSome then
              let (lhs, rhs) := (lastNamedBin env ``UInt64.mod t).getD fallback
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else
              let (lhs, rhs) := (lastNamedBin env ``HDiv.hDiv t).getD fallback
              return .ok #[.checkedDivU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
        else
          let condE := args[args.size - 4]!
          match asCondition env condE,
              decodeExpr env fuel' t (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth)
                (stateType? := stateType?) (deepScalars := deepScalars) with
          | some (cmp, lv, rv), .ok thn =>
            return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
          | _, _ => return .error "extract/unsupported: ite cond"
      else
        let isValueCmp (a : Expr) : Bool :=
          (asCmp env a).isSome &&
            (asCheckedAddGuard env a).isNone &&
            (asCheckedMulGuard env a).isNone &&
            !checkedSubMatches a
        if isForInYield f && !stateful then
          let some condE := findBy args isValueCmp <|> findBy args (fun a => (asCmp env a).isSome)
            | return .error s!"extract/unsupported: ite cond: {args[args.size - 4]!}"
          let some (cmp, lv, rv) := asCmp env condE
            | return .error s!"extract/unsupported: ite cond: {condE}"
          match decodeExpr env fuel' t (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars) with
          | .ok thn => return .ok #[.ite cmp lv rv thn #[]]
          | .error r => return .error s!"extract/unsupported: forBody then {r}"
        let some condE := findBy args isValueCmp <|> findBy args (fun a => (asCmp env a).isSome)
          | match asCondition env args[args.size - 4]! with
            | some condition =>
              match decodeExpr env fuel' t (stateful := stateful)
                    (preserveLocals := preserveLocals) (localDepth := localDepth)
                    (stateType? := stateType?) (deepScalars := deepScalars),
                  decodeExpr env fuel' f (stateful := stateful)
                    (preserveLocals := preserveLocals) (localDepth := localDepth)
                    (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok thn, .ok els => return .ok #[.ite condition.1 condition.2.1 condition.2.2 thn els]
              | .error r, _ =>
                return .error (if stateful then s!"state loop then: {r}" else s!"ite then: {r}")
              | _, .error r =>
                return .error (if stateful then s!"state loop else: {r}" else s!"ite else: {r}")
            | none => return .error s!"extract/unsupported: ite cond: {args[args.size - 4]!}"
        let some (cmp, lv, rv) := asCmp env condE
          | return .error s!"extract/unsupported: ite cond: {condE}"
        match decodeExpr env fuel' t (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars),
            decodeExpr env fuel' f (stateful := stateful)
              (preserveLocals := preserveLocals) (localDepth := localDepth)
              (stateType? := stateType?) (deepScalars := deepScalars) with
        | .ok thn, .ok els => return .ok #[.ite cmp lv rv thn els]
        | .error r, _ =>
          return .error (if stateful then s!"state loop then: {r}" else s!"ite then: {r}")
        | _, .error r =>
          return .error (if stateful then s!"state loop else: {r}" else s!"ite else: {r}")
    else if let some ops := decodeNearEffect env e then
      return .ok ops
    else if let some ops := decodeEvmEffect env e then
      return .ok ops
    else if let some call := decodeComponentCall env e <|> findComponentCall env 8 e then
      return .ok #[.component call, .returnU64 (.lit 0)]
    else if let some inv := decodeInvokeArgs env e <|> findInvoke env 8 e then
      return invokeOpsWithRet env e inv
    else if let some reduced := reduceUInt64NewtypeMatch? env e then
      return decodeExpr env fuel' reduced (stateful := stateful)
        (preserveLocals := preserveLocals) (localDepth := localDepth)
        (stateType? := stateType?) (deepScalars := deepScalars)
    else if isUInt64VariantMatcher env e then
      let args := e.getAppArgs
      let some matcherName := e.getAppFn.constName?
        | return .error "extract/unsupported: variant matcher name"
      let some info := Lean.Meta.getMatcherInfoCore? env matcherName
        | return .error "extract/unsupported: variant matcher metadata"
      let some variantName := matcherDiscrTypeName? env e
        | return .error "extract/unsupported: variant discriminant type"
      let some payloadWidth := uint64VariantPayloadWidth? env variantName
        | return .error "extract/unsupported: variant payload layout"
      let some disc := args[info.getFirstDiscrPos]?
        | return .error "extract/unsupported: variant discriminant"
      let tag :=
        match val env disc with
        | some (.field base name) =>
          if name.endsWith "_tag" then .field base name else .field base s!"{name}_tag"
        | some base => .field base "variant_tag"
        | none => .field (.arg 0) "variant_tag"
      let payloads : Array Ops.Val := Id.run do
        let mut payloads : Array Ops.Val := #[]
        for index in [:payloadWidth] do
          let payload :=
            match tag with
            | .field base name =>
              let root := if name.endsWith "_tag" then name.dropEnd 4 |>.copy else name
              .field base s!"{root}_p{index}"
            | _ => .field (.arg 0) s!"variant_p{index}"
          payloads := payloads.push payload
        return payloads
      let alternativesResult : Except String (Array (Array Ops.Op)) := Id.run do
        let mut alternatives : Array (Array Ops.Op) := #[]
        for index in [:info.numAlts] do
          let some altInfo := info.altInfos[index]?
            | return .error "extract/unsupported: variant alternative metadata"
          let some altExpr := args[info.getFirstAltPos + index]?
            | return .error "extract/unsupported: variant alternative"
          if altInfo.numFields > payloads.size then
            return .error "extract/unsupported: variant alternative exceeds payload layout"
          let altBody? : Option Expr := Id.run do
            let mut body := altExpr
            for fieldIndex in [:altInfo.numFields] do
              match strip body with
              | .lam _ _ lamBody _ =>
                let marker := mkApp (mkConst ``localRef) (mkNatLit (localDepth + fieldIndex))
                body := lamBody.instantiate1 marker
              | _ => return none
            return some body
          let some altBody := altBody?
            | return .error "extract/unsupported: variant alternative binders"
          -- Lean represents a nullary matcher branch as `Unit → result`; payload alternatives
          -- have already consumed their source-field binders above.
          let altBody := peelMatcherLams 8 altBody
          match decodeExpr env fuel' altBody (stateful := stateful)
              (preserveLocals := preserveLocals)
              (localDepth := localDepth + altInfo.numFields) (stateType? := stateType?)
              (deepScalars := deepScalars) with
          | .ok ops =>
            let mut withPayloads : Array Ops.Op := #[]
            for fieldIndex in [:altInfo.numFields] do
              withPayloads := withPayloads.push
                (.letLocal (localDepth + fieldIndex) payloads[fieldIndex]!)
            alternatives := alternatives.push (withPayloads ++ ops)
          | .error reason => return .error reason
        return .ok alternatives
      match alternativesResult with
      | .error reason => return .error reason
      | .ok alternatives =>
        let mut chain : Array Ops.Op := #[.errorNamed "invalidVariant"]
        for offset in [:alternatives.size] do
          let index := alternatives.size - 1 - offset
          chain := #[.ite .eq tag (.lit (UInt64.ofNat index)) alternatives[index]! chain]
        return .ok chain
    else if isOptionLikeMatcher env e && e.getAppArgs.size ≥ 3 then
      -- `match opt with | none => a | some n => b` → ite (eq tag 0) a b。
      let args := e.getAppArgs
      let disc := args[args.size - 3]!
      let noneE := peelLets args[args.size - 2]!
      let someE := peelLets args[args.size - 1]!
      let tag :=
        match val env disc with
        | some (.field b n) =>
          if n.endsWith "_tag" then .field b n else .field b s!"{n}_tag"
        | some b => .field b "slot_tag"
        | none => .field (.arg 0) "slot_tag"
      let payload :=
        match tag with
        | .field b n =>
          let base := if n.endsWith "_tag" then n.dropEnd 4 |>.copy else n
          .field b s!"{base}_p0"
        | _ => .field (.arg 0) "slot_p0"
      let noneBody := peelMatcherLams 8 noneE
      match decodeExpr env fuel' noneBody (stateful := stateful)
          (preserveLocals := preserveLocals) (localDepth := localDepth)
          (stateType? := stateType?) (deepScalars := deepScalars) with
      | .error r => return .error r
      | .ok noneOps =>
        match strip someE with
        | .lam _ _ body _ =>
          match strip body with
          | .bvar 0 =>
            return .ok #[.ite .eq tag (.lit 0) noneOps #[.returnU64 payload]]
          | _ =>
            let marker := mkApp (mkConst ``localRef) (mkNatLit localDepth)
            let someBody := peelMatcherLams 8 (body.instantiate1 marker)
            match decodeExpr env fuel' someBody (stateful := stateful)
                (preserveLocals := preserveLocals) (localDepth := localDepth + 1)
                (stateType? := stateType?) (deepScalars := deepScalars) with
            | .ok someOps =>
              return .ok #[.ite .eq tag (.lit 0) noneOps
                (#[.letLocal localDepth payload] ++ someOps)]
            | .error r => return .error r
        | _ =>
          let someBody := peelMatcherLams 8 someE
          let someOps :=
            match strip someBody with
            | .bvar _ => #[.returnU64 payload]
            | _ =>
              match decodeExpr env fuel' someBody (stateful := stateful)
                  (preserveLocals := preserveLocals) (localDepth := localDepth)
                  (stateType? := stateType?) (deepScalars := deepScalars) with
              | .ok ops =>
                match ops with
                | #[.returnU64 (.arg _)] => #[.returnU64 payload]
                | #[.returnState (.arg _)] => #[.returnU64 payload]
                | _ => ops
              | .error _ => #[.returnU64 payload]
          return .ok #[.ite .eq tag (.lit 0) noneOps someOps]
    else
      return decodePlain env e stateful localDepth stateType? deepScalars


end ProofForge.Extract
