import ProofForge
import Examples.MultiToken
import Examples.CraftToken

/-!
EVM-SDK-8 focused suite: bounded ERC-1155 key envelope, predicate surface, and two independent
consumers with stable extracted digests. Live mint/burn/transfer/operator matrices live in
`runtime-tests/evm/anvil_multitoken.sh` and `anvil_crafttoken.sh`; the aggregate EVM gate builds and
runs both consumers.
-/

namespace Tests.EvmErc1155Spec

open ProofForge.Evm
open ProofForge.Evm.Sdk
open Lean Elab Command

namespace UnsupportedConditionFixture

structure State where
  value : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

/-- An unmarked host definition is not an extraction contract and must never be constant-folded. -/
@[irreducible] def hostPredicate (_value : UInt64) : Bool := true

@[pf_entry] def init (value : UInt64) : State := ⟨value⟩

@[pf_entry] def guarded (state : State) (value : UInt64) : Except Error State :=
  if hostPredicate value then .ok ⟨value⟩ else .ok state

end UnsupportedConditionFixture

-- Key envelope: only ids with a zero top limb are encodable; tokenKey truncates, so every
-- consumer path must gate first.
#guard Erc1155.canEncode ⟨1, 0, 0, 0⟩
#guard Erc1155.canEncode ⟨0, 1, 0, 0⟩
#guard Erc1155.canEncode ⟨0, 0, 1, 0⟩
#guard !Erc1155.canEncode ⟨0, 0, 0, 1⟩
#guard !Erc1155.canEncode ⟨1, 0, 0, 1⟩
#guard Erc1155.tokenKey ⟨7, 8, 9, 0⟩ == (⟨7, 8, 9⟩ : Address)
#guard Erc1155.tokenKey ⟨7, 8, 9, 1⟩ == (⟨7, 8, 9⟩ : Address)

def specBalances : Erc1155.Balances := Storage.Layout.root.addressPairMap256.handle
def specOperators : Erc1155.Operators :=
  Storage.Layout.root.addressPairMap256.next.addressPairMap.handle
def specOwner : Address := ⟨1, 2, 3⟩
def specOther : Address := ⟨4, 5, 6⟩
def specId : UInt256 := ⟨7, 0, 0, 0⟩
def specAliasId : UInt256 := ⟨7, 0, 0, 1⟩
def specAmount : UInt256 := ⟨9, 0, 0, 0⟩

-- Disjoint compile-time namespaces for both consumers.
#guard Examples.MultiToken.balances.base == 0
#guard Examples.MultiToken.operators.base == 1
#guard Examples.CraftToken.balances.base == 0
#guard Examples.CraftToken.operators.base == 1
#guard Examples.CraftToken.supply.base == 2
#guard Examples.CraftToken.maxPerId == (⟨1000, 0, 0, 0⟩ : UInt256)

-- The SDK-owned checked view rejects an unencodable alias before its hashed-map read.
-- `canEncode` is honest Bool arithmetic, so these guards are kernel-checkable on host; the
-- hashed-map load itself host-evaluates to zero (empty map).
#guard Examples.MultiToken.balanceOf ⟨0⟩ specOwner specId == UInt256.zero
#guard Examples.MultiToken.balanceOf ⟨0⟩ specOwner specAliasId == UInt256.zero
#guard Examples.CraftToken.balanceOf ⟨0⟩ specOwner specAliasId == UInt256.zero
#guard Examples.CraftToken.supplyOf ⟨0⟩ specAliasId == UInt256.zero

-- Pre-write/pre-auth envelope gates: unencodable ids fail every mutation and authorization
-- predicate. These guards are honest on host because `canEncode` is the first `&&` conjunct and
-- short-circuits before the comparison leaves. Positive encodable-id predicate semantics are NOT
-- host-checkable: `Runtime.evmGe256`/`evmEq20` are placeholder constants (`true`) whose real
-- behavior is an extraction contract, covered end-to-end by the Anvil fixtures.
#guard !Erc1155.Balances.canCredit specBalances specOwner specAliasId specAmount
#guard !Erc1155.Balances.canDebit specBalances specOwner specAliasId specAmount
#guard !Erc1155.Balances.canTransfer specBalances specOwner specOther specAliasId specAmount
#guard !Erc1155.canMint specBalances specOwner specAliasId specAmount
#guard !Erc1155.canBurn specBalances specOwner specAliasId specAmount
#guard !Erc1155.isApprovedOrOwner specOperators specOwner specOwner specAliasId
#guard !Erc1155.isApprovedOrOwner specOperators specOther specOwner specAliasId

/-- Compile-time surface check for the checked mint/burn/transfer branches. Map/comparison
Runtime leaves are extraction contracts and are not assigned host-evaluation semantics. -/
def erc1155TransferSurface (source to : Address) (tokenId amount : UInt256) : UInt64 :=
  if Erc1155.Balances.canTransfer specBalances source to tokenId amount then
    Erc1155.Balances.transfer specBalances source to tokenId amount
  else
    0

private partial def valContainsBalanceRead : ProofForge.Extract.IR.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => valContainsBalanceRead base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valContainsBalanceRead lhs || valContainsBalanceRead rhs
  | .indexGet base _ idx _ _ =>
      valContainsBalanceRead base || valContainsBalanceRead idx
  | .select _ lhs rhs thn els =>
      valContainsBalanceRead lhs || valContainsBalanceRead rhs ||
        valContainsBalanceRead thn || valContainsBalanceRead els
  | .ext kind operands =>
      (match kind with
        | .evm (.component (.hashedMap (.getPair256 _))) => true
        | _ => false) || operands.any valContainsBalanceRead

private def opValues : ProofForge.Extract.IR.Op → Array ProofForge.Extract.IR.Val
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value => #[value]
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs => #[lhs, rhs]
  | .ite _ lhs rhs _ _ => #[lhs, rhs]
  | .indexSetLeaf _ idx value _ _ | .indexSet _ idx value _ _ => #[idx, value]
  | .ext payload => ProofForge.Extract.IR.OpExt.values payload
  | .joinLocal _ | .forBody _ _ | .errorOverflow | .errorNamed _ => #[]

private partial def opsContainBalanceRead (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.any fun op =>
    (opValues op).any valContainsBalanceRead || match op with
      | .ite _ _ _ thn els => opsContainBalanceRead thn || opsContainBalanceRead els
      | .forBody _ body => opsContainBalanceRead body
      | _ => false

/-- A checked SDK view must not evaluate a truncated hashed-map key before entering its gate. -/
private partial def balanceReadsAreGuarded
    (ops : Array ProofForge.Extract.IR.Op) (guarded := false) : Bool :=
  ops.all fun op =>
    (guarded || !(opValues op).any valContainsBalanceRead) && match op with
      | .ite _ _ _ thn els =>
          balanceReadsAreGuarded thn true && balanceReadsAreGuarded els true
      | .forBody _ body => balanceReadsAreGuarded body guarded
      | _ => true

private partial def hasControlFlow (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.any fun op => match op with
    | .ite _ _ _ _ _ => true
    | .forBody _ body => hasControlFlow body
    | _ => false

private partial def valContainsNamedCapComparison : ProofForge.Extract.IR.Val → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => false
  | .field base _ | .bitNot base => valContainsNamedCapComparison base
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      valContainsNamedCapComparison lhs || valContainsNamedCapComparison rhs
  | .indexGet base _ idx _ _ =>
      valContainsNamedCapComparison base || valContainsNamedCapComparison idx
  | .select _ lhs rhs thn els =>
      valContainsNamedCapComparison lhs || valContainsNamedCapComparison rhs ||
        valContainsNamedCapComparison thn || valContainsNamedCapComparison els
  | .ext (.evm (.component (.wideWord .ge256))) operands =>
      operands.size == 8 && operands[0]! == .lit 1000 && operands[1]! == .lit 0 &&
        operands[2]! == .lit 0 && operands[3]! == .lit 0
  | .ext _ operands => operands.any valContainsNamedCapComparison

/-- The application-owned named `UInt256` cap must remain a real packed comparison condition. -/
private partial def hasNamedCapGate (ops : Array ProofForge.Extract.IR.Op) : Bool :=
  ops.any fun op => match op with
    | .ite .ne lhs (.lit 0) thn els =>
        valContainsNamedCapComparison lhs || hasNamedCapGate thn || hasNamedCapGate els
    | .ite _ _ _ thn els => hasNamedCapGate thn || hasNamedCapGate els
    | .forBody _ body => hasNamedCapGate body
    | _ => false

private def expectDigest (moduleName : Name) (digest : String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env moduleName with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  unless IR.digestHex program == digest do
    throwError s!"{moduleName} digest drifted: {IR.digestHex program}"

private def expectErc1155 : CommandElabM Unit := do
  expectDigest `Examples.MultiToken "1b6452b87efd2019"
  expectDigest `Examples.CraftToken "5e5565fbbc6d9de2"
  let env ← getEnv
  let multi := (ProofForge.Extract.extractModuleIR env `Examples.MultiToken).toOption.get!
  let balanceOps := (multi.methods.find? (·.ixName == "balanceOf")).get!.ops
  unless hasControlFlow balanceOps && opsContainBalanceRead balanceOps &&
      balanceReadsAreGuarded balanceOps do
    throwError "MultiToken.balanceOf: checked SDK view lost its pre-read key-envelope gate"
  let craft := (ProofForge.Extract.extractModuleIR env `Examples.CraftToken).toOption.get!
  let mintOps := (craft.methods.find? (·.ixName == "mint")).get!.ops
  unless hasNamedCapGate mintOps do
    throwError "CraftToken.mint: named UInt256 maxPerId did not remain a packed comparison gate"
  match ProofForge.Extract.extractModuleIR env `Tests.EvmErc1155Spec.UnsupportedConditionFixture with
  | .error _ => pure ()
  | .ok _ =>
      throwError "unsupported unmarked Bool condition was unsafely host-folded during extraction"

elab "#pf_guard_evm_erc1155" : command => expectErc1155

#pf_guard_evm_erc1155

end Tests.EvmErc1155Spec
