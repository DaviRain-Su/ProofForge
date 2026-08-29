namespace ProofForge.Evm.CallResult

/-!
Target-local typed result contract for one closed external call (EVM-RT-2a).

This module is the plan layer of the shared call-result policy. It names the established
returndata gates that used to be inlined per call site in `Evm.ClosedCall.Emit`:

- `Policy.canonicalTrueOrCodeBackedEmpty` — the safe ERC-20 mutation rule: the CALL must succeed;
  returndata is either exactly one canonical ABI `true` word, or empty while the target still has
  runtime code after the call;
- `Policy.exactWord` — an exact-one-word STATICCALL read: the call must succeed and returndata
  must be exactly one 32-byte word, which is handed to the caller;
- `Policy.contractSuccess` — the call must succeed; returndata is not copied or consumed, and an
  empty result is accepted only while the target still has runtime code after the call.

Every policy keeps returndata bounded to one 32-byte word (`Policy.retBound ≤ 32`) and fails
closed on call failure and on any shape the policy does not name. Calldata always starts at
memory offset 0, returndata is always copied to memory offset 0, msg.value never rides a
STATICCALL, and no policy opens arbitrary callee selection, delegatecall/create, or returndata
beyond one word. `Evm.CallResult.Emit` is the sole interpreter; `Evm.ClosedCall.Emit` consumes it
so all closed ERC-20 / WETH / Uniswap / permit call sites share one gate spelling.
-/

/-- Opcode family of one closed external call. -/
inductive Kind where
  | call
  | staticcall
  deriving BEq, Repr, Inhabited

def abiWordBytes : Nat := 32

/-- Typed result contract applied to the returndata of one closed external call. -/
inductive Policy where
  /-- Safe ERC-20 compatibility rule: CALL must succeed; returndata is either exactly one word
  equal to canonical ABI `true` (`1`), or empty while the target has runtime code after the call.
  This rejects EOAs/nonexistent targets whose CALL otherwise reports success with empty data. -/
  | canonicalTrueOrCodeBackedEmpty
  /-- Exact-one-word read: the call must succeed and returndata must be exactly one 32-byte
  word; the word is bound for the caller. Any other length reverts. -/
  | exactWord
  /-- Contract success: the call must succeed and returndata is ignored. Empty returndata also
  requires runtime code at the target after the call, so an EOA cannot masquerade as a contract. -/
  | contractSuccess
  deriving BEq, Repr, Inhabited

/-- Bytes of returndata copied to memory offset 0. Bounded to one 32-byte word. -/
def Policy.retBound : Policy → Nat
  | .canonicalTrueOrCodeBackedEmpty | .exactWord => abiWordBytes
  | .contractSuccess => 0

/-- One closed external call together with its typed result contract. Calldata occupies
`memory[0, inSize)`; returndata is copied to `memory[0, retBound)`. `value` marks a CALL that
carries msg.value (the value expression is supplied at emission); it is never valid on a
STATICCALL. -/
structure Request where
  kind : Kind
  inSize : Nat
  policy : Policy
  value : Bool := false
  deriving BEq, Repr, Inhabited

/-- Returndata bytes copied by this request. -/
def Request.retBound (request : Request) : Nat :=
  request.policy.retBound

/-- Fail-closed shape gate: returndata stays within one 32-byte word and msg.value never rides
a STATICCALL. -/
def Request.wellFormed (request : Request) : Bool :=
  request.retBound ≤ abiWordBytes && (!request.value || request.kind == .call)

/-- Safe ERC-20 compatibility rule: CALL must succeed and returndata is either exactly canonical
ABI `true`, or empty with runtime code still present at the target after the call. -/
def Request.erc20Mutation (inSize : Nat) : Request :=
  { kind := .call, inSize, policy := .canonicalTrueOrCodeBackedEmpty }

/-- Exact-one-word STATICCALL read: the call must succeed and returndata must be exactly one
32-byte word. -/
def Request.staticWord (inSize : Nat) : Request :=
  { kind := .staticcall, inSize, policy := .exactWord }

/-- Contract-success CALL: returndata is not copied or consumed; an empty result additionally
requires runtime code at the target after the call. -/
def Request.successOnly (inSize : Nat) (value : Bool := false) : Request :=
  { kind := .call, inSize, policy := .contractSuccess, value }

end ProofForge.Evm.CallResult
