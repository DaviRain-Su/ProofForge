namespace ProofForge.Evm.Precompile

/-!
Target-local typed plan for the closed ecrecover precompile contract (EVM-RT-2d).

This module is the plan layer of the single precompile the closed runtime uses: the EIP-2612
permit path in `Evm.ClosedCall.Emit` recovers the signer with a STATICCALL to the ecrecover
precompile. The plan names the exact contract that used to be inlined at that one site:

- `ecrecoverAddress = 1` — the fixed precompile address; no other address is expressible;
- `ecrecoverInputBytes = 128` — the fixed input frame `hash ‖ v ‖ r ‖ s` at `memory[0, 128)`
  (the caller owns frame construction; the plan pins only its length);
- `ecrecoverOutputBytes = 32` — the fixed output word copied to `memory[0, 32)`;
- `requireSuccess` — the STATICCALL must succeed;
- `requireExactOutput` — returndata must be exactly one 32-byte word;
- `requireNonzeroResult` — the recovered address word must be nonzero.

Returndata semantics justify the exact-size gate: on a valid signature ecrecover always
returns exactly one left-padded 32-byte address word; on an invalid signature (non-27/28 `v`
or out-of-range `r`/`s`) the call succeeds with empty returndata. Accepting any other length
would fail open on stale output memory, so exact 32 is the only sound contract. The nonzero
gate names the established zero-signer rejection (ecrecover never returns a zero address on
success, so this is belt-and-braces fail-closed).

`Plan.wellFormed` is the fail-closed shape gate: any deviation in address, input/output
geometry, or a missing check rejects before Yul is rendered. `Evm.Precompile.Emit` is the
sole interpreter; it renders the STATICCALL, success, and exact-word gates through the shared
`Evm.CallResult.Emit` interpreter so those spellings stay single-sourced, and appends the
nonzero gate itself. This is a closed runtime capability, not a source opcode: no plan opens
arbitrary precompile addresses, arbitrary STATICCALL, delegatecall, create, or unbounded
returndata, and no Ops/IR/source vocabulary is added.
-/

/-- Fixed address of the ecrecover precompile. -/
def ecrecoverAddress : Nat := 1

/-- Fixed ecrecover input frame: 32-byte hash, v, r, s words at `memory[0, 128)`. -/
def ecrecoverInputBytes : Nat := 128

/-- Fixed ecrecover output: one left-padded 32-byte address word at `memory[0, 32)`. -/
def ecrecoverOutputBytes : Nat := 32

/-- Typed contract for one ecrecover STATICCALL. The three `require*` flags name the
fail-closed gates; a well-formed plan must pin the exact address, frame, and output geometry
and must carry every gate. -/
structure Plan where
  address : Nat
  inputBytes : Nat
  outputBytes : Nat
  requireSuccess : Bool
  requireExactOutput : Bool
  requireNonzeroResult : Bool
  deriving BEq, Repr, Inhabited

/-- Fail-closed shape gate: only the exact ecrecover contract above is well-formed. Any other
address, input/output size, or a missing success/exact-size/nonzero check is rejected before
rendering. -/
def Plan.wellFormed (plan : Plan) : Bool :=
  plan.address == ecrecoverAddress &&
    plan.inputBytes == ecrecoverInputBytes &&
    plan.outputBytes == ecrecoverOutputBytes &&
    plan.requireSuccess && plan.requireExactOutput && plan.requireNonzeroResult

/-- The one established plan: the permit ecrecover recovery. -/
def Plan.ecrecover : Plan :=
  { address := ecrecoverAddress
    inputBytes := ecrecoverInputBytes
    outputBytes := ecrecoverOutputBytes
    requireSuccess := true
    requireExactOutput := true
    requireNonzeroResult := true }

end ProofForge.Evm.Precompile
