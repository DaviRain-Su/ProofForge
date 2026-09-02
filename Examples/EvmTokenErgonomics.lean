import ProofForge

namespace Examples.EvmTokenErgonomics

open ProofForge.Evm.Sdk

/-!
# Sequential CallResult surface (`erg-evm-effect-001`)

Demonstrates `Effect.ensure` / `Effect.abort` for fail-closed Bool ABI methods
without nested `if`/`else` ladders. Soft reverts stay `.ok (state, Bool)` (R5-012);
hard failures remain `Except.error`. Full `Examples.Token` migration stays a
follow-up so existing supply-preservation proofs remain untouched.
-/

structure State where
  paused : UInt8
  flag : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[reducible, pf_inline] private def hold (s : State) : State :=
  { paused := s.paused, flag := s.flag }

@[pf_entry]
def init (_seed : UInt64) : State :=
  { paused := Pausable.running, flag := 0 }

@[pf_entry]
def flagOf (s : State) : UInt64 :=
  s.flag

/-- Pause-gated approve-shaped Bool method: sequential `Effect.ensure` gates. -/
@[pf_entry]
def approve (s : State) (spender : Address) (amount : UInt256) :
    Except Error (State × Bool) :=
  Effect.ensure (Access.requireRunning s.paused) (hold s) Access.runningViolation fun _ =>
  Effect.ensure (!Address.isZero spender) (hold s) Revert.zeroAddress fun _ =>
  if (0 : UInt64) ≠ 1 then
    .ok ({ paused := s.paused, flag := amount.w0 },
      Effect.thenTrue (Event.approval Context.caller spender amount))
  else
    .error .overflow

/-- Pause-gated transfer-shaped Bool method: sequential gates then a nonzero-limb check. -/
@[pf_entry]
def transfer (s : State) (destination : Address) (amount : UInt256) :
    Except Error (State × Bool) :=
  Effect.ensure (Access.requireRunning s.paused) (hold s) Access.runningViolation fun _ =>
  Effect.ensure (!Address.isZero destination) (hold s) Revert.zeroAddress fun _ =>
  Effect.ensure (amount.w0 ≠ 0) (hold s)
      (Revert.insufficient ⟨0, 0, 0, 0⟩ amount) fun _ =>
  if (0 : UInt64) ≠ 1 then
    .ok ({ paused := s.paused, flag := amount.w0 },
      Effect.thenTrue (Event.transfer Context.caller destination amount))
  else
    .error .overflow

end Examples.EvmTokenErgonomics
