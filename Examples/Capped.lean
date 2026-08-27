import ProofForge

namespace Examples.Capped

open ProofForge.Evm.Sdk

/-- paused 是 UInt8（0 运行，1 暂停）；cap / supply 是账户里的 UInt256。
    owner 是构造期 immutable。没有 hashed map。 -/
structure State where
  paused : UInt8
  cap : UInt256
  supply : UInt256
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_owner : Address) : State :=
  { paused := 0, cap := ⟨100, 0, 0, 0⟩, supply := UInt256.zero }

/-- 只有构造期 owner 能加 supply。
    非 owner → `Unauthorized(caller)`；paused → `Paused()`；
    `supply + v` 超过 cap → `CapExceeded()`。 -/
@[pf_entry]
def mint (s : State) (value : UInt256) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if s.paused != 0 then
      .ok ({ paused := s.paused, cap := s.cap, supply := s.supply },
        Revert.paused)
    else if UInt256.atLeast s.cap (UInt256.add s.supply value) then
      if (0 : UInt64) ≠ 1 then
        .ok ({ paused := s.paused, cap := s.cap,
               supply := UInt256.add s.supply value },
          value.w0)
      else
        .error .overflow
    else
      .ok ({ paused := s.paused, cap := s.cap, supply := s.supply },
        Revert.capExceeded)
  else
    .ok ({ paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.unauthorized Context.caller)

/-- 只有构造期 owner 能暂停。非 owner → `Unauthorized(caller)`。 -/
@[pf_entry]
def pause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if (0 : UInt64) ≠ 1 then
      .ok ({ paused := 1, cap := s.cap, supply := s.supply }, 1)
    else
      .error .overflow
  else
    .ok ({ paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.unauthorized Context.caller)

/-- 只有构造期 owner 能恢复。非 owner → `Unauthorized(caller)`。 -/
@[pf_entry]
def unpause (s : State) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if (0 : UInt64) ≠ 1 then
      .ok ({ paused := 0, cap := s.cap, supply := s.supply }, 0)
    else
      .error .overflow
  else
    .ok ({ paused := s.paused, cap := s.cap, supply := s.supply },
      Revert.unauthorized Context.caller)

@[pf_entry]
def pausedOf (s : State) : UInt8 :=
  s.paused

@[pf_entry]
def capOf (s : State) : UInt256 :=
  s.cap

@[pf_entry]
def totalSupply (s : State) : UInt256 :=
  s.supply

@[pf_entry]
def ownerOf (_s : State) : Address :=
  Immutable.address

end Examples.Capped
