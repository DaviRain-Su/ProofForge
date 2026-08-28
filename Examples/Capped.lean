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
  { paused := Pausable.running, cap := ⟨100, 0, 0, 0⟩, supply := UInt256.zero }

/-- 只有构造期 owner 能加 supply。
    非 owner → `Unauthorized(caller)`；paused → `Paused()`；
    `supply + v` 超过 cap → `CapExceeded()`。 -/
@[pf_entry]
def mint (s : State) (value : UInt256) : Except Error (State × UInt64) :=
  if Address.eqImmutable Context.caller then
    if s.paused != Pausable.running then
      .ok ({ paused := s.paused, cap := s.cap, supply := s.supply },
        Access.runningViolation)
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
      .ok ({ paused := Pausable.pause s.paused, cap := s.cap, supply := s.supply }, 1)
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
      .ok ({ paused := Pausable.unpause s.paused, cap := s.cap, supply := s.supply }, 0)
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

section Proofs

/-! ## 第一批 kernel 证明：Capped mint 的 cap 不变量与 supply 效应

对上面 `@[pf_entry]` 函数的普通 kernel-checked 性质；证明不依赖运行时值
（`Context.caller` 是不透明运行时值，所以结论是全路径的）。 -/

/-- **cap 不变量**：只要进入时 `supply ≤ cap`（用 `atLeast` 表示），mint 的
任何返回结果（含各 revert 路径）都保持 `supply ≤ cap`。 -/
theorem mint_supply_within_cap (s : State) (v : UInt256) {t : State} {r : UInt64}
    (hcap : UInt256.atLeast s.cap s.supply = true)
    (h : mint s v = .ok (t, r)) :
    UInt256.atLeast t.cap t.supply = true := by
  unfold mint at h
  split at h
  · split at h
    · rename_i _hp
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact hcap
    · rename_i _hp
      split at h
      · rename_i hc
        split at h
        · simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact hc
        · simp at h
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact hcap
  · simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact hcap

/-- **supply 效应**：mint 要么不动 supply，要么恰好加上 `v`（不会减）。 -/
theorem mint_supply_effect (s : State) (v : UInt256) {t : State} {r : UInt64}
    (h : mint s v = .ok (t, r)) :
    t.supply = s.supply ∨ t.supply = UInt256.add s.supply v := by
  unfold mint at h
  split at h
  · split at h
    · simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl rfl
    · split at h
      · rename_i _hc
        split at h
        · simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr rfl
        · simp at h
      · simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl rfl
  · simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl rfl

end Proofs

end Examples.Capped
