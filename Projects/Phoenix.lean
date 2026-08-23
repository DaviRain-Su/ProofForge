import ProofForge

/-!
Phoenix v1 在本仓剖面下的第二刀：固定 4 档 ask 书。

官方是红黑树 + u128 费用 + 席位 PDA。这里用 `Vector UInt64 4`
表示同一价上的 4 个数量槽（空档 = 0）。吃单从 0 扫到 3，
碰到第一档非空且 `want ≤ size` 就成交。

限价仍是市场统一 `askPrice`。多价档 / 自成交 / TIF 下一刀。
-/
namespace Projects.Phoenix

open ProofForge.Runtime

structure State where
  askPrice : UInt64
  sizes : Vector UInt64 4
  baseFree : UInt64
  deriving Repr, DecidableEq

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (price : UInt64) : State :=
  { askPrice := price, sizes := #v[0, 0, 0, 0], baseFree := 0 }

/-- 挂到第一档空位。四档都满则 overflow。 -/
@[pf_entry]
def postAsk (s : State) (size : UInt64) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .ok ({ s with sizes := s.sizes.set 0 size }, size)
  else if s.sizes[1]! = 0 then
    .ok ({ s with sizes := s.sizes.set 1 size }, size)
  else if s.sizes[2]! = 0 then
    .ok ({ s with sizes := s.sizes.set 2 size }, size)
  else if s.sizes[3]! = 0 then
    .ok ({ s with sizes := s.sizes.set 3 size }, size)
  else
    .error .overflow

/--
IOC 买：从档 0 扫到 3。第一档 `want ≤ size` 且 `baseFree` 不溢出才成交。
成交走 Token TransferChecked（decimals=6）。
-/
@[pf_entry]
def swapBuy (s : State) (want : UInt64) : Except Error (State × UInt64) :=
  if s.baseFree ≤ u64Max - want then
    if want ≤ s.sizes[0]! then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              sizes := s.sizes.set 0 (s.sizes[0]! - want)
              baseFree := s.baseFree + want }, want)
    else if want ≤ s.sizes[1]! then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              sizes := s.sizes.set 1 (s.sizes[1]! - want)
              baseFree := s.baseFree + want }, want)
    else if want ≤ s.sizes[2]! then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              sizes := s.sizes.set 2 (s.sizes[2]! - want)
              baseFree := s.baseFree + want }, want)
    else if want ≤ s.sizes[3]! then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              sizes := s.sizes.set 3 (s.sizes[3]! - want)
              baseFree := s.baseFree + want }, want)
    else
      .error .overflow
  else
    .error .overflow

@[pf_entry]
def bestAsk (s : State) : UInt64 :=
  s.askPrice

@[pf_entry]
def askQty (s : State) : UInt64 :=
  s.sizes[0]! + s.sizes[1]! + s.sizes[2]! + s.sizes[3]!

@[pf_entry]
def makerBase (s : State) : UInt64 :=
  s.baseFree

@[pf_entry]
def level0 (s : State) : UInt64 :=
  s.sizes[0]!

end Projects.Phoenix
