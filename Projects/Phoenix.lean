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

/-- 挂到档 0。已有挂单则拒绝。多档扫描下一刀补循环改状态。 -/
@[pf_entry]
def postAsk (s : State) (size : UInt64) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .ok ({ s with sizes := s.sizes.set 0 size }, size)
  else
    .error .overflow

/-- 挂到档 1。档 1 必须空。 -/
@[pf_entry]
def postAsk1 (s : State) (size : UInt64) : Except Error (State × UInt64) :=
  if s.sizes[1]! = 0 then
    .ok ({ s with sizes := s.sizes.set 1 size }, size)
  else
    .error .overflow

/--
IOC 买档 0：`want ≤ sizes[0]` 且 `baseFree` 不溢出。
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
    else
      .error .overflow
  else
    .error .overflow

/-- IOC 买档 1。 -/
@[pf_entry]
def swapBuy1 (s : State) (want : UInt64) : Except Error (State × UInt64) :=
  if s.baseFree ≤ u64Max - want then
    if want ≤ s.sizes[1]! then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              sizes := s.sizes.set 1 (s.sizes[1]! - want)
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
  s.sizes[0]!

@[pf_entry]
def makerBase (s : State) : UInt64 :=
  s.baseFree

@[pf_entry]
def level0 (s : State) : UInt64 :=
  s.sizes[0]!

end Projects.Phoenix
