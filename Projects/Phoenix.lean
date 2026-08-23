import ProofForge

/-!
Phoenix v1 在本仓剖面下的第四刀：4 档 ask + 官方吃单顺序。

官方 FIFO 吃单从最优档开始，允许部分成交，不会跳档。
这里档 0 是最优 ask。`swapBuy` 只打档 0：`want ≤ size` 整档减，
否则吃光档 0。跨档、限价进链上入口、u128 费用仍关。

官方还有 ReduceOrder / CancelOrder。这里用 `reduceAsk` / `cancelAsk`
钉同一语义：减档 0，减到 0 就是撤。
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

/-- 费用按 bps 收。不是官方 u128 四舍五入。 -/
def feeBps : UInt64 := 5

def feeOf (qty : UInt64) : UInt64 :=
  qty * feeBps / 10000

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
IOC 买，官方顺序：只打最优档（档 0），且 `want ≤ sizes[0]`。
装不下或档 0 空则 overflow，不会跳到档 1。
部分成交 / 撤单是宿主函数。成交走 Token TransferChecked。
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

/-- 官方部分成交：吃光档 0。档 0 空则 overflow。 -/
def sweepAsk (s : State) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .error .overflow
  else if s.baseFree ≤ u64Max - s.sizes[0]! then
    let _ := tokenTransferChecked s.sizes[0]! 6
    .ok ({ s with
            sizes := s.sizes.set 0 (s.sizes[0]! - s.sizes[0]!)
            baseFree := s.baseFree + s.sizes[0]! }, s.sizes[0]!)
  else
    .error .overflow

/-- 官方 ReduceOrder：只减档 0，且 `qty ≤ sizes[0]`。超额 overflow。 -/
@[pf_entry]
def reduceAsk (s : State) (qty : UInt64) : Except Error (State × UInt64) :=
  if qty ≤ s.sizes[0]! then
    .ok ({ s with sizes := s.sizes.set 0 (s.sizes[0]! - qty) }, qty)
  else
    .error .overflow

/-- 官方 CancelOrder：撤档 0。空档 overflow。抽出还认不了 `size - size`。 -/
def cancelAsk (s : State) : Except Error (State × UInt64) :=
  if s.sizes[0]! = 0 then
    .error .overflow
  else
    .ok ({ s with sizes := s.sizes.set 0 (s.sizes[0]! - s.sizes[0]!) }, s.sizes[0]!)

/-- UInt64 bps 费用。宿主侧可算；抽出还认不了 `qty * 5 / 10000`。 -/
def takeFee (qty : UInt64) : UInt64 :=
  if qty = 0 then 0 else qty * feeBps / 10000

/-- 限价：`limit < askPrice` 不成交。宿主侧可算。 -/
def checkLimit (s : State) (limit : UInt64) : Bool :=
  limit ≥ s.askPrice

/-- TIF：`deadline = 0` 不过期。宿主侧可算。 -/
def checkTif (deadline : UInt64) : Bool :=
  deadline = 0 || unixTime < deadline

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
