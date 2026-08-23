import ProofForge

/-!
Phoenix v1 在本仓剖面下的第三刀：4 档 ask + 限价 / TIF / 部分成交 / UInt64 费用。

官方是红黑树 + u128 费用 + 席位 PDA + 双 vault。这里仍用
`Vector UInt64 4` 表示同一价上的 4 个数量槽。循环改状态
（`forBody`）已开，但 Phoenix 入口还用展开的 4 路 `ite`，
等抽出器能区分循环 binder 和外层参数后再收成 `for`。

席位 / 双 vault 初始化是独立入口，不跟挂单/吃单混在一个
Program 里（CPI 账户表不同，不能抬高 `cpiAccountCount`）。
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
IOC 买：第一档有货且 `want ≤ size` 才整档成交。部分成交 /
跨档扫书等 `forBody` 抽出器能认循环 binder 后再开。
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
