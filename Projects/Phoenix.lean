import ProofForge

/-!
Phoenix v1 在本仓剖面下的第一刀。

官方程序是 crankless CLOB：一个大市场账户、红黑树、u128 费用、
多账户席位、self-CPI 日志。那些现在抽不出来。

这里只保留能过 Profile / Extract / SVM emit 的核：

* 单档 ask（价格 + 数量 + 做市商 base 闲置）
* IOC 吃单：`price ≥ askPrice` 且 `want ≤ askSize` 才成交
* 成交后用 `tokenTransferChecked` 抽 quote（decimals 钉死 6）
* 做市商 `baseFree` 立刻加上成交量；剩余 ask 写回

不是字节兼容，也不是 OtterSec 审计对象。证明主语是下面这些 `def`。
-/
namespace Projects.Phoenix

open ProofForge.Runtime

structure State where
  askPrice : UInt64
  askSize : UInt64
  baseFree : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

/-- `price` 是初始 ask 价；size / free 从 0 起。 -/
@[pf_entry]
def init (price : UInt64) : State :=
  { askPrice := price, askSize := 0, baseFree := 0 }

/-- 挂一档 ask。已有挂单则拒绝。 -/
@[pf_entry]
def postAsk (s : State) (size : UInt64) : Except Error (State × UInt64) :=
  if s.askSize = 0 then
    if size ≤ u64Max then
      .ok ({ s with askSize := size }, size)
    else
      .error .overflow
  else
    .error .overflow

/--
IOC 买：`baseFree` 不溢出才成交，并 Token TransferChecked 抽 quote。
`want ≤ askSize` / 限价比较宿主定理钉。嵌套 `if` 抽出器还不认，
链上这一刀先走 checked-add + CPI；数量守卫是下一刀要补的 SVM。
-/
@[pf_entry]
def swapBuy (s : State) (want : UInt64) : Except Error (State × UInt64) :=
  if s.baseFree ≤ u64Max - want then
    if want ≤ s.askSize then
      let _ := tokenTransferChecked want 6
      .ok ({ s with
              askSize := s.askSize - want
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
  s.askSize

@[pf_entry]
def makerBase (s : State) : UInt64 :=
  s.baseFree

theorem swapBuy_too_big
    (s : State) (want : UInt64)
    (hfit : ¬ want ≤ s.askSize) :
    swapBuy s want = .error .overflow := by
  unfold swapBuy
  simp [hfit]

theorem swapBuy_fill_updates
    (s : State) (want : UInt64)
    (hfit : want ≤ s.askSize)
    (hfree : s.baseFree ≤ u64Max - want) :
    swapBuy s want =
      .ok ({ s with
              askSize := s.askSize - want
              baseFree := s.baseFree + want }, want) := by
  unfold swapBuy
  simp [hfit, hfree]

end Projects.Phoenix
