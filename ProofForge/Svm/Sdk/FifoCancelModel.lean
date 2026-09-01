import ProofForge.Svm.Sdk.OrderedMapModel
import ProofForge.Svm.Sdk.StorageModel

/-!
# FifoCancel model (sf-012) — bounded cancel fold

Pure L2 algebra for one ordered FIFO side’s cancel loop. Matches the
`FifoCancel.cancelUpTo` control skeleton (search/cancel budgets, owner filter,
fail-closed guards) without venue fee/match semantics or RB link geometry.

Interface:

* `OrderBook` — FIFO-ordered resting orders + cursor index
* `cancelStep` — one scan step (advance cursor; maybe cancel at cursor)
* `cancelGo` / `cancelUpTo` — bounded fold under `searchLimit` / `cancelLimit`
* fail-closed: trader `0` or zero budgets leave the book unchanged (rewound)
-/

namespace ProofForge.Svm.Sdk.FifoCancelModel

open ProofForge.Svm.Sdk.StorageModel

/-- One resting order on a FIFO side (logical key = price×sequence). -/
structure Order where
  price : UInt64
  sequence : UInt64
  owner : UInt64
  size : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Side book: orders in cursor-traversal order; `cursor` is a 0-based index. -/
structure OrderBook where
  capacity : Nat
  orders : List Order
  cursor : Nat
  deriving Repr, Inhabited

@[inline] def OrderBook.count (b : OrderBook) : Nat :=
  b.orders.length

def OrderBook.empty (capacity : Nat) : OrderBook :=
  { capacity, orders := [], cursor := 0 }

/-- Order at the current cursor, or `none` at end. -/
def OrderBook.atCursor (b : OrderBook) : Option Order :=
  b.orders[b.cursor]?

/-- Drop the order at `cursor`; next survivor slides into the same index. -/
def OrderBook.cancelAtCursor (b : OrderBook) : OrderBook :=
  if b.cursor < b.orders.length then
    { b with orders := b.orders.take b.cursor ++ b.orders.drop (b.cursor + 1) }
  else
    b

/-- Advance cursor by one without canceling. -/
def OrderBook.advance (b : OrderBook) : OrderBook :=
  { b with cursor := b.cursor + 1 }

/-- Reset cursor to the logical first order. -/
def OrderBook.rewind (b : OrderBook) : OrderBook :=
  { b with cursor := 0 }

/-! ## Single step -/

/-- Outcome of one scan step. -/
structure StepResult where
  book : OrderBook
  canceled : Bool
  scanned : Bool
  deriving Repr

/--
One cancel-scan step:

* end of book → no-op (`scanned = false`)
* owner mismatch or price above `tickLimit` → advance only
* else cancel at cursor (cursor stays on the shifted next)
-/
def cancelStep (b : OrderBook) (trader tickLimit : UInt64) : StepResult :=
  match b.atCursor with
  | none => { book := b, canceled := false, scanned := false }
  | some o =>
      if o.owner ≠ trader then
        { book := b.advance, canceled := false, scanned := true }
      else if tickLimit < o.price then
        { book := b.advance, canceled := false, scanned := true }
      else
        { book := b.cancelAtCursor, canceled := true, scanned := true }

/-! ## Bounded fold -/

/-- Accumulators for a bounded cancel pass. -/
structure CancelState where
  book : OrderBook
  searched : Nat
  canceled : Nat
  deriving Repr

def CancelState.init (b : OrderBook) : CancelState :=
  { book := b.rewind, searched := 0, canceled := 0 }

/-- Recursive engine for `cancelUpTo` (exposed for induction). -/
def cancelGo (trader tickLimit : UInt64) (searchLimit cancelLimit : Nat) :
    CancelState → Nat → CancelState
  | st, 0 => st
  | st, fuel + 1 =>
      if searchLimit ≤ st.searched || cancelLimit ≤ st.canceled then
        st
      else
        let step := cancelStep st.book trader tickLimit
        if !step.scanned then
          st
        else
          cancelGo trader tickLimit searchLimit cancelLimit
            { book := step.book
              searched := st.searched + 1
              canceled := if step.canceled then st.canceled + 1 else st.canceled }
            fuel

/--
Bounded cancel fold. Budgets are `Nat` mirrors of the invocation U64 limits.
Fail-closed when `trader = 0` or either budget is 0.
-/
def cancelUpTo (b : OrderBook) (trader : UInt64)
    (tickLimit : UInt64) (searchLimit cancelLimit : Nat) : CancelState :=
  if trader = 0 || searchLimit = 0 || cancelLimit = 0 then
    CancelState.init b
  else
    cancelGo trader tickLimit searchLimit cancelLimit
      (CancelState.init b) (max searchLimit b.count)

/-! ## Fail-closed -/

theorem cancelUpTo_trader_zero (b : OrderBook) (tickLimit : UInt64)
    (searchLimit cancelLimit : Nat) :
    cancelUpTo b 0 tickLimit searchLimit cancelLimit = CancelState.init b := by
  simp [cancelUpTo]

theorem cancelUpTo_search_zero (b : OrderBook) (trader tickLimit : UInt64)
    (cancelLimit : Nat) (hne : trader ≠ 0) :
    cancelUpTo b trader tickLimit 0 cancelLimit = CancelState.init b := by
  simp [cancelUpTo, hne]

theorem cancelUpTo_cancel_zero (b : OrderBook) (trader tickLimit : UInt64)
    (searchLimit : Nat) (hne : trader ≠ 0) (hs : searchLimit ≠ 0) :
    cancelUpTo b trader tickLimit searchLimit 0 = CancelState.init b := by
  simp [cancelUpTo, hne, hs]

theorem cancelUpTo_fail_closed_book (b : OrderBook) (trader tickLimit : UInt64)
    (searchLimit cancelLimit : Nat)
    (hfail : trader = 0 ∨ searchLimit = 0 ∨ cancelLimit = 0) :
    (cancelUpTo b trader tickLimit searchLimit cancelLimit).book = b.rewind := by
  rcases hfail with h | h | h
  · simp [cancelUpTo, CancelState.init, h]
  · by_cases ht : trader = 0
    · simp [cancelUpTo, CancelState.init, ht]
    · simp [cancelUpTo, CancelState.init, ht, h]
  · by_cases ht : trader = 0
    · simp [cancelUpTo, CancelState.init, ht]
    · by_cases hs : searchLimit = 0
      · simp [cancelUpTo, CancelState.init, ht, hs]
      · simp [cancelUpTo, CancelState.init, ht, hs, h]

/-! ## Step lemmas -/

theorem cancelStep_end (b : OrderBook) (trader tickLimit : UInt64)
    (hend : b.atCursor = none) :
    cancelStep b trader tickLimit =
      { book := b, canceled := false, scanned := false } := by
  simp [cancelStep, hend]

theorem cancelStep_skip_owner (b : OrderBook) (trader tickLimit : UInt64) (o : Order)
    (hat : b.atCursor = some o) (hne : o.owner ≠ trader) :
    cancelStep b trader tickLimit =
      { book := b.advance, canceled := false, scanned := true } := by
  simp [cancelStep, hat, hne]

theorem cancelStep_cancel (b : OrderBook) (trader tickLimit : UInt64) (o : Order)
    (hat : b.atCursor = some o) (how : o.owner = trader)
    (htick : ¬ tickLimit < o.price) :
    cancelStep b trader tickLimit =
      { book := b.cancelAtCursor, canceled := true, scanned := true } := by
  simp [cancelStep, hat, how, htick]

theorem cancelAtCursor_length (b : OrderBook) (h : b.cursor < b.orders.length) :
    (b.cancelAtCursor).count = b.count - 1 := by
  simp [OrderBook.cancelAtCursor, OrderBook.count, h, List.length_append,
    List.length_take, List.length_drop]
  omega

/-! ## Budget invariants -/

theorem cancelGo_canceled_le
    (trader tickLimit : UInt64) (searchLimit cancelLimit : Nat)
    (st : CancelState) (fuel : Nat)
    (hle : st.canceled ≤ cancelLimit) :
    (cancelGo trader tickLimit searchLimit cancelLimit st fuel).canceled ≤
      cancelLimit := by
  induction fuel generalizing st with
  | zero => simpa [cancelGo] using hle
  | succ fuel ih =>
      rw [cancelGo]
      by_cases hstop :
          (decide (searchLimit ≤ st.searched) || decide (cancelLimit ≤ st.canceled)) = true
      · simp [hstop]; exact hle
      · simp [hstop]
        by_cases hscan : (cancelStep st.book trader tickLimit).scanned = false
        · simp [hscan]; exact hle
        · simp [hscan]
          refine ih _ ?_
          have hpair :
              ¬ searchLimit ≤ st.searched ∧ ¬ cancelLimit ≤ st.canceled := by
            have hfalse :
                (decide (searchLimit ≤ st.searched) ||
                  decide (cancelLimit ≤ st.canceled)) = false :=
              Bool.eq_false_iff.2 hstop
            have ⟨hsf, hcf⟩ := Bool.or_eq_false_iff.1 hfalse
            exact ⟨of_decide_eq_false hsf, of_decide_eq_false hcf⟩
          by_cases hc : (cancelStep st.book trader tickLimit).canceled = true
          · simp [hc]; omega
          · simp [hc]; exact hle

theorem cancelUpTo_canceled_le
    (b : OrderBook) (trader tickLimit : UInt64)
    (searchLimit cancelLimit : Nat) :
    (cancelUpTo b trader tickLimit searchLimit cancelLimit).canceled ≤ cancelLimit := by
  by_cases htr : trader = 0
  · simp [cancelUpTo, CancelState.init, htr]
  · by_cases hs : searchLimit = 0
    · simp [cancelUpTo, CancelState.init, htr, hs]
    · by_cases hc : cancelLimit = 0
      · simp [cancelUpTo, CancelState.init, htr, hs, hc]
      · simp [cancelUpTo, htr, hs, hc]
        exact cancelGo_canceled_le trader tickLimit searchLimit cancelLimit
          (CancelState.init b) (max searchLimit b.count) (by simp [CancelState.init])

theorem cancelGo_searched_le
    (trader tickLimit : UInt64) (searchLimit cancelLimit : Nat)
    (st : CancelState) (fuel : Nat)
    (hle : st.searched ≤ searchLimit) :
    (cancelGo trader tickLimit searchLimit cancelLimit st fuel).searched ≤
      searchLimit := by
  induction fuel generalizing st with
  | zero => simpa [cancelGo] using hle
  | succ fuel ih =>
      rw [cancelGo]
      by_cases hstop :
          (decide (searchLimit ≤ st.searched) || decide (cancelLimit ≤ st.canceled)) = true
      · simp [hstop]; exact hle
      · simp [hstop]
        by_cases hscan : (cancelStep st.book trader tickLimit).scanned = false
        · simp [hscan]; exact hle
        · simp [hscan]
          refine ih _ ?_
          have hpair :
              ¬ searchLimit ≤ st.searched ∧ ¬ cancelLimit ≤ st.canceled := by
            have hfalse :
                (decide (searchLimit ≤ st.searched) ||
                  decide (cancelLimit ≤ st.canceled)) = false :=
              Bool.eq_false_iff.2 hstop
            have ⟨hsf, hcf⟩ := Bool.or_eq_false_iff.1 hfalse
            exact ⟨of_decide_eq_false hsf, of_decide_eq_false hcf⟩
          exact Nat.succ_le_of_lt (Nat.not_le.mp hpair.1)

theorem cancelUpTo_searched_le
    (b : OrderBook) (trader tickLimit : UInt64)
    (searchLimit cancelLimit : Nat) :
    (cancelUpTo b trader tickLimit searchLimit cancelLimit).searched ≤ searchLimit := by
  by_cases htr : trader = 0
  · simp [cancelUpTo, CancelState.init, htr]
  · by_cases hs : searchLimit = 0
    · simp [cancelUpTo, CancelState.init, htr, hs]
    · by_cases hc : cancelLimit = 0
      · simp [cancelUpTo, CancelState.init, htr, hs, hc]
      · simp [cancelUpTo, htr, hs, hc]
        exact cancelGo_searched_le trader tickLimit searchLimit cancelLimit
          (CancelState.init b) (max searchLimit b.count) (by simp [CancelState.init])

/-- Empty book stays empty under the cancel fold. -/
theorem cancelGo_empty_orders
    (capacity : Nat) (trader tickLimit : UInt64)
    (searchLimit cancelLimit : Nat) (fuel : Nat) :
    (cancelGo trader tickLimit searchLimit cancelLimit
      { book := { capacity := capacity, orders := [], cursor := 0 }
        searched := 0
        canceled := 0 }
      fuel).book.orders = [] := by
  induction fuel with
  | zero => simp [cancelGo]
  | succ fuel ih =>
      unfold cancelGo
      have hstep :
          cancelStep { capacity := capacity, orders := [], cursor := 0 } trader tickLimit =
            { book := { capacity := capacity, orders := [], cursor := 0 }
              canceled := false
              scanned := false } := by
        simp [cancelStep, OrderBook.atCursor]
      split <;> simp [hstep]

theorem cancelUpTo_empty_orders
    (capacity : Nat) (trader tickLimit : UInt64)
    (searchLimit cancelLimit : Nat) :
    (cancelUpTo (OrderBook.empty capacity) trader tickLimit searchLimit cancelLimit).book.orders =
      [] := by
  by_cases htr : trader = 0
  · simp [cancelUpTo, CancelState.init, OrderBook.empty, OrderBook.rewind, htr]
  · by_cases hs : searchLimit = 0
    · simp [cancelUpTo, CancelState.init, OrderBook.empty, OrderBook.rewind, htr, hs]
    · by_cases hc : cancelLimit = 0
      · simp [cancelUpTo, CancelState.init, OrderBook.empty, OrderBook.rewind, htr, hs, hc]
      · simp [cancelUpTo, CancelState.init, OrderBook.empty, OrderBook.rewind, htr, hs, hc]
        simpa [OrderBook.empty, OrderBook.count] using
          cancelGo_empty_orders capacity trader tickLimit searchLimit cancelLimit
            (max searchLimit 0)

/-! ## AccountWords cursor bridge (sf-012)

A single account word holds the 0-based cursor. Fail-closed cancel paths do not
write the word. Successful bounded folds write the final `OrderBook.cursor`.
-/

/-- Read a cursor word; values beyond the book length are treated as end-of-book. -/
def mReadCursor (mem : AccountWords) (cursorWord : Nat) : Nat :=
  (mem cursorWord).toNat

/-- Write the current book cursor into an account word. -/
def mWriteCursor (mem : AccountWords) (cursorWord : Nat) (cursor : Nat) : AccountWords :=
  mWriteWord mem cursorWord (UInt64.ofNat cursor)

/-- Load `OrderBook.cursor` from account words (clamped to `count`). -/
def OrderBook.loadCursor (b : OrderBook) (mem : AccountWords) (cursorWord : Nat) : OrderBook :=
  let c := mReadCursor mem cursorWord
  { b with cursor := if c ≤ b.count then c else b.count }

/-- Persist `OrderBook.cursor` after a cancel fold. -/
def OrderBook.storeCursor (b : OrderBook) (mem : AccountWords) (cursorWord : Nat) : AccountWords :=
  mWriteCursor mem cursorWord b.cursor

/-- Fail-closed cancel leaves the cursor word unchanged. -/
theorem cancelUpTo_fail_closed_cursor_word
    (b : OrderBook) (mem : AccountWords) (cursorWord : Nat)
    (trader tickLimit : UInt64) (searchLimit cancelLimit : Nat)
    (hfail : trader = 0 ∨ searchLimit = 0 ∨ cancelLimit = 0) :
    let st := cancelUpTo b trader tickLimit searchLimit cancelLimit
    -- no store issued on fail-closed; any prior word is preserved by not calling storeCursor
    mReadCursor mem cursorWord = mReadCursor mem cursorWord ∧
      st.book = b.rewind := by
  refine ⟨rfl, cancelUpTo_fail_closed_book b trader tickLimit searchLimit cancelLimit hfail⟩

/-- After a store, the loaded cursor matches the book cursor (when in range). -/
theorem storeCursor_loadCursor
    (b : OrderBook) (mem : AccountWords) (cursorWord : Nat)
    (hle : b.cursor ≤ b.count) (hbound : b.count < UInt64.size) :
    (OrderBook.loadCursor b (OrderBook.storeCursor b mem cursorWord) cursorWord).cursor =
      b.cursor := by
  have hc : b.cursor < UInt64.size := Nat.lt_of_le_of_lt hle hbound
  have hmod : b.cursor % UInt64.size = b.cursor := Nat.mod_eq_of_lt hc
  simp [OrderBook.loadCursor, OrderBook.storeCursor, mReadCursor, mWriteCursor, mWriteWord,
    UInt64.toNat_ofNat, hmod, hle]

/-- Writing the cursor word does not change any other account word. -/
theorem mWriteCursor_other (mem : AccountWords) (cursorWord other : Nat) (cursor : Nat)
    (hne : other ≠ cursorWord) :
    mWriteCursor mem cursorWord cursor other = mem other := by
  simp [mWriteCursor, mWriteWord, hne]

/-! ## Sdk facade alignment (definition note)

`ProofForge.Svm.FifoCancel.Call.cancelUpTo` carries the same scalar budgets
(`traderIndex`, `tickLimit`, `searchLimit`, `cancelLimit`) and a static side
`Config`. This model erases recorder / collateral release and keeps the fold
skeleton plus a one-word AccountWords cursor bridge:

rewind → scan ≤ searchLimit → cancel ≤ cancelLimit → owner+tick filters →
fail-closed on zero trader/budgets → optional `storeCursor`.
-/

end ProofForge.Svm.Sdk.FifoCancelModel
