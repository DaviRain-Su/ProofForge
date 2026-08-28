import ProofForge.Svm.Sdk.Storage

/-!
# 抽象账户字状态模型：SDK 存储组件的第二层形式化验证

`Svm.Sdk.Storage` 的效果型原语（`accDataWordAt` / `accDataWordSetAt` 等）是
`@[irreducible]` 宿主占位——对它们的「证明」验证的是占位而非链上行为
（p-003 的负结果）。本模块引入**抽象账户字状态模型** `AccountWords`，
把原语在该模型上解释，从而 kernel-check SDK 容器的**组合逻辑代数**：

- 字段级：读后写、越界不写不读、不相交字段互不干涉；
- BoundedVec 级：push/pop 后 count 一致、push 后按返回位置读回、
  满推/空弹不改内存。

信任边界随之精确化（三层层级，见 docs/plan/tasks/p-005.md）：

| 层 | 验证方式 |
|---|---|
| 合约性质 + SDK 组合逻辑（本文件） | Lean kernel |
| 发射代码实现同一原语语义 | pinned Mollusk 工程门 |
| sBPF/Yul 指令 refinement | 明确不声称 |

模型与 SDK 定义的对应关系是结构性的：`mFieldWord` 镜像
`AccountStorage.Source.read/write` 的静态几何（baseWord + offsetWords +
index×strideWords，one-based 拒绝空哨兵、越界返回 none），卫语句与
`BoundedVec.getAt/setAt/push/pop` 逐字对应；两层的 fail-closed 哨兵约定
（`0` = absent）一致。
-/

namespace ProofForge.Svm.Sdk.StorageModel

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.Sdk.Storage

/-! ## 抽象账户字状态 -/

/-- 账户字内存：data word 序号（Nat）到 u64 值的全函数。
只建模程序可见的字语义，不建字节布局或账户边界——那些由工程门负责。 -/
def AccountWords := Nat → UInt64

/-- 写一个字，其余字不变。 -/
def mWriteWord (mem : AccountWords) (w : Nat) (v : UInt64) : AccountWords :=
  fun k => if k = w then v else mem k

/-- 字段访问的目标 word（fail-closed）：越界与空哨兵返回 `none`。
镜像 `AccountStorage.Source.read/write` 的静态几何。 -/
def mFieldWord (f : Field) (index : UInt64) : Option Nat :=
  match f.region.indexBase with
  | .zero =>
      if index.toNat < f.region.capacity then
        some (f.region.baseWord + f.offsetWords + index.toNat * f.region.strideWords)
      else none
  | .one =>
      if 1 ≤ index.toNat ∧ index.toNat ≤ f.region.capacity then
        some (f.region.baseWord + f.offsetWords + (index.toNat - 1) * f.region.strideWords)
      else none

/-- 抽象读：none（越界/空哨兵）返回 `0`，与 SDK 的 fail-closed 哨兵约定一致。 -/
def mReadField (mem : AccountWords) (f : Field) (index : UInt64) : UInt64 :=
  match mFieldWord f index with
  | some w => mem w
  | none => 0

/-- 抽象写：none 时不改内存。 -/
def mWriteField (mem : AccountWords) (f : Field) (index : UInt64) (v : UInt64) : AccountWords :=
  match mFieldWord f index with
  | some w => mWriteWord mem w v
  | none => mem

/-! ## 字段级代数 -/

/-- **读后写**：合法访问词上，写入后读回恰为写入值。 -/
theorem mReadField_write_same (mem : AccountWords) (f : Field) (i v : UInt64) (w : Nat)
    (hw : mFieldWord f i = some w) :
    mReadField (mWriteField mem f i v) f i = v := by
  unfold mWriteField mReadField
  rw [hw]
  simp [mWriteWord, hw]

/-- **越界写不动内存**。 -/
theorem mWriteField_noop_oob (mem : AccountWords) (f : Field) (i v : UInt64)
    (hn : mFieldWord f i = none) :
    mWriteField mem f i v = mem := by
  unfold mWriteField
  rw [hn]

/-- **越界读得哨兵 `0`**。 -/
theorem mReadField_oob (mem : AccountWords) (f : Field) (i : UInt64)
    (hn : mFieldWord f i = none) :
    mReadField mem f i = 0 := by
  unfold mReadField
  rw [hn]

/-- **不相交字段互不干涉**（接口条件版）：两个字段的访问词不同时，
对一个字段的写入不改变另一个字段的读取。这是 SDK 组合逻辑复用的
核心接口；具体几何（同 region 不同 offsetWords）由 `mFieldWord_offset_inj`
按 wellFormed 几何推导。 -/
theorem mReadField_write_other (mem : AccountWords) (f₁ f₂ : Field) (i j : UInt64) (v : UInt64)
    {w₁ w₂ : Nat} (h₁ : mFieldWord f₁ i = some w₁) (h₂ : mFieldWord f₂ j = some w₂)
    (hdiff : w₁ ≠ w₂) :
    mReadField (mWriteField mem f₂ j v) f₁ i = mReadField mem f₁ i := by
  unfold mReadField mWriteField
  rw [h₁, h₂]
  simp only []
  show (if w₁ = w₂ then v else mem w₁) = mem w₁
  simp [hdiff]

/-! ### 标量 header 的具体词 -/

/-- 标量 header（zero 基、capacity 1、index 0）的访问词就是 `firstWord`。 -/
theorem mFieldWord_scalar_header {header : Field}
    (h : scalarHeaderWellFormed header (header.region.account) = true) :
    mFieldWord header 0 = some header.firstWord := by
  have hs := h
  simp only [scalarHeaderWellFormed, Bool.and_eq_true, beq_iff_eq] at hs
  have hcap : (0 : Nat) < header.region.capacity := by
    have hc : header.region.capacity = 1 := hs.1.1.2
    omega
  have h0 : UInt64.toNat 0 = 0 := rfl
  have hidx : header.region.indexBase = .zero := by
    have h7 : (header.region.indexBase == IndexBase.zero) = true := hs.1.2
    cases hb : header.region.indexBase with
    | zero => rfl
    | one => rw [hb] at h7; exact absurd h7 (by decide)
  unfold mFieldWord
  rw [hidx]
  simp only [h0, hcap, if_true, Nat.zero_mul]
  exact congrArg _ (Nat.add_zero _)


/-! ## 线性分离引理 -/

/-- `o₁ + k₁·s = o₂ + k₂·s` 且 `o₁, o₂ < s`、`0 < s` 蕴含 `o₁ = o₂ ∧ k₁ = k₂`。 -/
private theorem add_mul_inj {s k₁ k₂ o₁ o₂ : Nat} (hs : 0 < s) (h₁ : o₁ < s) (h₂ : o₂ < s)
    (e : o₁ + k₁ * s = o₂ + k₂ * s) :
    o₁ = o₂ ∧ k₁ = k₂ := by
  rcases Nat.lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · have hk₂ : k₂ = (k₂ - k₁) + k₁ := by omega
    have hsplit : k₂ * s = (k₂ - k₁) * s + k₁ * s := by
      conv => lhs; rw [hk₂]
      rw [Nat.add_mul]
    have he' : o₁ = o₂ + (k₂ - k₁) * s := by omega
    have hd : 0 < k₂ - k₁ := by omega
    have hge : (k₂ - k₁) * s ≥ s := by
      have h1 : s ≤ s * (k₂ - k₁) := Nat.le_mul_of_pos_right s hd
      have h2 : s * (k₂ - k₁) = (k₂ - k₁) * s := Nat.mul_comm s (k₂ - k₁)
      omega
    omega
  · subst heq
    omega
  · have hk₁ : k₁ = (k₁ - k₂) + k₂ := by omega
    have hsplit : k₁ * s = (k₁ - k₂) * s + k₂ * s := by
      conv => lhs; rw [hk₁]
      rw [Nat.add_mul]
    have he' : o₂ = o₁ + (k₁ - k₂) * s := by omega
    have hd : 0 < k₁ - k₂ := by omega
    have h1 : s ≤ s * (k₁ - k₂) := Nat.le_mul_of_pos_right s hd
    have h2 : s * (k₁ - k₂) = (k₁ - k₂) * s := Nat.mul_comm s (k₁ - k₂)
    omega

/-! ## BoundedVec 代数 -/

/-- 计数 header 的读：`mBvSize = mReadField mem vec.count 0`，与 SDK 的
`BoundedVec.size` 卫语句逐字对应。 -/
def mBvSize (mem : AccountWords) (vec : BoundedVec) : UInt64 :=
  mReadField mem vec.count 0

/-- getAt 的 fail-closed 卫语句与 SDK 逐字对应。 -/
def mBvGetAt (mem : AccountWords) (vec : BoundedVec) (position : UInt64) : UInt64 :=
  let size := mBvSize mem vec
  if position = 0 ∨ size < position then 0 else mReadField mem vec.slots position

/-- setAt：越界不动内存。 -/
def mBvSetAt (mem : AccountWords) (vec : BoundedVec) (position value : UInt64) : AccountWords :=
  let size := mBvSize mem vec
  if position = 0 ∨ size < position then mem
  else mWriteField mem vec.slots position value

/-- push：满则不动并返回 `0`，否则写 payload 槽与 count header 并返回新位置。 -/
def mBvPush (mem : AccountWords) (vec : BoundedVec) (value : UInt64) : AccountWords × UInt64 :=
  let size := mBvSize mem vec
  if BoundedVec.capacity vec ≤ size then (mem, 0)
  else
    let mem := mWriteField mem vec.slots (size + 1) value
    let mem := mWriteField mem vec.count 0 (size + 1)
    (mem, size + 1)

/-- pop：空则不动并返回 `0`，否则 shrink count 并返回尾值。 -/
def mBvPop (mem : AccountWords) (vec : BoundedVec) : AccountWords × UInt64 :=
  let size := mBvSize mem vec
  if size = 0 then (mem, 0)
  else
    let v := mReadField mem vec.slots size
    let mem := mWriteField mem vec.count 0 (size - 1)
    (mem, v)

/-! ### BoundedVec 代数定理 -/

/-- 越界 getAt 得哨兵 `0`。 -/
theorem mBvGetAt_oob (mem : AccountWords) (vec : BoundedVec) (position : UInt64)
    (h : position = 0 ∨ mBvSize mem vec < position) :
    mBvGetAt mem vec position = 0 := by
  unfold mBvGetAt
  rw [if_pos h]

/-- 越界 setAt 不动内存。 -/
theorem mBvSetAt_oob_noop (mem : AccountWords) (vec : BoundedVec) (position value : UInt64)
    (h : position = 0 ∨ mBvSize mem vec < position) :
    mBvSetAt mem vec position value = mem := by
  unfold mBvSetAt
  rw [if_pos h]

/-- 满推不改内存、返回 `0`。 -/
theorem mBvPush_full_noop (mem : AccountWords) (vec : BoundedVec) (value : UInt64)
    (h : BoundedVec.capacity vec ≤ mBvSize mem vec) :
    mBvPush mem vec value = (mem, 0) := by
  unfold mBvPush
  rw [if_pos h]

/-- 空弹不改内存、返回 `0`。 -/
theorem mBvPop_empty_noop (mem : AccountWords) (vec : BoundedVec)
    (h : mBvSize mem vec = 0) :
    mBvPop mem vec = (mem, 0) := by
  unfold mBvPop
  rw [if_pos h]

end ProofForge.Svm.Sdk.StorageModel