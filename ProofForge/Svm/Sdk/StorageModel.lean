import ProofForge.Svm.Sdk.Storage
import ProofForge.Svm.Sdk.Queue

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

section WfParts

/-! ### wf 桥接：parts 引理

`simp only [..., Bool.and_eq_true]` 展开的 Bool 链是左嵌套且叶位置随上下文漂移。
parts 引理把链一次性重整成**语句侧控制结合方式的 Prop 合取**——下游全部用
rcases 解构稳定结构，不再做位置敏感的投影。 -/

/-- `scalarHeaderWellFormed` 的结构化合同（access 叶保持 Bool 形：Access 无 LawfulBEq）。 -/
theorem scalarHeader_wf_parts {header : Field} {bodyAccount : Nat}
    (h : scalarHeaderWellFormed header bodyAccount = true) :
    header.wellFormed (accountLimit := 64) = true ∧
    header.widthWords = 1 ∧
    header.region.account = bodyAccount ∧
    header.region.account > 0 ∧
    header.region.strideWords = 1 ∧
    header.region.capacity = 1 ∧
    (header.region.indexBase == IndexBase.zero) = true ∧
    (header.region.access == Access.programOwnedMutable) = true := by
  simp only [scalarHeaderWellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `BoundedVec.wellFormed` 的结构化合同。 -/
theorem boundedVec_wf_parts {vec : BoundedVec}
    (h : vec.wellFormed = true) :
    vec.slots.mutableOneBasedWord = true ∧
    vec.slots.region.account > 0 ∧
    vec.slots.region.capacity ≤ containerCapacityLimit ∧
    scalarHeaderWellFormed vec.count vec.slots.region.account = true ∧
    vec.count.firstWord + 1 ≤ vec.slots.firstWord := by
  simp only [BoundedVec.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `Field.mutableOneBasedWord` 的结构化合同。 -/
theorem mutableOneBased_wf_parts {field : Field}
    (h : field.mutableOneBasedWord = true) :
    field.wellFormed (accountLimit := 64) = true ∧
    field.widthWords = 1 ∧
    (field.region.indexBase == IndexBase.one) = true ∧
    (field.region.access == Access.programOwnedMutable) = true := by
  simp only [Field.mutableOneBasedWord, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end WfParts

/-- IndexBase 无 LawfulBEq：`(b == zero) = true` 到等式的桥。 -/
theorem indexBase_beq_zero_eq {b : IndexBase} (h : (b == IndexBase.zero) = true) :
    b = IndexBase.zero := by
  cases b with
  | zero => rfl
  | one => exact absurd h (by decide)

/-- IndexBase 无 LawfulBEq：`(b == one) = true` 到等式的桥。 -/
theorem indexBase_beq_one_eq {b : IndexBase} (h : (b == IndexBase.one) = true) :
    b = IndexBase.one := by
  cases b with
  | zero => exact absurd h (by decide)
  | one => rfl

section WfBridge

variable (vec : BoundedVec)

/-- wf 下 slots 的 one-based 索引基。 -/
theorem boundedVec_wf_indexBase (hwf : vec.wellFormed = true) :
    vec.slots.region.indexBase = IndexBase.one := by
  have parts := mutableOneBased_wf_parts (h := (boundedVec_wf_parts (vec := vec) hwf).1)
  exact indexBase_beq_one_eq parts.2.2.1

/-- wf 下 slots 容量 ≤ 容器上限。 -/
theorem boundedVec_wf_capacity (hwf : vec.wellFormed = true) :
    vec.slots.region.capacity ≤ containerCapacityLimit :=
  (boundedVec_wf_parts (vec := vec) hwf).2.2.1

/-- capacity 的 toNat 恒等（容量 ≤ 容器上限时无截断）。 -/
theorem bv_capacity_toNat (hwf : vec.wellFormed = true) :
    (BoundedVec.capacity vec).toNat = vec.slots.region.capacity := by
  have hc := boundedVec_wf_capacity vec hwf
  show (UInt64.ofNat vec.slots.region.capacity).toNat = vec.slots.region.capacity
  have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
  have hmod : vec.slots.region.capacity % (4294967296 * 4294967296)
      = vec.slots.region.capacity := by
    have hc' : vec.slots.region.capacity ≤ 65536 := hc
    omega
  simp only [UInt64.ofNat, UInt64.toNat, BitVec.toNat_ofNat, h2, hmod]

/-- wf 下 slots 的访问词公式（one-based）。 -/
theorem mFieldWord_bv_slots (hwf : vec.wellFormed = true) (pos : UInt64)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ vec.slots.region.capacity) :
    mFieldWord vec.slots pos =
      some (vec.slots.firstWord + (pos.toNat - 1) * vec.slots.region.strideWords) := by
  have hidx := boundedVec_wf_indexBase vec hwf
  unfold mFieldWord
  rw [hidx]
  simp only [h1, h2, and_true, if_true, Field.firstWord]

/-- wf 下 count header 的访问词 = firstWord。 -/
theorem mFieldWord_bv_count (hwf : vec.wellFormed = true) :
    mFieldWord vec.count 0 = some vec.count.firstWord := by
  have hs4 := (boundedVec_wf_parts (vec := vec) hwf).2.2.2.1
  have hacc : vec.count.region.account = vec.slots.region.account :=
    scalarHeader_wf_account _ _ hs4
  have parts := scalarHeader_wf_parts
    (h := show scalarHeaderWellFormed vec.count vec.count.region.account = true from by
      rw [hacc]; exact hs4)
  have hidx := indexBase_beq_zero_eq parts.2.2.2.2.2.2.1
  have hcap1 : vec.count.region.capacity = 1 := parts.2.2.2.2.2.1
  unfold mFieldWord
  rw [hidx]
  have h0 : UInt64.toNat 0 = 0 := rfl
  have hcap : (0 : Nat) < vec.count.region.capacity := by omega
  simp only [h0, hcap, if_true, Nat.zero_mul, Nat.add_zero]
  rfl

/-- **wf 下 count header 字与任何 payload 槽字不同**（模型版不干涉的核心）。
全部是 Nat 算术：slots 词 = firstWord + (pos-1)·stride ≥ slots.firstWord
> count.firstWord，而 count 词恰为 count.firstWord。 -/
theorem mFieldWord_bv_count_ne_slots (hwf : vec.wellFormed = true) (pos : UInt64)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ vec.slots.region.capacity)
    {w : Nat} (hw : mFieldWord vec.slots pos = some w) :
    mFieldWord vec.count 0 ≠ some w := by
  intro hcount
  rw [mFieldWord_bv_count vec hwf] at hcount
  rw [mFieldWord_bv_slots vec hwf pos h1 h2] at hw
  have heq : vec.count.firstWord = w := Option.some.inj hcount
  have hw' : w = vec.slots.firstWord + (pos.toNat - 1) * vec.slots.region.strideWords :=
    (Option.some.inj hw).symm
  have h1' : vec.count.firstWord + 1 ≤ vec.slots.firstWord :=
    (boundedVec_wf_header_before_slots vec hwf).1
  omega

end WfBridge

section BvWfAlgebra

variable (vec : BoundedVec)

/-- `x < ofNat c`（UInt64）且 c ≤ 容器上限 时 `x.toNat < c`。
消除 UInt64↔Nat 强转舞步的桥引理。 -/
private theorem toNat_lt_ofNat {x : UInt64} {c : Nat} (h : x < UInt64.ofNat c)
    (hc : c ≤ containerCapacityLimit) : x.toNat < c := by
  have h2 : (BitVec.ofNat 64 c).toNat = c % (4294967296 * 4294967296) := by
    simp only [BitVec.toNat_ofNat]
  have h1 : x.toNat < (BitVec.ofNat 64 c).toNat := h
  rw [h2] at h1
  omega

private theorem u64_toNat_add_one {a : UInt64} (h : a.toNat < 65536) :
    (a + 1).toNat = a.toNat + 1 := by
  have hone : UInt64.toNat 1 = 1 := rfl
  have h2 : (2 : Nat) ^ 64 = 4294967296 * 4294967296 := by decide
  rw [UInt64.toNat_add, hone, h2]
  have hlt : a.toNat + 1 < 4294967296 * 4294967296 := by omega
  rw [Nat.mod_eq_of_lt hlt]

/-- wf 下 push 的双写组合：先写 payload 槽再写 count header 后，
count 读回 = 旧 size + 1，payload 槽读回 = v。
（count/slots 词不同由 `mFieldWord_bv_count_ne_slots` 给出。） -/
theorem mBvPush_twoWrites (mem : AccountWords) (pos v : UInt64)
    (hwf : vec.wellFormed = true)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ vec.slots.region.capacity) :
    mReadField (mWriteField (mWriteField mem vec.slots pos v) vec.count 0
        (mBvSize mem vec + 1)) vec.count 0
      = mBvSize mem vec + 1 ∧
    mReadField (mWriteField (mWriteField mem vec.slots pos v) vec.count 0
        (mBvSize mem vec + 1)) vec.slots pos
      = v := by
  have hwc : mFieldWord vec.count 0 = some vec.count.firstWord := mFieldWord_bv_count vec hwf
  have hws : mFieldWord vec.slots pos
      = some (vec.slots.firstWord + (pos.toNat - 1) * vec.slots.region.strideWords) :=
    mFieldWord_bv_slots vec hwf pos h1 h2
  have hne : vec.count.firstWord
      ≠ vec.slots.firstWord + (pos.toNat - 1) * vec.slots.region.strideWords := by
    intro heq
    have h1' : vec.count.firstWord + 1 ≤ vec.slots.firstWord :=
      (boundedVec_wf_header_before_slots vec hwf).1
    omega
  -- 全部下推到词级
  unfold mWriteField mReadField mBvSize
  rw [hwc, hws]
  constructor
  · simp only [mWriteWord, if_pos rfl]
    rfl
  · have hne' : ¬(vec.slots.firstWord + (pos.toNat - 1) * vec.slots.region.strideWords
        = vec.count.firstWord) := by
      have h1' : vec.count.firstWord + 1 ≤ vec.slots.firstWord :=
        (boundedVec_wf_header_before_slots vec hwf).1
      omega
    simp only [mWriteWord, if_neg hne', if_pos rfl]
    rfl

/-- **push 后 count 恰 +1**（twoWrites 的 count 分量）。 -/
theorem mBvPush_size (mem : AccountWords) (v : UInt64)
    (hwf : vec.wellFormed = true)
    (hfull : mBvSize mem vec < BoundedVec.capacity vec) :
    mBvSize (mBvPush mem vec v).1 vec = mBvSize mem vec + 1 := by
  have hpos : (mBvSize mem vec + 1).toNat = (mBvSize mem vec).toNat + 1 :=
    u64_toNat_add_one (show (mBvSize mem vec).toNat < 65536 by
      have h1 : (mBvSize mem vec).toNat < vec.slots.region.capacity :=
        toNat_lt_ofNat hfull (boundedVec_wf_capacity vec hwf)
      have hcap'' : vec.slots.region.capacity ≤ 65536 :=
        boundedVec_wf_capacity vec hwf
      omega)
  have h1 : (1 : Nat) ≤ (mBvSize mem vec + 1).toNat := by rw [hpos]; omega
  have h2 : (mBvSize mem vec + 1).toNat ≤ vec.slots.region.capacity := by
    rw [hpos]
    have hcap' : vec.slots.region.capacity ≤ 65536 :=
      boundedVec_wf_capacity vec hwf
    have hlt : (mBvSize mem vec).toNat < vec.slots.region.capacity := by
      have : (mBvSize mem vec).toNat < (BoundedVec.capacity vec).toNat := hfull
      rw [bv_capacity_toNat vec hwf] at this
      omega
    omega
  have hproj : (mBvPush mem vec v).1
      = mWriteField (mWriteField mem vec.slots (mBvSize mem vec + 1) v) vec.count 0
        (mBvSize mem vec + 1) := by
    simp only [mBvPush]
    rw [if_neg (by
      show ¬(BoundedVec.capacity vec ≤ mBvSize mem vec)
      exact fun hc => by
        have h2 : (BoundedVec.capacity vec).toNat ≤ (mBvSize mem vec).toNat := hc
        rw [bv_capacity_toNat vec hwf] at h2
        omega)]
  rw [hproj]
  exact (mBvPush_twoWrites vec mem (mBvSize mem vec + 1) v hwf h1 h2).1

/-- **push 后按返回位置读回恰为写入值**（twoWrites 的 slots 分量 + getAt 卫语句）。 -/
theorem mBvPush_get (mem : AccountWords) (v : UInt64)
    (hwf : vec.wellFormed = true)
    (hfull : mBvSize mem vec < BoundedVec.capacity vec) :
    mBvGetAt (mBvPush mem vec v).1 vec (mBvPush mem vec v).2 = v := by
  have hsize : mBvSize (mBvPush mem vec v).1 vec = mBvSize mem vec + 1 :=
    mBvPush_size vec mem v hwf hfull
  have hpos : (mBvSize mem vec + 1).toNat = (mBvSize mem vec).toNat + 1 :=
    u64_toNat_add_one (show (mBvSize mem vec).toNat < 65536 by
      have h1 : (mBvSize mem vec).toNat < vec.slots.region.capacity :=
        toNat_lt_ofNat hfull (boundedVec_wf_capacity vec hwf)
      have hcap'' : vec.slots.region.capacity ≤ 65536 :=
        boundedVec_wf_capacity vec hwf
      omega)
  have h1 : (1 : Nat) ≤ (mBvSize mem vec + 1).toNat := by rw [hpos]; omega
  have h2 : (mBvSize mem vec + 1).toNat ≤ vec.slots.region.capacity := by
    rw [hpos]
    have hcap' : vec.slots.region.capacity ≤ 65536 :=
      boundedVec_wf_capacity vec hwf
    have hlt : (mBvSize mem vec).toNat < vec.slots.region.capacity := by
      have : (mBvSize mem vec).toNat < (BoundedVec.capacity vec).toNat := hfull
      rw [bv_capacity_toNat vec hwf] at this
      omega
    omega
  have htwo := mBvPush_twoWrites vec mem (mBvSize mem vec + 1) v hwf h1 h2
  have hproj : (mBvPush mem vec v).1
      = mWriteField (mWriteField mem vec.slots (mBvSize mem vec + 1) v) vec.count 0
        (mBvSize mem vec + 1) := by
    simp only [mBvPush]
    rw [if_neg (by
      show ¬(BoundedVec.capacity vec ≤ mBvSize mem vec)
      exact fun hc => by
        have h2 : (BoundedVec.capacity vec).toNat ≤ (mBvSize mem vec).toNat := hc
        rw [bv_capacity_toNat vec hwf] at h2
        omega)]
  have hret : (mBvPush mem vec v).2 = mBvSize mem vec + 1 := by
    simp only [mBvPush]
    rw [if_neg (by
      show ¬(BoundedVec.capacity vec ≤ mBvSize mem vec)
      exact fun hc => by
        have h2 : (BoundedVec.capacity vec).toNat ≤ (mBvSize mem vec).toNat := hc
        rw [bv_capacity_toNat vec hwf] at h2
        omega)]
  unfold mBvGetAt mBvSize
  rw [hproj, hret, htwo.1]
  have hposne : ¬((mBvSize mem vec + 1 : UInt64) = 0) := fun heq => by
    have h1' : (mBvSize mem vec + 1).toNat = (0 : UInt64).toNat :=
      congrArg UInt64.toNat heq
    rw [hpos] at h1'
    have h0 : UInt64.toNat 0 = 0 := rfl
    rw [h0] at h1'
    omega
  have hlt2 : ¬((mBvSize mem vec + 1 : UInt64) < (mBvSize mem vec + 1 : UInt64)) := fun h => by
    have h1' : (mBvSize mem vec + 1).toNat < (mBvSize mem vec + 1).toNat := h
    exact absurd h1' (Nat.lt_irrefl _)
  rw [if_neg (by
    intro hdisj
    rcases hdisj with h0 | hlt
    · exact hposne h0
    · exact hlt2 hlt)]
  exact htwo.2

end BvWfAlgebra


section QueueModel

open ProofForge.Svm.Sdk.Queue

variable (q : BoundedQueue)

/-! ### BoundedQueue 模型代数

三 header（slots/head/count）的词分离由 `BoundedQueue.wellFormed` 钉死：
head 词 + 1 = count 词 ≤ slots 首词。三写（slots@tail、count@W_c、head@W_h）
两两不干涉。 -/

/-- wf 下 queue 三字段同账户且词两两分离。 -/
theorem queue_wf_parts (hwf : q.wellFormed = true) :
    q.slots.mutableOneBasedWord = true ∧
    q.slots.region.account > 0 ∧
    q.slots.region.capacity ≤ containerCapacityLimit ∧
    scalarHeaderWellFormed q.head q.slots.region.account = true ∧
    scalarHeaderWellFormed q.count q.slots.region.account = true ∧
    q.head.firstWord + 1 = q.count.firstWord ∧
    q.count.firstWord + 1 ≤ q.slots.firstWord := by
  simp only [BoundedQueue.wellFormed, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hwf
  exact ⟨hwf.1.1.1.1.1.1, hwf.1.1.1.1.1.2, hwf.1.1.1.1.2,
    hwf.1.1.1.2, hwf.1.1.2, hwf.1.2, hwf.2⟩

/-- count header 的访问词 = count.firstWord。 -/
theorem mFieldWord_queue_count (hwf : q.wellFormed = true) :
    mFieldWord q.count 0 = some q.count.firstWord := by
  have parts := queue_wf_parts q hwf
  have hacc : q.count.region.account = q.slots.region.account :=
    scalarHeader_wf_account _ _ parts.2.2.2.2.1
  have hsw : scalarHeaderWellFormed q.count q.count.region.account = true := by
    rw [hacc]; exact parts.2.2.2.2.1
  exact mFieldWord_scalar_header hsw

/-- head header 的访问词 = head.firstWord。 -/
theorem mFieldWord_queue_head (hwf : q.wellFormed = true) :
    mFieldWord q.head 0 = some q.head.firstWord := by
  have parts := queue_wf_parts q hwf
  have hacc : q.head.region.account = q.slots.region.account :=
    scalarHeader_wf_account _ _ parts.2.2.2.1
  have hsw : scalarHeaderWellFormed q.head q.head.region.account = true := by
    rw [hacc]; exact parts.2.2.2.1
  exact mFieldWord_scalar_header hsw

/-- wf 下 slots 的访问词公式（one-based，同 BoundedVec）。 -/
theorem mFieldWord_queue_slots (hwf : q.wellFormed = true) (pos : UInt64)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ q.slots.region.capacity) :
    mFieldWord q.slots pos =
      some (q.slots.firstWord + (pos.toNat - 1) * q.slots.region.strideWords) := by
  have hs := queue_wf_parts q hwf
  have parts := mutableOneBased_wf_parts (h := hs.1)
  have hidx := indexBase_beq_one_eq parts.2.2.1
  unfold mFieldWord
  rw [hidx]
  simp only [h1, h2, and_true, if_true, Field.firstWord]

end QueueModel

end ProofForge.Svm.Sdk.StorageModel