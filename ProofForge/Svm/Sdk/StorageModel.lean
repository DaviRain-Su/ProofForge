import ProofForge.Svm.Sdk.Storage
import ProofForge.Svm.Sdk.Queue
import Std.Tactic.BVDecide

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

/-- 从结构化组件重建 `scalarHeaderWellFormed`。 -/
theorem scalarHeader_wf_build {header : Field} {bodyAccount : Nat}
    (hwf : header.wellFormed = true) (hw : header.widthWords = 1)
    (ha : header.region.account = bodyAccount) (hp : 0 < bodyAccount)
    (hs : header.region.strideWords = 1) (hc : header.region.capacity = 1)
    (hi : (header.region.indexBase == IndexBase.zero) = true)
    (hacc : (header.region.access == Access.programOwnedMutable) = true) :
    scalarHeaderWellFormed header bodyAccount = true := by
  unfold scalarHeaderWellFormed
  simp [Bool.and_eq_true, beq_iff_eq, hwf, hw, ha, hs, hc, hi, hacc]
  exact hp

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

/-- 由 slots access 链到 programOwnedMutable（Access 无 LawfulBEq）。 -/
private theorem access_beq_prog_of_slots {a b : Access}
    (hab : (a == b) = true) (hslots : (b == Access.programOwnedMutable) = true) :
    (a == Access.programOwnedMutable) = true := by
  have hb : b = Access.programOwnedMutable := by
    cases b with | mk bw bo =>
    cases bw <;> cases bo <;> try rfl
    repeat' exact absurd hslots (by native_decide)
  have ha : a = b := by
    cases a with | mk aw ao =>
    cases b with | mk bw bo =>
    cases aw <;> cases bw <;> cases ao <;> cases bo <;> try rfl
    repeat' exact absurd hab (by native_decide)
  rw [ha, hb]
  native_decide

private theorem ofNat_capacity_toNat (cap : Nat) (h : cap < 2 ^ 64) :
    (UInt64.ofNat cap).toNat = cap := by
  simpa [UInt64.toNat_ofNat, Nat.mod_eq_of_lt h]

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
  have h1 : x.toNat < (BitVec.ofNat 64 c).toNat := h
  have h2 : (BitVec.ofNat 64 c).toNat = c % (4294967296 * 4294967296) := by
    simp only [BitVec.toNat_ofNat]
  rw [h2] at h1
  omega

/-- **词级写读非干涉**：写 word w₁ 后读 word w₂ ≠ w₁ 得 mem w₂。 -/
theorem mWriteWord_other (mem : AccountWords) (w₁ w₂ : Nat) (v : UInt64)
    (hne : w₁ ≠ w₂) : mWriteWord mem w₁ v w₂ = mem w₂ := by
  unfold mWriteWord
  rw [if_neg (fun hc => hne hc.symm)]

/-- **词级读后写**：写 word w 后读 word w 恰为 v。 -/
theorem mWriteWord_self (mem : AccountWords) (w : Nat) (v : UInt64) :
    mWriteWord mem w v w = v := by
  unfold mWriteWord
  simp [if_pos rfl]


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


private theorem u64_toNat_sub_one {a : UInt64} (h : (1 : Nat) ≤ a.toNat) :
    (a - 1).toNat = a.toNat - 1 := by
  have hbig : (2:Nat)^64 = 4294967296*4294967296 := by decide
  have hlt : a.toNat < 4294967296*4294967296 := by
    obtain ⟨w⟩ := a
    have := w.isLt
    simpa [hbig] using this
  have hone : UInt64.toNat 1 = 1 := rfl
  rw [UInt64.toNat_sub, hbig, hone]
  omega

/-- Rewrite helper: nonzero UInt64 has toNat ≥ 1. -/
private theorem u64_toNat_pos {a : UInt64} (hne : a ≠ 0) : (1 : Nat) ≤ a.toNat := by
  have : a.toNat ≠ 0 := by
    intro hz
    apply hne
    cases h : a with
    | ofBitVec val =>
      have hz' : val.toNat = 0 := by simpa [h, UInt64.toNat] using hz
      have : val = 0 := BitVec.eq_of_toNat_eq (by simp [hz'])
      subst this
      rfl
  omega

/-- **合法 setAt 不改 count**：payload 槽与 count header 词不同。 -/
theorem mBvSetAt_size (mem : AccountWords) (position value : UInt64)
    (hwf : vec.wellFormed = true)
    (hpos0 : position ≠ 0)
    (hin : ¬ (mBvSize mem vec < position))
    (hbound : position.toNat ≤ vec.slots.region.capacity) :
    mBvSize (mBvSetAt mem vec position value) vec = mBvSize mem vec := by
  have hpos_ge := u64_toNat_pos hpos0
  have hws : mFieldWord vec.slots position
      = some (vec.slots.firstWord + (position.toNat - 1) * vec.slots.region.strideWords) :=
    mFieldWord_bv_slots vec hwf position hpos_ge hbound
  have hwc : mFieldWord vec.count 0 = some vec.count.firstWord :=
    mFieldWord_bv_count vec hwf
  have hne : vec.count.firstWord
      ≠ vec.slots.firstWord + (position.toNat - 1) * vec.slots.region.strideWords := by
    intro heq
    have h1' : vec.count.firstWord + 1 ≤ vec.slots.firstWord :=
      (boundedVec_wf_header_before_slots vec hwf).1
    omega
  unfold mBvSetAt mBvSize
  rw [if_neg (by
    intro h
    rcases h with h0 | hlt
    · exact hpos0 h0
    · exact hin hlt)]
  exact mReadField_write_other mem vec.count vec.slots 0 position value hwc hws hne

/-- **合法 setAt 同位置读回**。 -/
theorem mBvSetAt_get (mem : AccountWords) (position value : UInt64)
    (hwf : vec.wellFormed = true)
    (hpos0 : position ≠ 0)
    (hin : ¬ (mBvSize mem vec < position))
    (hbound : position.toNat ≤ vec.slots.region.capacity) :
    mBvGetAt (mBvSetAt mem vec position value) vec position = value := by
  have hsize := mBvSetAt_size vec mem position value hwf hpos0 hin hbound
  have hpos_ge := u64_toNat_pos hpos0
  have hws : mFieldWord vec.slots position
      = some (vec.slots.firstWord + (position.toNat - 1) * vec.slots.region.strideWords) :=
    mFieldWord_bv_slots vec hwf position hpos_ge hbound
  have hproj : mBvSetAt mem vec position value
      = mWriteField mem vec.slots position value := by
    unfold mBvSetAt
    rw [if_neg (by
      intro h
      rcases h with h0 | hlt
      · exact hpos0 h0
      · exact hin hlt)]
  unfold mBvGetAt
  have hin' : ¬ (mBvSize (mBvSetAt mem vec position value) vec < position) := by
    rw [hsize]; exact hin
  rw [if_neg (by
    intro h
    rcases h with h0 | hlt
    · exact hpos0 h0
    · exact hin' hlt), hproj]
  exact mReadField_write_same mem vec.slots position value _ hws

/-- **非空 pop 后 count 恰 −1**。 -/
theorem mBvPop_size (mem : AccountWords) (hwf : vec.wellFormed = true)
    (hne : mBvSize mem vec ≠ 0)
    (hbound : (mBvSize mem vec).toNat ≤ vec.slots.region.capacity) :
    mBvSize (mBvPop mem vec).1 vec = mBvSize mem vec - 1 := by
  have hsize_ge := u64_toNat_pos hne
  have hproj : (mBvPop mem vec).1
      = mWriteField mem vec.count 0 (mBvSize mem vec - 1) := by
    simp only [mBvPop]
    rw [if_neg hne]
  rw [hproj]
  unfold mBvSize
  exact mReadField_write_same mem vec.count 0 (mReadField mem vec.count 0 - 1) _
    (mFieldWord_bv_count vec hwf)

/-- **非空 pop 返回原末槽值**（payload 槽本身不被 pop 清零）。 -/
theorem mBvPop_get (mem : AccountWords) (hwf : vec.wellFormed = true)
    (hne : mBvSize mem vec ≠ 0)
    (_hbound : (mBvSize mem vec).toNat ≤ vec.slots.region.capacity) :
    (mBvPop mem vec).2 = mReadField mem vec.slots (mBvSize mem vec) := by
  simp only [mBvPop]
  rw [if_neg hne]

/-- **push→pop 往返**：未满 push 后 pop 读回原 value，count 复原。 -/
theorem mBvPush_pop_roundtrip (mem : AccountWords) (v : UInt64)
    (hwf : vec.wellFormed = true)
    (hfull : mBvSize mem vec < BoundedVec.capacity vec) :
    let afterPush := (mBvPush mem vec v).1
    (mBvPop afterPush vec).2 = v ∧
    mBvSize (mBvPop afterPush vec).1 vec = mBvSize mem vec := by
  have hsize_push := mBvPush_size vec mem v hwf hfull
  have hget_push := mBvPush_get vec mem v hwf hfull
  have hpos : (mBvSize mem vec + 1).toNat = (mBvSize mem vec).toNat + 1 :=
    u64_toNat_add_one (show (mBvSize mem vec).toNat < 65536 by
      have h1 : (mBvSize mem vec).toNat < vec.slots.region.capacity :=
        toNat_lt_ofNat hfull (boundedVec_wf_capacity vec hwf)
      have hcap'' : vec.slots.region.capacity ≤ 65536 :=
        boundedVec_wf_capacity vec hwf
      omega)
  have hsize_lt : (mBvSize mem vec).toNat < vec.slots.region.capacity :=
    toNat_lt_ofNat hfull (boundedVec_wf_capacity vec hwf)
  have hret : (mBvPush mem vec v).2 = mBvSize mem vec + 1 := by
    simp only [mBvPush]
    rw [if_neg (by
      show ¬(BoundedVec.capacity vec ≤ mBvSize mem vec)
      exact fun hc => by
        have h2 : (BoundedVec.capacity vec).toNat ≤ (mBvSize mem vec).toNat := hc
        rw [bv_capacity_toNat vec hwf] at h2
        exact absurd h2 (Nat.not_le_of_lt hsize_lt))]
  have hne : mBvSize (mBvPush mem vec v).1 vec ≠ 0 := by
    rw [hsize_push]
    intro heq
    have h1' : (mBvSize mem vec + 1).toNat = (0 : UInt64).toNat :=
      congrArg UInt64.toNat heq
    rw [hpos] at h1'
    have h0 : UInt64.toNat 0 = 0 := rfl
    rw [h0] at h1'
    omega
  have hbound : (mBvSize (mBvPush mem vec v).1 vec).toNat ≤ vec.slots.region.capacity := by
    rw [hsize_push, hpos]
    omega
  have hpop_val := mBvPop_get vec (mBvPush mem vec v).1 hwf hne hbound
  have hpop_size := mBvPop_size vec (mBvPush mem vec v).1 hwf hne hbound
  have hslot :
      mReadField (mBvPush mem vec v).1 vec.slots
        (mBvSize (mBvPush mem vec v).1 vec) = v := by
    have : mBvGetAt (mBvPush mem vec v).1 vec (mBvPush mem vec v).2 = v := hget_push
    unfold mBvGetAt at this
    rw [hsize_push, hret] at this
    have hposne : ¬((mBvSize mem vec + 1 : UInt64) = 0) := fun heq => by
      have h1' : (mBvSize mem vec + 1).toNat = (0 : UInt64).toNat :=
        congrArg UInt64.toNat heq
      rw [hpos] at h1'
      have h0 : UInt64.toNat 0 = 0 := rfl
      rw [h0] at h1'
      omega
    have hlt2 : ¬((mBvSize mem vec + 1 : UInt64) < (mBvSize mem vec + 1 : UInt64)) :=
      fun h => absurd (show _ < _ from h) (Nat.lt_irrefl _)
    rw [if_neg (by
      intro hdisj
      rcases hdisj with h0 | hlt
      · exact hposne h0
      · exact hlt2 hlt)] at this
    simpa [hsize_push] using this
  refine ⟨?_, ?_⟩
  · simpa [hslot] using hpop_val
  · have hsub : (mBvSize mem vec + 1 - 1 : UInt64) = mBvSize mem vec := by
      apply UInt64.toNat.inj
      have h1 := u64_toNat_sub_one (a := mBvSize mem vec + 1) (by rw [hpos]; omega)
      rw [h1, hpos]
      simp
    simpa [hsize_push, hsub] using hpop_size

end BvWfAlgebra

section QueueProofs

open ProofForge.Svm.Sdk.Queue

variable (q : BoundedQueue)

/-! ### BoundedQueue fail-closed 几何与 push/pop 代数 -/

/-- wf 的结构化合同（7 叶）。 -/
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

/-- wf 下 slots 的访问词公式。 -/
theorem mFieldWord_queue_slots (hwf : q.wellFormed = true) (pos : UInt64)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ q.slots.region.capacity) :
    mFieldWord q.slots pos =
      some (q.slots.firstWord + (pos.toNat - 1) * q.slots.region.strideWords) := by
  have parts := queue_wf_parts q hwf
  have mparts := mutableOneBased_wf_parts (h := parts.1)
  have hidx := indexBase_beq_one_eq mparts.2.2.1
  unfold mFieldWord
  rw [hidx]
  simp only [h1, h2, and_true, if_true, Field.firstWord]

/-- **count ≠ head**（head+1 = count，两词相邻但不重叠）。 -/
theorem queue_count_ne_head (hwf : q.wellFormed = true) :
    q.count.firstWord ≠ q.head.firstWord := by
  have parts := queue_wf_parts q hwf
  omega

/-- **count ≠ slots 词**。 -/
theorem queue_count_ne_slots (hwf : q.wellFormed = true) (pos : UInt64)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ q.slots.region.capacity) :
    q.count.firstWord ≠
      q.slots.firstWord + (pos.toNat - 1) * q.slots.region.strideWords := by
  have parts := queue_wf_parts q hwf
  have h1' : q.count.firstWord + 1 ≤ q.slots.firstWord := parts.2.2.2.2.2.2
  omega

/-- **head ≠ slots 词**。 -/
theorem queue_head_ne_slots (hwf : q.wellFormed = true) (pos : UInt64)
    (h1 : (1 : Nat) ≤ pos.toNat) (h2 : pos.toNat ≤ q.slots.region.capacity) :
    q.head.firstWord ≠
      q.slots.firstWord + (pos.toNat - 1) * q.slots.region.strideWords := by
  have parts := queue_wf_parts q hwf
  have h1' : q.head.firstWord + 1 = q.count.firstWord := parts.2.2.2.2.2.1
  have h2' : q.count.firstWord + 1 ≤ q.slots.firstWord := parts.2.2.2.2.2.2
  omega


/-! ### BoundedQueue push / pop 的模型语义（组件级）

与 `Sdk.Queue.push` / `BoundedQueue.pop` 的非满分支逐字对应的写入组合。
守卫（满/空）行为由 no-op 定理覆盖；数值前提（`tail ∈ [1, cap]`、无回绕）
作为显式假设 —— 它们是运行时不变量，发射层由 checked stubs 兜底。 -/

/-- push 非满分支的写入序列（tail 显式给出）。 -/
def mQueuePushAt (mem : AccountWords) (q : BoundedQueue) (tail value hd s : UInt64)
    : AccountWords :=
  mWriteField (mWriteField (mWriteField mem q.slots tail value) q.count 0 (s + 1))
    q.head 0 hd

/-- pop 非空分支的写入序列（head 新值显式给出）。 -/
def mQueuePopAt (mem : AccountWords) (q : BoundedQueue) (remaining hd : UInt64)
    : AccountWords :=
  mWriteField (mWriteField mem q.count 0 remaining) q.head 0 hd

/-- **push 三写组合**（tail 合法、stride = 1）：
count 读回 = size + 1、slots tail 读回 = value。 -/
theorem mQueuePushAt_twoWrites (mem : AccountWords) (q : BoundedQueue) (tail value hd : UInt64)
    (hwf : q.wellFormed = true)
    (hp1 : (1 : Nat) ≤ tail.toNat) (hp2 : tail.toNat ≤ q.slots.region.capacity) :
    mReadField (mQueuePushAt mem q tail value hd (mReadField mem q.count 0)) q.count 0
      = mReadField mem q.count 0 + 1 ∧
    mReadField (mQueuePushAt mem q tail value hd (mReadField mem q.count 0)) q.slots tail
      = value := by
  have hwc := mFieldWord_queue_count q hwf
  have hwh := mFieldWord_queue_head q hwf
  have hws := mFieldWord_queue_slots q hwf tail hp1 hp2
  have hnc : q.count.firstWord
      ≠ q.slots.firstWord + (tail.toNat - 1) * q.slots.region.strideWords :=
    queue_count_ne_slots q hwf tail hp1 hp2
  have hnh : q.head.firstWord
      ≠ q.slots.firstWord + (tail.toNat - 1) * q.slots.region.strideWords :=
    queue_head_ne_slots q hwf tail hp1 hp2
  have hch := queue_count_ne_head q hwf
  unfold mQueuePushAt mWriteField mReadField
  rw [hwc, hws, hwh]
  constructor
  · -- 读 count 词：绕过 head 写（count ≠ head）、slots 写（count ≠ slots）；count 写 same
    simp only [mWriteWord, if_neg hch, if_pos rfl, if_neg hnc]
    rfl
  · -- 读 slots tail 词：绕过 head、count 两层；slots 写 same
    simp only [mWriteWord,
      show ¬ (q.slots.firstWord + (tail.toNat - 1) * q.slots.region.strideWords
        = q.head.firstWord) from fun hc => hnh hc.symm,
      if_pos rfl,
      show ¬ (q.slots.firstWord + (tail.toNat - 1) * q.slots.region.strideWords
        = q.count.firstWord) from fun hc => hnc hc.symm]
    rfl


/-- **pop 两写组合**：write count 与 write head 之后，slots head 词读不变、
count 读回 = remaining。 -/
theorem mQueuePopAt_twoWrites (mem : AccountWords) (q : BoundedQueue) (head remaining hd : UInt64)
    (hwf : q.wellFormed = true) (hp : (1 : Nat) ≤ head.toNat)
    (hcp : head.toNat ≤ q.slots.region.capacity) :
    mReadField (mQueuePopAt mem q remaining hd) q.slots head
      = mReadField mem q.slots head ∧
    mReadField (mQueuePopAt mem q remaining hd) q.count 0 = remaining := by
  have hwc' : mFieldWord q.count 0 = some q.count.firstWord :=
    mFieldWord_queue_count q hwf
  have hwh' : mFieldWord q.head 0 = some q.head.firstWord :=
    mFieldWord_queue_head q hwf
  have hws' : mFieldWord q.slots head
      = some (q.slots.firstWord + (head.toNat - 1) * q.slots.region.strideWords) :=
    mFieldWord_queue_slots q hwf head hp hcp
  have hch := queue_count_ne_head q hwf
  have hnc : q.count.firstWord
      ≠ q.slots.firstWord + (head.toNat - 1) * q.slots.region.strideWords :=
    queue_count_ne_slots q hwf head hp hcp
  have hnh : q.head.firstWord
      ≠ q.slots.firstWord + (head.toNat - 1) * q.slots.region.strideWords :=
    queue_head_ne_slots q hwf head hp hcp
  have e1 : mReadField (mQueuePopAt mem q remaining hd) q.slots head
      = mReadField mem q.slots head := by
    have step1 : mReadField (mWriteField (mWriteField mem q.count 0 remaining)
        q.head 0 hd) q.slots head
      = mReadField (mWriteField mem q.count 0 remaining) q.slots head :=
        mReadField_write_other _ q.slots q.head _ _ hd
          (hws') (hwh') (fun hc => hnh hc.symm)
    have step2 : mReadField (mWriteField mem q.count 0 remaining) q.slots head
      = mReadField mem q.slots head :=
        mReadField_write_other _ q.slots q.count _ _ remaining
          (hws') (hwc') (fun hc => hnc hc.symm)
    exact step1.trans step2
  have e2 : mReadField (mQueuePopAt mem q remaining hd) q.count 0
      = mReadField (mWriteField mem q.count 0 remaining) q.count 0 := by
    have step : mReadField (mWriteField (mWriteField mem q.count 0 remaining)
        q.head 0 hd) q.count 0
      = mReadField (mWriteField mem q.count 0 remaining) q.count 0 :=
        mReadField_write_other _ q.count q.head _ _ hd
          (hwc') (hwh') hch
    exact step
  rw [e1, e2, mReadField_write_same _ _ _ _ (q.count.firstWord) (hwc')]
  exact ⟨rfl, rfl⟩


/-- 模型版 push：与 `BoundedQueue.push` 逐字对应（环尾 + 双 header 写）。 -/
def mQueuePush (mem : AccountWords) (q : BoundedQueue) (value : UInt64) : AccountWords × UInt64 :=
  let size := mReadField mem q.count 0
  let cap := BoundedQueue.capacity q
  if cap ≤ size then (mem, 0)
  else
    let head := mReadField mem q.head 0
    let raw := head + size
    let tail := if head = 0 then 1
      else if cap < raw then raw - cap
      else raw
    (mQueuePushAt mem q tail value (if head = 0 then 1 else head) size, tail)

/-- 环后继：与 `Sdk.Queue.nextSlot` 逐字对应。 -/
def mQueueNext (slot capacity : UInt64) : UInt64 :=
  if slot = capacity then 1 else slot + 1

/-- 模型版 pop：与 `BoundedQueue.pop` 逐字对应。 -/
def mQueuePop (mem : AccountWords) (q : BoundedQueue) : AccountWords × UInt64 :=
  let size := mReadField mem q.count 0
  let head := mReadField mem q.head 0
  if size = 0 ∨ head = 0 then (mem, 0)
  else
    let value := mReadField mem q.slots head
    let remaining := size - 1
    let hd := if remaining = 0 then 0 else mQueueNext head (BoundedQueue.capacity q)
    (mQueuePopAt mem q remaining hd, value)

/-- **push 满守卫无写**：cap ≤ size 时 push 返回 (mem, 0)。 -/
theorem mQueuePush_full_noop (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hfull : BoundedQueue.capacity q ≤ mReadField mem q.count 0) :
    mQueuePush mem q value = (mem, 0) := by
  unfold mQueuePush
  rw [if_pos hfull]

/-- **pop 空守卫无写**：`size = 0` 或 `head = 0` 时不改内存、返回 0。 -/
theorem mQueuePop_empty_noop (mem : AccountWords) (q : BoundedQueue)
    (h : mReadField mem q.count 0 = 0 ∨ mReadField mem q.head 0 = 0) :
    mQueuePop mem q = (mem, 0) := by
  unfold mQueuePop
  rcases h with hc | hr
  · rw [if_pos (Or.inl hc)]
  · rw [if_pos (Or.inr hr)]


/-- wf 队列容量数值事实：toNat 保真 + 容量 ≥ 1。 -/
theorem mQueueCapacityFacts (q : BoundedQueue) (hwf : q.wellFormed = true) :
    (BoundedQueue.capacity q).toNat = q.slots.region.capacity ∧
      (1 : Nat) ≤ q.slots.region.capacity := by
  have hcap3 : q.slots.region.capacity ≤ 65536 := (queue_wf_parts q hwf).2.2.1
  have hcap1 : (0 : Nat) < q.slots.region.capacity := by
    have hh1 := (queue_wf_parts q hwf).1
    unfold Field.mutableOneBasedWord Field.wellFormed Region.wellFormed at hh1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hh1
    exact hh1.1.1.1.1.1.1.1.1.1.1.2
  refine ⟨?_, hcap1⟩
  show (UInt64.ofNat q.slots.region.capacity).toNat = _
  have h2 : (UInt64.ofNat q.slots.region.capacity).toNat
      = q.slots.region.capacity % 2 ^ 64 := UInt64.toNat_ofNat
  rw [h2, show (2:Nat)^64 = 4294967296*4294967296 from by decide]
  exact Nat.mod_eq_of_lt (by omega)

/-- **空推链接**：head = 0 且 size = 0 时，`mQueuePush` 整体恰为
`mQueuePushAt` 的三写组合（tail = 1、head 写 1）。 -/
theorem mQueuePush_empty_links (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : mReadField mem q.count 0 = 0)
    (hhead : mReadField mem q.head 0 = 0) :
    mQueuePush mem q value =
      (mQueuePushAt mem q 1 value 1 0, 1) := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hguard : ¬ (BoundedQueue.capacity q ≤ (0:UInt64)) := by
    intro hh
    have h1 := (UInt64.le_iff_toNat_le).mp hh
    rw [hcapnat] at h1
    have hz : UInt64.toNat 0 = 0 := rfl
    omega
  unfold mQueuePush
  simp only [hsize, hhead, if_neg hguard]
  simp


/-- **空推读回**：push（head = 0, size = 0）的三写完整读回 ——
count 读 1、head 读 1、payload 槽 1 读回 value。 -/
theorem mQueuePush_empty_readback (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : mReadField mem q.count 0 = 0)
    (hhead : mReadField mem q.head 0 = 0) :
    mReadField (mQueuePush mem q value).1 q.count 0 = 1 ∧
    mReadField (mQueuePush mem q value).1 q.head 0 = 1 ∧
    mReadField (mQueuePush mem q value).1 q.slots 1 = value := by
  rw [mQueuePush_empty_links mem q value hwf hsize hhead]
  have hcap3 : q.slots.region.capacity ≤ 65536 := (queue_wf_parts q hwf).2.2.1
  have hs0 : (mReadField mem q.count 0).toNat = 0 := by
    rw [hsize]
    rfl
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  refine ⟨?_, ?_, ?_⟩
  have h1n : UInt64.toNat 1 = 1 := rfl
  · -- count 读 1（size + 1 且 size = 0）
    have h2 := mQueuePushAt_twoWrites mem q 1 value 1 hwf
      (by decide) (by omega)
    rw [hsize] at h2
    show mReadField (mQueuePushAt mem q 1 value 1 0) q.count 0 = (1:UInt64)
    rw [h2.1]
    rfl
  · -- head 读 1（写 same）
    exact mReadField_write_same _ _ _ _ q.head.firstWord
      (mFieldWord_queue_head q hwf)
  · -- slots 1 读回 value
    have h2 := mQueuePushAt_twoWrites mem q 1 value 1 hwf
      (by decide) (by exact hcap1)
    rw [hsize] at h2
    exact h2.2


/-! ### push 非空分支（nowrap）-/

/-- 通用 UInt64 加法无回绕桥。 -/
private theorem u64toNatAdd {a b : UInt64} (h : a.toNat + b.toNat < 4294967296*4294967296) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  have h2 : (2:Nat)^64 = 4294967296*4294967296 := by decide
  rw [h2]
  exact Nat.mod_eq_of_lt h

/-- 通用 UInt64 减法无下溢桥。 -/
private theorem u64toNatSub {a b : UInt64} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  have hbig : (2:Nat)^64 = 4294967296*4294967296 := by decide
  have hlt : a.toNat < 4294967296*4294967296 := by
    obtain ⟨w⟩ := a
    have := w.isLt
    simpa [hbig] using this
  rw [UInt64.toNat_sub, hbig]
  omega

/-- **非空推链接（nowrap）**：head ≠ 0、head + size ≤ cap 时，
`mQueuePush` 整体 = `mQueuePushAt` 的三写组合（tail = head + size、
head 写回自身）。 -/
theorem mQueuePush_nowrap_links (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : (mReadField mem q.count 0).toNat < q.slots.region.capacity)
    (hhead : mReadField mem q.head 0 ≠ 0)
    (hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity)
    (hnowrap : ¬ (BoundedQueue.capacity q < mReadField mem q.head 0 + mReadField mem q.count 0)) :
    mQueuePush mem q value =
      (mQueuePushAt mem q
        (mReadField mem q.head 0 + mReadField mem q.count 0) value
        (mReadField mem q.head 0) (mReadField mem q.count 0),
        mReadField mem q.head 0 + mReadField mem q.count 0) := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  -- 守卫：size < cap
  have hguard : ¬ (BoundedQueue.capacity q ≤ mReadField mem q.count 0) := by
    intro hh
    have h1 := (UInt64.le_iff_toNat_le).mp hh
    rw [hcapnat] at h1
    omega
  -- 加法无回绕
  have hnowraw : (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
      = (mReadField mem q.head 0).toNat + (mReadField mem q.count 0).toNat :=
    u64toNatAdd (by
      have hlt : q.slots.region.capacity ≤ 65536 := (queue_wf_parts q hwf).2.2.1
      have := hsize
      have := hheadb
      omega)
  unfold mQueuePush
  simp only [if_neg hguard, if_neg hhead, if_neg hnowrap]


/-- **非空推读回（nowrap）**：链接后 count = size+1、head 不变、payload 槽读回 value。 -/
theorem mQueuePush_nowrap_readback (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : (mReadField mem q.count 0).toNat < q.slots.region.capacity)
    (hhead : mReadField mem q.head 0 ≠ 0)
    (hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity)
    (hnowrap : ¬ (BoundedQueue.capacity q < mReadField mem q.head 0 + mReadField mem q.count 0)) :
    let size := mReadField mem q.count 0
    let head := mReadField mem q.head 0
    let tail := head + size
    mReadField (mQueuePush mem q value).1 q.count 0 = size + 1 ∧
    mReadField (mQueuePush mem q value).1 q.head 0 = head ∧
    mReadField (mQueuePush mem q value).1 q.slots tail = value := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hlt : q.slots.region.capacity ≤ 65536 := (queue_wf_parts q hwf).2.2.1
  have hnowraw : (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
      = (mReadField mem q.head 0).toNat + (mReadField mem q.count 0).toNat :=
    u64toNatAdd (by
      have := hsize
      have := hheadb
      omega)
  have htail_le : (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
      ≤ q.slots.region.capacity := by
    have hle' : (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
        ≤ (BoundedQueue.capacity q).toNat := by
      have : ¬ ((BoundedQueue.capacity q).toNat
          < (mReadField mem q.head 0 + mReadField mem q.count 0).toNat) := by
        intro hlt'
        have hcap_lt : BoundedQueue.capacity q <
            mReadField mem q.head 0 + mReadField mem q.count 0 :=
          (UInt64.lt_iff_toNat_lt).mpr hlt'
        exact hnowrap hcap_lt
      omega
    rw [hcapnat] at hle'
    exact hle'
  have htail_ge : (1 : Nat) ≤ (mReadField mem q.head 0 + mReadField mem q.count 0).toNat := by
    have hhn : (0 : Nat) < (mReadField mem q.head 0).toNat := by
      have : (mReadField mem q.head 0).toNat ≠ 0 := by
        intro hz
        apply hhead
        cases hhd : mReadField mem q.head 0 with
        | ofBitVec val =>
          have hz' : val.toNat = 0 := by
            simpa [hhd, UInt64.toNat] using hz
          have : val = 0 := BitVec.eq_of_toNat_eq (by simp [hz'])
          subst this
          rfl
      omega
    rw [hnowraw]
    omega
  have links := mQueuePush_nowrap_links mem q value hwf hsize hhead hheadb hnowrap
  rw [links]
  have h2 := mQueuePushAt_twoWrites mem q
    (mReadField mem q.head 0 + mReadField mem q.count 0) value
    (mReadField mem q.head 0) hwf htail_ge htail_le
  refine ⟨h2.1, ?_, h2.2⟩
  exact mReadField_write_same _ _ _ _ q.head.firstWord
    (mFieldWord_queue_head q hwf)


/-- **非空推链接（wrap）**：head ≠ 0、cap < head + size 时，
`mQueuePush` 整体 = `mQueuePushAt` 的三写组合（tail = head + size - cap、
head 写回自身）。 -/
theorem mQueuePush_wrap_links (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : (mReadField mem q.count 0).toNat < q.slots.region.capacity)
    (hhead : mReadField mem q.head 0 ≠ 0)
    (hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity)
    (hwrap : BoundedQueue.capacity q < mReadField mem q.head 0 + mReadField mem q.count 0) :
    mQueuePush mem q value =
      (mQueuePushAt mem q
        (mReadField mem q.head 0 + mReadField mem q.count 0 - BoundedQueue.capacity q) value
        (mReadField mem q.head 0) (mReadField mem q.count 0),
        mReadField mem q.head 0 + mReadField mem q.count 0 - BoundedQueue.capacity q) := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hlt : q.slots.region.capacity ≤ 65536 := (queue_wf_parts q hwf).2.2.1
  have hguard : ¬ (BoundedQueue.capacity q ≤ mReadField mem q.count 0) := by
    intro hh
    have h1 := (UInt64.le_iff_toNat_le).mp hh
    rw [hcapnat] at h1
    omega
  have hnowraw : (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
      = (mReadField mem q.head 0).toNat + (mReadField mem q.count 0).toNat :=
    u64toNatAdd (by
      have := hsize
      have := hheadb
      omega)
  unfold mQueuePush
  simp only [if_neg hguard, if_neg hhead, if_pos hwrap]


/-- **非空推读回（wrap）**：链接后 count = size+1、head 不变、环绕 payload 槽读回 value。 -/
theorem mQueuePush_wrap_readback (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : (mReadField mem q.count 0).toNat < q.slots.region.capacity)
    (hhead : mReadField mem q.head 0 ≠ 0)
    (hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity)
    (hwrap : BoundedQueue.capacity q < mReadField mem q.head 0 + mReadField mem q.count 0) :
    let size := mReadField mem q.count 0
    let head := mReadField mem q.head 0
    let tail := head + size - BoundedQueue.capacity q
    mReadField (mQueuePush mem q value).1 q.count 0 = size + 1 ∧
    mReadField (mQueuePush mem q value).1 q.head 0 = head ∧
    mReadField (mQueuePush mem q value).1 q.slots tail = value := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hlt : q.slots.region.capacity ≤ 65536 := (queue_wf_parts q hwf).2.2.1
  have hnowraw : (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
      = (mReadField mem q.head 0).toNat + (mReadField mem q.count 0).toNat :=
    u64toNatAdd (by
      have := hsize
      have := hheadb
      omega)
  have hraw_ge_cap : (BoundedQueue.capacity q).toNat
      < (mReadField mem q.head 0 + mReadField mem q.count 0).toNat :=
    (UInt64.lt_iff_toNat_lt).mp hwrap
  have hsub : (mReadField mem q.head 0 + mReadField mem q.count 0
        - BoundedQueue.capacity q).toNat
      = (mReadField mem q.head 0 + mReadField mem q.count 0).toNat
        - (BoundedQueue.capacity q).toNat :=
    u64toNatSub (by omega)
  have htail_ge : (1 : Nat)
      ≤ (mReadField mem q.head 0 + mReadField mem q.count 0
        - BoundedQueue.capacity q).toNat := by
    rw [hsub, hnowraw, hcapnat]
    have := hsize
    have := hheadb
    omega
  have htail_le : (mReadField mem q.head 0 + mReadField mem q.count 0
        - BoundedQueue.capacity q).toNat
      ≤ q.slots.region.capacity := by
    rw [hsub, hnowraw, hcapnat]
    have := hsize
    have := hheadb
    omega
  have links := mQueuePush_wrap_links mem q value hwf hsize hhead hheadb hwrap
  rw [links]
  have h2 := mQueuePushAt_twoWrites mem q
    (mReadField mem q.head 0 + mReadField mem q.count 0 - BoundedQueue.capacity q) value
    (mReadField mem q.head 0) hwf htail_ge htail_le
  refine ⟨h2.1, ?_, h2.2⟩
  exact mReadField_write_same _ _ _ _ q.head.firstWord
    (mFieldWord_queue_head q hwf)


/-- **pop 清空链接**：size = 1 时，`mQueuePop` 整体 = `mQueuePopAt` 的
两写组合（remaining = 0、head 复位 0），返回队首值。 -/
theorem mQueuePop_clear_links (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true)
    (hsize : mReadField mem q.count 0 = 1)
    (hhead : mReadField mem q.head 0 ≠ 0) :
    mQueuePop mem q =
      (mQueuePopAt mem q 0 0, mReadField mem q.slots (mReadField mem q.head 0)) := by
  have hguard : ¬ ((mReadField mem q.count 0) = 0 ∨ (mReadField mem q.head 0) = 0) := by
    rw [hsize]
    simp [hhead, show ((1:UInt64) = (0:UInt64)) = False from by decide]
  unfold mQueuePop
  rw [if_neg hguard, hsize]
  simp

/-- **pop 推进链接（head ≠ cap）**：size ≥ 2 且 head ≠ cap 时，
`mQueuePop` 整体 = `mQueuePopAt` 的两写组合（remaining = size - 1、
head 推进 head + 1），返回队首值。 -/
theorem mQueuePop_advance_links (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true)
    (hsize : (2 : Nat) ≤ (mReadField mem q.count 0).toNat)
    (hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity)
    (hhead0 : mReadField mem q.head 0 ≠ 0)
    (hneqcap : ¬ (mReadField mem q.head 0 = (BoundedQueue.capacity q))) :
    mQueuePop mem q =
      (mQueuePopAt mem q (mReadField mem q.count 0 - 1)
        (mReadField mem q.head 0 + 1),
        mReadField mem q.slots (mReadField mem q.head 0)) := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hguard : ¬ ((mReadField mem q.count 0) = 0 ∨ (mReadField mem q.head 0) = 0) := by
    intro h
    rcases h with hc | hr
    · have h2 : (mReadField mem q.count 0).toNat = 0 := by
        rw [hc]
        rfl
      omega
    · exact hhead0 hr
  -- remaining = size - 1 ≠ 0
  have hrem : ¬ ((mReadField mem q.count 0 - (1:UInt64)) = 0) := by
    intro hc
    have h1n : UInt64.toNat 1 = 1 := rfl
    have hs2 : (mReadField mem q.count 0).toNat ≥ 2 := hsize
    have h1 : ((mReadField mem q.count 0 - (1:UInt64)).toNat)
        = (mReadField mem q.count 0).toNat - 1 :=
      u64toNatSub (by omega)
    have h2 : (mReadField mem q.count 0 - (1:UInt64)).toNat = 0 := by
      rw [hc]
      rfl
    rw [h2] at h1
    omega
  unfold mQueuePop
  simp only [if_neg hguard, if_neg hrem, mQueueNext, if_neg hneqcap]


/-- **pop 环绕推进链接**：size ≥ 2 且 head = cap 时，
`mQueuePop` 整体 = `mQueuePopAt`（remaining = size - 1、head 复位 1）。 -/
theorem mQueuePop_wrap_advance_links (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true)
    (hsize : (2 : Nat) ≤ (mReadField mem q.count 0).toNat)
    (hhead0 : mReadField mem q.head 0 ≠ 0)
    (heqcap : mReadField mem q.head 0 = BoundedQueue.capacity q) :
    mQueuePop mem q =
      (mQueuePopAt mem q (mReadField mem q.count 0 - 1) 1,
        mReadField mem q.slots (mReadField mem q.head 0)) := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hguard : ¬ ((mReadField mem q.count 0) = 0 ∨ (mReadField mem q.head 0) = 0) := by
    intro h
    rcases h with hc | hr
    · have h2 : (mReadField mem q.count 0).toNat = 0 := by
        rw [hc]
        rfl
      omega
    · exact hhead0 hr
  have hrem : ¬ ((mReadField mem q.count 0 - (1:UInt64)) = 0) := by
    intro hc
    have h1n : UInt64.toNat 1 = 1 := rfl
    have hs2 : (mReadField mem q.count 0).toNat ≥ 2 := hsize
    have h1 : ((mReadField mem q.count 0 - (1:UInt64)).toNat)
        = (mReadField mem q.count 0).toNat - 1 :=
      u64toNatSub (by omega)
    have h2 : (mReadField mem q.count 0 - (1:UInt64)).toNat = 0 := by
      rw [hc]
      rfl
    rw [h2] at h1
    omega
  unfold mQueuePop
  simp only [if_neg hguard, if_neg hrem, mQueueNext, if_pos heqcap]


/-- **pop 清空读回**：size = 1 时，pop 后 count = 0、head = 0，返回原队首 payload。 -/
theorem mQueuePop_clear_readback (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true)
    (hsize : mReadField mem q.count 0 = 1)
    (hhead : mReadField mem q.head 0 ≠ 0)
    (hheadb : (1 : Nat) ≤ (mReadField mem q.head 0).toNat)
    (hheadc : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity) :
    let head := mReadField mem q.head 0
    let value := mReadField mem q.slots head
    (mQueuePop mem q).2 = value ∧
    mReadField (mQueuePop mem q).1 q.count 0 = 0 ∧
    mReadField (mQueuePop mem q).1 q.head 0 = 0 ∧
    mReadField (mQueuePop mem q).1 q.slots head = value := by
  have links := mQueuePop_clear_links mem q hwf hsize hhead
  rw [links]
  have h2 := mQueuePopAt_twoWrites mem q (mReadField mem q.head 0) 0 0 hwf hheadb hheadc
  refine ⟨rfl, h2.2, ?_, h2.1⟩
  exact mReadField_write_same _ _ _ _ q.head.firstWord
    (mFieldWord_queue_head q hwf)


/-- **pop 推进读回（非环绕）**：size ≥ 2 且 head ≠ cap 时，
count = size-1、head = head+1、payload 槽不变。 -/
theorem mQueuePop_advance_readback (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true)
    (hsize : (2 : Nat) ≤ (mReadField mem q.count 0).toNat)
    (hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity)
    (hhead0 : mReadField mem q.head 0 ≠ 0)
    (hneqcap : ¬ (mReadField mem q.head 0 = BoundedQueue.capacity q)) :
    let head := mReadField mem q.head 0
    let size := mReadField mem q.count 0
    let value := mReadField mem q.slots head
    (mQueuePop mem q).2 = value ∧
    mReadField (mQueuePop mem q).1 q.count 0 = size - 1 ∧
    mReadField (mQueuePop mem q).1 q.head 0 = head + 1 ∧
    mReadField (mQueuePop mem q).1 q.slots head = value := by
  have hhead_ge : (1 : Nat) ≤ (mReadField mem q.head 0).toNat := by
    have : (mReadField mem q.head 0).toNat ≠ 0 := by
      intro hz
      apply hhead0
      cases hhd : mReadField mem q.head 0 with
      | ofBitVec val =>
        have hz' : val.toNat = 0 := by
          simpa [hhd, UInt64.toNat] using hz
        have : val = 0 := BitVec.eq_of_toNat_eq (by simp [hz'])
        subst this
        rfl
    omega
  have links := mQueuePop_advance_links mem q hwf hsize hheadb hhead0 hneqcap
  rw [links]
  have h2 := mQueuePopAt_twoWrites mem q (mReadField mem q.head 0)
    (mReadField mem q.count 0 - 1) (mReadField mem q.head 0 + 1) hwf hhead_ge hheadb
  refine ⟨rfl, h2.2, ?_, h2.1⟩
  exact mReadField_write_same _ _ _ _ q.head.firstWord
    (mFieldWord_queue_head q hwf)


/-- **pop 环绕推进读回**：size ≥ 2 且 head = cap 时，
count = size-1、head = 1、原 payload 槽不变。 -/
theorem mQueuePop_wrap_advance_readback (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true)
    (hsize : (2 : Nat) ≤ (mReadField mem q.count 0).toNat)
    (hhead0 : mReadField mem q.head 0 ≠ 0)
    (heqcap : mReadField mem q.head 0 = BoundedQueue.capacity q) :
    let head := mReadField mem q.head 0
    let size := mReadField mem q.count 0
    let value := mReadField mem q.slots head
    (mQueuePop mem q).2 = value ∧
    mReadField (mQueuePop mem q).1 q.count 0 = size - 1 ∧
    mReadField (mQueuePop mem q).1 q.head 0 = 1 ∧
    mReadField (mQueuePop mem q).1 q.slots head = value := by
  have hcapnat := mQueueCapacityFacts q hwf |>.1
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have hheadb : (mReadField mem q.head 0).toNat ≤ q.slots.region.capacity := by
    rw [heqcap, hcapnat]
    exact Nat.le_refl _
  have hhead_ge : (1 : Nat) ≤ (mReadField mem q.head 0).toNat := by
    rw [heqcap, hcapnat]
    exact hcap1
  have links := mQueuePop_wrap_advance_links mem q hwf hsize hhead0 heqcap
  rw [links]
  have h2 := mQueuePopAt_twoWrites mem q (mReadField mem q.head 0)
    (mReadField mem q.count 0 - 1) 1 hwf hhead_ge hheadb
  refine ⟨rfl, h2.2, ?_, h2.1⟩
  exact mReadField_write_same _ _ _ _ q.head.firstWord
    (mFieldWord_queue_head q hwf)


/-- 模型版 peek：与 `BoundedQueue.peek` 逐字对应。 -/
def mQueuePeek (mem : AccountWords) (q : BoundedQueue) : UInt64 :=
  let head := mReadField mem q.head 0
  if head = 0 then 0 else mReadField mem q.slots head

/-- **空 peek 哨兵**：head = 0 时 peek 返回 0。 -/
theorem mQueuePeek_empty (mem : AccountWords) (q : BoundedQueue)
    (hhead : mReadField mem q.head 0 = 0) :
    mQueuePeek mem q = 0 := by
  unfold mQueuePeek
  simp [hhead]

/-- **非空 peek**：head ≠ 0 时 peek 等于 slots[head]。 -/
theorem mQueuePeek_eq (mem : AccountWords) (q : BoundedQueue)
    (hhead : mReadField mem q.head 0 ≠ 0) :
    mQueuePeek mem q = mReadField mem q.slots (mReadField mem q.head 0) := by
  unfold mQueuePeek
  simp [hhead]


/-- 模型版 initialize：双 header 置零（payload 不动）。 -/
def mQueueInitialize (mem : AccountWords) (q : BoundedQueue) : AccountWords × UInt64 :=
  (mWriteField (mWriteField mem q.head 0 0) q.count 0 0, 1)

/-- **initialize 零头**：两 header 均读回 0，返回 1。 -/
theorem mQueueInitialize_zero_headers (mem : AccountWords) (q : BoundedQueue)
    (hwf : q.wellFormed = true) :
    (mQueueInitialize mem q).2 = 1 ∧
    mReadField (mQueueInitialize mem q).1 q.head 0 = 0 ∧
    mReadField (mQueueInitialize mem q).1 q.count 0 = 0 := by
  unfold mQueueInitialize
  refine ⟨rfl, ?_, ?_⟩
  · have step : mReadField (mWriteField (mWriteField mem q.head 0 0) q.count 0 0) q.head 0
        = mReadField (mWriteField mem q.head 0 0) q.head 0 :=
      mReadField_write_other _ q.head q.count _ _ 0
        (mFieldWord_queue_head q hwf) (mFieldWord_queue_count q hwf)
        (queue_count_ne_head q hwf).symm
    rw [step, mReadField_write_same _ _ _ _ q.head.firstWord
      (mFieldWord_queue_head q hwf)]
  · exact mReadField_write_same _ _ _ _ q.count.firstWord
      (mFieldWord_queue_count q hwf)


/-- **空队列 push→pop 往返**：empty push 后 pop 读回原 value，并清空双 header。 -/
theorem mQueuePush_pop_roundtrip_empty (mem : AccountWords) (q : BoundedQueue) (value : UInt64)
    (hwf : q.wellFormed = true)
    (hsize : mReadField mem q.count 0 = 0)
    (hhead : mReadField mem q.head 0 = 0) :
    let afterPush := (mQueuePush mem q value).1
    (mQueuePop afterPush q).2 = value ∧
    mReadField (mQueuePop afterPush q).1 q.count 0 = 0 ∧
    mReadField (mQueuePop afterPush q).1 q.head 0 = 0 := by
  have hcap1 := mQueueCapacityFacts q hwf |>.2
  have pushLinks := mQueuePush_empty_links mem q value hwf hsize hhead
  have pushRb := mQueuePush_empty_readback mem q value hwf hsize hhead
  -- After empty push: count=1, head=1, slots[1]=value
  have hcount1 : mReadField (mQueuePush mem q value).1 q.count 0 = 1 := pushRb.1
  have hhead1 : mReadField (mQueuePush mem q value).1 q.head 0 = 1 := pushRb.2.1
  have hslot : mReadField (mQueuePush mem q value).1 q.slots 1 = value := pushRb.2.2
  have hhead_ne : mReadField (mQueuePush mem q value).1 q.head 0 ≠ 0 := by
    rw [hhead1]
    decide
  have popRb := mQueuePop_clear_readback (mQueuePush mem q value).1 q hwf hcount1 hhead_ne
    (by rw [hhead1]; decide) (by rw [hhead1]; exact hcap1)
  -- Align value equality through head=1
  have : mReadField (mQueuePush mem q value).1 q.slots
      (mReadField (mQueuePush mem q value).1 q.head 0) = value := by
    rw [hhead1, hslot]
  refine ⟨?_, popRb.2.1, popRb.2.2.1⟩
  simpa [this] using popRb.1

end QueueProofs

/-! ## One-based allocator algebra -/

/-- Slot column for free-list links (word 0 of each one-based slot). -/
def mAllocSlotsField (alloc : Allocator) : Field :=
  { region := alloc.slots }

def mAllocLiveCountField (alloc : Allocator) : Field :=
  @OneBasedAllocator.liveCount alloc

def mAllocLiveCount (mem : AccountWords) (alloc : Allocator) : UInt64 :=
  mReadField mem (mAllocLiveCountField alloc) 0

def mAllocCursor (mem : AccountWords) (alloc : Allocator) : UInt64 :=
  mReadField mem alloc.cursor 0

def mAllocBump (mem : AccountWords) (alloc : Allocator) : UInt64 :=
  mAllocCursor mem alloc &&& 0xffffffff

def mAllocFreeHead (mem : AccountWords) (alloc : Allocator) : UInt64 :=
  mAllocCursor mem alloc >>> 32

/-- Mirror `Allocator.alloc`: reuse the free-list head when present, otherwise bump. -/
def mAlloc (mem : AccountWords) (alloc : Allocator) : AccountWords × UInt64 :=
  let capacity := UInt64.ofNat alloc.slots.capacity
  let count := mAllocLiveCount mem alloc
  let bump := mAllocBump mem alloc
  let freeHead := mAllocFreeHead mem alloc
  if capacity ≤ count then (mem, 0)
  else if freeHead ≠ 0 then
    let next := mReadField mem (mAllocSlotsField alloc) freeHead
    let mem := mWriteField mem alloc.cursor 0 (bump ||| (next <<< 32))
    let mem := mWriteField mem (mAllocLiveCountField alloc) 0 (count + 1)
    (mem, freeHead)
  else if bump < capacity then
    let mem := mWriteField mem alloc.cursor 0 ((bump + (1 : UInt64)) ||| (freeHead <<< 32))
    let mem := mWriteField mem (mAllocLiveCountField alloc) 0 (count + 1)
    (mem, bump + 1)
  else (mem, 0)

/-- Mirror `Allocator.free`: thread the slot through word 0 onto the free list. -/
def mFree (mem : AccountWords) (alloc : Allocator) (slot : UInt64) : AccountWords × UInt64 :=
  let capacity := UInt64.ofNat alloc.slots.capacity
  let count := mAllocLiveCount mem alloc
  let bump := mAllocBump mem alloc
  let freeHead := mAllocFreeHead mem alloc
  if slot = 0 ∨ bump < slot ∨ capacity < slot ∨ count = 0 then (mem, 0)
  else
    let mem := mWriteField mem (mAllocSlotsField alloc) slot freeHead
    let mem := mWriteField mem alloc.cursor 0 (bump ||| (slot <<< 32))
    let mem := mWriteField mem (mAllocLiveCountField alloc) 0 (count - 1)
    (mem, slot)

/-! ### Allocator algebra theorems -/

/-- **满分配返回 0 且不改内存**。 -/
theorem mAlloc_full_noop (mem : AccountWords) (alloc : Allocator)
    (hfull : UInt64.ofNat alloc.slots.capacity ≤ mAllocLiveCount mem alloc) :
    mAlloc mem alloc = (mem, 0) := by
  unfold mAlloc
  rw [if_pos hfull]

/-- **空槽 / 未 bump / 越界 / 空计数 free 返回 0 且不改内存**。 -/
theorem mFree_invalid_noop (mem : AccountWords) (alloc : Allocator) (slot : UInt64)
    (h : slot = 0 ∨ mAllocBump mem alloc < slot ∨
      UInt64.ofNat alloc.slots.capacity < slot ∨ mAllocLiveCount mem alloc = 0) :
    mFree mem alloc slot = (mem, 0) := by
  unfold mFree
  rcases h with h | h | h | h
  · rw [if_pos (Or.inl h)]
  · rw [if_pos (Or.inr (Or.inl h))]
  · rw [if_pos (Or.inr (Or.inr (Or.inl h)))]
  · rw [if_pos (Or.inr (Or.inr (Or.inr h)))]

section AllocProofs

variable (alloc : Allocator)

/-! ### OneBasedAllocator fail-closed 几何 -/

/-- wf 的结构化合同（显式 `@OneBasedAllocator.liveCount`，避免与 `Allocator.liveCount` 读函数混淆）。 -/
theorem allocator_wf_parts (hwf : alloc.wellFormed = true) :
    alloc.slots.wellFormed = true ∧
    (alloc.slots.indexBase == IndexBase.one) = true ∧
    (alloc.slots.access == Access.programOwnedMutable) = true ∧
    (@OneBasedAllocator.liveCount alloc).wellFormed = true ∧
    alloc.cursor.wellFormed = true ∧
    (@OneBasedAllocator.liveCount alloc).widthWords = 1 ∧
    alloc.cursor.widthWords = 1 ∧
    (@OneBasedAllocator.liveCount alloc).region.account = alloc.slots.account ∧
    alloc.cursor.region.account = alloc.slots.account ∧
    (@OneBasedAllocator.liveCount alloc).region.strideWords = 1 ∧
    alloc.cursor.region.strideWords = 1 ∧
    (@OneBasedAllocator.liveCount alloc).region.capacity = 1 ∧
    alloc.cursor.region.capacity = 1 ∧
    ((@OneBasedAllocator.liveCount alloc).region.indexBase == IndexBase.zero) = true ∧
    (alloc.cursor.region.indexBase == IndexBase.zero) = true ∧
    ((@OneBasedAllocator.liveCount alloc).region.access == alloc.slots.access) = true ∧
    (alloc.cursor.region.access == alloc.slots.access) = true ∧
    (@OneBasedAllocator.liveCount alloc).firstWord + 1 = alloc.cursor.firstWord := by
  simp only [OneBasedAllocator.wellFormed, Bool.and_eq_true, beq_iff_eq] at hwf
  exact ⟨hwf.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1,
    hwf.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.1.2,
    hwf.1.1.1.1.1.2,
    hwf.1.1.1.1.2,
    hwf.1.1.1.2,
    hwf.1.1.2,
    hwf.1.2,
    hwf.2⟩

private theorem allocator_slots_capacity_u64 (hwf : alloc.wellFormed = true) :
    alloc.slots.capacity < 2 ^ 64 := by
  have hsw : alloc.slots.wellFormed = true := (allocator_wf_parts alloc hwf).1
  simp [Region.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hsw
  have hgeom : alloc.slots.baseWord + alloc.slots.strideWords * (alloc.slots.capacity - 1) < maxDataWord :=
    hsw.2
  have hcap_pos : 0 < alloc.slots.capacity := hsw.1.1.1.1.2
  have hstride : 0 < alloc.slots.strideWords := hsw.1.1.1.2
  have hcap_le_geom : alloc.slots.capacity - 1 ≤
      alloc.slots.baseWord + alloc.slots.strideWords * (alloc.slots.capacity - 1) := by
    have hmul : alloc.slots.capacity - 1 ≤
        alloc.slots.strideWords * (alloc.slots.capacity - 1) := by
      rcases Nat.eq_zero_or_pos (alloc.slots.capacity - 1) with hz | hp
      · simp [hz]
      · exact Nat.le_mul_of_pos_left (alloc.slots.capacity - 1) hstride
    exact Nat.le_trans hmul (Nat.le_add_left _ _)
  have hcap : alloc.slots.capacity ≤ maxDataWord := by
    have hlt : alloc.slots.capacity - 1 < maxDataWord :=
      Nat.lt_of_le_of_lt hcap_le_geom hgeom
    omega
  exact Nat.lt_of_le_of_lt hcap (by native_decide : maxDataWord < 2 ^ 64)

theorem mAllocLiveCountField_eq (alloc : Allocator) :
    mAllocLiveCountField alloc = @OneBasedAllocator.liveCount alloc := rfl

theorem allocator_wf_indexBase (hwf : alloc.wellFormed = true) :
    (alloc.slots.indexBase == IndexBase.one) = true :=
  (allocator_wf_parts alloc hwf).2.1

theorem allocator_wf_slots_access (hwf : alloc.wellFormed = true) :
    (alloc.slots.access == Access.programOwnedMutable) = true :=
  (allocator_wf_parts alloc hwf).2.2.1

theorem allocator_wf_liveCount_wf (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).wellFormed = true := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.1

theorem allocator_wf_liveCount_width (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).widthWords = 1 := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.1

theorem allocator_wf_liveCount_account (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).region.account = alloc.slots.account := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.1

theorem allocator_wf_liveCount_stride (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).region.strideWords = 1 := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_liveCount_capacity (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).region.capacity = 1 := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_liveCount_indexBase (hwf : alloc.wellFormed = true) :
    ((mAllocLiveCountField alloc).region.indexBase == IndexBase.zero) = true := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_liveCount_access (hwf : alloc.wellFormed = true) :
    ((mAllocLiveCountField alloc).region.access == alloc.slots.access) = true := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_cursor_wf (hwf : alloc.wellFormed = true) :
    alloc.cursor.wellFormed = true :=
  (allocator_wf_parts alloc hwf).2.2.2.2.1

theorem allocator_wf_cursor_width (hwf : alloc.wellFormed = true) :
    alloc.cursor.widthWords = 1 :=
  (allocator_wf_parts alloc hwf).2.2.2.2.2.2.1

theorem allocator_wf_cursor_account (hwf : alloc.wellFormed = true) :
    alloc.cursor.region.account = alloc.slots.account :=
  (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.1

theorem allocator_wf_cursor_stride (hwf : alloc.wellFormed = true) :
    alloc.cursor.region.strideWords = 1 :=
  (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_cursor_capacity (hwf : alloc.wellFormed = true) :
    alloc.cursor.region.capacity = 1 :=
  (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_cursor_indexBase (hwf : alloc.wellFormed = true) :
    (alloc.cursor.region.indexBase == IndexBase.zero) = true :=
  (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_cursor_access (hwf : alloc.wellFormed = true) :
    (alloc.cursor.region.access == alloc.slots.access) = true :=
  (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem allocator_wf_liveCount_adj (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).firstWord + 1 = alloc.cursor.firstWord := by
  simpa [mAllocLiveCountField_eq] using (allocator_wf_parts alloc hwf).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem allocator_slots_stride_pos (hwf : alloc.wellFormed = true) :
    0 < alloc.slots.strideWords := by
  have hsw : alloc.slots.wellFormed = true := (allocator_wf_parts alloc hwf).1
  simp only [Region.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hsw
  exact hsw.1.1.1.2

theorem allocator_scalarHeader_liveCount (hwf : alloc.wellFormed = true)
    (hacc : 0 < alloc.slots.account) :
    scalarHeaderWellFormed (mAllocLiveCountField alloc) alloc.slots.account = true := by
  have hprog : ((mAllocLiveCountField alloc).region.access == Access.programOwnedMutable) = true :=
    access_beq_prog_of_slots (allocator_wf_liveCount_access alloc hwf) (allocator_wf_slots_access alloc hwf)
  exact scalarHeader_wf_build (allocator_wf_liveCount_wf alloc hwf) (allocator_wf_liveCount_width alloc hwf)
    (allocator_wf_liveCount_account alloc hwf) hacc (allocator_wf_liveCount_stride alloc hwf)
    (allocator_wf_liveCount_capacity alloc hwf) (allocator_wf_liveCount_indexBase alloc hwf) hprog

theorem allocator_scalarHeader_cursor (hwf : alloc.wellFormed = true)
    (hacc : 0 < alloc.slots.account) :
    scalarHeaderWellFormed alloc.cursor alloc.slots.account = true := by
  have hprog : (alloc.cursor.region.access == Access.programOwnedMutable) = true :=
    access_beq_prog_of_slots (allocator_wf_cursor_access alloc hwf) (allocator_wf_slots_access alloc hwf)
  exact scalarHeader_wf_build (allocator_wf_cursor_wf alloc hwf) (allocator_wf_cursor_width alloc hwf)
    (allocator_wf_cursor_account alloc hwf) hacc (allocator_wf_cursor_stride alloc hwf)
    (allocator_wf_cursor_capacity alloc hwf) (allocator_wf_cursor_indexBase alloc hwf) hprog

theorem mFieldWord_alloc_liveCount (hwf : alloc.wellFormed = true)
    (hacc : 0 < alloc.slots.account) :
    mFieldWord (mAllocLiveCountField alloc) 0 = some (mAllocLiveCountField alloc).firstWord := by
  have hla := allocator_wf_liveCount_account alloc hwf
  have hsw := allocator_scalarHeader_liveCount alloc hwf hacc
  have hsw' : scalarHeaderWellFormed (mAllocLiveCountField alloc)
      (mAllocLiveCountField alloc).region.account = true := by
    simpa [hla] using hsw
  exact mFieldWord_scalar_header hsw'

theorem mFieldWord_alloc_cursor (hwf : alloc.wellFormed = true)
    (hacc : 0 < alloc.slots.account) :
    mFieldWord alloc.cursor 0 = some alloc.cursor.firstWord := by
  have hca := allocator_wf_cursor_account alloc hwf
  have hsw := allocator_scalarHeader_cursor alloc hwf hacc
  have hsw' : scalarHeaderWellFormed alloc.cursor alloc.cursor.region.account = true := by
    simpa [hca] using hsw
  exact mFieldWord_scalar_header hsw'

theorem mFieldWord_alloc_slots (hwf : alloc.wellFormed = true) (slot : UInt64)
    (hp1 : (1 : Nat) ≤ slot.toNat) (hp2 : slot.toNat ≤ alloc.slots.capacity) :
    mFieldWord (mAllocSlotsField alloc) slot =
      some (alloc.slots.baseWord + (slot.toNat - 1) * alloc.slots.strideWords) := by
  have hidx := allocator_wf_indexBase alloc hwf
  have hidx' := indexBase_beq_one_eq hidx
  unfold mAllocSlotsField mFieldWord
  simp only [hidx', hp1, hp2, and_true, if_true, Field.firstWord, Nat.zero_add]
  rfl

theorem alloc_liveCount_ne_cursor (hwf : alloc.wellFormed = true) :
    (mAllocLiveCountField alloc).firstWord ≠ alloc.cursor.firstWord := by
  have hadj := allocator_wf_liveCount_adj alloc hwf
  omega

theorem alloc_liveCount_ne_slots (hwf : alloc.wellFormed = true) (slot : UInt64)
    (hp1 : (1 : Nat) ≤ slot.toNat) (hp2 : slot.toNat ≤ alloc.slots.capacity)
    (hsep : (mAllocLiveCountField alloc).firstWord + 1 ≤ alloc.slots.baseWord) :
    (mAllocLiveCountField alloc).firstWord ≠
      alloc.slots.baseWord + (slot.toNat - 1) * alloc.slots.strideWords := by
  have _ := allocator_slots_stride_pos alloc hwf
  omega

theorem alloc_cursor_ne_slots (hwf : alloc.wellFormed = true) (slot : UInt64)
    (hp1 : (1 : Nat) ≤ slot.toNat) (hp2 : slot.toNat ≤ alloc.slots.capacity)
    (hsep : alloc.cursor.firstWord + 1 ≤ alloc.slots.baseWord) :
    alloc.cursor.firstWord ≠
      alloc.slots.baseWord + (slot.toNat - 1) * alloc.slots.strideWords := by
  have _ := allocator_slots_stride_pos alloc hwf
  omega

theorem mAllocBump_masked (mem : AccountWords) (alloc : Allocator) :
    mAllocBump mem alloc = mAllocBump mem alloc &&& 0xffffffff := by
  unfold mAllocBump
  bv_decide

private theorem u64_pack_high_masked (bump slot : UInt64)
    (hbump : bump = bump &&& 0xffffffff) :
    (bump ||| slot <<< 32) >>> 32 = slot &&& 0xffffffff := by
  rw [hbump]
  exact packed_cursor_high bump slot

/-- free 有效分支的写入序列。 -/
def mFreeAt (mem : AccountWords) (alloc : Allocator) (slot freeHead bump count : UInt64)
    : AccountWords :=
  let mem := mWriteField mem (mAllocSlotsField alloc) slot freeHead
  mWriteField (mWriteField mem alloc.cursor 0 (bump ||| (slot <<< 32)))
    (mAllocLiveCountField alloc) 0 (count - 1)

/-- **free 三写后 cursor 高 32 位 = slot**（bump 已 u32 掩码）。 -/
theorem mFreeAt_freeHead (mem : AccountWords) (alloc : Allocator)
    (slot freeHead bump count : UInt64)
    (hwf : alloc.wellFormed = true) (hacc : 0 < alloc.slots.account)
    (hslot : slot.toNat ≤ containerCapacityLimit)
    (hp1 : (1 : Nat) ≤ slot.toNat) (hp2 : slot.toNat ≤ alloc.slots.capacity)
    (hsep : alloc.cursor.firstWord + 1 ≤ alloc.slots.baseWord)
    (hbump : bump = bump &&& 0xffffffff) :
    mAllocFreeHead (mFreeAt mem alloc slot freeHead bump count) alloc = slot := by
  have hread : mReadField (mFreeAt mem alloc slot freeHead bump count) alloc.cursor 0
      = bump ||| slot <<< 32 := by
    unfold mFreeAt mWriteField mReadField
    rw [mFieldWord_alloc_cursor alloc hwf hacc, mFieldWord_alloc_liveCount alloc hwf hacc,
      mFieldWord_alloc_slots alloc hwf slot hp1 hp2]
    simp only [mWriteWord,
      if_neg (Ne.symm (alloc_liveCount_ne_cursor alloc hwf)),
      if_neg fun hc => (alloc_cursor_ne_slots alloc hwf slot hp1 hp2 hsep) hc,
      if_pos rfl]
    rfl
  unfold mAllocFreeHead mAllocCursor
  rw [hread]
  rw [u64_pack_high_masked bump slot hbump, slot_low_u32 slot hslot]

/-- **有效 free 链接到 `mFreeAt` 三写组合**。 -/
theorem mFree_valid_links (mem : AccountWords) (alloc : Allocator) (slot : UInt64)
    (hwf : alloc.wellFormed = true) (hslot : slot ≠ 0) (hslot_le : slot ≤ mAllocBump mem alloc)
    (hp2 : slot.toNat ≤ alloc.slots.capacity)
    (hcount : 0 < mAllocLiveCount mem alloc) :
    mFree mem alloc slot =
      (mFreeAt mem alloc slot (mAllocFreeHead mem alloc) (mAllocBump mem alloc)
        (mAllocLiveCount mem alloc), slot) := by
  unfold mFree mFreeAt
  simp only [mAllocLiveCount, mAllocBump, mAllocFreeHead, mAllocCursor]
  by_cases hguard :
      slot = 0 ∨ mReadField mem alloc.cursor 0 &&& 4294967295 < slot ∨
        UInt64.ofNat alloc.slots.capacity < slot ∨ mReadField mem (mAllocLiveCountField alloc) 0 = 0
  · exfalso
    rcases hguard with h | h | h | h
    · exact hslot h
    · exact (UInt64.not_lt.mpr hslot_le) h
    · have hlt : UInt64.ofNat alloc.slots.capacity < slot := h
      have hle : slot.toNat ≤ (UInt64.ofNat alloc.slots.capacity).toNat := by
        rw [ofNat_capacity_toNat alloc.slots.capacity (allocator_slots_capacity_u64 alloc hwf)]
        exact hp2
      exact (UInt64.not_lt).2 (by
        apply (UInt64.le_iff_toNat_le).2
        exact hle) hlt
    · rw [mAllocLiveCount] at hcount
      rw [h] at hcount
      exact absurd (UInt64.lt_iff_toNat_lt.mp hcount) (Nat.lt_irrefl 0)
  · simp only [if_neg hguard]

/-- **free 后再 alloc 取回同一槽（自由表头路径）**。 -/
theorem mFree_then_mAlloc_same (mem : AccountWords) (alloc : Allocator) (slot : UInt64)
    (hwf : alloc.wellFormed = true) (hacc : 0 < alloc.slots.account)
    (hslot : slot ≠ 0) (hslot_le : slot ≤ mAllocBump mem alloc)
    (hp1 : (1 : Nat) ≤ slot.toNat) (hp2 : slot.toNat ≤ alloc.slots.capacity)
    (hsep : alloc.cursor.firstWord + 1 ≤ alloc.slots.baseWord)
    (hslotcap : slot.toNat ≤ containerCapacityLimit)
    (hcount : 0 < mAllocLiveCount mem alloc)
    (hroom : mAllocLiveCount mem alloc < UInt64.ofNat alloc.slots.capacity) :
    (mAlloc (mFree mem alloc slot).1 alloc).2 = slot := by
  have links := mFree_valid_links mem alloc slot hwf hslot hslot_le hp2 hcount
  let mem' := mFreeAt mem alloc slot (mAllocFreeHead mem alloc) (mAllocBump mem alloc)
    (mAllocLiveCount mem alloc)
  have hmem' : (mFree mem alloc slot).1 = mem' := congrArg Prod.fst links
  have hfh := mFreeAt_freeHead mem alloc slot (mAllocFreeHead mem alloc) (mAllocBump mem alloc)
    (mAllocLiveCount mem alloc) hwf hacc hslotcap hp1 hp2 hsep (mAllocBump_masked mem alloc)
  have hfhAt : mAllocFreeHead mem' alloc = slot := hfh
  have hfhAt_ne : mAllocFreeHead mem' alloc ≠ 0 := by
    rw [hfhAt]
    intro h0
    exact hslot h0
  have hcountPost : mAllocLiveCount mem' alloc = mAllocLiveCount mem alloc - 1 := by
    change mAllocLiveCount (mFreeAt mem alloc slot (mAllocFreeHead mem alloc) (mAllocBump mem alloc)
      (mAllocLiveCount mem alloc)) alloc = mAllocLiveCount mem alloc - 1
    rw [mAllocLiveCount]
    unfold mFreeAt mReadField mWriteField
    rw [mFieldWord_alloc_liveCount alloc hwf hacc, mFieldWord_alloc_cursor alloc hwf hacc,
      mFieldWord_alloc_slots alloc hwf slot hp1 hp2]
    simp only [mWriteWord,
      if_neg (Ne.symm (alloc_liveCount_ne_cursor alloc hwf)),
      if_neg fun hc => (alloc_cursor_ne_slots alloc hwf slot hp1 hp2 hsep) hc]
    rfl
  have hnotfull : ¬(UInt64.ofNat alloc.slots.capacity ≤ mAllocLiveCount mem' alloc) := by
    intro hle
    have hlt : mAllocLiveCount mem' alloc < UInt64.ofNat alloc.slots.capacity := by
      rw [hcountPost]
      apply (UInt64.lt_iff_toNat_lt).2
      rw [u64_toNat_sub_one (by have := (UInt64.lt_iff_toNat_lt).1 hcount; omega)]
      have hcap : (UInt64.ofNat alloc.slots.capacity).toNat = alloc.slots.capacity :=
        ofNat_capacity_toNat alloc.slots.capacity (allocator_slots_capacity_u64 alloc hwf)
      rw [hcap]
      have := (UInt64.lt_iff_toNat_lt).1 hroom
      have := (UInt64.lt_iff_toNat_lt).1 hcount
      omega
    exact (UInt64.not_le).2 hlt hle
  have halloc : (mAlloc mem' alloc).2 = mAllocFreeHead mem' alloc := by
    unfold mAlloc
    simp only [mAllocLiveCount, mAllocBump, mAllocFreeHead, mAllocCursor, hcountPost]
    by_cases hfull : UInt64.ofNat alloc.slots.capacity ≤ mReadField mem' (mAllocLiveCountField alloc) 0
    · exact absurd hfull hnotfull
    · simp only [if_neg hfull]
      have hfhne' : mReadField mem' alloc.cursor 0 >>> 32 ≠ 0 := by
        rw [show mReadField mem' alloc.cursor 0 >>> 32 = mAllocFreeHead mem' alloc from rfl]
        exact hfhAt_ne
      simp only [if_pos hfhne']
  have hstep := congrArg Prod.snd (congrArg (fun m => mAlloc m alloc) hmem')
  rw [hstep, halloc, hfhAt]

end AllocProofs

/-! ## OrderedMap find 模型（SF-5b / sf-009）

抽象 `AccountStorage.Source.findKey4`：空根短路返回 `0`；fifo 变体恒为 miss。
完整 RB 遍历与旋转保持委托 `Runtime.accDataRbTreeKey4Find` stub（sf-011 或 Tree 片）。
find 是纯读：不返回新 `AccountWords`。 -/

namespace MapProofs

open ProofForge.Svm.AccountStorage

/-- Zero-based account data word read (mirrors `Runtime.accDataWord`). -/
def mAccDataWord (mem : AccountWords) (word : Nat) : UInt64 := mem word

/-- Map root scalar at compile-time `rootWord`. -/
def mMapRoot (mem : AccountWords) (map : RbMap) : UInt64 :=
  match map with
  | .key4 rootWord _ | .fifo rootWord _ => mAccDataWord mem rootWord

/-- Bounded key4 lookup model: empty root is an immediate miss.
Non-empty trees delegate to the runtime stub until sf-011 fills traversal. -/
def mAccDataRbTreeKey4Find
    (mem : AccountWords) (rootWord : Nat) (_tree : Key4RbTree)
    (_key0 _key1 _key2 _key3 : UInt64) : UInt64 :=
  if mAccDataWord mem rootWord = 0 then 0 else 0

/-- Abstract four-word-key lookup mirroring `AccountStorage.Source.findKey4`. -/
def mFindKey4 (mem : AccountWords) (map : RbMap) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  match map with
  | .key4 rootWord tree => mAccDataRbTreeKey4Find mem rootWord tree key0 key1 key2 key3
  | .fifo .. => 0

/-- Payload read at a one-based slot; slot `0` is the absent sentinel. -/
def mSlotValue (mem : AccountWords) (payload : Field) (slot : UInt64) : UInt64 :=
  if slot = 0 then 0 else mReadField mem payload slot

/-- Composed find + payload read (mirrors `OrderedMap.findValueKey4`). -/
def mFindValueKey4 (mem : AccountWords) (orderedMap : OrderedMap) (payload : Field)
    (key0 key1 key2 key3 : UInt64) : UInt64 :=
  mSlotValue mem payload (mFindKey4 mem orderedMap.map key0 key1 key2 key3)

/-- Fifo-backed maps never expose four-word keys through this entry point. -/
theorem mFindKey4_fifo_miss (mem : AccountWords) (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) :
    mFindKey4 mem (.fifo rootWord tree) k0 k1 k2 k3 = 0 := rfl

/-- Empty tree root (`0` sentinel) implies miss for any key. -/
theorem mFindKey4_empty_root (mem : AccountWords) (rootWord : Nat) (tree : Key4RbTree)
    (k0 k1 k2 k3 : UInt64) (hroot : mAccDataWord mem rootWord = 0) :
    mFindKey4 mem (.key4 rootWord tree) k0 k1 k2 k3 = 0 := by
  unfold mFindKey4 mAccDataRbTreeKey4Find
  simp [hroot]

/-- Miss lookup yields payload sentinel `0`. -/
theorem mFindValueKey4_miss (mem : AccountWords) (orderedMap : OrderedMap) (payload : Field)
    (k0 k1 k2 k3 : UInt64) (h : mFindKey4 mem orderedMap.map k0 k1 k2 k3 = 0) :
    mFindValueKey4 mem orderedMap payload k0 k1 k2 k3 = 0 := by
  unfold mFindValueKey4 mSlotValue
  simp [h]

/-- Hit lookup reads payload at the one-based slot returned by find. -/
theorem mFindValueKey4_hit (mem : AccountWords) (orderedMap : OrderedMap) (payload : Field)
    (k0 k1 k2 k3 slot : UInt64) (hslot : slot ≠ 0)
    (hfind : mFindKey4 mem orderedMap.map k0 k1 k2 k3 = slot) :
    mFindValueKey4 mem orderedMap payload k0 k1 k2 k3 = mReadField mem payload slot := by
  unfold mFindValueKey4 mSlotValue
  simp [hfind, hslot]

/-- Find is a pure read: identical memory yields identical results. -/
theorem mFindKey4_ext (mem mem' : AccountWords) (map : RbMap) (k0 k1 k2 k3 : UInt64)
    (h : ∀ w, mem w = mem' w) :
    mFindKey4 mem map k0 k1 k2 k3 = mFindKey4 mem' map k0 k1 k2 k3 := by
  unfold mFindKey4 mAccDataRbTreeKey4Find mAccDataWord
  cases map <;> simp [h]

/-- Insert stub matching `Runtime.accDataRbTreeKey4Insert` until sf-011. -/
def mAccDataRbTreeKey4Insert
    (_mem : AccountWords) (_rootWord : Nat) (_tree : Key4RbTree)
    (_key0 _key1 _key2 _key3 : UInt64) : UInt64 := 0

/-- Remove stub matching `Runtime.accDataRbTreeKey4Remove` until sf-011. -/
def mAccDataRbTreeKey4Remove
    (_mem : AccountWords) (_rootWord : Nat) (_tree : Key4RbTree)
    (_key0 _key1 _key2 _key3 : UInt64) : UInt64 := 0

/-- Abstract four-word-key insert mirroring `AccountStorage.Source.insertKey4`. -/
def mInsertKey4 (mem : AccountWords) (map : RbMap) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  match map with
  | .key4 rootWord tree => mAccDataRbTreeKey4Insert mem rootWord tree key0 key1 key2 key3
  | .fifo .. => 0

/-- Abstract four-word-key remove mirroring `AccountStorage.Source.removeKey4`. -/
def mRemoveKey4 (mem : AccountWords) (map : RbMap) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  match map with
  | .key4 rootWord tree => mAccDataRbTreeKey4Remove mem rootWord tree key0 key1 key2 key3
  | .fifo .. => 0

theorem mInsertKey4_fifo_fail (mem : AccountWords) (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) :
    mInsertKey4 mem (.fifo rootWord tree) k0 k1 k2 k3 = 0 := rfl

theorem mRemoveKey4_fifo_fail (mem : AccountWords) (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) :
    mRemoveKey4 mem (.fifo rootWord tree) k0 k1 k2 k3 = 0 := rfl

/-- Absent keys stay absent under the current insert/remove stubs. -/
theorem mRemoveKey4_after_find_miss (mem : AccountWords) (map : RbMap) (k0 k1 k2 k3 : UInt64)
    (_h : mFindKey4 mem map k0 k1 k2 k3 = 0) :
    mRemoveKey4 mem map k0 k1 k2 k3 = 0 := by
  unfold mRemoveKey4 mAccDataRbTreeKey4Remove
  cases map <;> rfl

/-- Remove is a pure read until sf-011 wires RB mutation (stub returns `0`). -/
theorem mRemoveKey4_ext (mem mem' : AccountWords) (map : RbMap) (k0 k1 k2 k3 : UInt64)
    (_h : ∀ w, mem w = mem' w) :
    mRemoveKey4 mem map k0 k1 k2 k3 = mRemoveKey4 mem' map k0 k1 k2 k3 := by
  unfold mRemoveKey4 mAccDataRbTreeKey4Remove
  cases map <;> rfl

/-- Post-remove find is miss for fifo maps (index layer; RB linking deferred to sf-011). -/
theorem mFindKey4_after_remove_fifo (mem : AccountWords) (rootWord : Nat) (tree : FifoRbTree)
    (k0 k1 k2 k3 : UInt64) (_hrem : mRemoveKey4 mem (.fifo rootWord tree) k0 k1 k2 k3 = 0) :
    mFindKey4 mem (.fifo rootWord tree) k0 k1 k2 k3 = 0 :=
  mFindKey4_fifo_miss mem rootWord tree k0 k1 k2 k3

/-- On miss, allocate a fresh one-based slot; on hit return the existing slot without touching
the allocator. RB tree linking deferred to sf-011 — this layer models slot acquisition only. -/
def mInsertKey4Alloc (mem : AccountWords) (map : RbMap) (alloc : Allocator)
    (key0 key1 key2 key3 : UInt64) : AccountWords × UInt64 :=
  let slot := mFindKey4 mem map key0 key1 key2 key3
  if slot = 0 then mAlloc mem alloc else (mem, slot)

/-- Fifo maps always miss find, so insert allocates like a fresh key. -/
theorem mInsertKey4Alloc_fifo_alloc (mem : AccountWords) (rootWord : Nat) (tree : FifoRbTree)
    (alloc : Allocator) (k0 k1 k2 k3 : UInt64) :
    mInsertKey4Alloc mem (.fifo rootWord tree) alloc k0 k1 k2 k3 =
      mAlloc mem alloc := by
  unfold mInsertKey4Alloc mFindKey4
  simp

/-- Miss path delegates slot acquisition to `mAlloc`. -/
theorem mInsertKey4Alloc_miss_alloc (mem : AccountWords) (map : RbMap) (alloc : Allocator)
    (k0 k1 k2 k3 : UInt64) (h : mFindKey4 mem map k0 k1 k2 k3 = 0) :
    mInsertKey4Alloc mem map alloc k0 k1 k2 k3 = mAlloc mem alloc := by
  unfold mInsertKey4Alloc
  simp [h]

/-- Hit path is a pure read: memory unchanged, slot preserved. -/
theorem mInsertKey4Alloc_hit (mem : AccountWords) (map : RbMap) (alloc : Allocator)
    (k0 k1 k2 k3 slot : UInt64) (hfind : mFindKey4 mem map k0 k1 k2 k3 = slot)
    (hne : slot ≠ 0) :
    mInsertKey4Alloc mem map alloc k0 k1 k2 k3 = (mem, slot) := by
  unfold mInsertKey4Alloc
  simp [hfind, hne]

/-- Hit path leaves account words unchanged (allocator not consulted). -/
theorem mInsertKey4Alloc_hit_mem (mem : AccountWords) (map : RbMap) (alloc : Allocator)
    (k0 k1 k2 k3 slot : UInt64) (hfind : mFindKey4 mem map k0 k1 k2 k3 = slot)
    (hne : slot ≠ 0) :
    (mInsertKey4Alloc mem map alloc k0 k1 k2 k3).1 = mem := by
  rw [mInsertKey4Alloc_hit mem map alloc k0 k1 k2 k3 slot hfind hne]

/-- Full allocator on miss is fail-closed like bare `mAlloc`. -/
theorem mInsertKey4Alloc_full (mem : AccountWords) (map : RbMap) (alloc : Allocator)
    (k0 k1 k2 k3 : UInt64) (hmiss : mFindKey4 mem map k0 k1 k2 k3 = 0)
    (hfull : UInt64.ofNat alloc.slots.capacity ≤ mAllocLiveCount mem alloc) :
    mInsertKey4Alloc mem map alloc k0 k1 k2 k3 = (mem, 0) := by
  rw [mInsertKey4Alloc_miss_alloc mem map alloc k0 k1 k2 k3 hmiss, mAlloc_full_noop mem alloc hfull]

/-- Returned slot is either the hit index or the allocator result. -/
theorem mInsertKey4Alloc_slot (mem : AccountWords) (map : RbMap) (alloc : Allocator)
    (k0 k1 k2 k3 : UInt64) :
    (mInsertKey4Alloc mem map alloc k0 k1 k2 k3).2 =
      if mFindKey4 mem map k0 k1 k2 k3 = 0 then
        (mAlloc mem alloc).2
      else
        mFindKey4 mem map k0 k1 k2 k3 := by
  unfold mInsertKey4Alloc
  by_cases h : mFindKey4 mem map k0 k1 k2 k3 = 0
  · simp [h]
  · simp [h]

end MapProofs

end ProofForge.Svm.Sdk.StorageModel
