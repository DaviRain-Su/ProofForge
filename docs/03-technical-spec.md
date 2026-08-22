# 03 技术规格（v0 切片）

权威：本文件。代码与本文件冲突时先改本文件。

## 常量

| 名 | 值 |
|---|---|
| Lean toolchain | 与 ProofForge 对齐：`leanprover/lean4:v4.31.0` |
| `sbpf` | 0.2.2，commit `d835bc6e638e4f55b88f31a31bbc92e3a2e0a5ba`（第二刀才锁） |
| 状态宽度 | `UInt64`，8 字节 LE |
| 账户数 | 1（state account，writable） |
| overflow | 失败且不写回（与 PF StateCell `0x1001` 对齐，第二刀接线后钉死码） |

## 用户表面（必须是普通 Lean）

```lean
structure CounterState where
  value : UInt64
deriving Repr, DecidableEq

inductive CounterError where
  | overflow
deriving Repr, DecidableEq

def increment (s : CounterState) (delta : UInt64) :
    Except CounterError (CounterState × UInt64) :=
  if h : s.value ≤ UInt64.max - delta then
    let next := s.value + delta
    .ok ({ value := next }, next)
  else
    .error .overflow

def init (initial : UInt64) : CounterState :=
  { value := initial }

def get (s : CounterState) : UInt64 :=
  s.value
```

入口标记（v0 可用手工 `Program` 描述符代替 attribute，避免第一刀就碰 elaborator）：

```lean
def counterProgram : ProofForge.IR.Program :=
  ProofForge.IR.counterProgramFor increment init get
```

第一刀允许 `counterProgramFor` 是**显式构造 IR 的受控 API**（惰性数据，禁止 `IO` / 任意元程序）。第二刀改为从 `increment` 的 `Expr` 抽出，构造结果必须与手工 IR digest 相同。

## 语义

`increment` 的 Lean 求值就是参考语义。

| 输入 | 输出 |
|---|---|
| `s.value + delta` 不溢出 | `.ok ({value := s.value+delta}, s.value+delta)` |
| 否则 | `.error .overflow`；状态概念上不变 |

`init` 产生 `{value := initial}`。`get` 只读。

定理直接写在这些函数上，例如：

```lean
theorem increment_overflow_preserves
    (s : CounterState) (d : UInt64)
    (h : increment s d = .error .overflow) :
    True := trivial  -- v0 占位；产品定理应推出「无状态更新」
```

第一刀至少要有一条非 `trivial`、对 `increment` 的真定理（overflow ⇒ 不是 `.ok`）。

## Profile（子集）

可执行闭包只允许：

- `UInt64`、`Bool`、上述 `structure` / `inductive` / `Except`
- `if`、`let`、构造子、投影、`+`、`-` 在已检查不溢出的分支里
- 非递归 `def`

拒绝（第一刀可用静态白名单近似；第二刀走 `Expr` 闭包）：

- `IO`、`Task`、`partial`、`unsafe`
- `sorry` / axiom 出现在可执行依赖里
- `@[extern]`、`@[implemented_by]`
- `Nat` 作为状态或链上算术（证明里的 `Nat` 可以，但不能是 compiled 根的运行类型）

## IR

```lean
inductive MethodKind where
  | init | increment | get

structure Method where
  kind : MethodKind
  name : String

structure Program where
  name : String
  methods : Array Method
  -- v0: 语义由对应 Lean 函数定义；IR 只记录可编译形状
```

digest = `IR.digestHex`：规范化文本（name / fields / kind / ixName / paramCount / ops，按 ixName 排序）的 FNV-1a 64。Lean 4.31 无内建 SHA-256；digest 必须能进 `#guard`。`#pf_build` 抽出的已知例子必须与 `ProofForge.Golden` 同一 digest，否则 `ir/mismatch`。新例子加进 `Golden.programs`。

## Lower / Assemble

第一刀：**不调用** PF。只保证 IR 形状与 Counter 三方法对齐。

第二刀：`Lower` 把 IR 填进 PF `HandlerIR`（单账户、UInt64、checked add），再 `emitSbpfAsmV1`。

第三刀：`Assemble` 子进程 `sbpf build`，Mollusk 复用 PF `state_cell_shaped_product` 行为。

## 错误

| 码 | 何时 |
|---|---|
| `profile/rejected` | 闭包含禁止声明 |
| `extract/unsupported` | `Expr` 形状不在白名单 |
| `ir/mismatch` | 抽出 IR 与手工夹具 digest 不同 |
| `assemble/tool` | `sbpf` 非 0（第三刀） |

无静默降级。不认识就失败。

## 边界（至少）

1. `value = 0, delta = 0` → ok，仍为 0
2. `value = 0, delta = 1` → 1
3. `value = max, delta = 0` → ok，仍为 max
4. `value = max, delta = 1` → overflow
5. `value = max-1, delta = 1` → max
6. `value = max-1, delta = 2` → overflow
7. `init 0` / `init max`
8. `get` 不改 state
9. 禁止把 `IO Unit` 标成入口
10. 禁止入口直接 `sorry`

## 与 PF StateCell 对齐（第三刀）

| Lean | 链上 |
|---|---|
| `init initial` | init 写 8 字节 LE |
| `increment` ok | 写回新 count，return 新 count |
| `increment` overflow | 失败，账户字节不变 |
| `get` | return count，不写 |
