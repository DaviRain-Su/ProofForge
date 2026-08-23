# ProofForge.Extract

## Purpose

从 elaborated `Expr` 抽出 `IR.Program`。前端先从 `init` 的结果类型建立 target-neutral
typed state schema，再抽方法 Ops；物理槽表只是 schema 的兼容视图。

## State schema

`ProofForge.Core.Schema` 是状态布局的 source of truth：

- `Place` / `PathStep` 保存稳定的源位置身份。structure 字段由 owner type + 声明序号标识，
  字段名不参与身份判定，只用于诊断和兼容叶名；Vector 元素用 index；Option 的 tag /
  payload 是显式路径步骤。
- `Leaf` 保存 source scalar type；`VectorLayout` 保存长度、每元素字节数和每元素叶子数，
  不包含 SVM byte offset 或 EVM storage slot。
- `IR.Program.slots` 由 `IR.slotsOfSchema` 生成，继续保留 `nodes_0_value`、`slot_tag`
  这类 ABI / 显示名，以保持已有 digest、IDL 和产物不变。抽出的程序必须满足
  `IR.schemaMatchesSlots`。

SVM / EVM emitter 不再扫描 `_0_left`、`_tag`、`_p0` 来猜 Vector / Option 布局；
它们只调用各自 IR 层的 typed layout 查询。旧的手写 `Golden` fixture 没有 schema，
因此字符串兼容解析仅集中保留在 IR 层，不能再进入 emitter。

## Core evaluation and writeback

`ProofForge.Core.Eval` 在 schema 和规范化 Ops 都可用后，为每个抽出方法建立
`IR.Method.evaluation`：

- checked add/sub/mul/div/mod 变成显式 `ValueRef.checked kind lhs rhs`，状态写入不再依赖
  emitter 的“最近一次计算结果”寄存器。
- 静态状态写入使用 typed `Place`；Option 成功结果明确列出 tag 和 payload 两次写入；
  多叶 record diff 的每个 `storeField` 也有对应 typed write event。
- lexical scalar let、branch / bounded loop 保留为结构化 state-effect tree，不依赖 emitter
  的遍历游标。
- 运行时 Vector 下标写入使用 `DynamicPlace(vector Place, index, elementPath)`；其 commit
  明确没有虚构的静态首槽写入。
- `Evaluation.explicit = false` 只用于没有 schema 的旧手写 fixture。

当前 `Ops` 仍是前端 compatibility lowering，但 emitter 不再直接消费它：
`Svm.IR.fromProgram` / `Evm.IR.fromProgram` 分别把它降到两个互不共享 constructor 的 target
`Op`，并把 typed `Place` 物化成 SVM account-data byte offset 或 EVM storage slot。
`Core.Evaluation` 随 target method 保留，下一步用它替换 target `okState` 的兼容写回规则。这里刻意
不让旧规则进入 Core：旧 SVM 对 `indexSet + okState` 会额外覆写首槽，而 EVM 不会；把任一旧
行为塞回 Core 都会污染 target-neutral 语义。

## Source-form normalization

抽出器承诺对已测试的 syntax-only 写法保持同一 Core：直接 record constructor 与等价的
外层 pure `let` + record update 会抽成相同 schema、slots、方法 Ops 和 evaluation。规范化刻意很窄：
窄整数 alias 和包住 `if` 的 pure head `let` 做 zeta-reduction；`UInt64` pure let 保留成
`letLocal`，纯值 `if` 保留成 `Val.select`，避免把同一 mutation continuation 复制到两个
分支。`invoke`、EVM effect 和循环仍交给专用 decoder。这里不做全局 `whnf`，新增 Lean
表面形式应先加等价性 characterization test，再扩规范化或 decoder。

方法完成规范化后会递归检查所有 Val、CPI data、branch 和 loop 的 `.arg`。init 只允许
`arg < paramCount`；mutate/view 另允许 `arg == paramCount` 表示隐式 state。任何 proof / let /
callback binder 泄漏都会在 target lowering 之前 fail closed，不能再被 emitter 误认成 calldata。

## Boundary

递归下降 `Expr`。`x ≤ u64Max - y` → `checkedAddU64`；`y ≤ x` → `checkedSubU64`；`y = 0 ∨ x ≤ u64Max / y` → `checkedMulU64`；`y ≠ 0` 后 `/` `%` → `checkedDivU64` / `checkedModU64`。比较认 `=` `≠` `<` `≤` `>` `≥`。假支不必是 overflow。`match opt with | none => a | some n => b` 抽成 `ite (eq tag 0)`。`ProofForge.Svm.Runtime.clockSlot` / `signerKey0` / `acc*` 抽成 SVM 运行时叶子；`ProofForge.Evm.Runtime.evm*` 抽成 EVM 叶子。`invoke programIx metas data` 抽成 `Op.invoke`。`systemTransfer` / `invokeAcc1` 是普通包装，展开成同一条。`findPda "seed"` 抽成运行时叶子。`evmDeposit` / `evmSendEth` / `evmLog*` / pair-key Map / 全部 EVM 环境叶抽成独立 ops。位运算 / 有界 `forIn [:N]` / 运行时 `Vector` 下标 / 命名 `Error` 构造子 / `UInt64 × UInt64` view 也抽。SVM 发射器再拒语言叶和 EVM 叶。可变方法无 checked 算术 / ite / invoke / EVM 效应 / 语言叶则 fail closed。嵌套用户 structure 摊成 `parent_child` 槽；`Vector Nested n` 每个元素再摊，例如 `nodes_0_value`。`extends` 仍关。Sokoban 节点是普通 structure + `Vector Node n`。mutate 的 `State.mk` / `Vector.set` / 嵌套 `with` 按叶 diff：改了几个槽就发几条 `storeField`，不按合约猜 dest。单叶仍压成 `okState`。`for i in [:n]` 改状态抽出 `forBody`，循环下标是 `loopIx`，payload 仍是外层参数。运行时下标读写嵌套记录走 `indexGet` / `indexSet`，`elemOff` 是被改那一叶的偏移（`right`=8，`parent`=16，`value`=40）。多出来的 `toNat` binder 折到第一个 ix 参数。N=4 Tree 已覆盖 allocator、free-list、完整左右旋、duplicate update 和 red-uncle / LL / RR / LR / RL insertion fixup；删除 fixup 与 `extends` 仍关。

schema 默认从 `init` 返回类型收：必须是已注册 `structure`、无 `extends`。叶子只接受 `UInt8/16/32/64`、`Bool`（1 字节 u8-le）、`Option UInt64`（展开双叶）、`Vector UInt64 n`（展开 `name_0…name_{n-1}`）、无 payload 用户枚举（一叶 tag），两构造子且其中一个带一个 `UInt64` 的 inductive（按 Option 双叶），以及嵌套用户 structure（摊成 `parent_child`）。不定长 `Array`、多字段 inductive fail closed。`#pf_extract … with "a","b"` 仍可覆盖槽名，且必须与 schema 导出的表一致。ops 里出现的字段名必须在表内。

用户合约不绑仓库目录名。`#pf_build Ns` 收任意名字空间下的 `@[pf_entry]`。字段投影认已注册 structure，排除 `ProofForge` / `Lean` / `Std` / `Init`。`Examples.` / `Projects.` 不是准入条件。

`@[pf_entry]` 只是标记。种类从返回类型推断：structure → init；`Except` → mutate；`UInt64` → view。Lean `init` 的链上名是 `initialize`。允许多个 init / mutate / view；槽表从名为 `init` 的那个收。重复链上名 fail closed。`init` 的 `paramCount` 按 λ 个数算。抽出按类型展开槽名（`name_tag` / `name_i`），不按合约字段名写死。

## API

- `inferSchema env initName : Except String Core.Schema`
- `inferSlots env initName : Except String (Array IR.Slot)`（schema 的兼容视图）
- `inferFields env initName : Except String (Array String)`
- `extractProgram env init increment get (name?) (fields?)`
- `#pf_extract init increment get`
- `#pf_extract init increment get with "left", "right"`
- `#pf_build Namespace`（收 `@[pf_entry]`）
- `extractModule env ns`

## Tests

`Tests/ExtractSpec.lean`：Counter / Pair / Flag / Maybe / Window 抽出；非支持叶子与不定长 Array 拒绝。
`Tests/BuildSpec.lean`：`#pf_build` 收入口；无标记 fail closed。
`Tests/LayoutSpec.lean`：窄字段偏移、Option 双叶、layout marker。
`Tests/NormalizationSpec.lean`：等价 Lean 表面形式抽成同一 Core；Tree 的 typed Vector schema
固定为 4 个元素、每元素 48 字节 / 6 叶；checked result、Option 双叶和动态 Vector
writeback 的 Core evaluation 是显式且 typed 的；Tree allocator 已覆盖同一动态元素一次
改写六个叶子、静态 allocator 元数据 writeback 以及 LIFO free-list 复用。完整左右旋
进一步覆盖条件分支、同一返回中的静态 root + 动态 Vector 写，以及只沿
`Vector.set` base 追溯旧写，避免把 payload read 指数级复制成写。同一 Tree `Place`
在 SVM target IR 中变成 byte offset/stride，在 EVM target IR 中变成
slot/slot-stride；Maybe 的 Option tag/payload 也保持同一 typed identity。Maybe / Window
的 typed 与 legacy schema 路径生成逐字节相同的 SVM 输出，适用程序的 EVM 输出也相同；
真实 Tree 已超出旧手写 fixture，只钉 source digest 和 typed target identity。N=4 insertion
还逐项检查四种旋转、red-uncle、duplicate-full、overflow、free-list reuse、BST 顺序、parent、
root-black、red-red 和 black-height 不变量。当前产物为 426,823-byte source assembly 和
115,640-byte eBPF ELF；lexical locals 让增长保持线性，而不是按搜索分支复制 allocator/fixup。
