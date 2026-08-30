import type { Lang } from "@/lib/i18n";

export const REPO = "https://github.com/DaviRain-Su/ProofForge";
export const MCP = "https://proof-forge-mcp.davirain-yin.workers.dev/mcp";

export const NAV = [
  { href: "/", zh: "概览", en: "Overview" },
  { href: "/docs", zh: "文档", en: "Docs" },
  { href: "/examples", zh: "示例", en: "Examples" },
  { href: "/cli", zh: "CLI", en: "CLI" },
] as const;

export const HERO = {
  kicker: { zh: "Lean 4 编译剖面", en: "Lean 4 compiler profile" },
  title: { zh: "普通 Lean。链上字节。", en: "Ordinary Lean. On-chain bytes." },
  lead: {
    zh: "不是一门新合约语言。普通 def 写合约，普通 theorem 证合约。同一主语抽出到 Solana sBPF 与 EVM Yul。",
    en: "Not a new contract language. Write contracts as defs, prove them as theorems. One subject lowers to Solana sBPF and EVM Yul.",
  },
};

export const PIPELINE = [
  {
    id: "lean",
    zh: "普通 Lean",
    en: "Ordinary Lean",
    detail: {
      zh: "def / theorem / structure。入口用 @[pf_entry] 标记。没有 program … where。",
      en: "def / theorem / structure. Mark entries with @[pf_entry]. No program … where.",
    },
  },
  {
    id: "profile",
    zh: "Profile",
    en: "Profile",
    detail: {
      zh: "传递闭包准入。拒绝 IO、partial、sorry、@[extern]、无界递归。Fail-closed。",
      en: "Transitive-closure admission. Rejects IO, partial, sorry, @[extern], unbounded recursion. Fail-closed.",
    },
  },
  {
    id: "extract",
    zh: "Extract",
    en: "Extract",
    detail: {
      zh: "Expr → typed Core + target-neutral Ops。证明主语与编译主语共享 IR digest。",
      en: "Expr → typed Core + target-neutral Ops. Proof subject and compile subject share the IR digest.",
    },
  },
  {
    id: "split",
    zh: "SVM | EVM",
    en: "SVM | EVM",
    detail: {
      zh: "各自物化布局。SVM：账户几何 / CPI / IDL。EVM：storage slot / selector / ABI。",
      en: "Each target owns layout. SVM: account geometry / CPI / IDL. EVM: storage slots / selector / ABI.",
    },
  },
  {
    id: "emit",
    zh: ".so / .bin",
    en: ".so / .bin",
    detail: {
      zh: "sbpf 锁版本出 .so。solc 锁版本出 .bin。工程门：Mollusk / Surfpool / Anvil。",
      en: "Pinned sbpf writes .so. Pinned solc writes .bin. Engineering gates: Mollusk / Surfpool / Anvil.",
    },
  },
];

export const PILLARS = [
  {
    title: { zh: "同一主语", en: "One subject" },
    body: {
      zh: "定理钉在用户 def 上，编译走同一抽出 IR。禁止「证的是 A，编的是 B」。",
      en: "Theorems pin the user def; compile walks the same extracted IR. No proving A while emitting B.",
    },
  },
  {
    title: { zh: "Fail-closed 子集", en: "Fail-closed subset" },
    body: {
      zh: "能降到链上的才过 Profile。过不了的不是警告，是拒绝。",
      en: "Only what can lower on-chain passes Profile. Failures are refusals, not warnings.",
    },
  },
  {
    title: { zh: "两个剖面，一条 Core", en: "Two profiles, one Core" },
    body: {
      zh: "SVM 与 EVM 共享 Lean / Profile / Extract / CFG，不共享物理存储模型。",
      en: "SVM and EVM share Lean / Profile / Extract / CFG. They do not share a physical store.",
    },
  },
  {
    title: { zh: "诚实的信任边界", en: "Honest trust boundary" },
    body: {
      zh: "Kernel 接受的是关于 def / IR 的定理。不声称 .so、loader 或公网部署正确。",
      en: "The kernel accepts theorems about the def / IR. That is not a claim about .so, the loader, or mainnet.",
    },
  },
];

export const TARGETS = [
  {
    id: "svm" as const,
    name: "Solana",
    kicker: { zh: "sBPF / Loader V3", en: "sBPF / Loader V3" },
    artifacts: [".so", ".s", ".idl.json"],
    points: {
      zh: [
        "EntryAdapter 统一 packed wire 与账户合同",
        "AccountStorage：账户驻留 Map / Queue / tree",
        "Heap 只作 invocation-local bump，不进账户",
        "Phoenix-v1 在 Surfpool 上跑，不用 test-validator",
      ],
      en: [
        "EntryAdapter owns packed wire and the account contract",
        "AccountStorage: account-resident Map / Queue / tree",
        "Heap is invocation-local bump only — never in accounts",
        "Phoenix-v1 runs on Surfpool, not solana-test-validator",
      ],
    },
  },
  {
    id: "evm" as const,
    name: "EVM",
    kicker: { zh: "Yul / ABI", en: "Yul / ABI" },
    artifacts: [".bin", ".yul", ".abi.json"],
    points: {
      zh: [
        "Evm.Sdk：Address、UInt256、typed hashed maps",
        "Storage.Layout 编译期 cursor，descriptor 抽取期消去",
        "封闭 call facade；不隐藏 .ok / .error",
        "Anvil 工程门，v0 拒绝公网 broadcast",
      ],
      en: [
        "Evm.Sdk: Address, UInt256, typed hashed maps",
        "Storage.Layout is a compile-time cursor; descriptors erase",
        "Closed-call facade — does not hide .ok / .error",
        "Anvil engineering gate; v0 refuses public broadcast",
      ],
    },
  },
];

export const TRUST = {
  title: { zh: "信任边界", en: "Trust boundary" },
  weak: {
    zh: "弱声明：kernel 接受了关于用户 def / 抽出 IR 的定理。TCB = Lean kernel + 主语绑定。",
    en: "Weak claim: the kernel accepted theorems about the user def / extracted IR. TCB = Lean kernel + subject binding.",
  },
  eng: {
    zh: "工程声明：同一 IR 经发射器 + 钉死的 sbpf / solc，在 Mollusk 或 Anvil 上与夹具一致。",
    en: "Engineering claim: the same IR, through the emitter and pinned sbpf / solc, matches fixtures on Mollusk or Anvil.",
  },
  not: {
    zh: "不做的声明：.so / loader / 全 SVM refinement / 定理 ⇒ 已部署程序。",
    en: "Not claimed: .so / loader / full SVM refinement / theorem ⇒ deployed program.",
  },
};

export const TOOLCHAIN = [
  { name: "Lean 4", value: "v4.31.0" },
  { name: "sbpf", value: "0.2.2" },
  { name: "Surfpool", value: "1.5.0" },
  { name: "CLI", value: "pf" },
];

export const COMMANDS = [
  {
    title: { zh: "构建编译器", en: "Build the compiler" },
    cmd: "lake build",
  },
  {
    title: { zh: "Solana 目标", en: "Solana target" },
    cmd: "lake exe pf -- build --target svm --out build/sbpf Counter",
    note: { zh: "写出 Counter.so / Counter.s / Counter.idl.json", en: "Writes Counter.so / Counter.s / Counter.idl.json" },
  },
  {
    title: { zh: "EVM 目标", en: "EVM target" },
    cmd: "lake exe pf -- build --target evm --out build/evm Counter",
    note: { zh: "写出 Counter.bin / Counter.yul / Counter.abi.json", en: "Writes Counter.bin / Counter.yul / Counter.abi.json" },
  },
  {
    title: { zh: "Mollusk 回归", en: "Mollusk regression" },
    cmd: "cd runtime-tests/solana && PF_COUNTER_SO=../../build/sbpf/Counter.so cargo test --locked --test counter",
  },
  {
    title: { zh: "Phoenix · Surfpool", en: "Phoenix · Surfpool" },
    cmd: "runtime-tests/surfpool/smoke.sh PhoenixV1Profile",
  },
];

export const DOC_SECTIONS = [
  { id: "start", zh: "开始", en: "Start" },
  { id: "surface", zh: "语言表面", en: "Surface" },
  { id: "pipeline", zh: "编译链", en: "Pipeline" },
  { id: "svm", zh: "SVM", en: "SVM" },
  { id: "evm", zh: "EVM", en: "EVM" },
  { id: "proofs", zh: "证明", en: "Proofs" },
  { id: "trust", zh: "信任", en: "Trust" },
  { id: "mcp", zh: "MCP", en: "MCP" },
] as const;

export type DocId = (typeof DOC_SECTIONS)[number]["id"];

export const DOCS: Record<DocId, { zh: { title: string; blocks: string[] }; en: { title: string; blocks: string[] } }> = {
  start: {
    zh: {
      title: "开始",
      blocks: [
        "ProofForge 是 Lean 4 的编译剖面，不是 DSL。克隆仓库，用 Lake 构建，用 pf 选目标。",
        "Toolchain 钉死：leanprover/lean4:v4.31.0、sbpf 0.2.2、Surfpool 1.5.0。不要用 PATH 里随便一个汇编器顶替锁版本。",
        "第一份合约建议从 Examples.Counter 读起：单账户、UInt64、checked add。同一文件里有 Proofs 节。",
      ],
    },
    en: {
      title: "Start",
      blocks: [
        "ProofForge is a Lean 4 compiler profile, not a DSL. Clone the repo, build with Lake, pick a target with pf.",
        "Toolchain is pinned: leanprover/lean4:v4.31.0, sbpf 0.2.2, Surfpool 1.5.0. Do not substitute a PATH assembler for the lock.",
        "Read Examples.Counter first: one account, UInt64, checked add. The Proofs section lives in the same file.",
      ],
    },
  },
  surface: {
    zh: {
      title: "语言表面",
      blocks: [
        "用户写的是普通 Lean。没有 program … where。入口用 @[pf_entry]；内联用 @[pf_inline]。",
        "Profile 检查传递闭包：IO、partial、sorry、@[extern]、@[implemented_by]、无界递归一律拒绝。",
        "抽出权威是 elaborated Expr 闭包，不是 Lean.Compiler.IR。业务类型检查仍由 Lean 完成。",
      ],
    },
    en: {
      title: "Surface",
      blocks: [
        "Users write ordinary Lean. There is no program … where. Mark entries @[pf_entry]; inline with @[pf_inline].",
        "Profile checks the transitive closure: IO, partial, sorry, @[extern], @[implemented_by], unbounded recursion are refused.",
        "Extract authority is the elaborated Expr closure, not Lean.Compiler.IR. Lean still owns business typing.",
      ],
    },
  },
  pipeline: {
    zh: {
      title: "编译链",
      blocks: [
        "Profile → Extract.IR / Core → Svm.IR | Evm.IR → target emitter。Core 拥有 schema、control、checked arithmetic。",
        "Core.Target 做公共 Val/Op/Program 投影。具体 syscall / opcode 留在 target-owned 模块。",
        "CLI 构建必须重新从用户模块抽 IR，不能组装 legacy Golden fixture。Registry 只列可构建模块并钉 digest。",
      ],
    },
    en: {
      title: "Pipeline",
      blocks: [
        "Profile → Extract.IR / Core → Svm.IR | Evm.IR → target emitter. Core owns schema, control, checked arithmetic.",
        "Core.Target projects Val/Op/Program. Concrete syscalls / opcodes stay in target-owned modules.",
        "CLI build re-extracts IR from the user module. It does not assemble a legacy Golden fixture. The registry lists modules and pins digests.",
      ],
    },
  },
  svm: {
    zh: {
      title: "SVM",
      blocks: [
        "Svm.EntryAdapter 拥有 packed wire、raw/generated dispatch、账户前缀。AccountStorage 拥有账户内 Region/Field 与 bounded Query/Call。",
        "持久 Map/Queue 是账户 bytes 上的固定容量 POD 视图。Heap 是 32 KiB（可到 256 KiB）向下 bump，dealloc 不回收，指针不进账户。",
        "新容器能力扩 component-owned 模块，不横向改 Extract/IR/主 Emit。Phoenix tag 6/7 FifoCancel 是这一边界的实例。",
      ],
    },
    en: {
      title: "SVM",
      blocks: [
        "Svm.EntryAdapter owns packed wire, raw/generated dispatch, and the account prefix. AccountStorage owns in-account Region/Field and bounded Query/Call.",
        "Persistent Map/Queue are fixed-capacity POD views on account bytes. Heap is a 32 KiB (up to 256 KiB) downward bump; dealloc does not reclaim; pointers never enter accounts.",
        "New container capability extends a component-owned module — it does not cut sideways through Extract/IR/main Emit. Phoenix tag 6/7 FifoCancel is the instance of that boundary.",
      ],
    },
  },
  evm: {
    zh: {
      title: "EVM",
      blocks: [
        "EVM 与 SVM 共享普通 Lean、Profile、Extract 和 Core CFG，但不共享物理存储。",
        "Evm.Sdk 是合同源到既有 component/runtime 的 facade。静态 cursor 在抽取期把 typed map 分到 hashed-map namespace。",
        "SDK 不包装 .ok / .error，不改变 Lean 控制流。Examples.Token / Capped 已迁到该表面，target IR digest 不变。",
      ],
    },
    en: {
      title: "EVM",
      blocks: [
        "EVM shares ordinary Lean, Profile, Extract, and Core CFG with SVM. It does not share a physical store.",
        "Evm.Sdk is a facade from contract source onto the existing component/runtime. A static cursor assigns typed maps to a hashed-map namespace at extract.",
        "The SDK does not wrap .ok / .error and does not change Lean control flow. Examples.Token / Capped already sit on this surface with an unchanged target IR digest.",
      ],
    },
  },
  proofs: {
    zh: {
      title: "证明",
      blocks: [
        "第一批 kernel-checked 性质落在合约文件的 Proofs 节：成功路径后置条件、单调性、Token supply 效应、Capped cap 不变量。",
        "只依赖标准公理 propext / Quot.sound。CI 由 scripts/check_no_sorry.py 保证证明批次不含占位符。",
        "证明主语和编译主语必须共享同一个 IR digest。",
      ],
    },
    en: {
      title: "Proofs",
      blocks: [
        "The first kernel-checked properties live in each contract file's Proofs section: success postconditions, monotonicity, Token supply effect, Capped cap invariant.",
        "They depend only on the standard axioms propext / Quot.sound. CI (scripts/check_no_sorry.py) refuses placeholders in the proof batch.",
        "Proof subject and compile subject must share the same IR digest.",
      ],
    },
  },
  trust: {
    zh: {
      title: "信任",
      blocks: [
        "弱声明（对外 v0）：kernel 接受了关于用户 def / 抽出 IR 的定理。TCB = Lean kernel + 主语绑定。",
        "工程声明：同一 IR 经 PF 发射器 + pinned sbpf 得到的 .so，在 pinned Mollusk 上行为与夹具一致。",
        "不做的声明：.so / loader / 全 SVM refinement；定理不蕴含公网部署正确。",
      ],
    },
    en: {
      title: "Trust",
      blocks: [
        "Weak claim (v0 public): the kernel accepted theorems about the user def / extracted IR. TCB = Lean kernel + subject binding.",
        "Engineering claim: the .so from that IR through the PF emitter + pinned sbpf matches fixtures on pinned Mollusk.",
        "Not claimed: .so / loader / full SVM refinement. A theorem does not imply a correct public deployment.",
      ],
    },
  },
  mcp: {
    zh: {
      title: "MCP",
      blocks: [
        "远程 MCP 只提供文档、目录与脚手架指导，不 spawn Lean，不持有密钥，不广播。",
        "本机 stdio MCP 才封装 pf doctor / install / build / artifacts / local。local 仅 EVM 与 Solana。",
        "Agent 接线：codex mcp add proof-forge-mcp --url https://proof-forge-mcp.davirain-yin.workers.dev/mcp",
      ],
    },
    en: {
      title: "MCP",
      blocks: [
        "The remote MCP serves docs, catalogs, and scaffold guidance. It does not spawn Lean, hold keys, or broadcast.",
        "The local stdio MCP wraps pf doctor / install / build / artifacts / local. local is EVM and Solana only.",
        "Agent wiring: codex mcp add proof-forge-mcp --url https://proof-forge-mcp.davirain-yin.workers.dev/mcp",
      ],
    },
  },
};

export function copy(lang: Lang, rec: { zh: string; en: string }): string {
  return rec[lang];
}
