import { copy } from "@/lib/content";
import { useI18n } from "@/lib/i18n";
import { cn } from "@/lib/utils";

const TRUNK = [
  {
    n: "01",
    title: { zh: "普通 Lean", en: "Ordinary Lean" },
    body: { zh: "def / theorem / @[pf_entry]", en: "def / theorem / @[pf_entry]" },
  },
  {
    n: "02",
    title: { zh: "Profile", en: "Profile" },
    body: { zh: "fail-closed 子集检查", en: "fail-closed subset check" },
  },
  {
    n: "03",
    title: { zh: "Extract → Core", en: "Extract → Core" },
    body: { zh: "目标无关 Ops，钉 IR digest", en: "target-neutral Ops, pinned IR digest" },
  },
] as const;

const BRANCHES = [
  {
    id: "svm",
    ir: { zh: "SVM IR + IDL", en: "SVM IR + IDL" },
    irBody: { zh: "账户几何 / CPI", en: "account geometry / CPI" },
    out: { zh: "sBPF .so / .s", en: "sBPF .so / .s" },
  },
  {
    id: "evm",
    ir: { zh: "EVM IR + ABI", en: "EVM IR + ABI" },
    irBody: { zh: "storage slot / selector", en: "storage slots / selector" },
    out: { zh: "Yul .bin / .yul", en: "Yul .bin / .yul" },
  },
] as const;

export function Architecture() {
  const { lang } = useI18n();

  return (
    <div className="min-w-0 overflow-hidden rounded-[var(--radius-xl)] bg-surface p-4 shadow-[var(--shadow-border)] sm:p-6">
      <div className="mx-auto flex max-w-xl flex-col items-center">
        {TRUNK.map((node, i) => (
          <div key={node.n} className="flex w-full flex-col items-center">
            {i > 0 ? <Stem /> : null}
            <Node n={node.n} title={copy(lang, node.title)} body={copy(lang, node.body)} />
          </div>
        ))}

        <Fork />

        <div className="grid w-full grid-cols-1 gap-6 sm:grid-cols-2 sm:gap-4">
          {BRANCHES.map((b) => (
            <div key={b.id} className="flex min-w-0 flex-col items-center">
              <Node n={b.id === "svm" ? "04a" : "04b"} title={copy(lang, b.ir)} body={copy(lang, b.irBody)} />
              <Stem />
              <Node n={b.id === "svm" ? "05a" : "05b"} title={copy(lang, b.out)} body={b.id.toUpperCase()} mute />
            </div>
          ))}
        </div>
      </div>
      <p className="mx-auto mt-6 max-w-xl text-center text-sm leading-relaxed text-muted">
        {copy(lang, {
          zh: "证明和编译钉同一 IR digest。Core 不做 syscall；SVM 与 EVM 不共享物理存储。",
          en: "Proof and compile pin the same IR digest. Core emits no syscalls. SVM and EVM do not share a physical store.",
        })}
      </p>
    </div>
  );
}

function Node({
  n,
  title,
  body,
  mute,
}: {
  n: string;
  title: string;
  body: string;
  mute?: boolean;
}) {
  return (
    <div
      className={cn(
        "w-full rounded-[var(--radius-md)] bg-bg px-4 py-3 shadow-[var(--shadow-border)]",
        mute && "opacity-90",
      )}
    >
      <p className="font-mono text-[10px] tracking-[0.14em] text-subtle">{n}</p>
      <p className="mt-1 text-sm font-medium text-fg">{title}</p>
      <p className="mt-0.5 font-mono text-xs text-muted">{body}</p>
    </div>
  );
}

function Stem() {
  return (
    <div className="flex h-6 w-px items-center bg-border" aria-hidden="true" />
  );
}

function Fork() {
  return (
    <div className="flex w-full flex-col items-center" aria-hidden="true">
      <div className="h-5 w-px bg-border" />
      <svg viewBox="0 0 320 28" className="hidden h-7 w-full text-border sm:block">
        <path
          d="M160 0v8M24 8h272M24 8v20M296 8v20"
          fill="none"
          stroke="currentColor"
          strokeWidth="1.25"
        />
      </svg>
      <div className="flex w-full items-center gap-3 py-2 sm:hidden">
        <span className="h-px flex-1 bg-border" />
        <span className="font-mono text-[10px] tracking-[0.16em] text-subtle uppercase">split</span>
        <span className="h-px flex-1 bg-border" />
      </div>
    </div>
  );
}
