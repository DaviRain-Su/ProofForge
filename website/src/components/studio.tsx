import { useMemo, useState } from "react";
import { Hammer, LoaderCircle } from "lucide-react";
import { CodeBlock } from "@/components/code-block";
import { Badge } from "@/components/ui/badge";
import { Button } from "@/components/ui/button";
import { copy } from "@/lib/content";
import { EXAMPLES, type Example, type TargetId } from "@/lib/examples";
import { useI18n } from "@/lib/i18n";
import { cn } from "@/lib/utils";

const STAGES = [
  { id: "profile", zh: "Profile", en: "Profile" },
  { id: "extract", zh: "Extract", en: "Extract" },
  { id: "ir", zh: "Target IR", en: "Target IR" },
  { id: "emit", zh: "Emit", en: "Emit" },
] as const;

type Tab = "lean" | "artifact" | "proofs";

export function Studio({ initialId }: { initialId?: string }) {
  const { lang } = useI18n();
  const [exampleId, setExampleId] = useState(initialId ?? EXAMPLES[0].id);
  const example = EXAMPLES.find((e) => e.id === exampleId) ?? EXAMPLES[0];
  const [target, setTarget] = useState<TargetId>(example.targets[0]);
  const [stage, setStage] = useState(-1);
  const [running, setRunning] = useState(false);
  const [tab, setTab] = useState<Tab>("lean");
  const done = stage >= STAGES.length - 1 && !running;

  const artifact = useMemo(() => artifactFor(example, target), [example, target]);

  function pickExample(next: Example) {
    setExampleId(next.id);
    const t = next.targets.includes(target) ? target : next.targets[0];
    setTarget(t);
    setStage(-1);
    setTab("lean");
  }

  async function forge() {
    if (running) return;
    setRunning(true);
    setStage(-1);
    setTab("artifact");
    for (let i = 0; i < STAGES.length; i += 1) {
      await wait(i === 0 ? 180 : 320);
      setStage(i);
    }
    setRunning(false);
  }

  return (
    <div className="grid min-w-0 gap-4 lg:grid-cols-[16rem_minmax(0,1fr)]">
      <aside className="min-w-0 overflow-hidden rounded-[var(--radius-xl)] bg-surface p-3 shadow-[var(--shadow-border)]">
        <p className="px-2 pt-1 pb-2 font-mono text-[10px] tracking-[0.16em] text-subtle uppercase">
          {copy(lang, { zh: "模块", en: "modules" })}
        </p>
        <ul className="flex flex-row gap-1 overflow-x-auto lg:flex-col">
          {EXAMPLES.map((item) => {
            const on = item.id === example.id;
            return (
              <li key={item.id} className="min-w-36 lg:min-w-0">
                <button
                  type="button"
                  onClick={() => pickExample(item)}
                  className={cn(
                    "flex w-full flex-col items-start rounded-[var(--radius-md)] px-3 py-2.5 text-left transition-colors duration-[var(--motion-quick)]",
                    on ? "bg-surface-2 text-fg" : "text-muted hover:text-fg",
                  )}
                >
                  <span className="font-mono text-sm">{item.name}</span>
                  <span className="mt-0.5 text-xs text-subtle">
                    {item.targets.map((t) => t.toUpperCase()).join(" · ")}
                  </span>
                </button>
              </li>
            );
          })}
        </ul>
      </aside>

      <div className="min-w-0 rounded-[var(--radius-xl)] bg-surface p-3 shadow-[var(--shadow-border)] sm:p-4">
        <div className="flex flex-col gap-4 sm:flex-row sm:items-start sm:justify-between">
          <div>
            <div className="flex flex-wrap items-center gap-2">
              <h2 className="font-display text-3xl tracking-tight">{example.name}</h2>
              {example.tags.map((tag) => (
                <Badge key={tag.en} tone="muted">
                  {copy(lang, tag)}
                </Badge>
              ))}
            </div>
            <p className="mt-2 max-w-xl text-sm leading-relaxed text-muted">
              {copy(lang, example.summary)}
            </p>
          </div>
          <div className="flex flex-wrap items-center gap-2">
            <div className="flex rounded-[var(--radius-md)] bg-bg p-1 shadow-[var(--shadow-border)]">
              {example.targets.map((t) => (
                <button
                  key={t}
                  type="button"
                  onClick={() => {
                    setTarget(t);
                    setStage(-1);
                  }}
                  className={cn(
                    "h-9 rounded-[var(--radius-sm)] px-3 font-mono text-xs uppercase transition-colors duration-[var(--motion-quick)]",
                    target === t ? "bg-surface-2 text-fg" : "text-muted hover:text-fg",
                  )}
                >
                  {t === "svm" ? "Solana" : "EVM"}
                </button>
              ))}
            </div>
            <Button type="button" onClick={forge} disabled={running}>
              {running ? (
                <LoaderCircle className="size-4 animate-spin" />
              ) : (
                <Hammer className="size-4" />
              )}
              {copy(lang, { zh: "锻造", en: "Forge" })}
            </Button>
          </div>
        </div>

        <ol className="mt-5 grid grid-cols-2 gap-2 sm:grid-cols-4">
          {STAGES.map((s, i) => {
            const on = i <= stage;
            return (
              <li
                key={s.id}
                className={cn(
                  "rounded-[var(--radius-md)] px-3 py-2 shadow-[var(--shadow-border)] transition-colors duration-[var(--motion-fast)]",
                  on ? "bg-bg text-fg" : "text-subtle",
                )}
              >
                <span className="font-mono text-[10px] tracking-[0.14em]">
                  {String(i + 1).padStart(2, "0")}
                </span>
                <div className="text-sm">{copy(lang, s)}</div>
              </li>
            );
          })}
        </ol>

        <div className="mt-4 flex gap-1 rounded-[var(--radius-md)] bg-bg p-1 shadow-[var(--shadow-border)]">
          {(
            [
              ["lean", { zh: "源", en: "Source" }],
              ["artifact", { zh: "产物", en: "Artifact" }],
              ["proofs", { zh: "证明", en: "Proofs" }],
            ] as const
          ).map(([id, label]) => (
            <button
              key={id}
              type="button"
              onClick={() => setTab(id)}
              className={cn(
                "h-10 flex-1 rounded-[var(--radius-sm)] text-sm transition-colors duration-[var(--motion-quick)]",
                tab === id ? "bg-surface-2 text-fg" : "text-muted hover:text-fg",
              )}
            >
              {copy(lang, label)}
            </button>
          ))}
        </div>

        <div className="mt-3">
          {tab === "lean" ? (
            <CodeBlock code={example.lean} label={`${example.name}.lean`} />
          ) : null}
          {tab === "artifact" ? (
            done ? (
              <CodeBlock code={artifact.body} label={artifact.label} />
            ) : (
              <div className="flex min-h-48 items-center justify-center rounded-[var(--radius-lg)] bg-bg px-6 text-center text-sm text-muted">
                {running
                  ? copy(lang, {
                      zh: "正在抽出闭包、钉 digest、交给目标发射器。",
                      en: "Extracting the closure, pinning the digest, handing off to the target emitter.",
                    })
                  : copy(lang, {
                      zh: "点锻造。这是演示走查，不是本机 lake 编译。",
                      en: "Hit Forge. This is a walkthrough — not a local lake compile.",
                    })}
              </div>
            )
          ) : null}
          {tab === "proofs" ? (
            <ul className="space-y-2">
              {example.theorems.map((th) => (
                <li
                  key={th.name}
                  className="rounded-[var(--radius-lg)] bg-bg px-4 py-3 shadow-[var(--shadow-border)]"
                >
                  <p className="font-mono text-sm text-accent">{th.name}</p>
                  <p className="mt-1 text-sm leading-relaxed text-muted">{copy(lang, th.claim)}</p>
                </li>
              ))}
            </ul>
          ) : null}
        </div>
      </div>
    </div>
  );
}

function artifactFor(example: Example, target: TargetId): { label: string; body: string } {
  if (target === "svm") {
    return {
      label: `${example.name}.s`,
      body: example.svm?.asm ?? "; this example is EVM-only in the current tree",
    };
  }
  return {
    label: `${example.name}.yul`,
    body: example.evm?.yul ?? "; this example is SVM-only in the current tree",
  };
}

function wait(ms: number) {
  return new Promise((resolve) => {
    window.setTimeout(resolve, ms);
  });
}
