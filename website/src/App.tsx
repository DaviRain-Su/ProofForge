import { useEffect, useState, type ReactNode } from "react";
import { ArrowRight, GitBranch } from "lucide-react";
import { CodeBlock } from "@/components/code-block";
import { Pipeline } from "@/components/pipeline";
import { SiteShell } from "@/components/site-shell";
import { Studio } from "@/components/studio";
import { Badge } from "@/components/ui/badge";
import { Button } from "@/components/ui/button";
import {
  COMMANDS,
  copy,
  DOC_SECTIONS,
  DOCS,
  HERO,
  MCP,
  PILLARS,
  REPO,
  TARGETS,
  TOOLCHAIN,
  TRUST,
  type DocId,
} from "@/lib/content";
import { useI18n } from "@/lib/i18n";
import { cn } from "@/lib/utils";

function parsePath() {
  const raw = window.location.hash.replace(/^#/, "") || "/";
  const path = raw.startsWith("/") ? raw : `/${raw}`;
  return path.split("?")[0] || "/";
}

export function App() {
  const [path, setPath] = useState(parsePath);

  useEffect(() => {
    const onHash = () => setPath(parsePath());
    window.addEventListener("hashchange", onHash);
    return () => window.removeEventListener("hashchange", onHash);
  }, []);

  let page: ReactNode;
  if (path === "/docs") page = <DocsPage />;
  else if (path === "/examples") page = <ExamplesPage />;
  else if (path === "/cli") page = <CliPage />;
  else page = <HomePage />;

  return <SiteShell path={path}>{page}</SiteShell>;
}

function HomePage() {
  const { lang } = useI18n();
  return (
    <main>
      <section className="mx-auto max-w-6xl px-5 pt-16 pb-12 sm:pt-24">
        <Badge tone="steel">{copy(lang, HERO.kicker)}</Badge>
        <h1 className="mt-6 max-w-4xl font-display text-[clamp(2.6rem,7vw,5.4rem)] leading-[1.05] tracking-[-0.03em]">
          {copy(lang, HERO.title)}
        </h1>
        <p className="mt-6 max-w-2xl text-lg leading-relaxed text-muted">{copy(lang, HERO.lead)}</p>
        <div className="mt-8 flex flex-wrap gap-3">
          <Button asChild size="lg">
            <a href="#/examples">
              {copy(lang, { zh: "打开锻造台", en: "Open the forge" })}
              <ArrowRight className="size-4" />
            </a>
          </Button>
          <Button asChild size="lg" variant="secondary">
            <a href="#/cli">{copy(lang, { zh: "安装与 CLI", en: "Install & CLI" })}</a>
          </Button>
          <Button asChild size="lg" variant="ghost">
            <a href={REPO} target="_blank" rel="noreferrer">
              <GitBranch className="size-4" />
              GitHub
            </a>
          </Button>
        </div>
        <dl className="mt-12 grid grid-cols-2 gap-px overflow-hidden rounded-[var(--radius-lg)] bg-border sm:grid-cols-4">
          {TOOLCHAIN.map((row) => (
            <div key={row.name} className="bg-surface px-4 py-4">
              <dt className="font-mono text-[10px] tracking-[0.16em] text-subtle uppercase">{row.name}</dt>
              <dd className="mt-1 font-mono text-sm tabular-nums">{row.value}</dd>
            </div>
          ))}
        </dl>
      </section>
      <div className="rule mx-auto max-w-6xl" />
      <section className="mx-auto max-w-6xl px-5 py-16">
        <p className="font-mono text-[11px] tracking-[0.18em] text-subtle uppercase">
          {copy(lang, { zh: "编译链", en: "Pipeline" })}
        </p>
        <h2 className="mt-3 font-display text-4xl tracking-tight">
          {copy(lang, { zh: "一条主语，两条降低。", en: "One subject. Two lowerings." })}
        </h2>
        <p className="mt-3 max-w-2xl text-muted">
          {copy(lang, {
            zh: "点每一级看它拥有什么。Core 不做 syscall，target 不重做类型检查。",
            en: "Open a stage to see what it owns. Core does not emit syscalls. Targets do not re-typecheck.",
          })}
        </p>
        <div className="mt-8">
          <Pipeline />
        </div>
      </section>
      <section className="mx-auto max-w-6xl px-5 pb-16">
        <div className="grid gap-4 lg:grid-cols-2">
          {TARGETS.map((t) => (
            <article key={t.id} className="rounded-[var(--radius-xl)] bg-surface p-6 shadow-[var(--shadow-border)]">
              <p className="font-mono text-[11px] tracking-[0.16em] text-subtle uppercase">{copy(lang, t.kicker)}</p>
              <h3 className="mt-2 font-display text-3xl">{t.name}</h3>
              <div className="mt-3 flex flex-wrap gap-1.5">
                {t.artifacts.map((a) => (
                  <Badge key={a} tone="muted">
                    {a}
                  </Badge>
                ))}
              </div>
              <ul className="mt-5 space-y-2 text-sm leading-relaxed text-muted">
                {t.points[lang].map((p) => (
                  <li key={p} className="flex gap-2">
                    <span className="mt-2 size-1 shrink-0 rounded-full bg-accent" />
                    <span>{p}</span>
                  </li>
                ))}
              </ul>
            </article>
          ))}
        </div>
      </section>
      <section className="mx-auto max-w-6xl px-5 pb-16">
        <p className="font-mono text-[11px] tracking-[0.18em] text-subtle uppercase">
          {copy(lang, { zh: "原则", en: "Principles" })}
        </p>
        <div className="mt-6 grid gap-4 sm:grid-cols-2">
          {PILLARS.map((p) => (
            <article key={p.title.en} className="rounded-[var(--radius-xl)] bg-surface p-5 shadow-[var(--shadow-border)]">
              <h3 className="text-base font-medium">{copy(lang, p.title)}</h3>
              <p className="mt-2 text-sm leading-relaxed text-muted">{copy(lang, p.body)}</p>
            </article>
          ))}
        </div>
      </section>
      <section className="mx-auto max-w-6xl px-5 pb-16">
        <p className="font-mono text-[11px] tracking-[0.18em] text-subtle uppercase">
          {copy(lang, { zh: "锻造台", en: "Forge" })}
        </p>
        <h2 className="mt-3 font-display text-4xl tracking-tight">
          {copy(lang, { zh: "同一份 Counter，两个目标。", en: "The same Counter. Two targets." })}
        </h2>
        <p className="mt-3 mb-8 max-w-2xl text-muted">
          {copy(lang, {
            zh: "源在 Examples/*.lean。锻造按钮走的是剖面走查，产物是仓库里真实形状的摘录。",
            en: "Source lives in Examples/*.lean. Forge is a profile walkthrough; artifacts are excerpts in the real shape from the tree.",
          })}
        </p>
        <Studio />
      </section>
      <section className="mx-auto max-w-6xl px-5 pb-20">
        <div className="rounded-[var(--radius-xl)] bg-surface px-6 py-8 shadow-[var(--shadow-border)] sm:px-10">
          <p className="font-mono text-[11px] tracking-[0.18em] text-subtle uppercase">{copy(lang, TRUST.title)}</p>
          <div className="mt-5 grid gap-6 lg:grid-cols-3">
            <div>
              <h3 className="text-sm font-medium">{copy(lang, { zh: "弱声明", en: "Weak claim" })}</h3>
              <p className="mt-2 text-sm leading-relaxed text-muted">{copy(lang, TRUST.weak)}</p>
            </div>
            <div>
              <h3 className="text-sm font-medium">{copy(lang, { zh: "工程声明", en: "Engineering" })}</h3>
              <p className="mt-2 text-sm leading-relaxed text-muted">{copy(lang, TRUST.eng)}</p>
            </div>
            <div>
              <h3 className="text-sm font-medium">{copy(lang, { zh: "不做", en: "Not claimed" })}</h3>
              <p className="mt-2 text-sm leading-relaxed text-muted">{copy(lang, TRUST.not)}</p>
            </div>
          </div>
        </div>
      </section>
    </main>
  );
}

function DocsPage() {
  const { lang } = useI18n();
  const [id, setId] = useState<DocId>("start");
  const doc = DOCS[id][lang];
  return (
    <main className="mx-auto grid max-w-6xl gap-8 px-5 py-12 lg:grid-cols-[14rem_minmax(0,1fr)]">
      <nav aria-label="Docs">
        <p className="mb-3 font-mono text-[11px] tracking-[0.18em] text-subtle uppercase">
          {copy(lang, { zh: "文档", en: "Docs" })}
        </p>
        <ul className="flex gap-1 overflow-x-auto pb-2 lg:flex-col lg:overflow-visible">
          {DOC_SECTIONS.map((s) => (
            <li key={s.id}>
              <button
                type="button"
                onClick={() => setId(s.id)}
                className={cn(
                  "whitespace-nowrap rounded-[var(--radius-md)] px-3 py-2 text-sm transition-colors duration-[var(--motion-quick)] lg:w-full lg:text-left",
                  id === s.id ? "bg-surface text-fg" : "text-muted hover:text-fg",
                )}
              >
                {copy(lang, s)}
              </button>
            </li>
          ))}
        </ul>
      </nav>
      <article className="min-w-0">
        <h1 className="font-display text-5xl tracking-tight">{doc.title}</h1>
        <div className="mt-8 space-y-5">
          {doc.blocks.map((b) => (
            <p key={b} className="max-w-2xl text-base leading-relaxed text-muted">
              {b}
            </p>
          ))}
        </div>
      </article>
    </main>
  );
}

function ExamplesPage() {
  const { lang } = useI18n();
  return (
    <main className="mx-auto max-w-6xl px-5 py-12">
      <p className="font-mono text-[11px] tracking-[0.18em] text-subtle uppercase">Examples/*.lean</p>
      <h1 className="mt-3 font-display text-5xl tracking-tight">
        {copy(lang, { zh: "仓库里的合约。", en: "Contracts in the tree." })}
      </h1>
      <p className="mt-4 mb-10 max-w-2xl text-muted">
        {copy(lang, {
          zh: "这些不是玩具伪代码。源、定理名、产物形状来自 ProofForge 仓库。锻造台演示剖面走查。",
          en: "Not toy pseudocode. Source, theorem names, and artifact shape come from the ProofForge tree. The forge walks the profile.",
        })}
      </p>
      <Studio />
    </main>
  );
}

function CliPage() {
  const { lang } = useI18n();
  return (
    <main className="mx-auto max-w-6xl px-5 py-12">
      <Badge tone="steel">pf</Badge>
      <h1 className="mt-4 font-display text-5xl tracking-tight">
        {copy(lang, { zh: "钉死工具，再编译。", en: "Pin the tools. Then compile." })}
      </h1>
      <p className="mt-4 max-w-2xl text-muted">
        {copy(lang, {
          zh: "CLI 是 pf。目标 svm 或 evm。不提供 PATH fallback。不默认公网广播。",
          en: "The CLI is pf. Targets are svm or evm. No PATH fallback. No default public broadcast.",
        })}
      </p>
      <dl className="mt-10 grid grid-cols-2 gap-3 sm:grid-cols-4">
        {TOOLCHAIN.map((row) => (
          <div key={row.name} className="rounded-[var(--radius-lg)] bg-surface px-4 py-4 shadow-[var(--shadow-border)]">
            <dt className="font-mono text-[10px] tracking-[0.16em] text-subtle uppercase">{row.name}</dt>
            <dd className="mt-1 font-mono text-sm">{row.value}</dd>
          </div>
        ))}
      </dl>
      <div className="mt-12 space-y-8">
        {COMMANDS.map((c) => (
          <section key={c.cmd}>
            <h2 className="mb-3 text-sm font-medium">{copy(lang, c.title)}</h2>
            <CodeBlock code={c.cmd} label="sh" />
            {"note" in c && c.note ? <p className="mt-2 text-sm text-muted">{copy(lang, c.note)}</p> : null}
          </section>
        ))}
      </div>
      <section className="mt-14 rounded-[var(--radius-xl)] bg-surface p-6 shadow-[var(--shadow-border)]">
        <h2 className="font-display text-3xl tracking-tight">MCP</h2>
        <p className="mt-3 max-w-2xl text-sm leading-relaxed text-muted">
          {copy(lang, {
            zh: "远程边只提供文档与脚手架，不 spawn Lean。本机 stdio 才接 doctor / build / local。",
            en: "The remote edge serves docs and scaffolds. It does not spawn Lean. Local stdio is what wraps doctor / build / local.",
          })}
        </p>
        <div className="mt-5">
          <CodeBlock label="codex" code={`codex mcp add proof-forge-mcp --url ${MCP}`} />
        </div>
        <p className="mt-4 font-mono text-xs text-subtle">
          <a href={REPO} className="hover:text-fg" target="_blank" rel="noreferrer">
            {REPO}
          </a>
        </p>
      </section>
    </main>
  );
}
