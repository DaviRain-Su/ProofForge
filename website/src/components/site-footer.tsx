import { copy, MCP, REPO } from "@/lib/content";
import { useI18n } from "@/lib/i18n";

export function SiteFooter() {
  const { lang } = useI18n();
  return (
    <footer className="border-t border-border">
      <div className="mx-auto flex max-w-6xl flex-col gap-6 px-5 py-10 sm:flex-row sm:items-end sm:justify-between">
        <div>
          <p className="font-display text-2xl tracking-tight">ProofForge</p>
          <p className="mt-2 max-w-sm text-sm leading-relaxed text-muted">
            {copy(lang, {
              zh: "Lean 4 编译剖面。普通 def 写合约，普通 theorem 证合约。当前目标：Solana sBPF、EVM Yul。",
              en: "A Lean 4 compiler profile. Ordinary defs write contracts; ordinary theorems prove them. Targets: Solana sBPF, EVM Yul.",
            })}
          </p>
        </div>
        <div className="flex flex-wrap gap-x-6 gap-y-2 font-mono text-xs text-muted">
          <a href={REPO} className="hover:text-fg" target="_blank" rel="noreferrer">
            GitHub
          </a>
          <a href={`${REPO}/blob/main/docs/INDEX.md`} className="hover:text-fg" target="_blank" rel="noreferrer">
            {copy(lang, { zh: "文档索引", en: "Docs index" })}
          </a>
          <a href={MCP} className="hover:text-fg" target="_blank" rel="noreferrer">
            MCP
          </a>
          <span>Lean 4.31.0</span>
        </div>
      </div>
    </footer>
  );
}
