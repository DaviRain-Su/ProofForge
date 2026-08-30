import { Github, Menu } from "lucide-react";
import { ProofMark } from "@/components/mark";
import { ThemeToggle } from "@/components/theme-toggle";
import { Button } from "@/components/ui/button";
import { Sheet, SheetContent, SheetTrigger } from "@/components/ui/sheet";
import { copy, MCP, NAV, REPO } from "@/lib/content";
import { useI18n } from "@/lib/i18n";
import { cn } from "@/lib/utils";

function hrefOf(path: string) {
  return `#${path === "/" ? "/" : path}`;
}

export function SiteHeader({ path }: { path: string }) {
  const { lang, toggle } = useI18n();

  return (
    <header className="sticky top-0 z-40 border-b border-border bg-bg/85 backdrop-blur-md">
      <div className="mx-auto flex h-16 max-w-6xl items-center justify-between gap-4 px-5">
        <a href={hrefOf("/")} className="flex items-center gap-2.5 text-fg">
          <ProofMark className="size-8" />
          <span className="font-display text-xl tracking-tight">ProofForge</span>
        </a>

        <nav className="hidden items-center gap-1 md:flex">
          {NAV.map((item) => {
            const active =
              item.href === "/"
                ? path === "/"
                : path === item.href || path.startsWith(`${item.href}/`);
            return (
              <a
                key={item.href}
                href={hrefOf(item.href)}
                className={cn(
                  "rounded-[var(--radius-sm)] px-3 py-2 text-sm transition-colors duration-[var(--motion-quick)]",
                  active ? "text-fg" : "text-muted hover:text-fg",
                )}
              >
                {copy(lang, item)}
              </a>
            );
          })}
        </nav>

        <div className="flex items-center gap-1">
          <Button
            type="button"
            variant="ghost"
            size="sm"
            className="font-mono text-xs uppercase"
            onClick={toggle}
            aria-label="Language"
          >
            {lang === "zh" ? "EN" : "中文"}
          </Button>
          <ThemeToggle />
          <Button asChild variant="ghost" size="icon" className="hidden sm:inline-flex">
            <a href={REPO} target="_blank" rel="noreferrer" aria-label="GitHub">
              <Github className="size-4" />
            </a>
          </Button>
          <div className="md:hidden">
            <Sheet>
              <SheetTrigger asChild>
                <Button variant="ghost" size="icon" aria-label="Menu">
                  <Menu className="size-4" />
                </Button>
              </SheetTrigger>
              <SheetContent>
                <div className="mt-10 flex flex-col gap-1">
                  {NAV.map((item) => (
                    <a
                      key={item.href}
                      href={hrefOf(item.href)}
                      className="rounded-[var(--radius-md)] px-3 py-3 text-base text-fg"
                    >
                      {copy(lang, item)}
                    </a>
                  ))}
                  <a
                    href={REPO}
                    className="rounded-[var(--radius-md)] px-3 py-3 text-muted"
                    target="_blank"
                    rel="noreferrer"
                  >
                    GitHub
                  </a>
                  <a
                    href={MCP}
                    className="rounded-[var(--radius-md)] px-3 py-3 text-muted"
                    target="_blank"
                    rel="noreferrer"
                  >
                    MCP
                  </a>
                </div>
              </SheetContent>
            </Sheet>
          </div>
        </div>
      </div>
    </header>
  );
}
