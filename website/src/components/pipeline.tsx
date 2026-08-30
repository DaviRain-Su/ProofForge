import { useState } from "react";
import { copy, PIPELINE } from "@/lib/content";
import { useI18n } from "@/lib/i18n";
import { cn } from "@/lib/utils";

export function Pipeline() {
  const { lang } = useI18n();
  const [active, setActive] = useState(PIPELINE[0].id);
  const current = PIPELINE.find((s) => s.id === active) ?? PIPELINE[0];

  return (
    <div className="rounded-[var(--radius-xl)] bg-surface p-3 shadow-[var(--shadow-border)] sm:p-4">
      <ol className="grid grid-cols-1 gap-2 min-[420px]:grid-cols-2 sm:grid-cols-5">
        {PIPELINE.map((step, i) => {
          const on = step.id === active;
          return (
            <li key={step.id}>
              <button
                type="button"
                onClick={() => setActive(step.id)}
                className={cn(
                  "flex h-full min-h-14 w-full flex-col items-start rounded-[var(--radius-md)] px-3 py-2.5 text-left transition-[background-color,color] duration-[var(--motion-quick)]",
                  on ? "bg-surface-2 text-fg" : "text-muted hover:text-fg",
                )}
              >
                <span className="font-mono text-[10px] tracking-[0.14em] text-subtle">
                  {String(i + 1).padStart(2, "0")}
                </span>
                <span className="mt-1 text-sm">{copy(lang, step)}</span>
              </button>
            </li>
          );
        })}
      </ol>
      <div className="mt-3 rounded-[var(--radius-lg)] bg-bg px-4 py-4">
        <p className="text-sm leading-relaxed text-muted">{copy(lang, current.detail)}</p>
      </div>
    </div>
  );
}
