import { useState } from "react";
import { Check, Copy } from "lucide-react";
import { cn } from "@/lib/utils";
import { Button } from "@/components/ui/button";

export function CodeBlock({
  code,
  label,
  className,
}: {
  code: string;
  label?: string;
  className?: string;
}) {
  const [copied, setCopied] = useState(false);

  async function onCopy() {
    try {
      await navigator.clipboard.writeText(code);
      setCopied(true);
      window.setTimeout(() => setCopied(false), 1400);
    } catch {
      /* ignore */
    }
  }

  return (
    <div
      className={cn(
        "min-w-0 overflow-hidden rounded-[var(--radius-lg)] bg-surface shadow-[var(--shadow-border)]",
        className,
      )}
    >
      <div className="flex items-center justify-between gap-3 border-b border-border px-4 py-2">
        <span className="font-mono text-xs tracking-wide text-muted uppercase">
          {label ?? "code"}
        </span>
        <Button
          type="button"
          variant="ghost"
          size="sm"
          className="h-9 px-2 text-muted"
          onClick={onCopy}
          aria-label="Copy"
        >
          {copied ? <Check className="size-3.5" /> : <Copy className="size-3.5" />}
          <span className="font-mono text-xs">{copied ? "copied" : "copy"}</span>
        </Button>
      </div>
      <pre className="max-h-[28rem] overflow-x-auto overflow-y-auto p-4 font-mono text-[13px] leading-relaxed break-all text-fg/90 sm:break-normal">
        <code>{code}</code>
      </pre>
    </div>
  );
}
