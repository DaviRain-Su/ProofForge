import type { ReactNode } from "react";
import { SiteFooter } from "@/components/site-footer";
import { SiteHeader } from "@/components/site-header";
import { TooltipProvider } from "@/components/ui/tooltip";

export function SiteShell({ path, children }: { path: string; children: ReactNode }) {
  return (
    <TooltipProvider>
      <div className="grain flex min-h-dvh flex-col overflow-x-hidden bg-bg text-fg">
        <SiteHeader path={path} />
        <div className="flex-1">{children}</div>
        <SiteFooter />
      </div>
    </TooltipProvider>
  );
}
