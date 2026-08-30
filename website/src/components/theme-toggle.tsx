import { Moon, Sun } from "lucide-react";
import { Button } from "@/components/ui/button";
import { copy } from "@/lib/content";
import { useI18n } from "@/lib/i18n";
import { useTheme } from "@/lib/theme";

export function ThemeToggle() {
  const { lang } = useI18n();
  const mode = useTheme((s) => s.mode);
  const toggle = useTheme((s) => s.toggle);
  const toLight = mode === "dark";

  return (
    <Button
      type="button"
      variant="ghost"
      size="icon"
      onClick={toggle}
      aria-label={copy(
        lang,
        toLight
          ? { zh: "切换到白天", en: "Switch to light" }
          : { zh: "切换到夜间", en: "Switch to dark" },
      )}
    >
      {toLight ? <Sun className="size-4" /> : <Moon className="size-4" />}
    </Button>
  );
}
