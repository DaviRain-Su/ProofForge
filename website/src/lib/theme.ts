import { useEffect } from "react";
import { create } from "zustand";
import { persist } from "zustand/middleware";

export type ThemeMode = "dark" | "light";

type ThemeState = {
  mode: ThemeMode;
  setMode: (mode: ThemeMode) => void;
  toggle: () => void;
};

const LIGHT_THEME = "#F3F1EA";
const DARK_THEME = "#0B0B0C";

export function applyTheme(mode: ThemeMode) {
  if (typeof document === "undefined") return;
  const root = document.documentElement;
  root.setAttribute("data-theme", mode);
  root.style.colorScheme = mode;
  const meta = document.querySelector('meta[name="theme-color"]');
  if (meta) meta.setAttribute("content", mode === "light" ? LIGHT_THEME : DARK_THEME);
}

export const useTheme = create<ThemeState>()(
  persist(
    (set, get) => ({
      mode: "dark",
      setMode: (mode) => {
        applyTheme(mode);
        set({ mode });
      },
      toggle: () => {
        const mode = get().mode === "dark" ? "light" : "dark";
        applyTheme(mode);
        set({ mode });
      },
    }),
    {
      name: "pf-theme",
      onRehydrateStorage: () => (state) => {
        if (state) applyTheme(state.mode);
      },
    },
  ),
);

export function ThemeSync() {
  const mode = useTheme((s) => s.mode);
  useEffect(() => {
    applyTheme(mode);
  }, [mode]);
  return null;
}
