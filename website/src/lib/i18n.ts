import { create } from "zustand";
import { persist } from "zustand/middleware";

export type Lang = "zh" | "en";

type Copy = Record<Lang, string>;

type I18nState = {
  lang: Lang;
  setLang: (lang: Lang) => void;
  toggle: () => void;
};

export const useI18n = create<I18nState>()(
  persist(
    (set, get) => ({
      lang: "zh",
      setLang: (lang) => set({ lang }),
      toggle: () => set({ lang: get().lang === "zh" ? "en" : "zh" }),
    }),
    { name: "pf-lang" },
  ),
);

export function tx(lang: Lang, copy: Copy): string {
  return copy[lang];
}
