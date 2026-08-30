import { cn } from "@/lib/utils";

export function ProofMark({ className }: { className?: string }) {
  return (
    <svg
      viewBox="0 0 32 32"
      className={cn("text-fg", className)}
      aria-hidden="true"
    >
      <rect
        x="1.5"
        y="1.5"
        width="29"
        height="29"
        rx="3"
        fill="none"
        stroke="currentColor"
        strokeWidth="1.25"
      />
      <path
        d="M8 9.5h5.2c3.4 0 5.5 1.85 5.5 4.55 0 2.75-2.15 4.6-5.55 4.6H11.2V23H8V9.5Zm3.2 2.35v4.45h1.85c1.7 0 2.65-.85 2.65-2.2 0-1.35-.92-2.25-2.6-2.25H11.2Z"
        fill="currentColor"
      />
      <path
        d="M21.2 16.2 24.4 23h-3.15l-.55-1.25h-3.35L16.8 23h-3.05l3.25-6.8h4.2Zm-2.55 3.55h1.85l-.9-2.05-.95 2.05Z"
        fill="currentColor"
        opacity="0.72"
      />
    </svg>
  );
}
