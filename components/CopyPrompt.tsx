"use client";
import { useState } from "react";

export default function CopyPrompt({ text, label = "Copy" }: { text: string; label?: string }) {
  const [done, setDone] = useState(false);
  return (
    <div className="prompt">
      <code>{text}</code>
      <button
        type="button"
        onClick={async () => {
          try {
            await navigator.clipboard.writeText(text);
            setDone(true);
            setTimeout(() => setDone(false), 1600);
          } catch {}
        }}
      >
        {done ? "Copied" : label}
      </button>
    </div>
  );
}
