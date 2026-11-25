"use client";
import { useEffect, useRef, useState } from "react";

type Row = [string, string, number, number, number, number, number];
const COLORS = { open: "#f0a04b", known: "#7aa7ff", warmup: "#3f8f6a", unformalized: "#8a7a9e", solved: "#5fd39b", live: "#ff5c5c" };
const CELL = 9, GAP = 2, LABEL = 22;

export default function MapCanvas() {
  const ref = useRef<HTMLCanvasElement>(null);
  const wrap = useRef<HTMLDivElement>(null);
  const [data, setData] = useState<{ sources: string[]; rows: Row[] } | null>(null);
  const [hover, setHover] = useState<{ x: number; y: number; r: Row } | null>(null);
  const [filter, setFilter] = useState<"all" | "open" | "known" | "warmup" | "unformalized">("all");
  const layout = useRef<{ x: number; y: number; r: Row }[]>([]);

  useEffect(() => { fetch("/api/map").then((r) => r.json()).then(setData).catch(() => {}); }, []);

  useEffect(() => {
    const c = ref.current, w = wrap.current;
    if (!c || !w || !data) return;
    const draw = () => {
      const width = w.clientWidth;
      const perRow = Math.max(10, Math.floor((width - 4) / (CELL + GAP)));
      const groups = data.sources.map((s, i) => ({ s, rows: data.rows.filter((r) => r[2] === i && (filter === "all" || ["open", "known", "warmup", "unformalized"][r[3]] === filter)) }))
        .filter((g) => g.rows.length).sort((a, b) => b.rows.length - a.rows.length);
      let height = 0;
      for (const g of groups) height += LABEL + Math.ceil(g.rows.length / perRow) * (CELL + GAP) + 10;
      const dpr = window.devicePixelRatio || 1;
      c.width = width * dpr; c.height = height * dpr; c.style.width = width + "px"; c.style.height = height + "px";
      const ctx = c.getContext("2d")!;
      ctx.scale(dpr, dpr);
      ctx.font = "600 12px Inter, system-ui, sans-serif";
      const L: { x: number; y: number; r: Row }[] = [];
      let y = 0;
      for (const g of groups) {
        ctx.fillStyle = "#9a9ca6";
        ctx.fillText(`${g.s} · ${g.rows.length}`, 0, y + 14);
        y += LABEL;
        g.rows.sort((a, b) => b[4] - a[4]).forEach((r, i) => {
          const x = (i % perRow) * (CELL + GAP), yy = y + Math.floor(i / perRow) * (CELL + GAP);
          ctx.fillStyle = r[6] ? COLORS.solved : r[5] ? COLORS.live : r[3] === 0 ? COLORS.open : r[3] === 1 ? COLORS.known : r[3] === 2 ? COLORS.warmup : COLORS.unformalized;
          ctx.globalAlpha = r[6] || r[5] ? 1 : 0.35 + 0.65 * (r[4] / 100);
          ctx.fillRect(x, yy, CELL, CELL);
          L.push({ x, y: yy, r });
        });
        ctx.globalAlpha = 1;
        y += Math.ceil(g.rows.length / perRow) * (CELL + GAP) + 10;
      }
      layout.current = L;
    };
    draw();
    const ro = new ResizeObserver(draw);
    ro.observe(w);
    return () => ro.disconnect();
  }, [data, filter]);

  const at = (e: React.MouseEvent) => {
    const rect = ref.current!.getBoundingClientRect();
    const x = e.clientX - rect.left, y = e.clientY - rect.top;
    return layout.current.find((p) => x >= p.x && x < p.x + CELL && y >= p.y && y < p.y + CELL);
  };

  return (
    <div>
      <div className="tabs">
        {(["all", "open", "unformalized", "known", "warmup"] as const).map((k) => (
          <button key={k} className="tab" aria-pressed={filter === k} onClick={() => setFilter(k)}>{k === "all" ? "Everything" : k === "known" ? "Known, needs proof" : k === "unformalized" ? "Not yet in Lean" : k[0].toUpperCase() + k.slice(1)}</button>
        ))}
      </div>
      <div style={{ display: "flex", gap: 16, flexWrap: "wrap", color: "var(--muted)", fontSize: ".82rem", marginBottom: 12 }}>
        {Object.entries({ "open problem": COLORS.open, "open, not yet in Lean": COLORS.unformalized, "known, no formal proof": COLORS.known, "warm-up": COLORS.warmup, "agent at work": COLORS.live, "solved here": COLORS.solved }).map(([l, c]) => (
          <span key={l}><i style={{ display: "inline-block", width: 10, height: 10, background: c, borderRadius: 2, marginRight: 6 }} />{l}</span>
        ))}
        <span>· brighter = harder</span>
      </div>
      <div ref={wrap} style={{ position: "relative" }}>
        {!data && <p style={{ color: "var(--faint)" }}>Loading the map…</p>}
        <canvas ref={ref}
          onMouseMove={(e) => { const p = at(e); setHover(p ? { x: p.x, y: p.y, r: p.r } : null); }}
          onMouseLeave={() => setHover(null)}
          onClick={(e) => { const p = at(e); if (p) window.location.href = `/p/${encodeURIComponent(p.r[0])}`; }}
          style={{ cursor: hover ? "pointer" : "default", display: "block" }} />
        {hover && (
          <div style={{ position: "absolute", left: Math.min(hover.x + 14, (wrap.current?.clientWidth ?? 600) - 260), top: hover.y + 14, background: "var(--card)", border: "1px solid var(--line-2)", borderRadius: 8, padding: "8px 10px", fontSize: ".82rem", width: 250, pointerEvents: "none", zIndex: 5 }}>
            <b>{hover.r[1]}</b>
            <div style={{ color: "var(--faint)" }}>difficulty {hover.r[4]}{hover.r[5] ? ` · ${hover.r[5]} agents live` : ""}{hover.r[6] ? " · solved" : ""}</div>
          </div>
        )}
      </div>
    </div>
  );
}
