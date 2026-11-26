"use client";
import { useEffect, useRef, useState } from "react";

type Row = [string, string, number, number, number, number, number];

/** Every problem as a tiny grey square; the ones this person touched in black, the ones they solved in green. */
export default function Footprint({ touched, solved }: { touched: string[]; solved: string[] }) {
  const ref = useRef<HTMLCanvasElement>(null);
  const wrap = useRef<HTMLDivElement>(null);
  const [rows, setRows] = useState<Row[] | null>(null);
  useEffect(() => { fetch("/api/map").then((r) => r.json()).then((d) => setRows(d.rows)).catch(() => setRows([])); }, []);
  useEffect(() => {
    const c = ref.current, w = wrap.current;
    if (!c || !w || !rows) return;
    const T = new Set(touched), S = new Set(solved);
    const draw = () => {
      const width = w.clientWidth - 24, cell = 3;
      const per = Math.floor(width / cell), height = Math.ceil(rows.length / per) * cell;
      const dpr = window.devicePixelRatio || 1;
      c.width = width * dpr; c.height = height * dpr; c.style.width = width + "px"; c.style.height = height + "px";
      const ctx = c.getContext("2d")!;
      ctx.scale(dpr, dpr);
      ctx.fillStyle = "#e3e3e3";
      rows.forEach((r, i) => ctx.fillRect((i % per) * cell, Math.floor(i / per) * cell, cell - 1, cell - 1));
      rows.forEach((r, i) => {
        if (!T.has(r[0]) && !S.has(r[0])) return;
        const x = (i % per) * cell, y = Math.floor(i / per) * cell;
        ctx.fillStyle = S.has(r[0]) ? "#1a7f37" : "#000";
        ctx.beginPath(); ctx.arc(x + 1, y + 1, 4, 0, Math.PI * 2); ctx.fill();
      });
    };
    draw();
    const ro = new ResizeObserver(draw);
    ro.observe(w);
    return () => ro.disconnect();
  }, [rows, touched, solved]);
  return (
    <div ref={wrap} className="footprint">
      {!rows && <p style={{ color: "var(--faint)", margin: 0 }}>Loading the map…</p>}
      <canvas ref={ref} style={{ display: "block" }} aria-label="Every problem on the site; this person's are marked" />
    </div>
  );
}
