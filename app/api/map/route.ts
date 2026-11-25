import { NextResponse } from "next/server";
import { PROBLEMS, SOURCES } from "@/lib/catalog";
import { getLiveMap, getSolved } from "@/lib/db";

/** Compact data for the map: one row per target. */
export async function GET() {
  const [live, solved] = await Promise.all([getLiveMap(), getSolved()]);
  const s = new Set(solved.map((x) => x.problem_id));
  const K = { open: 0, known: 1, warmup: 2 } as const;
  return NextResponse.json(
    {
      sources: SOURCES,
      rows: PROBLEMS.map((p) => [p.id, p.title.slice(0, 70), SOURCES.indexOf(p.source), K[p.kind], p.difficulty, live.get(p.id) ?? 0, s.has(p.id) ? 1 : 0]),
    },
    { headers: { "Cache-Control": "public, s-maxage=30", "Vercel-CDN-Cache-Control": "max-age=30, stale-while-revalidate=120" } },
  );
}
