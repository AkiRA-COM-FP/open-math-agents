import { NextRequest, NextResponse } from "next/server";
import { META, search, toCard, getProblem } from "@/lib/catalog";
import { getLiveMap, getStats } from "@/lib/db";

export async function GET(req: NextRequest) {
  const sp = req.nextUrl.searchParams;
  const sort = (sp.get("sort") ?? undefined) as "relevance" | "hardest" | "easiest" | "prize" | "active" | undefined;
  const [live, stats] = await Promise.all([getLiveMap(), getStats()]);
  const solved = new Set(stats.solved.map((s) => s.problem_id));
  const { total, items } = search({
    q: sp.get("q") ?? undefined,
    kind: sp.get("kind") ?? sp.get("status") ?? undefined,
    source: sp.get("source") ?? undefined,
    field: sp.get("field") ?? undefined,
    sort,
    limit: Number(sp.get("limit") ?? 30),
    offset: Number(sp.get("offset") ?? 0),
    live,
    solved,
    hideSolved: sp.get("unsolved") === "1",
  });
  const full = sp.get("full") === "1";
  return NextResponse.json(
    {
      total,
      upstream: { repo: META.upstream, commit: META.upstreamCommit },
      items: items.map((p) => ({
        ...(full ? getProblem(p.id) : toCard(p)),
        liveAgents: live.get(p.id) ?? 0,
        solved: solved.has(p.id),
      })),
    },
    {
      headers: {
        "Cache-Control": "public, s-maxage=30, stale-while-revalidate=120",
        // Next.js rewrites Cache-Control on route handlers; this header is read by Vercel's CDN only.
        "Vercel-CDN-Cache-Control": "max-age=30, stale-while-revalidate=120",
        "Access-Control-Allow-Origin": "*",
      },
    },
  );
}
