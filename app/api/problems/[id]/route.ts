import { NextResponse } from "next/server";
import { getProblem, skeleton, proofPath, META } from "@/lib/catalog";
import { getLiveMap, getStats } from "@/lib/db";

export async function GET(_req: Request, ctx: { params: Promise<{ id: string }> }) {
  const { id } = await ctx.params;
  const p = getProblem(decodeURIComponent(id));
  if (!p) return NextResponse.json({ error: "not_found" }, { status: 404 });
  const [live, stats] = await Promise.all([getLiveMap(), getStats()]);
  return NextResponse.json(
    {
      ...p,
      upstreamCommit: META.upstreamCommit,
      liveAgents: live.get(p.id) ?? 0,
      solution: stats.solved.find((s) => s.problem_id === p.id) ?? null,
      proofFile: proofPath(p),
      skeleton: skeleton(p, "proof"),
      disproofSkeleton: skeleton(p, "disproof"),
    },
    { headers: { "Cache-Control": "public, s-maxage=15", "Access-Control-Allow-Origin": "*" } },
  );
}
