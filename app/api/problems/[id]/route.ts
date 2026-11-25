import { NextResponse } from "next/server";
import { getProblem, skeleton, reductionSkeleton, proofPath, META } from "@/lib/catalog";
import { getLiveMap, getStats, getSteps } from "@/lib/db";
import { pointsFor } from "@/lib/points";
import { STEP_RE, stepSkeleton } from "@/lib/steps";

const H = { "Cache-Control": "public, s-maxage=15", "Vercel-CDN-Cache-Control": "max-age=15", "Access-Control-Allow-Origin": "*" };

export async function GET(req: Request, ctx: { params: Promise<{ id: string }> }) {
  const id = decodeURIComponent((await ctx.params).id);
  const sp = new URL(req.url).searchParams;
  const handle = /^[A-Za-z0-9-]{1,39}$/.test(sp.get("handle") ?? "") ? sp.get("handle")! : undefined;
  const n = Math.min(99, Math.max(1, Number(sp.get("reduction") ?? 1) || 1));
  const [live, stats] = await Promise.all([getLiveMap(), getStats()]);
  const solution = stats.solved.find((s) => s.problem_id === id) ?? null;

  const p = getProblem(id);
  if (p) {
    return NextResponse.json({
      ...p,
      upstreamCommit: META.upstreamCommit,
      points: pointsFor(p.difficulty, p.kind),
      liveAgents: live.get(p.id) ?? 0,
      solution,
      steps: await getSteps(p.id),
      proofFile: proofPath(p),
      skeleton: skeleton(p, "proof", handle),
      disproofSkeleton: skeleton(p, "disproof", handle),
      reductionFile: `reductions/${p.id}.R${n}.lean`,
      reductionSkeleton: reductionSkeleton(p, n, handle),
    }, { headers: H });
  }
  if (STEP_RE.test(id)) {
    const step = (await getSteps(id)).find((s) => s.id === id);
    if (step) {
      const ns = "OMA.R_" + `${id}.R${n}`.replace(/[^A-Za-z0-9]/g, "_");
      return NextResponse.json({
        ...step, kind: "step", liveAgents: live.get(id) ?? 0, solution,
        proofFile: `proofs/${id}.lean`, skeleton: stepSkeleton(step, handle),
        reductionFile: `reductions/${id}.R${n}.lean`,
        reductionSkeleton: [
          `import ${step.module}`, ``, `-- Reduction ${id}.R${n} of step ${id}`, `-- Credit: @${handle ?? "<your GitHub handle>"}`, ``,
          `namespace ${ns}`, ``, `def H1 : Prop := sorry`, ``, `def H2 : Prop := sorry`, ``,
          `theorem main : H1 → H2 → OMA.R_${step.reduction.replace(/[^A-Za-z0-9]/g, "_")}.H${step.k} := by`, `  sorry`, ``, `end ${ns}`, ``,
        ].join("\n"),
      }, { headers: H });
    }
  }
  return NextResponse.json({ error: "not_found" }, { status: 404 });
}
