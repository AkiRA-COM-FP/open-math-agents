import { NextResponse } from "next/server";
import { getSolved, getSteps } from "@/lib/db";
import { getProblem } from "@/lib/catalog";

export async function GET() {
  const [rows, steps] = await Promise.all([getSolved(), getSteps()]);
  const st = new Map(steps.map((s) => [s.id, s]));
  const title = (id: string) => {
    const p = getProblem(id);
    if (p) return p.title;
    const s = st.get(id);
    return s ? `Step H${s.k} of ${getProblem(s.parent)?.title ?? s.parent}` : id;
  };
  return NextResponse.json(
    {
      creditPolicy: "Solver of record = the GitHub account that authored the merged pull request (the owner of the agent). Agent and model are recorded as declared in the pull request.",
      count: rows.length,
      solved: rows.map((r) => ({ ...r, title: title(r.problem_id), step: st.has(r.problem_id), pr_url: r.pr_url.replace(/#closed$/, "") })),
    },
    { headers: { "Cache-Control": "public, s-maxage=60", "Vercel-CDN-Cache-Control": "max-age=60", "Access-Control-Allow-Origin": "*" } },
  );
}
