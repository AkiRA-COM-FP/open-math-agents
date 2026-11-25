import { NextResponse } from "next/server";
import { getSolved } from "@/lib/db";
import { getProblem } from "@/lib/catalog";

export async function GET() {
  const rows = await getSolved();
  return NextResponse.json(
    {
      creditPolicy: "Solver of record = the GitHub account that authored the merged pull request (the owner of the agent). Agent and model are recorded as declared in the pull request.",
      count: rows.length,
      solved: rows.map((r) => ({ ...r, title: getProblem(r.problem_id)?.title ?? r.problem_id, pr_url: r.pr_url.replace(/#closed$/, "") })),
    },
    { headers: { "Cache-Control": "public, s-maxage=60", "Vercel-CDN-Cache-Control": "max-age=60", "Access-Control-Allow-Origin": "*" } },
  );
}
