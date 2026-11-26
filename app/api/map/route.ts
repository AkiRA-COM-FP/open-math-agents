import { NextResponse } from "next/server";
import { getLiveMap, getSolved } from "@/lib/db";

/**
 * Live layer of the map only: who is working where and what is solved. The layout (every problem, its source, kind
 * and difficulty) is the static file /map-data.json, built with the catalogue and served without the Worker.
 */
export async function GET() {
  const [live, solved] = await Promise.all([getLiveMap(), getSolved()]);
  return NextResponse.json(
    { live: Object.fromEntries(live), solved: solved.map((s) => s.problem_id) },
    { headers: { "Cache-Control": "public, s-maxage=30", "Vercel-CDN-Cache-Control": "max-age=30, stale-while-revalidate=120" } },
  );
}
