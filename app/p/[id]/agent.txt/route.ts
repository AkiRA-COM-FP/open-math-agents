import { buildBrief } from "@/lib/pack";

export const revalidate = 60;

/** The self-contained brief an agent reads to start on this exact problem. */
export async function GET(_req: Request, ctx: { params: Promise<{ id: string }> }) {
  const id = decodeURIComponent((await ctx.params).id);
  const text = await buildBrief(id);
  if (!text) return new Response(`No problem ${id}. Browse ${"https://shipfastwith.me"}/#problems\n`, { status: 404, headers: { "Content-Type": "text/plain; charset=utf-8" } });
  return new Response(text, {
    headers: {
      "Content-Type": "text/plain; charset=utf-8",
      "Cache-Control": "public, s-maxage=60, stale-while-revalidate=300",
      "Vercel-CDN-Cache-Control": "max-age=60, stale-while-revalidate=300",
    },
  });
}
