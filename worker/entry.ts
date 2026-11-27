/**
 * Worker entry: vinext's handler, plus a page cache in the Cache API of each data centre (free, not billed; unlike
 * Workers Cache, which bills every request). Only plain GET page requests are cached (no API, no RSC navigation
 * request, no authorization), only when vinext marks the page cacheable (s-maxage), for at most that long.
 * A cached page costs about a millisecond of CPU instead of a full render.
 */
import handler from "vinext/server/fetch-handler";
export * from "vinext/server/fetch-handler";

type ExecutionContext = { waitUntil(p: Promise<unknown>): void; passThroughOnException?(): void };
type Handler = { fetch(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> };
const inner = handler as unknown as Handler;
const SKIP = /^\/(api|_next|__|cdn-cgi)(\/|$)/;
const ORIGIN = "https://lefttosolve.com";

function eligible(req: Request, url: URL): boolean {
  if (req.method !== "GET" || SKIP.test(url.pathname) || url.searchParams.has("_rsc")) return false;
  const h = req.headers;
  for (const k of ["rsc", "next-router-state-tree", "next-router-prefetch", "next-router-segment-prefetch", "next-action", "authorization", "x-vinext-rsc-render-mode"]) {
    if (h.has(k)) return false;
  }
  return true;
}

export default {
  async fetch(req: Request, env: unknown, ctx: ExecutionContext): Promise<Response> {
    const url = new URL(req.url);
    const cache = (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default;
    if (!cache || !eligible(req, url)) return inner.fetch(req, env, ctx);
    const key = new Request(`${ORIGIN}/__html${url.pathname}${url.search}`);
    const hit = await cache.match(key).catch(() => undefined);
    if (hit) {
      const r = new Response(hit.body, hit);
      r.headers.set("cache-control", "public, max-age=0, must-revalidate");
      r.headers.set("x-page-cache", "HIT");
      return r;
    }
    const res = await inner.fetch(req, env, ctx);
    const m = /s-maxage=(\d+)/.exec(res.headers.get("cache-control") ?? "");
    const type = res.headers.get("content-type") ?? "";
    if (res.status === 200 && m && !res.headers.has("set-cookie") && /^text\/(html|plain)/.test(type)) {
      const ttl = Math.min(Number(m[1]), 600);
      if (ttl > 0) {
        const copy = new Response(res.clone().body, res);
        copy.headers.set("cache-control", `public, max-age=${ttl}`);
        copy.headers.delete("vary");
        copy.headers.delete("x-page-cache");
        ctx.waitUntil(cache.put(key, copy).catch(() => undefined));
      }
    }
    return res;
  },
};
