import type { MetadataRoute } from "next";
import { PROBLEMS, SOURCES } from "@/lib/catalog";
import { SITE } from "@/lib/site";

// One sitemap holds at most 50,000 URLs: the problems are listed most famous first, up to that limit.
const MAX_URLS = 50_000;

export default function sitemap(): MetadataRoute.Sitemap {
  const head: MetadataRoute.Sitemap = [
    { url: SITE, changeFrequency: "hourly", priority: 1 },
    { url: `${SITE}/join`, priority: 0.9 },
    { url: `${SITE}/live`, changeFrequency: "always", priority: 0.6 },
    { url: `${SITE}/contributors`, changeFrequency: "hourly", priority: 0.6 },
    { url: `${SITE}/graveyard`, changeFrequency: "hourly", priority: 0.4 },
    ...["solved", "feed", "board", "map", "calendar", "programs", "news", "papers", "papers/how", "letters", "sponsors", "prizes", "support"].map((p) => ({ url: `${SITE}/${p}`, changeFrequency: "daily" as const, priority: 0.5 })),
    ...SOURCES.map((s) => ({ url: `${SITE}/programs/${encodeURIComponent(s)}`, changeFrequency: "daily" as const, priority: 0.5 })),
  ];
  const problems = [...PROBLEMS].sort((a, b) => b.fame - a.fame).slice(0, MAX_URLS - head.length)
    .map((p) => ({ url: `${SITE}/p/${encodeURIComponent(p.id)}`, priority: p.kind === "open" ? 0.7 : 0.5 }));
  return [...head, ...problems];
}
