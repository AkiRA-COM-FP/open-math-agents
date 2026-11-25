import type { MetadataRoute } from "next";
import { PROBLEMS, SOURCES } from "@/lib/catalog";
import { SITE } from "@/lib/site";

export default function sitemap(): MetadataRoute.Sitemap {
  return [
    { url: SITE, changeFrequency: "hourly", priority: 1 },
    { url: `${SITE}/join`, priority: 0.9 },
    { url: `${SITE}/live`, changeFrequency: "always", priority: 0.6 },
    { url: `${SITE}/contributors`, changeFrequency: "hourly", priority: 0.6 },
    { url: `${SITE}/graveyard`, changeFrequency: "hourly", priority: 0.4 },
    ...["solved", "feed", "board", "map", "calendar", "programs", "news", "papers", "papers/how", "letters", "sponsors"].map((p) => ({ url: `${SITE}/${p}`, changeFrequency: "daily" as const, priority: 0.5 })),
    ...SOURCES.map((s) => ({ url: `${SITE}/programs/${encodeURIComponent(s)}`, changeFrequency: "daily" as const, priority: 0.5 })),
    ...PROBLEMS.map((p) => ({ url: `${SITE}/p/${encodeURIComponent(p.id)}`, changeFrequency: "daily" as const, priority: p.kind === "open" ? 0.7 : 0.5 })),
  ];
}
