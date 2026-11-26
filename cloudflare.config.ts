import { bindings, defineConfig, defineWorker } from "cf/config";
import { createWorkersCacheConfig } from "@vinext/cloudflare/cache/config";

const cache = await createWorkersCacheConfig();

export default defineConfig({
  worker: defineWorker({
    ...cache,
    name: "open-math-agents",
    entrypoint: "vinext/server/fetch-handler",
    compatibilityDate: "2026-11-10",
    assets: {
      htmlHandling: "none",
      notFoundHandling: "none",
      runWorkerFirst: ["/*", "!/_next/static/*", "!/*/_next/static/*"],
    },
    env: {
      ...cache.env,
      ASSETS: bindings.assets(),
      // Public settings (also read at build time: NEXT_PUBLIC_* are inlined into the pages).
      NEXT_PUBLIC_SITE_URL: bindings.text("https://shipfastwith.me"),
      NEXT_PUBLIC_SUPPORT_URL: bindings.text("https://ko-fi.com/guillaumebaud"),
      NEXT_PUBLIC_SPONSOR_URL: bindings.text("https://ko-fi.com/guillaumebaud"),
      SUPABASE_URL: bindings.text("https://fcuptmutkcstnaxmqsmg.supabase.co"),
      // Set with the secrets API, never in this file.
      SUPABASE_PUBLISHABLE_KEY: bindings.secret(),
      OMA_DB_SECRET: bindings.secret(),
      OMA_IP_SALT: bindings.secret(),
      OMA_VERDICT_SECRET: bindings.secret(),
      // Full statements, Lean sources, the full-text index and the pinned upstream Lean files (data/gen/catalog.sql).
      CATALOG: bindings.d1({ id: "740a3c15-d8dd-460c-bcdd-938e38df77b7", name: "oma-catalog" }),
    },
  }),
});
