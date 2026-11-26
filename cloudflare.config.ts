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
      // Full statements, Lean sources, the full-text index and the pinned upstream Lean files (data/gen/catalog.sql).
      CATALOG: bindings.d1({ id: "740a3c15-d8dd-460c-bcdd-938e38df77b7", name: "oma-catalog" }),
    },
  }),
});
