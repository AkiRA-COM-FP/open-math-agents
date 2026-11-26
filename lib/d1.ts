import "server-only";
import { env } from "cloudflare:workers";

/**
 * The half of the catalogue that does not fit in a Worker's memory, in D1 (built by scripts/build_data.mjs):
 * full statements and Lean sources, the full-text index, and the pinned upstream Lean files.
 * Long values are stored in parts (D1 caps one SQL statement at 100 KB) and joined back here.
 */
const db = () => (env as unknown as { CATALOG: D1Database }).CATALOG;

async function joined(sql: string, key: string): Promise<string | null> {
  const r = await db().prepare(sql).bind(key).all<{ v: string }>();
  return r.results.length ? r.results.map((x) => x.v).join("") : null;
}

export async function problemDetail(id: string): Promise<Record<string, unknown> | null> {
  const s = await joined("SELECT data AS v FROM problem WHERE id = ? ORDER BY part", id);
  return s ? JSON.parse(s) : null;
}

/** Details of many problems in at most a few queries (D1 binds up to 100 parameters per statement). */
export async function problemDetails(ids: string[]): Promise<Map<string, Record<string, unknown>>> {
  const out = new Map<string, Record<string, unknown>>();
  for (let i = 0; i < ids.length; i += 90) {
    const chunk = ids.slice(i, i + 90);
    const r = await db().prepare(`SELECT id, data FROM problem WHERE id IN (${chunk.map(() => "?").join(",")}) ORDER BY id, part`).bind(...chunk).all<{ id: string; data: string }>();
    const parts = new Map<string, string>();
    for (const row of r.results) parts.set(row.id, (parts.get(row.id) ?? "") + row.data);
    for (const [id, s] of parts) out.set(id, JSON.parse(s));
  }
  return out;
}

export function upstreamFileFromDb(path: string): Promise<string | null> {
  return joined("SELECT content AS v FROM upstream_file WHERE path = ? ORDER BY part", path);
}

/** Words of a query, lower-cased and without accents, as FTS5 prefix terms ("erdos"* AND "prime"*). */
function terms(q: string): string[] {
  const words = q.toLowerCase().normalize("NFKD").replace(/[̀-ͯ]/g, "").match(/[\p{L}\p{N}]+/gu) ?? [];
  return words.slice(0, 8).map((w) => (w.length >= 2 ? `"${w}"*` : `"${w}"`));
}

/** Problem ids matching a free-text query, best first (BM25; title counts 4×, Lean name 2×, fields and tags 1.5×). */
export async function catalogSearch(q: string, limit = 2000): Promise<string[]> {
  const t = terms(q);
  if (t.length === 0) return [];
  const run = async (match: string) =>
    (await db().prepare("SELECT id FROM fts WHERE fts MATCH ? ORDER BY bm25(fts, 0.0, 4.0, 1.0, 2.0, 1.5) LIMIT ?").bind(match, limit).all<{ id: string }>()).results.map((r) => r.id);
  try {
    const hits = await run(t.join(" AND "));
    return hits.length || t.length === 1 ? hits : await run(t.join(" OR "));
  } catch (e) {
    console.error("catalogSearch", e);
    return [];
  }
}
