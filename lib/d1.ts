import "server-only";
import { env } from "cloudflare:workers";

/**
 * The half of the catalogue that does not fit in a Worker's memory, in D1 (built by scripts/build_data.mjs).
 *  - core (shard 0): one row per problem in `problem` (long values in parts), full-text index `fts`, upstream Lean files.
 *  - MathOverflow (shard 1): ~20 questions per row in `mo_detail` (bucket = question id mod bucket count), and a
 *    contentless full-text index `mo_fts` whose rowid is the question id. Packing keeps D1 row writes low.
 */
const db = () => (env as unknown as { CATALOG: D1Database }).CATALOG;
type Ref = { id: string; shard: number };
const qid = (id: string) => Number(id.slice(3));

async function joined(sql: string, key: string): Promise<string | null> {
  const r = await db().prepare(sql).bind(key).all<{ v: string }>();
  return r.results.length ? r.results.map((x) => x.v).join("") : null;
}

async function moBuckets(refs: Ref[], buckets: number): Promise<Map<string, Record<string, unknown>>> {
  const out = new Map<string, Record<string, unknown>>();
  const bs = Array.from(new Set(refs.map((r) => qid(r.id) % buckets)));
  for (let i = 0; i < bs.length; i += 90) {
    const chunk = bs.slice(i, i + 90);
    const r = await db().prepare(`SELECT data FROM mo_detail WHERE b IN (${chunk.map(() => "?").join(",")})`).bind(...chunk).all<{ data: string }>();
    for (const row of r.results) for (const [id, d] of Object.entries(JSON.parse(row.data) as Record<string, Record<string, unknown>>)) out.set(id, d);
  }
  return out;
}

export async function problemDetail(p: Ref, buckets: number): Promise<Record<string, unknown> | null> {
  if (p.shard === 1) return (await moBuckets([p], buckets)).get(p.id) ?? null;
  const s = await joined("SELECT data AS v FROM problem WHERE id = ? ORDER BY part", p.id);
  return s ? JSON.parse(s) : null;
}

/** Details of many problems in a few queries (D1 binds up to 100 parameters per statement). */
export async function problemDetails(ps: Ref[], buckets: number): Promise<Map<string, Record<string, unknown>>> {
  const out = await moBuckets(ps.filter((p) => p.shard === 1), buckets);
  const ids = ps.filter((p) => p.shard !== 1).map((p) => p.id);
  for (let i = 0; i < ids.length; i += 90) {
    const chunk = ids.slice(i, i + 90);
    const r = await db().prepare(`SELECT id, data FROM problem WHERE id IN (${chunk.map(() => "?").join(",")}) ORDER BY id, part`).bind(...chunk).all<{ id: string; data: string }>();
    const parts = new Map<string, string>();
    for (const row of r.results) parts.set(row.id, (parts.get(row.id) ?? "") + row.data);
    for (const [id, s] of parts) out.set(id, JSON.parse(s));
  }
  return out;
}

/** The first characters of each statement, for list rows (only the rows a page shows). */
export async function excerpts(ps: Ref[], buckets: number): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  if (ps.length === 0) return out;
  try {
    for (const [id, d] of await moBuckets(ps.filter((p) => p.shard === 1), buckets)) out.set(id, String(d.statement ?? "").slice(0, 400));
    const ids = ps.filter((p) => p.shard !== 1).map((p) => p.id);
    for (let i = 0; i < ids.length; i += 90) {
      const chunk = ids.slice(i, i + 90);
      const r = await db().prepare(
        `SELECT id, substr(json_extract(data, '$.statement'), 1, 400) AS s FROM problem WHERE part = 0 AND json_valid(data) AND id IN (${chunk.map(() => "?").join(",")})`,
      ).bind(...chunk).all<{ id: string; s: string | null }>();
      for (const row of r.results) if (row.s) out.set(row.id, row.s);
    }
  } catch (e) {
    console.error("excerpts", e);
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

/**
 * Problem ids matching a free-text query, best first. Core (BM25; title 4×, Lean name 2×, fields and tags 1.5×) and
 * MathOverflow (BM25 on title 4×, text 1×, tags 1.5×) are queried together and interleaved by rank.
 */
export async function catalogSearch(q: string, limit = 2000): Promise<string[]> {
  const t = terms(q);
  if (t.length === 0) return [];
  const run = async (match: string) => {
    const [a, b] = await Promise.all([
      db().prepare("SELECT id FROM fts WHERE fts MATCH ? ORDER BY bm25(fts, 0.0, 4.0, 1.0, 2.0, 1.5) LIMIT ?").bind(match, limit).all<{ id: string }>()
        .then((r) => r.results.map((x) => x.id)),
      db().prepare("SELECT rowid AS n FROM mo_fts WHERE mo_fts MATCH ? ORDER BY bm25(mo_fts, 4.0, 1.0, 1.5) LIMIT ?").bind(match, limit).all<{ n: number }>()
        .then((r) => r.results.map((x) => `mo-${x.n}`)).catch(() => [] as string[]),
    ]);
    const out: string[] = [];
    for (let i = 0; i < Math.max(a.length, b.length); i++) { if (i < a.length) out.push(a[i]); if (i < b.length) out.push(b[i]); }
    return out;
  };
  try {
    const hits = await run(t.join(" AND "));
    return hits.length || t.length === 1 ? hits : await run(t.join(" OR "));
  } catch (e) {
    console.error("catalogSearch", e);
    return [];
  }
}
