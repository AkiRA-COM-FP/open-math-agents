#!/usr/bin/env node
// Build the two halves of the catalogue for Cloudflare Workers, where a Worker has 128 MB of memory:
//   data/gen/cards.json   what lists, filters and sorts need, kept in memory (~10 MB of heap)
//   data/gen/catalog.sql  full statements, Lean sources, the full-text index and the upstream Lean files, loaded into D1
// Run after scripts/build_statements.mjs. Usage: node scripts/build_data.mjs
import fs from "node:fs";
import path from "node:path";
import zlib from "node:zlib";

const ROOT = path.join(path.dirname(new URL(import.meta.url).pathname), "..");
const D = (f) => JSON.parse(fs.readFileSync(path.join(ROOT, "data", f), "utf8"));
const catalog = D("catalog.json");
const extra = D("extra.json");
const e2 = D("extra2.json");
const statements = D("statements.json");

const lg = (x) => Math.log10(1 + x);
const prizeUsd = (p) => { const m = (p ?? "").replace(/,/g, "").match(/[$£](\d+)/); return m ? Number(m[1]) : 0; };
function fameOf(p) {
  const base = {
    "Millennium Prize": 100, "Hilbert's Problems": 95, "Wikipedia": 85, "Green's 100 Open Problems": 78, "Kourovka Notebook": 60,
    "MathOverflow": 58, "Erdős Problems": 62, "OEIS": 42, "Wikipedia list (not formalized)": 80, "Open Problem Garden": 45,
    "Erdős Problems (not formalized)": 58,
  };
  let f = base[p.source] ?? 50;
  if (p.prize) f += Math.min(18, 4 * lg(prizeUsd(p.prize)));
  if (p.stars) f += 8 * p.stars;
  if (p.cites) f += Math.min(10, 3 * lg(p.cites));
  if (p.forumPosts) f += Math.min(6, p.forumPosts / 5);
  if (/\.variants?\.|\.parts?\./.test(p.decl)) f -= 8;
  if (p.kind === "warmup") f -= 20;
  return Math.max(1, Math.min(100, Math.round(f)));
}
const formalized = (p) => {
  const st = statements[p.id];
  return st ? { ...p, kind: "open", category: "research open (formalized here)", decl: st.decl, module: st.module, lean: st.lean, file: st.file, formalizedHere: true } : p;
};

const all = [
  ...catalog.problems.map((p) => ({ ...p, fame: fameOf(p) })),
  ...extra.problems.map((p) => formalized({ ...p, fame: fameOf(p) })),
  ...e2.rows.map(([id, title, si, fields, statement, ref, authors, fame, difficulty, tags, area, posts]) => formalized({
    id, title, source: e2.sources[si], kind: "unformalized", category: "unformalized", fields, tags, statement, ref, authors, fame, difficulty,
    area, decl: "", lean: "", module: "", file: "", line: 0, prize: null, erdos: null, erdosState: null, forumPosts: posts, license: e2.licenses[e2.sources[si]],
  })),
];

// Same TeX → Unicode as lib/catalog.ts texPlain, for the one-line excerpt kept in memory.
const TEX = {
  mathbb: "", mathbf: "", mathrm: "", mathcal: "", operatorname: "", text: "", textrm: "", mathfrak: "",
  le: "≤", leq: "≤", ge: "≥", geq: "≥", ne: "≠", neq: "≠", in: "∈", notin: "∉", subset: "⊂", subseteq: "⊆",
  cup: "∪", cap: "∩", infty: "∞", to: "→", rightarrow: "→", mapsto: "↦", times: "×", cdot: "·", cdots: "…", ldots: "…", dots: "…",
  sum: "∑", prod: "∏", int: "∫", sqrt: "√", log: "log", exp: "exp", lim: "lim", liminf: "liminf", limsup: "limsup", sim: "∼",
  approx: "≈", ll: "≪", gg: "≫", forall: "∀", exists: "∃", neg: "¬", land: "∧", lor: "∨", mid: "|", lvert: "|", rvert: "|", vert: "|",
  alpha: "α", beta: "β", gamma: "γ", delta: "δ", epsilon: "ε", varepsilon: "ε", zeta: "ζ", eta: "η", theta: "θ", lambda: "λ",
  mu: "μ", nu: "ν", pi: "π", rho: "ρ", sigma: "σ", tau: "τ", phi: "φ", varphi: "φ", chi: "χ", psi: "ψ", omega: "ω",
  Gamma: "Γ", Delta: "Δ", Lambda: "Λ", Sigma: "Σ", Phi: "Φ", Omega: "Ω", left: "", right: "", lfloor: "⌊", rfloor: "⌋",
  lceil: "⌈", rceil: "⌉", binom: "binom", frac: "", pmod: "mod", bmod: "mod", equiv: "≡", setminus: "∖", emptyset: "∅",
};
const BB = { N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", P: "ℙ", F: "𝔽" };
const texPlain = (s) => s
  .replace(/\\mathbb\s*\{?([A-Z])\}?/g, (_, c) => BB[c] ?? c)
  .replace(/\\frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, "($1)/($2)")
  .replace(/\\([A-Za-z]+)/g, (m, w) => (w in TEX ? TEX[w] : w))
  .replace(/\\[,;!: ]/g, " ")
  .replace(/[{}$*`]/g, "")
  .replace(/\s+/g, " ")
  .trim();

// ---- cards.json ----------------------------------------------------------------------------------------
const sources = Array.from(new Set(all.map((p) => p.source))).sort();
const KINDS = ["open", "known", "warmup", "unformalized"];
// id, title, source index, kind index, fields, tags, difficulty, fame, prize, forumPosts, erdos, excerpt, decl
const rows = all.map((p) => [
  p.id, p.title, sources.indexOf(p.source), KINDS.indexOf(p.kind), p.fields ?? [], p.tags ?? [], p.difficulty, p.fame,
  p.prize ?? null, p.forumPosts ?? 0, p.erdos ?? null, texPlain(p.statement ?? "").slice(0, 200), p.decl ?? "",
]);
fs.mkdirSync(path.join(ROOT, "data", "gen"), { recursive: true });
fs.writeFileSync(path.join(ROOT, "data", "gen", "cards.json"), JSON.stringify({
  meta: { ...catalog.meta, extra: extra.meta, extra2: e2.meta }, sources, kinds: KINDS, rows,
}));

// ---- catalog.sql ---------------------------------------------------------------------------------------
// D1 caps one SQL statement at 100 KB, so long values are split into parts of at most 12,000 characters (36 KB of UTF-8 at worst).
const q = (s) => "'" + String(s).replace(/'/g, "''") + "'";
const PART = 12000;
const parts = (s) => { const out = []; for (let i = 0; i < s.length || i === 0; i += PART) out.push(s.slice(i, i + PART)); return out; };
const out = [
  "DROP TABLE IF EXISTS problem;", "DROP TABLE IF EXISTS fts;", "DROP TABLE IF EXISTS upstream_file;", "DROP TABLE IF EXISTS meta;",
  "CREATE TABLE problem (id TEXT NOT NULL, part INTEGER NOT NULL, data TEXT NOT NULL, PRIMARY KEY (id, part));",
  "CREATE VIRTUAL TABLE fts USING fts5(id UNINDEXED, title, statement, decl, extra, tokenize = 'unicode61 remove_diacritics 2', prefix = '2 3 4');",
  "CREATE TABLE upstream_file (path TEXT NOT NULL, part INTEGER NOT NULL, content TEXT NOT NULL, PRIMARY KEY (path, part));",
  "CREATE TABLE meta (k TEXT PRIMARY KEY, v TEXT NOT NULL);",
];
const DETAIL = ["statement", "lean", "module", "file", "line", "category", "ref", "erdosState", "license", "authors", "area", "alsoIn", "formalizedHere"];
for (const p of all) {
  const d = {};
  for (const k of DETAIL) if (p[k] !== undefined && p[k] !== null && p[k] !== "") d[k] = p[k];
  parts(JSON.stringify(d)).forEach((s, i) => out.push(`INSERT INTO problem VALUES (${q(p.id)}, ${i}, ${q(s)});`));
  const extraText = [p.source, ...(p.fields ?? []), ...(p.tags ?? []), p.erdos ? `erdos ${p.erdos} erdős ${p.erdos}` : ""].join(" ");
  out.push(`INSERT INTO fts (id, title, statement, decl, extra) VALUES (${q(p.id)}, ${q(p.title)}, ${q((p.statement ?? "").replace(/[\\${}_^]/g, " ").slice(0, 12000))}, ${q((p.decl ?? "").replace(/[._]/g, " "))}, ${q(extraText)});`);
}
const files = JSON.parse(zlib.gunzipSync(fs.readFileSync(path.join(ROOT, "data", "fc_files.json.gz"))).toString("utf8"));
for (const [p, content] of Object.entries(files)) parts(content).forEach((s, i) => out.push(`INSERT INTO upstream_file VALUES (${q(p)}, ${i}, ${q(s)});`));
const version = `${catalog.meta.upstreamCommit.slice(0, 12)}-${all.length}-${Object.keys(statements).length}`;
out.push(`INSERT INTO meta VALUES ('version', ${q(version)});`);
fs.writeFileSync(path.join(ROOT, "data", "gen", "catalog.sql"), out.join("\n") + "\n");
fs.writeFileSync(path.join(ROOT, "data", "gen", "version.txt"), version + "\n");
const mb = (f) => (fs.statSync(path.join(ROOT, "data", "gen", f)).size / 1e6).toFixed(1);
console.log(`cards.json ${mb("cards.json")} MB (${rows.length} problems) · catalog.sql ${mb("catalog.sql")} MB (${out.length} statements, ${Object.keys(files).length} upstream files) · version ${version}`);
