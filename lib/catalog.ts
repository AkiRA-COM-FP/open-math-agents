import "server-only";
import MiniSearch from "minisearch";
import raw from "@/data/catalog.json";
import extraRaw from "@/data/extra.json";
import statementsRaw from "@/data/statements.json";
import extra2Raw from "@/data/extra2.json";
import overridesRaw from "@/data/status_overrides.json";

/** open/known/warmup: has a Lean statement, provable now. unformalized: open, but nobody has stated it in Lean yet. */
export type Kind = "open" | "known" | "warmup" | "unformalized";

export type Problem = {
  id: string;
  decl: string;
  title: string;
  source: string;
  kind: Kind;
  category: string;
  fields: string[];
  tags: string[];
  statement: string;
  lean: string;
  module: string;
  file: string;
  line: number;
  ref: string | null;
  prize: string | null;
  erdos: number | null;
  erdosState: string | null;
  forumPosts: number;
  difficulty: number;
  // extra sources only
  license?: string;
  authors?: string[];
  area?: string;
  alsoIn?: string[];
  formalizedHere?: boolean;
  /** How well known the problem is, 0-100: the default order, most famous first. */
  fame: number;
  /** A solution has been announced but is not verified (or is disputed). */
  claim?: { summary: string; date: string; sources: string[] };
  /** Editorial note (e.g. why a related result does not settle this one). */
  note?: { summary: string; sources: string[] };
};

export type Override = { id: string; status: "solved" | "claimed" | "open"; title?: string; summary: string; date: string; sources: string[] };
const OVERRIDES = (overridesRaw as unknown as { reviewed: string; entries: Override[] }).entries;
export const STATUS_REVIEWED = (overridesRaw as unknown as { reviewed: string }).reviewed;
const OV = new Map(OVERRIDES.map((o) => [o.id, o]));

type Catalog = {
  meta: { upstream: string; upstreamCommit: string; license: string; counts: Record<"open" | "known" | "warmup", number>; total: number };
  problems: Problem[];
};

const catalog = raw as unknown as Catalog;
const extra = extraRaw as unknown as { meta: { counts: Record<string, number>; total: number; note: string }; problems: Problem[] };
const statements = statementsRaw as unknown as Record<string, { decl: string; module: string; lean: string; file: string }>;

const lg = (x: number) => Math.log10(1 + x);
const prizeUsd = (p: string | null) => { const m = (p ?? "").replace(/,/g, "").match(/[$£](\d+)/); return m ? Number(m[1]) : 0; };
/** Fame of the Lean catalogue and of the first extra batch (the long tail carries its own). */
function fameOf(p: Omit<Problem, "fame"> & { stars?: number; cites?: number }): number {
  const base: Record<string, number> = {
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

// A merged statements/<id>.lean turns an unformalized problem into a provable open problem.
const extraProblems: Problem[] = (extra.problems as (Problem & { stars?: number; cites?: number })[]).map((p) => {
  const st = statements[p.id];
  const q = { ...p, fame: fameOf(p) };
  return st ? { ...q, kind: "open", category: "research open (formalized here)", decl: st.decl, module: st.module, lean: st.lean, file: st.file, formalizedHere: true } : q;
});

// The long tail (OEIS conjectures, MathOverflow / Math.SE questions), stored as compact rows.
type Row = [string, string, number, string[], string, string, string[], number, number, string[], string, number];
const e2 = extra2Raw as unknown as { meta: { counts: Record<string, number>; total: number }; sources: string[]; licenses: Record<string, string>; rows: Row[] };
const extra2Problems: Problem[] = e2.rows.map(([id, title, si, fields, statement, ref, authors, fame, difficulty, tags, area, posts]) => {
  const st = statements[id];
  const p: Problem = {
    id, title, source: e2.sources[si], kind: "unformalized", category: "unformalized", fields, tags, statement, ref, authors, fame, difficulty,
    area, decl: "", lean: "", module: "", file: "", line: 0, prize: null, erdos: null, erdosState: null, forumPosts: posts, license: e2.licenses[e2.sources[si]],
  };
  return st ? { ...p, kind: "open", category: "research open (formalized here)", decl: st.decl, module: st.module, lean: st.lean, file: st.file, formalizedHere: true } : p;
});

const ALL: Problem[] = [
  ...(catalog.problems as Omit<Problem, "fame">[]).map((p) => ({ ...p, fame: fameOf(p) })),
  ...extraProblems,
  ...extra2Problems,
];

/** Problems settled recently (verified), removed from the open list and shown on /status. */
export const SETTLED: (Override & { problem?: Problem })[] = OVERRIDES.filter((o) => o.status === "solved").map((o) => ({ ...o, problem: ALL.find((p) => p.id === o.id) }));
/** Problems with an announced but unverified solution: kept, flagged, ranked lower. */
export const CLAIMED: Override[] = OVERRIDES.filter((o) => o.status === "claimed");

export const PROBLEMS: Problem[] = ALL.filter((p) => OV.get(p.id)?.status !== "solved").map((p) => {
  const o = OV.get(p.id);
  if (!o) return p;
  if (o.status === "claimed") return { ...p, fame: Math.max(1, p.fame - 30), claim: { summary: o.summary, date: o.date, sources: o.sources } };
  return { ...p, title: o.title ?? p.title, note: { summary: o.summary, sources: o.sources } };
});
const count = (k: Kind) => PROBLEMS.filter((p) => p.kind === k).length;
export const META = {
  ...catalog.meta,
  counts: { open: count("open"), known: count("known"), warmup: count("warmup"), unformalized: count("unformalized") } as Record<Kind, number>,
  total: PROBLEMS.length,
  extra: extra.meta,
  extra2: e2.meta,
};
/** Every open problem, stated in Lean or not. */
export const OPEN_TOTAL = META.counts.open + META.counts.unformalized;
const BY_ID = new Map(PROBLEMS.map((p) => [p.id, p]));

export const KIND_LABEL: Record<Kind, string> = {
  open: "Open problem",
  known: "Known result, no formal proof",
  warmup: "Warm-up",
  unformalized: "Open, not yet stated in Lean",
};

export const isProvable = (p: Problem) => p.kind !== "unformalized";

export function getProblem(id: string) {
  return BY_ID.get(id);
}

export const SOURCES = Array.from(new Set(PROBLEMS.map((p) => p.source))).sort();
export const FIELDS = Array.from(new Set(PROBLEMS.flatMap((p) => p.fields))).sort();

let index: MiniSearch<Problem> | null = null;
function getIndex() {
  if (index) return index;
  index = new MiniSearch<Problem>({
    fields: ["title", "statement", "decl", "source", "fieldsText", "tagsText", "erdosText"],
    storeFields: [],
    extractField: (doc, field) => {
      if (field === "fieldsText") return doc.fields.join(" ");
      if (field === "tagsText") return doc.tags.join(" ");
      if (field === "erdosText") return doc.erdos ? `erdos ${doc.erdos} erdős ${doc.erdos}` : "";
      if (field === "statement") return doc.statement.replace(/[\\${}_^]/g, " ");
      return (doc as unknown as Record<string, string>)[field];
    },
    searchOptions: {
      boost: { title: 4, decl: 2, tagsText: 2, fieldsText: 1.5, erdosText: 3 },
      prefix: true,
      fuzzy: 0.15,
      combineWith: "AND",
    },
  });
  index.addAll(PROBLEMS);
  return index;
}

export type Query = {
  q?: string;
  kind?: string;
  source?: string;
  field?: string;
  sort?: "relevance" | "famous" | "hardest" | "easiest" | "prize" | "active";
  limit?: number;
  offset?: number;
  live?: Map<string, number>;
  solved?: Set<string>;
  hideSolved?: boolean;
};

export function prizeValue(p: Problem) {
  if (!p.prize) return 0;
  const m = p.prize.replace(/,/g, "").match(/[$£](\d+)/);
  return m ? Number(m[1]) : 0;
}

export function search(query: Query) {
  let list: Problem[];
  const q = query.q?.trim();
  const erdos = q?.match(/^erd(?:o|ő|oe)s\s*#?\s*(\d+)$/i);
  if (erdos) {
    list = PROBLEMS.filter((p) => p.erdos === Number(erdos[1]));
  } else if (q) {
    let hits = getIndex().search(q);
    if (hits.length === 0) hits = getIndex().search(q, { combineWith: "OR" });
    list = hits.map((h) => BY_ID.get(h.id as string)!).filter(Boolean);
  } else {
    list = PROBLEMS.slice();
  }
  if (query.kind && query.kind !== "all") list = list.filter((p) => p.kind === query.kind);
  if (query.source && query.source !== "all") list = list.filter((p) => p.source === query.source);
  if (query.field && query.field !== "all") list = list.filter((p) => p.fields.includes(query.field!));
  if (query.hideSolved && query.solved) list = list.filter((p) => !query.solved!.has(p.id));
  const sort = query.sort ?? (q ? "relevance" : "famous");
  if (sort === "famous") list.sort((a, b) => b.fame - a.fame || b.difficulty - a.difficulty || a.id.localeCompare(b.id));
  if (sort === "hardest") list.sort((a, b) => b.difficulty - a.difficulty || a.id.localeCompare(b.id));
  if (sort === "easiest") list.sort((a, b) => a.difficulty - b.difficulty || a.id.localeCompare(b.id));
  if (sort === "prize") list.sort((a, b) => prizeValue(b) - prizeValue(a) || b.difficulty - a.difficulty);
  if (sort === "active" && query.live) {
    const live = query.live;
    list.sort((a, b) => (live.get(b.id) ?? 0) - (live.get(a.id) ?? 0) || b.difficulty - a.difficulty);
  }
  const total = list.length;
  const offset = Math.max(0, query.offset ?? 0);
  const limit = Math.min(200, Math.max(1, query.limit ?? 30));
  return { total, items: list.slice(offset, offset + limit) };
}

const TEX: Record<string, string> = {
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
const BB: Record<string, string> = { N: "ℕ", Z: "ℤ", Q: "ℚ", R: "ℝ", C: "ℂ", P: "ℙ", F: "𝔽" };

/** Rough TeX → Unicode for one-line excerpts (the problem page renders real KaTeX). */
export function texPlain(s: string) {
  return s
    .replace(/\\mathbb\s*\{?([A-Z])\}?/g, (_, c) => BB[c] ?? c)
    .replace(/\\frac\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g, "($1)/($2)")
    .replace(/\\([A-Za-z]+)/g, (m, w) => (w in TEX ? TEX[w] : w))
    .replace(/\\[,;!: ]/g, " ")
    .replace(/[{}$*`]/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

/** Compact card shape sent to the browser. */
export function toCard(p: Problem) {
  return {
    claimed: Boolean(p.claim),
    id: p.id,
    title: p.title,
    source: p.source,
    kind: p.kind,
    fields: p.fields,
    difficulty: p.difficulty,
    prize: p.prize,
    excerpt: texPlain(p.statement).slice(0, 260),
  };
}
export type Card = ReturnType<typeof toCard>;

/** The Lean skeleton an agent fills in. `type_of%` pins the exact upstream statement. */
export function skeleton(p: Problem, polarity: "proof" | "disproof" = "proof", handle = "<your GitHub handle>") {
  const target = polarity === "proof" ? `type_of% @${p.decl}` : `¬ (type_of% @${p.decl})`;
  return [
    `import ${p.module}`,
    ``,
    `-- Problem: ${p.title}`,
    `-- Upstream: formal-conjectures ${p.file}:${p.line} (declaration ${p.decl})`,
    `-- Credit: @${handle} (the owner of the agent is credited as the solver)`,
    `-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.`,
    ``,
    `theorem OMA.${polarity === "proof" ? "solution" : "disproof"} : ${target} := by`,
    `  sorry`,
    ``,
  ].join("\n");
}

/** Skeleton of a reduction: 2 to 4 smaller statements that together imply the target. */
export function reductionSkeleton(p: Problem, n = 1, handle = "<your GitHub handle>") {
  const ns = "OMA.R_" + `${p.id}.R${n}`.replace(/[^A-Za-z0-9]/g, "_");
  return [
    `import ${p.module}`,
    ``,
    `-- Reduction ${p.id}.R${n} of ${p.title}`,
    `-- Credit: @${handle}`,
    `-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.`,
    ``,
    `namespace ${ns}`,
    ``,
    `def H1 : Prop := sorry -- a smaller statement`,
    ``,
    `def H2 : Prop := sorry -- another one`,
    ``,
    `theorem main : H1 → H2 → type_of% @${p.decl} := by`,
    `  sorry`,
    ``,
    `end ${ns}`,
    ``,
  ].join("\n");
}

/** Skeleton of a Lean statement for a problem that has none. Reviewed by a person before it is merged. */
export function statementSkeleton(p: Problem, handle = "<your GitHub handle>") {
  const ns = "OMA.S_" + p.id.replace(/[^A-Za-z0-9]/g, "_");
  return [
    `import Mathlib`,
    ``,
    `/-!`,
    `# ${p.title}`,
    ``,
    `Source: ${p.ref ?? p.source}`,
    `Credit: @${handle}`,
    ``,
    `State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.`,
    `Do not prove it here: the theorem body stays \`sorry\`. A person reviews the translation before merging.`,
    `-/`,
    ``,
    `namespace ${ns}`,
    ``,
    `-- definitions the statement needs (no sorry, no axiom)`,
    ``,
    `theorem main : sorry := by`,
    `  sorry`,
    ``,
    `end ${ns}`,
    ``,
  ].join("\n");
}

export function proofPath(p: Problem) {
  return `proofs/${p.id}.lean`;
}
