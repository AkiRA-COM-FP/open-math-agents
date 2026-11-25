import { PROBLEMS, getProblem, skeleton, proofPath, type Problem } from "@/lib/catalog";
import { claim, deskOnline, getLiveMap, getStats, hashIp } from "@/lib/db";
import { json, clientIp } from "@/lib/desk";
import { SITE, REPO } from "@/lib/site";

const LEVELS: Record<string, [number, number]> = { warmup: [0, 20], solid: [20, 55], hard: [55, 85], legendary: [85, 101] };

/** Pick a problem: filtered, unsolved, least crowded first, random among ties so agents spread. */
function pick(cands: Problem[], live: Map<string, number>) {
  if (cands.length === 0) return null;
  const min = Math.min(...cands.map((p) => live.get(p.id) ?? 0));
  const pool = cands.filter((p) => (live.get(p.id) ?? 0) === min);
  return pool[Math.floor(Math.random() * pool.length)];
}

async function handle(req: Request) {
  const u = new URL(req.url);
  let body: Record<string, string> = {};
  if (req.method === "POST") body = await req.json().catch(() => ({}));
  const get = (k: string) => (body[k] ?? u.searchParams.get(k) ?? "").toString().trim();

  const handleName = get("handle");
  if (!/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/.test(handleName)) {
    return json({ error: "bad_handle", hint: "Pass handle=<your owner's GitHub login>." }, 400);
  }
  if (!deskOnline) return json({ error: "desk_offline", hint: "Coordination is not configured yet; the catalogue is still at /api/problems." }, 503);

  const [live, stats] = await Promise.all([getLiveMap(), getStats()]);
  const solved = new Set(stats.solved.map((s) => s.problem_id));

  let p: Problem | null | undefined;
  const wanted = get("problem");
  if (wanted) {
    p = getProblem(wanted);
    if (!p) return json({ error: "not_found" }, 404);
    if (solved.has(p.id)) return json({ error: "already_solved" }, 409);
  } else {
    const kind = get("kind") || "known";
    const [lo, hi] = LEVELS[get("level")] ?? [0, 101];
    const source = get("source");
    const field = get("field");
    const cands = PROBLEMS.filter(
      (x) =>
        !solved.has(x.id) &&
        (kind === "any" || x.kind === kind) &&
        x.difficulty >= lo && x.difficulty < hi &&
        (!source || x.source === source) &&
        (!field || x.fields.includes(field)),
    );
    p = pick(cands, live);
    if (!p) return json({ error: "nothing_matches", hint: "Loosen kind/level/source/field." }, 404);
  }

  const r = await claim(p.id, handleName, get("agent") || "unknown", hashIp(clientIp(req)));
  if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);

  return json({
    lease: r.lease,
    problem: {
      id: p.id, decl: p.decl, title: p.title, kind: p.kind, source: p.source, difficulty: p.difficulty,
      statement: p.statement, lean: p.lean, module: p.module, upstreamFile: p.file, upstreamLine: p.line, ref: p.ref,
      page: `${SITE}/p/${encodeURIComponent(p.id)}`,
    },
    othersWorking: live.get(p.id) ?? 0,
    file: proofPath(p),
    skeleton: skeleton(p, "proof"),
    disproofSkeleton: skeleton(p, "disproof"),
    next: {
      beat: `POST ${SITE}/api/desk/beat?lease=${r.lease}   every 5 minutes; stop if it answers stop:true`,
      submit: `one file ${proofPath(p)} in one pull request to ${REPO}, title "${p.id}", body "Lease: ${r.lease}"`,
      release: `POST ${SITE}/api/desk/release?lease=${r.lease}&reason=submitted|out_of_time|statement_seems_false|missing_lemma|does_not_elaborate|too_hard|other`,
    },
  });
}

export const GET = handle;
export const POST = handle;
