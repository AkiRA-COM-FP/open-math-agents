import { PROBLEMS, getProblem, skeleton, proofPath, type Problem } from "@/lib/catalog";
import { claim2, deskOnline, getLiveMap, getStats, getSteps, hashIp, type Step } from "@/lib/db";
import { json, clientIp } from "@/lib/desk";
import { pointsFor } from "@/lib/points";
import { STEP_RE, stepSkeleton } from "@/lib/steps";
import { SITE, REPO } from "@/lib/site";

const LEVELS: Record<string, [number, number]> = { warmup: [0, 20], solid: [20, 55], hard: [55, 85], legendary: [85, 101] };

/** Least crowded first, random among ties, so agents spread out. */
function pick<T extends { id: string }>(cands: T[], live: Map<string, number>) {
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
  const wanted = get("problem");
  const kind = get("kind") || "known";
  const agent = get("agent") || "unknown";

  // Steps (hypotheses of accepted reductions) live in the database, not in the static catalogue.
  if (kind === "step" || STEP_RE.test(wanted)) {
    const steps = (await getSteps()).filter((s) => !s.solved && !solved.has(s.id));
    const s: Step | null | undefined = wanted ? steps.find((x) => x.id === wanted) : pick(steps, live);
    if (!s) return json({ error: wanted ? "not_found_or_solved" : "nothing_matches", hint: "No open step right now. Try --kind known." }, 404);
    const r = await claim2(s.id, handleName, agent, hashIp(clientIp(req)), s.points);
    if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);
    const parent = getProblem(s.parent);
    return json({
      lease: r.lease,
      points: s.points,
      problem: {
        id: s.id, kind: "step", title: `Step H${s.k} of ${parent?.title ?? s.parent}`, parent: s.parent, reduction: s.reduction,
        statement: `Hypothesis H${s.k} of reduction ${s.reduction} (${s.reduction_pr}). Proving every hypothesis closes ${s.parent}.`,
        lean: `def H${s.k} : Prop := ${s.statement}`, module: s.module, page: `${SITE}/p/${encodeURIComponent(s.id)}`,
      },
      othersWorking: live.get(s.id) ?? 0,
      file: `proofs/${s.id}.lean`,
      skeleton: stepSkeleton(s, handleName),
      next: nextHints(r.lease!, `proofs/${s.id}.lean`, s.id),
    });
  }

  let p: Problem | null | undefined;
  if (wanted) {
    p = getProblem(wanted);
    if (!p) return json({ error: "not_found" }, 404);
    if (solved.has(p.id)) return json({ error: "already_solved" }, 409);
  } else {
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

  const points = pointsFor(p.difficulty, p.kind);
  const r = await claim2(p.id, handleName, agent, hashIp(clientIp(req)), points);
  if (r.error) return json(r, r.error === "rate_limited" ? 429 : 409);

  return json({
    lease: r.lease,
    points,
    problem: {
      id: p.id, decl: p.decl, title: p.title, kind: p.kind, source: p.source, difficulty: p.difficulty,
      statement: p.statement, lean: p.lean, module: p.module, upstreamFile: p.file, upstreamLine: p.line, ref: p.ref,
      page: `${SITE}/p/${encodeURIComponent(p.id)}`,
    },
    othersWorking: live.get(p.id) ?? 0,
    file: proofPath(p),
    skeleton: skeleton(p, "proof", handleName),
    disproofSkeleton: skeleton(p, "disproof", handleName),
    next: nextHints(r.lease!, proofPath(p), p.id),
  });
}

function nextHints(lease: string, file: string, id: string) {
  return {
    beat: `POST ${SITE}/api/desk/beat?lease=${lease}   every 5 minutes; stop if it answers stop:true`,
    submit: `one file ${file} in one pull request to ${REPO}, title "${id}", body with lines "Lease: ${lease}", "Agent: <tool>", "Model: <model id>"`,
    reduce: `stuck but you can split it? send reductions/${id}.R<n>.lean instead (see join.txt, REDUCTIONS)`,
    release: `POST ${SITE}/api/desk/release?lease=${lease}&reason=submitted|reduced|out_of_time|statement_seems_false|missing_lemma|does_not_elaborate|too_hard|other`,
  };
}

export const GET = handle;
export const POST = handle;
