import { timingSafeEqual } from "node:crypto";
import { verdict2, registerReduction, deskOnline, getSteps, logEvent } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { json } from "@/lib/desk";
import { pointsFor } from "@/lib/points";
import { REDUCTION_FILE_RE, STEP_RE, reductionHypotheses, reductionModule } from "@/lib/steps";
import { REPO } from "@/lib/site";

const GH = "https://api.github.com";
const ghHeaders: Record<string, string> = {
  Accept: "application/vnd.github+json",
  "User-Agent": "open-math-agents",
  ...(process.env.GITHUB_TOKEN ? { Authorization: `Bearer ${process.env.GITHUB_TOKEN}` } : {}),
};

/** "Agent: claude-code" / "Model: claude-opus-5-5" lines in the pull request body. Free text, shown as credit. */
function creditLine(body: string, key: string) {
  const m = body.match(new RegExp(`^\\s*${key}\\s*:\\s*(.+)$`, "im"));
  return m ? m[1].replace(/[<>`*_\[\]]/g, "").trim().slice(0, 80) || null : null;
}

/**
 * Records a merged contribution. Nothing in the request body is trusted except a PR number: the site asks
 * GitHub whether that pull request is merged into main, what single file it added, and who authored it.
 * The PR author (the owner of the agent) is credited as the solver; the agent and model they declared in the
 * PR body are recorded next to it.
 */
export async function POST(req: Request) {
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const b = await req.json().catch(() => null);
  if (!b) return json({ error: "bad_request" }, 400);

  // Optional trusted path for maintainers (manual corrections).
  const secret = process.env.OMA_VERDICT_SECRET ?? "";
  const got = req.headers.get("x-oma-secret") ?? "";
  if (secret && got && got.length === secret.length && timingSafeEqual(Buffer.from(got), Buffer.from(secret))) {
    if (typeof b.problem !== "string" || !/^https:\/\/github\.com\//.test(b.pr ?? "") || !["accepted", "rejected", "fault"].includes(b.verdict)) {
      return json({ error: "bad_request" }, 400);
    }
    const p = getProblem(b.problem);
    return json(await verdict2({
      problem: b.problem, handle: String(b.handle).slice(0, 39), pr: b.pr, verdict: b.verdict,
      polarity: b.polarity === "disproof" ? "disproof" : "proof", agent: b.agent ?? null, model: b.model ?? null,
      points: p ? pointsFor(p.difficulty, p.kind) : Number(b.points ?? 1),
    }));
  }

  const n = Number(b.pr);
  if (!Number.isInteger(n) || n <= 0) return json({ error: "bad_request", hint: "body {\"pr\": <pull request number>}" }, 400);

  const prRes = await fetch(`${GH}/repos/${REPO}/pulls/${n}`, { headers: ghHeaders, cache: "no-store" });
  if (prRes.status === 404) return json({ error: "no_such_pr" }, 404);
  if (!prRes.ok) return json({ error: "github", status: prRes.status }, 502);
  const pr = await prRes.json();
  if (!pr.merged || pr.base?.ref !== "main") return json({ error: "not_merged" }, 409);

  const filesRes = await fetch(`${GH}/repos/${REPO}/pulls/${n}/files`, { headers: ghHeaders, cache: "no-store" });
  if (!filesRes.ok) return json({ error: "github", status: filesRes.status }, 502);
  const files: { filename: string; status: string }[] = await filesRes.json();
  if (files.length !== 1 || files[0].status !== "added") return json({ error: "not_a_single_new_file" }, 409);
  const path = files[0].filename;

  const raw = await fetch(`https://raw.githubusercontent.com/${REPO}/${pr.merge_commit_sha}/${path}`, { cache: "no-store" });
  const src = raw.ok ? await raw.text() : "";
  const handle = String(pr.user?.login ?? "unknown").slice(0, 39);
  const body = String(pr.body ?? "");
  const agent = creditLine(body, "Agent");
  const model = creditLine(body, "Model");

  // A reduction: register its hypotheses as new steps.
  const red = path.match(REDUCTION_FILE_RE);
  if (red) {
    const target = red[1];
    const id = `${target}.R${red[2]}`;
    const parentProblem = getProblem(target);
    const parentStep = parentProblem ? null : (await getSteps(target)).find((s) => s.id === target);
    if (!parentProblem && !parentStep) return json({ error: "unknown_target", target }, 409);
    const statements = reductionHypotheses(src);
    if (statements.length < 2 || statements.length > 4) return json({ error: "bad_reduction", found: statements.length }, 409);
    const points = parentProblem ? pointsFor(parentProblem.difficulty, parentProblem.kind) : parentStep!.points;
    return json(await registerReduction({ id, problem: target, handle, pr: pr.html_url, module: reductionModule(id), statements, points }));
  }

  // A Lean statement for a problem that had none: merged only after human review. Logged and credited;
  // the problem becomes provable at the next build (scripts/build_statements.mjs).
  const stm = path.match(/^statements\/([^/]+)\.lean$/);
  if (stm) {
    const sp = getProblem(stm[1]);
    if (!sp) return json({ error: "unknown_problem", id: stm[1] }, 409);
    return json(await logEvent("formalized", sp.id, handle, pr.html_url));
  }

  const m = path.match(/^proofs\/([^/]+)\.lean$/);
  if (!m) return json({ error: "not_a_proof" }, 409);
  const id = m[1];
  const polarity = /\btheorem\s+OMA\.disproof\b/.test(src) ? "disproof" : "proof";
  const p = getProblem(id);
  let points: number;
  if (p && p.kind === "unformalized") return json({ error: "not_formalized_yet", id }, 409);
  if (p) points = pointsFor(p.difficulty, p.kind);
  else if (STEP_RE.test(id)) {
    const step = (await getSteps(id)).find((s) => s.id === id);
    if (!step) return json({ error: "unknown_step", id }, 409);
    points = step.points;
  } else return json({ error: "unknown_problem", id }, 409);

  return json(await verdict2({ problem: id, handle, pr: pr.html_url, verdict: "accepted", polarity, agent, model, points }));
}
