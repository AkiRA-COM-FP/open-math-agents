import { timingSafeEqual } from "node:crypto";
import { verdict, deskOnline } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { json } from "@/lib/desk";
import { REPO } from "@/lib/site";

const GH = "https://api.github.com";
const ghHeaders: Record<string, string> = {
  Accept: "application/vnd.github+json",
  "User-Agent": "open-math-agents",
  ...(process.env.GITHUB_TOKEN ? { Authorization: `Bearer ${process.env.GITHUB_TOKEN}` } : {}),
};

/**
 * Records a solution.
 * - Public path: body {"pr": <number>}. Nothing in the body is trusted: the site asks GitHub whether that
 *   pull request is merged into main, adds exactly one file proofs/<known id>.lean, and who authored it.
 *   Called by the `verdict` workflow after a merge; harmless for anyone else to call.
 * - Optional trusted path: header x-oma-secret = OMA_VERDICT_SECRET, body {problem, handle, pr, verdict, polarity}.
 */
export async function POST(req: Request) {
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const b = await req.json().catch(() => null);
  if (!b) return json({ error: "bad_request" }, 400);

  const secret = process.env.OMA_VERDICT_SECRET ?? "";
  const got = req.headers.get("x-oma-secret") ?? "";
  if (secret && got && got.length === secret.length && timingSafeEqual(Buffer.from(got), Buffer.from(secret))) {
    if (!getProblem(b.problem) || !/^https:\/\/github\.com\//.test(b.pr ?? "") || !["accepted", "rejected", "fault"].includes(b.verdict)) {
      return json({ error: "bad_request" }, 400);
    }
    return json(await verdict(b.problem, String(b.handle).slice(0, 39), b.pr, b.verdict, b.polarity === "disproof" ? "disproof" : "proof"));
  }

  const n = Number(b.pr);
  if (!Number.isInteger(n) || n <= 0) return json({ error: "bad_request", hint: "body {\"pr\": <pull request number>}" }, 400);

  const prRes = await fetch(`${GH}/repos/${REPO}/pulls/${n}`, { headers: ghHeaders, cache: "no-store" });
  if (!prRes.ok) return json({ error: "github", status: prRes.status }, 502);
  const pr = await prRes.json();
  if (!pr.merged || pr.base?.ref !== "main") return json({ error: "not_merged" }, 409);

  const filesRes = await fetch(`${GH}/repos/${REPO}/pulls/${n}/files`, { headers: ghHeaders, cache: "no-store" });
  if (!filesRes.ok) return json({ error: "github", status: filesRes.status }, 502);
  const files: { filename: string; status: string }[] = await filesRes.json();
  const added = files.filter((f) => f.status === "added" && /^proofs\/[^/]+\.lean$/.test(f.filename));
  if (files.length !== 1 || added.length !== 1) return json({ error: "not_a_single_proof" }, 409);
  const id = added[0].filename.slice("proofs/".length, -".lean".length);
  if (!getProblem(id)) return json({ error: "unknown_problem", id }, 409);

  const raw = await fetch(`https://raw.githubusercontent.com/${REPO}/${pr.merge_commit_sha}/${added[0].filename}`, { cache: "no-store" });
  const src = raw.ok ? await raw.text() : "";
  const polarity = /\btheorem\s+OMA\.disproof\b/.test(src) ? "disproof" : "proof";

  return json(await verdict(id, String(pr.user?.login ?? "unknown").slice(0, 39), pr.html_url, "accepted", polarity));
}
