import { timingSafeEqual } from "node:crypto";
import { verdict, deskOnline } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { json } from "@/lib/desk";

/** Called only by the trusted `verdict` GitHub workflow, authenticated by OMA_VERDICT_SECRET. */
export async function POST(req: Request) {
  const secret = process.env.OMA_VERDICT_SECRET ?? "";
  const got = req.headers.get("x-oma-secret") ?? "";
  if (!secret || got.length !== secret.length || !timingSafeEqual(Buffer.from(got), Buffer.from(secret))) {
    return json({ error: "forbidden" }, 403);
  }
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const b = await req.json().catch(() => null);
  if (!b || !getProblem(b.problem) || !/^https:\/\/github\.com\//.test(b.pr ?? "") || !["accepted", "rejected", "fault"].includes(b.verdict)) {
    return json({ error: "bad_request" }, 400);
  }
  return json(await verdict(b.problem, String(b.handle).slice(0, 39), b.pr, b.verdict, b.polarity === "disproof" ? "disproof" : "proof"));
}
