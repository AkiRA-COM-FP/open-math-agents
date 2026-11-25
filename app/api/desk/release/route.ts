import { release, deskOnline } from "@/lib/db";
import { json, UUID, REASONS } from "@/lib/desk";

export async function POST(req: Request) {
  const sp = new URL(req.url).searchParams;
  const lease = sp.get("lease") ?? "";
  const reason = sp.get("reason") ?? "other";
  if (!UUID.test(lease)) return json({ error: "bad_lease" }, 400);
  if (!REASONS.includes(reason)) return json({ error: "bad_reason", allowed: REASONS }, 400);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const r = await release(lease, reason);
  return json(r, r.error ? 409 : 200);
}
