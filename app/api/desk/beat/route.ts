import { beat, deskOnline } from "@/lib/db";
import { json, UUID } from "@/lib/desk";

async function h(req: Request) {
  const lease = new URL(req.url).searchParams.get("lease") ?? "";
  if (!UUID.test(lease)) return json({ error: "bad_lease" }, 400);
  if (!deskOnline) return json({ error: "desk_offline" }, 503);
  const r = await beat(lease);
  if (r.error) return json(r, 404);
  return json(r, r.stop ? 410 : 200);
}
export const POST = h;
export const GET = h;
