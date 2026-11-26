import { NextResponse } from "next/server";
import { certificateId, verifySigned, type Certificate } from "@/lib/cert";

/** POST a signed certificate ({certificate, signature}); answers whether the signature matches the published key. */
export async function POST(req: Request) {
  const body = (await req.json().catch(() => null)) as { certificate?: Certificate; signature?: string } | null;
  if (!body?.certificate || typeof body.signature !== "string") return NextResponse.json({ valid: false, error: "expected {certificate, signature}" }, { status: 400 });
  const valid = await verifySigned({ certificate: body.certificate, signature: body.signature });
  return NextResponse.json({ valid, id: valid ? await certificateId(body.certificate) : null }, { headers: { "Access-Control-Allow-Origin": "*" } });
}
