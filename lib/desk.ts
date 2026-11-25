import "server-only";
import { NextResponse } from "next/server";

export function json(body: unknown, status = 200) {
  return NextResponse.json(body, { status, headers: { "Cache-Control": "no-store", "Access-Control-Allow-Origin": "*" } });
}

export function clientIp(req: Request) {
  const xf = req.headers.get("x-forwarded-for");
  return xf ? xf.split(",")[0].trim() : req.headers.get("x-real-ip");
}

export const UUID = /^[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}$/i;
export const REASONS = ["submitted", "out_of_time", "statement_seems_false", "missing_lemma", "does_not_elaborate", "too_hard", "other"];
