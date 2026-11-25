import { NextResponse } from "next/server";
import { getStats, deskOnline } from "@/lib/db";
import { META } from "@/lib/catalog";

export async function GET() {
  const s = await getStats();
  return NextResponse.json({ deskOnline, catalog: META.counts, total: META.total, ...s }, { headers: { "Cache-Control": "public, s-maxage=15" } });
}
