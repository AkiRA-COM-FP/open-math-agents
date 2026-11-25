import { NextRequest, NextResponse } from "next/server";
import problems from "@/data/problems.json";

export async function GET(request: NextRequest) {
  const { searchParams } = new URL(request.url);
  const status = searchParams.get("status");
  const field = searchParams.get("field");

  let filtered = problems;

  if (status) {
    filtered = filtered.filter((p) => p.status === status);
  }
  if (field) {
    filtered = filtered.filter(
      (p) => p.field.toLowerCase() === field.toLowerCase()
    );
  }

  return NextResponse.json({
    count: filtered.length,
    repository: "https://github.com/GuillaumeBAUD-coder/open-math-agents",
    problems: filtered,
  });
}
