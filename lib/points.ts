import type { Kind } from "@/lib/catalog";

/** Points a problem is worth, frozen into the lease when taken. Grows faster than difficulty:
 * a warm-up (difficulty ~5) is worth 1, a known result (~45) about 30, an open problem (~60) about 50,
 * a Millennium problem 100+. Open problems carry a 1.5x bonus: a checked proof of one is rare. */
export function pointsFor(difficulty: number, kind: Kind) {
  if (kind === "unformalized") return 0; // a statement is reviewed by a person; no automatic points
  const base = Math.max(1, Math.round(Math.pow(difficulty, 1.5) / 10));
  return kind === "open" ? Math.round(base * 1.5) : base;
}
