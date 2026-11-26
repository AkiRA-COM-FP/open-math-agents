import fs from "node:fs";
import path from "node:path";
import Link from "@/components/Link";

export type Sponsor = { name: string; url?: string; logo?: string; tier: "supporter" | "sponsor" | "lead"; since?: string };
export type Tier = { id: string; name: string; price: number; period: string; perks: string[] };

export function readSponsors(): Sponsor[] {
  try { return JSON.parse(fs.readFileSync(path.join(process.cwd(), "content", "sponsors.json"), "utf8")); } catch { return []; }
}
export function readTiers(): { currency: string; tiers: Tier[] } {
  try { return JSON.parse(fs.readFileSync(path.join(process.cwd(), "content", "sponsor_tiers.json"), "utf8")); } catch { return { currency: "USD", tiers: [] }; }
}
/** Payment page for a tier: NEXT_PUBLIC_SPONSOR_URL_<ID>, else NEXT_PUBLIC_SPONSOR_URL, else the sponsors page. */
export function tierUrl(id: string) {
  return process.env[`NEXT_PUBLIC_SPONSOR_URL_${id.toUpperCase()}`] ?? process.env.NEXT_PUBLIC_SPONSOR_URL ?? "/sponsors#tiers";
}
const fmt = (n: number, c: string) => n.toLocaleString("en-US", { style: "currency", currency: c, maximumFractionDigits: 0 });

/** "Backed by" strip for the home page: logos of lead sponsors and sponsors, then a "your logo" slot. */
export default function SponsorStrip() {
  const sponsors = readSponsors().filter((s) => s.tier !== "supporter" && s.logo);
  const { currency, tiers } = readTiers();
  const logoTier = tiers.find((t) => t.id === "sponsor");
  const ordered = [...sponsors.filter((s) => s.tier === "lead"), ...sponsors.filter((s) => s.tier === "sponsor")];
  return (
    <div className="sponsors">
      <span className="k">Backed by</span>
      {ordered.map((s) => (
        <a key={s.name} href={s.url ?? "/sponsors"} target={s.url ? "_blank" : undefined} rel="noreferrer sponsored" title={s.name} className={s.tier === "lead" ? "lead" : ""}>
          {/* eslint-disable-next-line @next/next/no-img-element */}
          <img src={s.logo} alt={s.name} />
        </a>
      ))}
      <Link href="/sponsors" className="slot">+ Your logo{logoTier ? ` · ${fmt(logoTier.price, currency)}` : ""} →</Link>
    </div>
  );
}
