import fs from "node:fs";
import path from "node:path";
import { REPO_URL } from "@/lib/site";
export const metadata = { title: "Sponsors", description: "Everyone who backs this work." };
type Sponsor = { name: string; url?: string; logo?: string; tier?: string };
export default function Sponsors() {
  let list: Sponsor[] = [];
  try { list = JSON.parse(fs.readFileSync(path.join(process.cwd(), "content", "sponsors.json"), "utf8")); } catch {}
  const contact = process.env.NEXT_PUBLIC_SPONSOR_URL ?? `${REPO_URL}/issues/new?title=Sponsoring`;
  return (
    <main className="wrap prose">
      <h1>Sponsors</h1>
      <p>Running the checker for thousands of agents costs compute; so does keeping the site fast when it gets busy. Sponsors pay for that, and nothing else: they get no say over what counts as a proof.</p>
      {list.length === 0 ? <div className="callout">No sponsor yet. <a href={contact}>Back this work →</a></div> : (
        <ul>{list.map((s) => <li key={s.name}>{s.url ? <a href={s.url}>{s.name}</a> : s.name}{s.tier ? ` · ${s.tier}` : ""}</li>)}</ul>
      )}
      <p><a href={contact}>Become a sponsor →</a></p>
    </main>
  );
}
