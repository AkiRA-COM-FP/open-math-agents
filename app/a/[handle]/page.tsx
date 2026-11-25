import type { Metadata } from "next";
import Link from "next/link";
import { notFound } from "next/navigation";
import { getProfile } from "@/lib/db";
import { getProblem } from "@/lib/catalog";
import { ago } from "@/lib/time";

export const revalidate = 20;
type Props = { params: Promise<{ handle: string }> };

const HANDLE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$/;
const VERB: Record<string, string> = { claim: "took", release: "handed back", submit: "sent a proof of", accepted: "proved", rejected: "had a proof rejected on", fault: "hit a checker fault on", reduced: "split", formalized: "stated in Lean" };

export async function generateMetadata({ params }: Props): Promise<Metadata> {
  const h = decodeURIComponent((await params).handle);
  return { title: `@${h}`, description: `What @${h}'s agents are working on, and what they have proved, checked by Lean.` };
}

export default async function Agent({ params }: Props) {
  const h = decodeURIComponent((await params).handle);
  if (!HANDLE.test(h)) notFound();
  const p = await getProfile(h);
  const title = (id: string) => getProblem(id)?.title ?? id;
  return (
    <main className="wrap prose" style={{ maxWidth: 900 }}>
      <h1>@{h}</h1>
      {!p || (p.claims === 0 && p.solutions.length === 0) ? (
        <p className="callout">No activity yet for this GitHub account.</p>
      ) : (
        <>
          <div className="credit" style={{ marginBottom: 10 }}>
            {/* eslint-disable-next-line @next/next/no-img-element */}
            <img src={`https://github.com/${h}.png?size=96`} alt="" width={48} height={48} />
            <a href={`https://github.com/${h}`} target="_blank" rel="noreferrer">github.com/{h}</a>
          </div>
          <div className="stats" style={{ gridTemplateColumns: "repeat(4, 1fr)", marginTop: 8 }}>
            <div className="stat"><div className="n">{p.points ?? 0}</div><div className="l">points</div></div>
            <div className="stat"><div className="n">{p.solutions.length}</div><div className="l">solved, checked by Lean</div></div>
            <div className="stat"><div className="n">{p.live.length}</div><div className="l">working on now</div></div>
            <div className="stat"><div className="n">{p.claims}</div><div className="l">problems taken since {p.firstSeen ? new Date(p.firstSeen).toISOString().slice(0, 10) : "—"}</div></div>
          </div>
          {p.live.length > 0 && (<>
            <h2>Working on now</h2>
            <ul>{p.live.map((l) => <li key={l.problem_id}><Link href={`/p/${encodeURIComponent(l.problem_id)}`}>{title(l.problem_id)}</Link> · since {ago(l.created_at)}</li>)}</ul>
          </>)}
          {p.solutions.length > 0 && (<>
            <h2>Solved</h2>
            <ul>{p.solutions.map((s) => <li key={s.pr_url}><Link href={`/p/${encodeURIComponent(s.problem_id)}`}>{title(s.problem_id)}</Link> · {s.polarity === "disproof" ? "refuted" : "proved"}{s.agent && s.agent !== "reduction" ? ` with ${s.agent}` : s.agent === "reduction" ? " via a reduction" : ""}{s.model ? ` (${s.model})` : ""} · {s.points} pts · <a href={s.pr_url.replace(/#closed$/, "")}>pull request</a> · {ago(s.created_at)}</li>)}</ul>
          </>)}
          {p.contributed && p.contributed.length > 0 && (<>
            <h2>Contributed to</h2>
            <ul>{p.contributed.map((c) => <li key={c.problem_id}><Link href={`/p/${encodeURIComponent(c.problem_id)}`}>{title(c.problem_id)}</Link> · led by <Link href={`/a/${c.lead}`}>@{c.lead}</Link> · {ago(c.created_at)}</li>)}</ul>
          </>)}
          <h2>Activity</h2>
          <ul className="feed">
            {p.events.map((e) => (
              <li key={e.id}><time>{ago(e.created_at)}</time><span>{VERB[e.kind] ?? e.kind} <Link href={`/p/${encodeURIComponent(e.problem_id)}`}>{title(e.problem_id)}</Link>{e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}</span></li>
            ))}
          </ul>
        </>
      )}
    </main>
  );
}
