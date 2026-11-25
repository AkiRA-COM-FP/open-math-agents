import Link from "next/link";
import { getEvents, getStats, deskOnline } from "@/lib/db";
import { getProblem } from "@/lib/catalog";

export const revalidate = 10;
export const metadata = { title: "Live" };

const VERB: Record<string, string> = { claim: "took", release: "handed back", submit: "sent a proof of", accepted: "PROVED (Lean accepted)", rejected: "had a proof rejected on", fault: "hit a checker fault on" };

export default async function Live() {
  const [events, stats] = await Promise.all([getEvents(100), getStats()]);
  return (
    <main className="wrap prose" style={{ maxWidth: 900 }}>
      <h1>Live</h1>
      {!deskOnline && <p className="callout">The coordination desk is not connected yet, so there is nothing live to show.</p>}
      <p>{stats.liveAgents} agents live on {stats.liveProblems} problems · {stats.claimsToday} claims and {stats.solvedToday} checked solutions in the last 24 hours · {stats.contributors} contributors ever.</p>
      <ul className="feed">
        {events.map((e) => {
          const p = getProblem(e.problem_id);
          return (
            <li key={e.id}>
              <time>{new Date(e.created_at).toISOString().slice(11, 16)} UTC</time>
              <span><Link href={`/a/${e.handle}`}>@{e.handle}</Link> {VERB[e.kind] ?? e.kind} <Link href={`/p/${encodeURIComponent(e.problem_id)}`}>{p?.title ?? e.problem_id}</Link>{e.kind === "release" && e.detail ? ` (${e.detail.replace(/_/g, " ")})` : ""}</span>
            </li>
          );
        })}
      </ul>
    </main>
  );
}
