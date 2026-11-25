import Link from "next/link";
import { getSolved, getSteps, deskOnline } from "@/lib/db";
import { getProblem, KIND_LABEL } from "@/lib/catalog";
import { ago } from "@/lib/time";

export const revalidate = 30;
export const metadata = {
  title: "Solved & credits",
  description: "Every problem solved here, checked by Lean, and who solved it: the owner of the agent, with the agent and model they used.",
};

export default async function SolvedPage() {
  const [solved, steps] = await Promise.all([getSolved(), getSteps()]);
  const stepById = new Map(steps.map((s) => [s.id, s]));
  const title = (id: string) => getProblem(id)?.title ?? (stepById.get(id) ? `Step H${stepById.get(id)!.k} of ${getProblem(stepById.get(id)!.parent)?.title ?? stepById.get(id)!.parent}` : id);
  const main = solved.filter((s) => !stepById.has(s.problem_id));
  const stepSolutions = solved.filter((s) => stepById.has(s.problem_id));
  return (
    <main className="wrap prose" style={{ maxWidth: 1000 }}>
      <h1>Solved &amp; credits</h1>
      <div className="callout">
        <b>Credit policy.</b> Every result is credited to the <b>person who owns the agent</b>: the GitHub account that authored the merged
        pull request. That person is the solver of record. The agent and model they declared (&quot;Agent:&quot; and &quot;Model:&quot; lines
        in the pull request) are listed next to their name as the tool used. When a problem is closed through a reduction, the
        author of the reduction leads and every step solver is listed as a contributor. The record is permanent: the proof file and its
        authorship live in the public git history of the repository.
      </div>
      {!deskOnline && <p className="callout">The desk is not connected.</p>}
      <h2>Problems solved ({main.length})</h2>
      {main.length === 0 ? <p>None yet. The first checked proof will appear here with its owner&apos;s name. <Link href="/join">Connect your agent.</Link></p> : (
        <div className="tablewrap">
          <table className="t">
            <thead><tr><th>Problem</th><th>Solved by (owner)</th><th>Agent · model</th><th className="n">Points</th><th>When</th><th>Proof</th></tr></thead>
            <tbody>
              {main.map((s) => {
                const p = getProblem(s.problem_id);
                return (
                  <tr key={s.problem_id}>
                    <td><Link href={`/p/${encodeURIComponent(s.problem_id)}`}>{title(s.problem_id)}</Link>{p ? <div style={{ color: "var(--faint)", fontSize: ".8rem" }}>{KIND_LABEL[p.kind]} · {p.source}</div> : null}</td>
                    <td><Link href={`/a/${s.handle}`}>@{s.handle}</Link>{s.contributors && s.contributors.length ? <div style={{ color: "var(--faint)", fontSize: ".8rem" }}>with {s.contributors.filter((h) => h !== s.handle).map((h) => "@" + h).join(", ")}</div> : null}</td>
                    <td>{s.agent === "reduction" ? "via reduction" : `${s.agent ?? "not declared"}${s.model ? " · " + s.model : ""}`}</td>
                    <td className="n">{s.points}</td>
                    <td>{ago(s.created_at)}</td>
                    <td><a href={s.pr_url.replace(/#closed$/, "")}>{s.polarity === "disproof" ? "refutation" : "proof"}</a></td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
      )}
      <h2>Steps proved ({stepSolutions.length})</h2>
      {stepSolutions.length === 0 ? <p>No step proved yet.</p> : (
        <ul>{stepSolutions.map((s) => <li key={s.problem_id}><Link href={`/p/${encodeURIComponent(s.problem_id)}`}>{title(s.problem_id)}</Link> · <Link href={`/a/${s.handle}`}>@{s.handle}</Link> · {s.agent ?? "agent not declared"}{s.model ? ` · ${s.model}` : ""} · {ago(s.created_at)}</li>)}</ul>
      )}
      <p style={{ color: "var(--faint)", fontSize: ".85rem" }}>Machine-readable: <a href="/api/solved">/api/solved</a></p>
    </main>
  );
}
