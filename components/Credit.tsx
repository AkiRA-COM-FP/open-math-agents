import Link from "@/components/Link";
import { SITE } from "@/lib/site";

export type CreditData = {
  problem_id: string; handle: string; agent: string | null; model: string | null; polarity: string;
  pr_url: string; points: number; contributors: string[] | null; created_at: string;
};

export function citation(c: CreditData, title: string) {
  const tool = [c.agent && c.agent !== "reduction" ? c.agent : null, c.model].filter(Boolean).join(", ");
  const others = (c.contributors ?? []).filter((h) => h !== c.handle);
  return `@${c.handle}${tool ? ` (AI agent: ${tool})` : ""}${others.length ? `, with ${others.map((h) => "@" + h).join(", ")}` : ""}. ` +
    `${c.polarity === "disproof" ? "Refutation" : "Proof"} of "${title}", checked by the Lean 4 kernel. ` +
    `Open Math Agents, ${c.created_at.slice(0, 10)}. ${c.pr_url.replace(/#closed$/, "")} · ${SITE}/p/${encodeURIComponent(c.problem_id)}`;
}

export default function Credit({ c, title, first = false }: { c: CreditData; title: string; first?: boolean }) {
  const others = (c.contributors ?? []).filter((h) => h !== c.handle);
  return (
    <div className="panel" style={{ borderColor: "var(--ok)" }}>
      <h4 style={{ color: "var(--warmup)" }}>{first ? (c.polarity === "disproof" ? "Refuted for the first time" : "Solved for the first time") : (c.polarity === "disproof" ? "Refuted" : "Proved")} · credited to the owner of the agent</h4>
      {first && <p style={{ margin: "0 0 12px", fontWeight: 600 }}>An open problem nobody had solved before. On the record, @{c.handle} is the person who solved it.</p>}
      <div className="credit">
        {/* eslint-disable-next-line @next/next/no-img-element */}
        <img src={`https://github.com/${c.handle}.png?size=88`} alt="" width={44} height={44} />
        <div>
          <div style={{ fontWeight: 650, fontSize: "1.05rem" }}><Link href={`/a/${c.handle}`}>@{c.handle}</Link></div>
          <div style={{ color: "var(--muted)", fontSize: ".9rem" }}>
            {c.agent === "reduction" ? "closed through a reduction into steps" : <>agent <b>{c.agent ?? "not declared"}</b>{c.model ? <> · model <b>{c.model}</b></> : null}</>}
            {" "}· {c.points} points · {c.created_at.slice(0, 10)} · <a href={c.pr_url.replace(/#closed$/, "")}>pull request</a>
          </div>
          {others.length > 0 && (
            <div style={{ color: "var(--muted)", fontSize: ".9rem", marginTop: 4 }}>
              with {others.map((h, i) => <span key={h}>{i ? ", " : ""}<Link href={`/a/${h}`}>@{h}</Link></span>)}
            </div>
          )}
        </div>
      </div>
      <p style={{ color: "var(--faint)", fontSize: ".82rem", margin: "12px 0 6px" }}>Cite this result:</p>
      <div className="cite">{citation(c, title)}</div>
    </div>
  );
}
