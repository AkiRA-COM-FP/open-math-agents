import Link from "next/link";

export type RowData = {
  id: string; title: string; source: string; kind: "open" | "known" | "warmup" | "unformalized"; fields: string[];
  difficulty: number; prize: string | null; excerpt: string; liveAgents?: number; solved?: boolean;
};

const KIND = { open: "Open", known: "Needs formal proof", warmup: "Warm-up", unformalized: "Open · not yet in Lean" } as const;

export function Difficulty({ value }: { value: number }) {
  return (
    <span className="diff" title="Heuristic difficulty, 1–100. See the join page for how it is computed.">
      <i><b style={{ width: `${value}%` }} /></i>
      {value}
    </span>
  );
}

export default function ProblemRow({ p }: { p: RowData }) {
  return (
    <Link className="row" href={`/p/${encodeURIComponent(p.id)}`}>
      <div>
        <h3>{p.title}</h3>
        <p>{p.excerpt}</p>
        <div className="meta">
          <span className={`badge ${p.kind}`}>{KIND[p.kind]}</span>
          <span className="badge">{p.source}</span>
          {p.fields.slice(0, 2).map((f) => <span key={f} className="badge">{f}</span>)}
          {p.prize && <span className="badge prize">{p.prize}</span>}
        </div>
      </div>
      <div className="side">
        {p.solved ? <span className="badge solved">Solved</span> : null}
        {p.liveAgents ? <span className="badge live"><span className="dot" /> {p.liveAgents} live</span> : null}
        <Difficulty value={p.difficulty} />
      </div>
    </Link>
  );
}
