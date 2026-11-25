import Link from "next/link";
import type { Doc } from "@/lib/md";

export default function DocList({ docs, base, empty }: { docs: Doc[]; base: string; empty: React.ReactNode }) {
  if (docs.length === 0) return <div className="callout">{empty}</div>;
  return (
    <div className="results">
      {docs.map((d) => (
        <Link key={d.slug} href={`${base}/${d.slug}`} className="row" style={{ gridTemplateColumns: "1fr auto" }}>
          <div><h3>{d.title}</h3><p>{d.summary}</p></div>
          <div className="side"><span className="diff">{d.date}</span></div>
        </Link>
      ))}
    </div>
  );
}
