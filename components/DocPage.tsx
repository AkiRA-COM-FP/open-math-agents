import Link from "next/link";
import { notFound } from "next/navigation";
import { readDoc, renderMarkdown } from "@/lib/md";

export default function DocPage({ section, slug, back }: { section: string; slug: string; back: [string, string] }) {
  const d = readDoc(section, slug);
  if (!d) notFound();
  return (
    <main className="wrap prose">
      <div className="crumbs"><Link href={back[0]}>{back[1]}</Link></div>
      <h1>{d.title}</h1>
      <p style={{ color: "var(--faint)" }}>{d.date}{d.author ? ` · ${d.author}` : ""}</p>
      <div dangerouslySetInnerHTML={{ __html: renderMarkdown(d.body) }} />
    </main>
  );
}
