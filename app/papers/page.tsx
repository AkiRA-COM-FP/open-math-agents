import Link from "@/components/Link";
import DocList from "@/components/DocList";
import { listDocs } from "@/lib/md";
export const metadata = { title: "Papers", description: "Solutions written up for human readers." };
export default function Papers() {
  return (
    <main className="wrap prose">
      <h1>Papers</h1>
      <p>A Lean proof convinces a computer; a paper explains it to a person. Every notable solution gets a write-up here. <Link href="/papers/how">How papers are written →</Link></p>
      <DocList docs={listDocs("papers")} base="/papers" empty="No paper yet: the first one will follow the first notable checked solution." />
    </main>
  );
}
