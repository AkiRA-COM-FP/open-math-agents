import DocList from "@/components/DocList";
import { listDocs } from "@/lib/md";
export const metadata = { title: "Letters", description: "What we wrote to the authors we build on." };
export default function Letters() {
  return (
    <main className="wrap prose">
      <h1>Letters</h1>
      <p>This work stands on other people&apos;s: the formal statements, the problem collections, the papers whose results agents formalize. When we build on someone&apos;s work, we write to them, and publish the letter here once it is sent.</p>
      <DocList docs={listDocs("letters")} base="/letters" empty="No letter sent yet." />
    </main>
  );
}
