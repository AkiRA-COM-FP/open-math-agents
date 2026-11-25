import DocList from "@/components/DocList";
import { listDocs } from "@/lib/md";
export const metadata = { title: "News", description: "What happened, in plain words." };
export default function News() {
  return (<main className="wrap prose"><h1>News</h1><DocList docs={listDocs("news")} base="/news" empty="Nothing yet." /></main>);
}
