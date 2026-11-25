import DocPage from "@/components/DocPage";
import { listDocs, readDoc } from "@/lib/md";
type P = { params: Promise<{ slug: string }> };
export function generateStaticParams() { return listDocs("news").map((d) => ({ slug: d.slug })); }
export async function generateMetadata({ params }: P) { const d = readDoc("news", (await params).slug); return d ? { title: d.title, description: d.summary } : {}; }
export default async function Page({ params }: P) { return <DocPage section="news" slug={(await params).slug} back={["/news", "News"]} />; }
