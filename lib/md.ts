import "server-only";
import katex from "katex";

/** Markdown files under content/<section>/*.md with a small front matter (title, date, summary, author). */
export type Doc = { slug: string; title: string; date: string; summary: string; author: string; body: string };

// Bundled at build time: a Worker has no file system to read content/ from.
const FILES = import.meta.glob("/content/**/*.md", { query: "?raw", import: "default", eager: true }) as Record<string, string>;

export function listDocs(section: string): Doc[] {
  const prefix = `/content/${section}/`;
  return Object.keys(FILES)
    .filter((k) => k.startsWith(prefix) && !k.slice(prefix.length).includes("/") && !k.slice(prefix.length).startsWith("_"))
    .map((k) => readDoc(section, k.slice(prefix.length, -3))!).filter(Boolean)
    .sort((a, b) => b.date.localeCompare(a.date));
}

export function readDoc(section: string, slug: string): Doc | null {
  if (!/^[a-z0-9-]+$/.test(slug)) return null;
  const raw = FILES[`/content/${section}/${slug}.md`];
  if (raw === undefined) return null;
  const m = raw.match(/^---\n([\s\S]*?)\n---\n([\s\S]*)$/);
  const meta: Record<string, string> = {};
  if (m) for (const line of m[1].split("\n")) { const i = line.indexOf(":"); if (i > 0) meta[line.slice(0, i).trim()] = line.slice(i + 1).trim(); }
  return { slug, title: meta.title ?? slug, date: meta.date ?? "", summary: meta.summary ?? "", author: meta.author ?? "", body: m ? m[2] : raw };
}

const esc = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
const tex = (s: string, d: boolean) => { try { return katex.renderToString(s, { displayMode: d, throwOnError: false }); } catch { return esc(s); } };

function inline(s: string) {
  const slots: string[] = [];
  const keep = (h: string) => { slots.push(h); return `\u0000${slots.length - 1}\u0000`; };
  s = s.replace(/`([^`]+)`/g, (_, c) => keep(`<code>${esc(c)}</code>`)).replace(/\$([^$\n]+)\$/g, (_, t) => keep(tex(t, false)));
  s = esc(s)
    .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[\s(])\*([^*\n]+)\*/g, "$1<em>$2</em>")
    .replace(/\[([^\]]+)\]\(((?:https?:\/\/|\/)[^)\s]+)\)/g, '<a href="$2">$1</a>');
  return s.replace(/\u0000(\d+)\u0000/g, (_, i) => slots[Number(i)]);
}

/** Headings, paragraphs, lists, quotes, fenced code and $$ display math. Everything else is escaped. */
export function renderMarkdown(md: string) {
  const out: string[] = [];
  const blocks = md.replace(/\r/g, "").split(/\n{2,}/);
  for (const b of blocks) {
    const t = b.trim();
    if (!t) continue;
    if (t.startsWith("```")) { out.push(`<pre>${esc(t.replace(/^```\w*\n?/, "").replace(/```$/, ""))}</pre>`); continue; }
    if (t.startsWith("$$") && t.endsWith("$$")) { out.push(tex(t.slice(2, -2), true)); continue; }
    const h = t.match(/^(#{1,3})\s+(.*)$/);
    if (h) { const n = h[1].length + 1; out.push(`<h${n}>${inline(h[2])}</h${n}>`); continue; }
    if (/^[-*] /.test(t)) { out.push("<ul>" + t.split(/\n(?=[-*] )/).map((li) => `<li>${inline(li.replace(/^[-*] /, "").replace(/\n\s*/g, " "))}</li>`).join("") + "</ul>"); continue; }
    if (/^\d+\. /.test(t)) { out.push("<ol>" + t.split(/\n(?=\d+\. )/).map((li) => `<li>${inline(li.replace(/^\d+\. /, "").replace(/\n\s*/g, " "))}</li>`).join("") + "</ol>"); continue; }
    if (t.startsWith("> ")) { out.push(`<blockquote>${inline(t.replace(/^> ?/gm, "").replace(/\n/g, " "))}</blockquote>`); continue; }
    out.push(`<p>${inline(t.replace(/\n/g, " "))}</p>`);
  }
  return out.join("\n");
}
