import "server-only";
import katex from "katex";

const esc = (s: string) => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

function tex(src: string, display: boolean) {
  try {
    return katex.renderToString(src, { displayMode: display, throwOnError: false, strict: "ignore", trust: false, output: "html" });
  } catch {
    return `<code>${esc(src)}</code>`;
  }
}

/** Upstream docstrings: Markdown-lite with $…$ / $$…$$ math. Output is escaped except KaTeX HTML. */
export function renderStatement(src: string): string {
  const parts: string[] = [];
  // pull math and code out first so their contents are never touched by markdown rules
  const re = /\$\$([\s\S]+?)\$\$|\\\[([\s\S]+?)\\\]|\$([^$\n]+?)\$|`([^`\n]+)`/g;
  let last = 0;
  let m: RegExpExecArray | null;
  const slots: string[] = [];
  let text = "";
  while ((m = re.exec(src))) {
    text += src.slice(last, m.index);
    const html = m[1] ?? m[2] ? tex((m[1] ?? m[2])!, true) : m[3] !== undefined ? tex(m[3], false) : `<code>${esc(m[4]!)}</code>`;
    slots.push(html);
    text += `\u0000${slots.length - 1}\u0000`;
    last = m.index + m[0].length;
  }
  text += src.slice(last);
  let html = esc(text)
    .replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[\s(])\*([^*\n]+)\*(?=[\s).,;:]|$)/g, "$1<em>$2</em>")
    .replace(/\[([^\]]+)\]\((https?:\/\/[^)\s]+)\)/g, '<a href="$2" target="_blank" rel="noreferrer">$1</a>');
  html = html
    .split(/\n{2,}/)
    .map((para) => `<p>${para.replace(/\n/g, " ")}</p>`)
    .join("");
  html = html.replace(/\u0000(\d+)\u0000/g, (_, i) => slots[Number(i)]);
  parts.push(html);
  return parts.join("");
}

/** Plain text for meta descriptions. */
export function plain(src: string, max = 200) {
  const t = src.replace(/\$\$?([^$]+)\$\$?/g, "$1").replace(/[*`\\]/g, "").replace(/\s+/g, " ").trim();
  return t.length > max ? t.slice(0, max - 1) + "…" : t;
}
