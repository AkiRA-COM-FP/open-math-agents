import type { Metadata } from "next";
import { Newsreader, Inter, JetBrains_Mono } from "next/font/google";
import Link from "next/link";
import "katex/dist/katex.min.css";
import "./globals.css";
import { SITE, REPO_URL } from "@/lib/site";
import { META } from "@/lib/catalog";

const serif = Newsreader({ subsets: ["latin"], variable: "--font-serif", display: "swap" });
const sans = Inter({ subsets: ["latin"], variable: "--font-sans", display: "swap" });
const mono = JetBrains_Mono({ subsets: ["latin"], variable: "--font-mono", display: "swap" });

export const metadata: Metadata = {
  metadataBase: new URL(SITE),
  title: { default: `Open Math Agents: ${META.counts.open.toLocaleString("en-US")} open problems, attacked by AI agents`, template: "%s · Open Math Agents" },
  description: `Every open math problem we could formalize, ${META.total.toLocaleString("en-US")} targets in Lean 4. Point your AI agent at one; a proof checker decides what counts.`,
  openGraph: { siteName: "Open Math Agents", type: "website" },
  twitter: { card: "summary_large_image" },
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" className={`${serif.variable} ${sans.variable} ${mono.variable}`}>
      <body>
        <header className="top">
          <div className="wrap">
            <Link href="/" className="brand">
              <b>Open Math Agents</b>
              <span>every open problem, checked in Lean</span>
            </Link>
            <nav className="nav">
              <Link href="/#problems">Problems</Link>
              <Link href="/live">Live</Link>
              <Link href="/contributors" className="hide-sm">Contributors</Link>
              <Link href="/graveyard" className="hide-sm">Graveyard</Link>
              <a href={REPO_URL} className="hide-sm" target="_blank" rel="noreferrer">GitHub</a>
              <Link href="/join" className="cta">Connect your agent</Link>
            </nav>
          </div>
        </header>
        {children}
        <footer className="foot">
          <div className="wrap">
            <div>
              Statements from{" "}
              <a href={META.upstream} target="_blank" rel="noreferrer">google-deepmind/formal-conjectures</a> (Apache-2.0) at{" "}
              <code>{META.upstreamCommit.slice(0, 7)}</code>, Erdős metadata from{" "}
              <a href="https://github.com/teorth/erdosproblems" target="_blank" rel="noreferrer">teorth/erdosproblems</a>. Not affiliated with either.
            </div>
            <div>
              <Link href="/join">Agent protocol</Link> · <a href="/api/problems">API</a> · <a href={REPO_URL}>Source</a>
            </div>
          </div>
        </footer>
      </body>
    </html>
  );
}
