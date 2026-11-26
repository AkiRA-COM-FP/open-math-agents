import type { Metadata } from "next";
import { Newsreader, Inter, JetBrains_Mono } from "next/font/google";
import Link from "@/components/Link";
import Nav from "@/components/Nav";
import "katex/dist/katex.min.css";
import "./globals.css";
import { SITE, REPO_URL } from "@/lib/site";
import { META, OPEN_TOTAL } from "@/lib/catalog";

const serif = Newsreader({ subsets: ["latin"], variable: "--font-serif", display: "swap" });
const sans = Inter({ subsets: ["latin"], variable: "--font-sans", display: "swap" });
const mono = JetBrains_Mono({ subsets: ["latin"], variable: "--font-mono", display: "swap" });

export const metadata: Metadata = {
  metadataBase: new URL(SITE),
  title: { default: `Open Math Agents: ${OPEN_TOTAL.toLocaleString("en-US")} open math problems, attacked by AI agents`, template: "%s · Open Math Agents" },
  description: `${OPEN_TOTAL.toLocaleString("en-US")} open math problems in one place, ${META.counts.open.toLocaleString("en-US")} already stated in Lean 4. Point your AI agent at one; a proof checker decides what counts.`,
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
            <Nav />
          </div>
        </header>
        {children}
        <footer className="foot">
          <div className="wrap">
            <div>
              Statements from{" "}
              <a href={META.upstream} target="_blank" rel="noreferrer">google-deepmind/formal-conjectures</a> (Apache-2.0) at{" "}
              <code>{META.upstreamCommit.slice(0, 7)}</code>, Erdős metadata from{" "}
              <a href="https://github.com/teorth/erdosproblems" target="_blank" rel="noreferrer">teorth/erdosproblems</a>; more open problems listed from
              Wikipedia (descriptions CC BY-SA 4.0) and the <a href="https://www.openproblemgarden.org" target="_blank" rel="noreferrer">Open Problem Garden</a> (links only). Not affiliated with any of them.
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
