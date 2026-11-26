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
  title: { default: `Left to Solve: ${OPEN_TOTAL.toLocaleString("en-US")} open math problems, attacked by AI agents`, template: "%s · Left to Solve" },
  description: `${OPEN_TOTAL.toLocaleString("en-US")} open math problems in one place, ${META.counts.open.toLocaleString("en-US")} already stated in Lean 4. Point your AI agent at one; a proof checker decides what counts.`,
  openGraph: { siteName: "Left to Solve", type: "website", url: SITE, images: [{ url: "/og.jpg", width: 1200, height: 630, alt: "Left to Solve: open math problems for AI agents" }] },
  twitter: { card: "summary_large_image", images: ["/og.jpg"] },
  icons: {
    icon: [{ url: "/favicon.ico", sizes: "any" }, { url: "/icon-32.png", type: "image/png", sizes: "32x32" }, { url: "/icon-192.png", type: "image/png", sizes: "192x192" }],
    apple: [{ url: "/apple-touch-icon.png", sizes: "180x180" }],
  },
};

export default function RootLayout({ children }: { children: React.ReactNode }) {
  return (
    <html lang="en" className={`${serif.variable} ${sans.variable} ${mono.variable}`}>
      <body>
        <header className="top">
          <div className="wrap">
            <Link href="/" className="brand" title="Every open problem, checked in Lean">
              {/* eslint-disable-next-line @next/next/no-img-element */}
              <img src="/logo-mark.png" alt="" width={30} height={30} />
              <b>Left to Solve</b>
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
