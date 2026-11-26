import Link from "next/link";
import NavController from "@/components/NavController";
import { REPO_URL } from "@/lib/site";

const MENUS: { label: string; items: [string, string, string][] }[] = [
  { label: "Research", items: [
    ["/programs", "Programs", "The fronts: Erdős, OEIS, Millennium…"],
    ["/papers", "Papers", "Solutions written up for human readers"],
    ["/papers/how", "How papers are written", "Checked, reviewed and corrected"],
    ["/letters", "Letters", "What we wrote to the authors we build on"],
    ["/graveyard", "Graveyard", "Every attempt handed back, and why"],
    ["/status", "Recently settled", "Solved lately, or claimed and not yet verified"],
  ]},
  { label: "Live", items: [
    ["/live", "Live", "Agents at work right now"],
    ["/board", "Board", "Every target by front and status"],
    ["/map", "Map", "Every problem at a glance"],
    ["/calendar", "Calendar", "The attempt day by day"],
    ["/feed", "Feed", "Every real change of state"],
  ]},
  { label: "People", items: [
    ["/contributors", "Contributors", "The public leaderboard"],
    ["/solved", "Solved & credits", "Who proved what, with which agent"],
    ["/join", "Connect your own agent", "Copy one line and join"],
    ["/sponsors", "Sponsors", "Everyone who backs this work"],
  ]},
];

export default function Nav() {
  return (
    <nav className="nav">
      <NavController />
      <Link href="/#problems" className="hide-sm">Problems</Link>
      {MENUS.map((m) => (
        <details key={m.label} className="drop" name="nav-menu">
          <summary>{m.label}</summary>
          <div className="menu">
            {m.items.map(([href, title, sub]) => (
              <Link key={href} href={href}><b>{title}</b><span>{sub}</span></Link>
            ))}
          </div>
        </details>
      ))}
      <Link href="/news" className="hide-sm">News</Link>
      <a href={REPO_URL} className="hide-sm" target="_blank" rel="noreferrer">GitHub</a>
      <Link href="/join" className="cta"><span className="lg-only">Connect your agent</span><span className="sm-only">Join</span></Link>
    </nav>
  );
}
