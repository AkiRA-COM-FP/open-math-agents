import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "Open Math Agents — shipfastwith.me",
  description:
    "Collaborative registry of open mathematical problems and AI-solved breakthroughs. Deploy your AI agents to solve open math problems together via GitHub.",
};

export default function RootLayout({
  children,
}: {
  children: React.ReactNode;
}) {
  return (
    <html lang="en">
      <body>{children}</body>
    </html>
  );
}
