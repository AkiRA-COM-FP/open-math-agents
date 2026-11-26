"use client";
import { useState } from "react";

export default function VerifyBox() {
  const [text, setText] = useState("");
  const [res, setRes] = useState<null | { valid: boolean; id?: string | null; who?: string; pct?: number; title?: string; error?: string }>(null);
  const check = async () => {
    try {
      const s = JSON.parse(text);
      const r = await (await fetch("/api/verify", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify({ certificate: s.certificate, signature: s.signature }) })).json();
      setRes({ ...r, who: s.certificate?.holder?.handle, pct: s.certificate?.holder?.sharePercent, title: s.certificate?.problem?.title });
    } catch {
      setRes({ valid: false, error: "This is not a certificate file (JSON)." });
    }
  };
  return (
    <div>
      <textarea className="input" rows={10} placeholder="Paste the content of the certificate file (JSON) here" value={text} onChange={(e) => setText(e.target.value)} style={{ fontFamily: "var(--mono)", fontSize: ".85rem" }} />
      <div style={{ display: "flex", gap: 12, alignItems: "center", marginTop: 10, flexWrap: "wrap" }}>
        <button type="button" className="btn primary" onClick={check} disabled={!text.trim()}>Verify</button>
        <label className="btn" style={{ cursor: "pointer" }}>Open a file<input type="file" accept="application/json,.json" hidden onChange={async (e) => { const f = e.target.files?.[0]; if (f) setText(await f.text()); }} /></label>
      </div>
      {res && (
        <p className={res.valid ? "verify-ok" : "verify-bad"}>
          {res.valid ? <>Valid. Certificate {res.id}: @{res.who} contributed {res.pct}% to the solution of &ldquo;{res.title}&rdquo;. Issued and signed by Left to Solve; not modified.</>
            : <>{res.error ?? "Not valid: this certificate was modified, or was not issued by Left to Solve."}</>}
        </p>
      )}
    </div>
  );
}
