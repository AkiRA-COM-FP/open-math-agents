#!/usr/bin/env node
// Load data/gen/catalog.sql into the catalogue D1 database, in batches (D1 caps one statement at 100 KB and one
// request at a few MB).
//   local (vite dev / preview running): node scripts/seed_d1.mjs --local http://localhost:3124
//   remote (Cloudflare API, token injected by the environment): node scripts/seed_d1.mjs --remote <account_id> <database_id>
import fs from "node:fs";

const [mode, a, b] = process.argv.slice(2);
const sql = fs.readFileSync(new URL("../data/gen/catalog.sql", import.meta.url), "utf8");

// Split on ";" outside single-quoted strings ('' is an escaped quote and toggles twice).
const stmts = [];
let start = 0, inq = false;
for (let i = 0; i < sql.length; i++) {
  const c = sql[i];
  if (c === "'") inq = !inq;
  else if (c === ";" && !inq) { const s = sql.slice(start, i + 1).trim(); if (s) stmts.push(s); start = i + 1; }
}

let url, headers = { "Content-Type": "application/json" };
if (mode === "--local") {
  const base = (a ?? "http://localhost:3124").replace(/\/$/, "") + "/cdn-cgi/local/explorer/api";
  const dbs = await (await fetch(`${base}/d1/database`)).json();
  const list = dbs.result ?? dbs;
  const db = list.find((d) => /catalog/i.test(d.name ?? d.binding ?? "")) ?? list[0];
  if (!db) throw new Error("no local D1 database: start vite dev or preview first");
  url = `${base}/d1/database/${db.uuid ?? db.id ?? db.database_id}/raw`;
} else if (mode === "--remote") {
  url = `https://api.cloudflare.com/client/v4/accounts/${a}/d1/database/${b}/raw`;
  headers.Authorization = "Bearer proxy-injected"; // replaced by the environment's network proxy
} else {
  console.error("usage: seed_d1.mjs --local [base] | --remote <account_id> <database_id>");
  process.exit(2);
}

const MAX = 90_000; // bytes of SQL per request: the whole batch counts against the 100 KB limit
let batch = [], size = 0, done = 0;
async function flush() {
  if (!batch.length) return;
  for (let attempt = 1; ; attempt++) {
    const r = await fetch(url, { method: "POST", headers, body: JSON.stringify({ sql: batch.join("\n") }) });
    const j = await r.json().catch(() => ({}));
    if (r.ok && j.success !== false) break;
    if (attempt >= 4) throw new Error(`batch at ${done}: HTTP ${r.status} ${JSON.stringify(j.errors ?? j).slice(0, 400)}`);
    await new Promise((res) => setTimeout(res, 1000 * attempt));
  }
  done += batch.length; batch = []; size = 0;
  if (done % 5000 < batch.length || done === stmts.length) console.log(`${done}/${stmts.length} statements`);
}
for (const s of stmts) {
  const n = Buffer.byteLength(s); if (size + n > MAX) await flush();
  batch.push(s); size += n + 1;
}
await flush();
console.log(`\nloaded ${stmts.length} statements into ${mode === "--local" ? "local" : "remote"} D1`);
