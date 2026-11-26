// Requests the page and the agent brief of EVERY problem (or a random sample) and reports anything that is not a 200.
// Run: BASE=http://localhost:3123 node tests/sweep.mjs [sampleSize]
const BASE = process.env.BASE ?? "http://localhost:3123";
const SAMPLE = Number(process.argv[2] ?? 0);
const ids = [];
for (let offset = 0; ; offset += 200) {
  const r = await (await fetch(`${BASE}/api/problems?kind=all&sort=hardest&limit=200&offset=${offset}`)).json();
  ids.push(...r.items.map((x) => x.id));
  if (ids.length >= r.total || r.items.length === 0) break;
}
let list = ids;
if (SAMPLE) list = ids.sort(() => Math.random() - 0.5).slice(0, SAMPLE);
console.log(`checking ${list.length} of ${ids.length} problems (page + brief)`);
const bad = [];
let done = 0;
const worker = async () => {
  while (list.length) {
    const id = list.pop();
    for (const path of [`/p/${encodeURIComponent(id)}`, `/p/${encodeURIComponent(id)}/agent.txt`]) {
      try {
        const r = await fetch(BASE + path);
        const body = await r.text();
        if (r.status !== 200 || body.length < 200 || /Application error|Internal Server Error/.test(body)) bad.push(`${r.status} ${path}`);
      } catch (e) { bad.push(`ERR ${path} ${e.message}`); }
    }
    if (++done % 1000 === 0) console.log(`  ${done} done, ${bad.length} bad`);
  }
};
await Promise.all(Array.from({ length: 12 }, worker));
console.log(bad.length ? `FAILED ${bad.length}:\n` + bad.slice(0, 50).join("\n") : `ALL PASSED (${done} problems)`);
process.exit(bad.length ? 1 : 0);
