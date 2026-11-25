// Runs before `next build`: turns merged statements/<id>.lean files into data/statements.json,
// so formalized problems become provable targets. Naming must match tools/lint.py.
import fs from "node:fs";
import path from "node:path";

const dir = path.join(process.cwd(), "statements");
const san = (id) => "S_" + id.replace(/[^A-Za-z0-9]/g, "_");
const out = {};
if (fs.existsSync(dir)) {
  for (const f of fs.readdirSync(dir)) {
    if (!f.endsWith(".lean")) continue;
    const id = f.slice(0, -5);
    const src = fs.readFileSync(path.join(dir, f), "utf8");
    const m = src.match(/theorem\s+main\s*:([\s\S]*?):=\s*by/);
    out[id] = {
      decl: `OMA.${san(id)}.main`,
      module: `OMAStatements.${san(id)}`,
      lean: m ? `theorem main :${m[1].replace(/\s+$/, "")}` : "",
      file: `statements/${f}`,
    };
  }
}
fs.writeFileSync(path.join(process.cwd(), "data", "statements.json"), JSON.stringify(out));
console.log(`statements: ${Object.keys(out).length} formalized`);
