# Sandbox only: registers a test catalogue entry for OeisA1818.a_2 (proved upstream by `decide`, so not in the
# real catalogue), places each case at the path a real submission would use, and runs tools/check.sh on it.
import json, os, shutil, subprocess, sys
cat = json.load(open("data/catalog.json"))
cat["problems"].append({"id": "OeisA1818.a_2", "decl": "OeisA1818.a_2", "title": "sandbox", "source": "OEIS", "kind": "warmup",
    "category": "test", "fields": [], "tags": [], "statement": "", "lean": "theorem a_2 : a 2 = 9", "module": "FormalConjectures.OEIS.«1818»",
    "file": "FormalConjectures/OEIS/1818.lean", "line": 49, "ref": None, "prize": None, "erdos": None, "erdosState": None, "forumPosts": 0, "difficulty": 1})
json.dump(cat, open("data/catalog.json", "w"))
cases = {"1_accept.lean": "proofs/OeisA1818.a_2.lean", "2_reject.lean": "proofs/OeisA1818.a_2.lean", "3_axiom.lean": "proofs/OeisA1818.a_2.lean",
         "4_statement.lean": "statements/wp-hadwiger-nelson-problem-on-the-chromatic-number-of-unit-distance-graphs.lean"}
out = []
for src, dst in cases.items():
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy(f"sandbox/cases/{src}", dst)
    subprocess.run(["tools/check.sh", dst, "/tmp/v.json"], env={**os.environ})
    v = json.load(open("/tmp/v.json"))
    out.append(f"| {src} | {v.get('verdict')} | {v.get('reason')} |")
    print(src, "->", v.get("verdict"), "-", v.get("reason")); print(v.get("log", "")[-1500:]); sys.stdout.flush()
    os.remove(dst)
open(os.environ.get("GITHUB_STEP_SUMMARY", "/dev/null"), "a").write("| case | verdict | reason |\n|---|---|---|\n" + "\n".join(out) + "\n")
