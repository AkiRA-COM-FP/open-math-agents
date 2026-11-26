# Sandbox only: registers a test catalogue entry for OeisA1818.a_2 (proved upstream by `decide`, so not in the
# real catalogue), places each case at the path a real submission would use, and runs tools/check.sh on it.
import json, os, shutil, subprocess, sys
cat = json.load(open("data/catalog.json"))
cat["problems"].append({"id": "OeisA1818.a_2", "decl": "OeisA1818.a_2", "title": "sandbox", "source": "OEIS", "kind": "warmup",
    "category": "test", "fields": [], "tags": [], "statement": "", "lean": "theorem a_2 : a 2 = 9", "module": "FormalConjectures.OEIS.«1818»",
    "file": "FormalConjectures/OEIS/1818.lean", "line": 49, "ref": None, "prize": None, "erdos": None, "erdosState": None, "forumPosts": 0, "difficulty": 1})
json.dump(cat, open("data/catalog.json", "w"))
cases_old = {"1_accept.lean": "proofs/OeisA1818.a_2.lean", "2_reject.lean": "proofs/OeisA1818.a_2.lean", "3_axiom.lean": "proofs/OeisA1818.a_2.lean",
         "4_statement.lean": "statements/wp-can-every-integer-be-written-as-a-sum-of-four-perfect-cubes.lean"}
ID = "wp-can-every-integer-be-written-as-a-sum-of-four-perfect-cubes"
# (case, destination, keep the file afterwards so later cases can build on it)
cases = [("1_accept.lean", "proofs/OeisA1818.a_2.lean", False), ("2_reject.lean", "proofs/OeisA1818.a_2.lean", False),
         ("3_axiom.lean", "proofs/OeisA1818.a_2.lean", False), ("4_statement.lean", f"statements/{ID}.lean", False),
         ("5_reduction.lean", "reductions/OeisA1818.a_2.R1.lean", True), ("6_step.lean", "proofs/OeisA1818.a_2.R1.H2.lean", False),
         ("7_trivial_statement.lean", f"statements/{ID}.lean", True), ("8_formalized_proof.lean", f"proofs/{ID}.lean", False)]
out = []
for src, dst, keep in cases:
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copy(f"sandbox/cases/{src}", dst)
    subprocess.run(["tools/check.sh", dst, "/tmp/v.json"], env={**os.environ})
    v = json.load(open("/tmp/v.json"))
    out.append(f"| {src} | {v.get('verdict')} | {v.get('reason')} |")
    reason = (v.get("reason") or "").replace("\n", " ")[:300]
    tail = (v.get("log") or "").replace("\n", " | ")[-600:]
    print(f"::notice title={src}::{v.get('verdict')} - {reason}")
    if v.get("verdict") != "accepted":
        print(f"::notice title={src} log::{tail}")
    print(v.get("log", "")[-1500:]); sys.stdout.flush()
    if not keep:
        os.remove(dst)
open(os.environ.get("GITHUB_STEP_SUMMARY", "/dev/null"), "a").write("| case | verdict | reason |\n|---|---|---|\n" + "\n".join(out) + "\n")
