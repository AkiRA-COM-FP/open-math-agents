#!/usr/bin/env python3
"""Add open conjectures stated in arXiv math abstracts to data/extra2.json.

Input: JSON lines from the arXiv API (id, title, summary, published, authors, primary category), harvested with
queries such as abs:"we conjecture" or abs:"remains open" per math category. arXiv metadata, abstracts included,
is CC0. Kept: abstracts that POSE a conjecture or an open question ("we conjecture", "conjecture that ...",
"remains open", "open problem/question", "we pose"). Dropped: abstracts where the paper settles it ("we prove the
conjecture", "confirming", "disproving", "answering an open question", "counterexample to"), unless it also poses a
new one; history/general-math categories; papers already in the catalogue (formal-conjectures arXiv entries).
One entry per paper; the statement leads with the sentences that state the conjecture, then the abstract.

Usage: python3 -I scripts/ingest_arxiv_conjectures.py <raw.jsonl>
"""
import json, os, re, sys, collections

HERE = os.path.dirname(os.path.abspath(__file__))
EXTRA2 = os.path.join(HERE, "..", "data", "extra2.json")
CATALOG = os.path.join(HERE, "..", "data", "catalog.json")
SRC = "arXiv abstracts (not formalized)"
LICENSE = "Abstract from arXiv (metadata CC0); the conjecture is the authors', see the paper"

FIELD = {"NT": "Number Theory", "CO": "Combinatorics", "AG": "Algebraic Geometry", "GT": "General Topology", "GR": "Group Theory",
         "PR": "Probability", "AP": "PDEs", "CA": "Real Functions", "DS": "Dynamical Systems", "FA": "Functional Analysis",
         "OA": "Operator Theory", "RT": "Group Theory", "LO": "Logic & Foundations", "MG": "Convex & Discrete Geometry",
         "DG": "Manifolds", "AT": "General Topology", "CV": "Complex Analysis", "RA": "Associative Rings", "AC": "Commutative Algebra",
         "SP": "Operator Theory", "CT": "Category Theory", "KT": "K-Theory", "GN": "General Topology", "QA": "Quantum Theory",
         "SG": "Manifolds", "IT": "Information & Communication", "OC": "Approximation", "ST": "Probability", "NA": "Approximation",
         "MP": "Quantum Theory"}
SKIP_CATS = {"HO", "GM"}

# Only the reliable phrasings: the authors themselves say it is open, or conjecture it.
POSE = re.compile(r"(?i)\b(we (also |further |now )?conjecture|it is natural to conjecture|we (pose|formulate|propose|state) (a |an |the |several |two |some )?(conjecture|question|problem|open)|we ask whether|we raise (the |an |a )?(question|problem)|remains? (an )?open|remain open|(is|are) still open|left open|we leave [^.]{0,60} open|conjecture that)")
# A sentence that answers, proves or settles something is not an open statement (even "partially").
SETTLE = re.compile(r"(?i)\b(prove[sd]?|proof of|proving|confirm(s|ed|ing)?|establish(es|ed|ing)?|resolve[sd]?|resolving|settle[sd]?|settling|disprove[sd]?|disproving|refute[sd]?|refuting|answer(s|ed|ing)?|verify|verifies|verified|solve[sd]?|solving|solution (to|of)|counterexample)\b[^.]{0,90}\b(conjecture|question|problem)\b")
OTHERS = re.compile(r"(?i)\b(posed by|raised by|asked by|proposed by|due to|question of [A-Z]|problem of [A-Z]|conjecture of [A-Z])\b")
NEW = re.compile(r"(?i)\b(we (also |further |now )?conjecture|we pose|we formulate|remains? open|remain open|(is|are) still open|left open|we ask)\b")
SENT = re.compile(r"(?<=[.!?])\s+(?=[A-Z$\\(])")

def norm(s):
    return re.sub(r"[^a-z0-9]+", " ", s.lower()).strip()

raw = {}
for line in open(sys.argv[1], encoding="utf-8"):
    r = json.loads(line); raw[r["id"]] = r

cat = json.load(open(CATALOG, encoding="utf-8"))["problems"]
in_core = set()
for p in cat:
    for m in re.finditer(r"(\d{4}\.\d{4,5})", p["id"] + " " + (p.get("ref") or "")):
        in_core.add(m.group(1))
d = json.load(open(EXTRA2, encoding="utf-8"))
have = {r[0] for r in d["rows"]}
titles = {norm(r[1]) for r in d["rows"]} | {norm(p["title"]) for p in cat}
if SRC not in d["sources"]: d["sources"].append(SRC)
d["licenses"][SRC] = LICENSE
si = d["sources"].index(SRC)

drop = collections.Counter(); added = []
for aid, r in raw.items():
    pc = (r.get("primary") or "").split(".")
    sub = pc[1] if len(pc) > 1 and pc[0] == "math" else None
    if sub is None:  # cross-listed into math: use the first math category
        sub = next((c.split(".")[1] for c in r.get("cats", []) if c.startswith("math.") and "." in c), None)
    if sub is None or sub in SKIP_CATS: drop["category"] += 1; continue
    s = r["summary"]
    sents = [x.strip() for x in SENT.split(s) if x.strip()]
    posing = [x for x in sents if POSE.search(x) and not SETTLE.search(x) and not (OTHERS.search(x) and not NEW.search(x))
              and not re.search(r"(?i)\bopen (and|dense|set|subset|map|cover|ball|neighbou?rhood|disc|disk)\b|\bopen in\b", x)
              and not re.search(r"(?i)conjecture that[^.]{0,120}\b(was|has been|had been|is now) (proved|proven|disproved|shown|established)", x)]
    if not posing: drop["no_open_statement"] += 1; continue
    if SETTLE.search(s) and not any(NEW.search(x) for x in posing): drop["settled_in_paper"] += 1; continue
    base = aid.replace("/", "_")
    rid = f"arxiv-{base}"
    if rid in have or aid in in_core: drop["already_listed"] += 1; continue
    if norm(r["title"]) in titles: drop["same_title"] += 1; continue
    head = " ".join(posing[:2])
    statement = head if len(s) <= len(head) + 20 else (head + "\n\n" + s)
    if len(statement) > 1400: statement = statement[:1350].rsplit(" ", 1)[0] + " …"
    year = int(r["published"][:4]) if r.get("published") else 2000
    fame = 18 + max(0, min(14, year - 2012))  # newer = more likely still open
    added.append([rid, r["title"][:200], si, [FIELD.get(sub, "Number Theory")], statement, f"https://arxiv.org/abs/{aid}",
                  r.get("authors", [])[:6], fame, 70, [f"math.{sub}", r["published"][:4]], f"arXiv {aid} · {r['published'][:10]}", 0])
    have.add(rid); titles.add(norm(r["title"]))

d["rows"].extend(added)
d["meta"]["counts"][SRC] = sum(1 for x in d["rows"] if x[2] == si)
d["meta"]["total"] = len(d["rows"])
d["meta"]["arxiv"] = {"harvested": len(raw), "added": len(added), "dropped": dict(drop)}
json.dump(d, open(EXTRA2, "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
print(json.dumps({"harvested": len(raw), "added": len(added), "dropped": dict(drop), "total_rows": len(d["rows"])}))
