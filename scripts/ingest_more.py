#!/usr/bin/env python3
"""Build data/extra2.json: the long tail of open problems, ranked by how well known they are.

  - OEIS: every sequence whose comments or formulas state a conjecture that is not marked proved, disproved or
    refuted (text CC BY-SA 4.0, OEIS Foundation; the conjecture's author is kept). One entry per sequence.
  - MathOverflow (tag open-problems) and Mathematics Stack Exchange (tag open-problem): questions without an
    accepted answer (titles and links only; content CC BY-SA, on the linked page).
Everything already in data/catalog.json or data/extra.json is skipped.

Usage: python3 -I scripts/ingest_more.py <oeisdata checkout> <stackexchange.json> [out]
"""
import json
import os
import re
import sys
import unicodedata

OEIS, SE = sys.argv[1], sys.argv[2]
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[3] if len(sys.argv) > 3 else os.path.join(HERE, "..", "data", "extra2.json")
CATALOG = json.load(open(os.path.join(HERE, "..", "data", "catalog.json"), encoding="utf-8"))["problems"]
EXTRA = json.load(open(os.path.join(HERE, "..", "data", "extra.json"), encoding="utf-8"))["problems"]


def norm(s):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode().lower()
    return re.sub(r"[^a-z0-9]+", "", s)


formal_oeis = set()
for p in CATALOG:
    m = re.match(r"Oeis(A\d{6})", p["decl"])
    if m:
        formal_oeis.add(m.group(1))
    for r in re.findall(r"oeis\.org/(A\d{6})", (p.get("ref") or "") + " " + p.get("statement", "")):
        formal_oeis.add(r)
known_titles = {norm(p["title"]) for p in CATALOG} | {norm(p["title"]) for p in EXTRA}

CONJ = re.compile(r"\b(conjecture[sd]?|conjecturally)\b", re.I)
SETTLED = re.compile(r"\b(proved|proven|proof|confirmed|verified for all|disproved|disproven|refuted|counterexample|false|is a theorem|now a theorem|settled|resolved)\b", re.I)
SIGN = re.compile(r"\s*-\s*_([^_]+)_,?\s*([A-Z][a-z]{2} \d{1,2} \d{4})?\.?\s*$")


def clean(t):
    t = re.sub(r"_([^_]+)_", r"\1", t)          # OEIS author markup
    t = re.sub(r"\s+", " ", t).strip()
    return t


FIELD_WORDS = (
    (("prime", "divisor", "sigma", "phi(", "totient", "squarefree", "digit", "base ", "congruen", "modulo", "mod ", "fibonacci", "integer"), "Number Theory"),
    (("graph", "tree", "partition", "permutation", "binomial", "catalan", "lattice path", "tiling", "word", "composition"), "Combinatorics"),
    (("polynomial", "group", "ring", "matrix", "field"), "General Algebra"),
    (("triangle", "polygon", "polyomino", "polyhedr", "circle", "sphere", "packing", "plane"), "Geometry"),
)


def fields_for(text):
    t = text.lower()
    for words, f in FIELD_WORDS:
        if any(w in t for w in words):
            return [f]
    return ["Number Theory"]


entries = []
seen_norm = set()

# ---- OEIS ----------------------------------------------------------------------------------------
scanned = kept = 0
for dp, _, fs in os.walk(os.path.join(OEIS, "seq")):
    for f in fs:
        if not f.endswith(".seq"):
            continue
        scanned += 1
        try:
            raw = open(os.path.join(dp, f), encoding="utf-8", errors="replace").read()
        except OSError:
            continue
        if "onjectur" not in raw:
            continue
        anum = f[:-4]
        lines = raw.splitlines()
        name = next((l[11:].strip() for l in lines if l.startswith("%N ")), "")
        kw = next((l[11:].strip() for l in lines if l.startswith("%K ")), "")
        keywords = set(kw.split(","))
        if anum in formal_oeis or "dead" in keywords or "dumb" in keywords or "obsc" in keywords:
            continue
        body = [l[11:] for l in lines if l[:2] in ("%C", "%F", "%e")]
        # join "(Start) … (End)" blocks into one paragraph
        joined, buf = [], None
        for l in body:
            if buf is not None:
                buf.append(l.strip())
                if "(End)" in l:
                    joined.append(" ".join(buf)); buf = None
                continue
            if l.rstrip().endswith("(Start)"):
                buf = [l.strip()]
                continue
            joined.append(l)
        if buf:
            joined.append(" ".join(buf))
        body = joined
        settled_global = any(CONJ.search(l) and SETTLED.search(l) for l in body)
        if settled_global:
            continue  # the sequence says a conjecture of it was settled: too risky to call any of it open
        conj = []
        for l in body:
            if CONJ.search(l) and not SETTLED.search(l) and not re.search(r"\b(see|cf\.|conjectured by .* \d{4} paper)\b", l[:30], re.I):
                text = l.strip()
                m = SIGN.search(text)
                author = m.group(1) if m else None
                text = SIGN.sub("", text).replace("(Start)", "").replace("(End)", "")
                if len(text) >= 25:
                    conj.append((clean(text), author))
        if not conj:
            continue
        kept += 1
        authors = sorted({a for _, a in conj if a})
        refs = sum(1 for l in lines if l.startswith("%D ") or l.startswith("%H "))
        num = int(anum[1:])
        # how well known: OEIS editors' keywords, size of the entry, age (low A-numbers are older)
        fitted = all(re.search(r"(?i)(g\.f\.|e\.g\.f\.|recurrence|a\(n\)\s*=.*a\(n-\d+\)|empirical)", t) for t, _ in conj)
        fame = 20 + (25 if "core" in keywords else 0) + (12 if "nice" in keywords else 0) + min(10, refs // 5) + (8 if num < 50000 else 4 if num < 150000 else 0) - (12 if fitted else 0)
        statement = " · ".join(t for t, _ in conj[:3])[:900]
        e = {
            "id": f"oeis-{anum.lower()}", "decl": "", "title": f"{anum}: {clean(name)[:130]}", "source": "OEIS conjectures (not formalized)",
            "kind": "unformalized", "category": "unformalized", "fields": fields_for(name + " " + statement), "tags": sorted(k for k in keywords if k in ("core", "nice", "hard", "more", "easy")),
            "statement": statement, "lean": "", "module": "", "file": "", "line": 0, "ref": f"https://oeis.org/{anum}", "prize": None, "erdos": None,
            "erdosState": None, "forumPosts": 0, "authors": authors[:5], "license": "Text: OEIS Foundation, CC BY-SA 4.0",
            "area": "OEIS " + ", ".join(sorted(keywords & {"core", "nice", "hard"})), "fame": fame,
        }
        e["difficulty"] = 45 + (10 if "hard" in keywords else 0) - (8 if "easy" in keywords else 0)
        entries.append(e)
        seen_norm.add(norm(e["title"]))
print(f"OEIS: scanned {scanned}, kept {kept}", file=sys.stderr)

# ---- MathOverflow / Math.SE ----------------------------------------------------------------------
se = json.load(open(SE, encoding="utf-8"))
se_kept = 0
for q in se:
    title = re.sub(r"\s+", " ", __import__("html").unescape(q["title"])).strip()
    if q.get("accepted") or "big-list" in q["tags"] or "reference-request" in q["tags"] or "soft-question" in q["tags"] or re.search(
            r"(?i)\b(list of|examples of|book|reference|soft question|why is|why do|what are some|how to|definition|attempted proof|history|who first|what is the status|status of|literature|survey|motivation|intuition)\b", title):
        continue
    if norm(title) in known_titles or norm(title) in seen_norm:
        continue
    site = "MathOverflow" if q["site"] == "mathoverflow" else "Mathematics Stack Exchange"
    fame = 25 + min(35, q["score"] // 4) + (8 if site == "MathOverflow" else 0)
    tags = [t for t in q["tags"] if t not in ("open-problems", "open-problem")]
    e = {
        "id": f"{'mo' if site == 'MathOverflow' else 'mse'}-{q['id']}", "decl": "", "title": title[:160], "source": f"{site} (not formalized)",
        "kind": "unformalized", "category": "unformalized", "fields": fields_for(" ".join(tags) + " " + title), "tags": tags[:6],
        "statement": "", "lean": "", "module": "", "file": "", "line": 0, "ref": q["link"], "prize": None, "erdos": None, "erdosState": None,
        "forumPosts": q.get("answers", 0), "authors": [q["author"]] if q.get("author") else [], "license": f"Question on {site} (CC BY-SA); text on the linked page",
        "area": ", ".join(tags[:4]), "fame": fame, "difficulty": 55 + min(15, q["score"] // 20),
    }
    entries.append(e)
    se_kept += 1
print(f"Stack Exchange: kept {se_kept} of {len(se)}", file=sys.stderr)

entries.sort(key=lambda e: (-e["fame"], e["id"]))
counts = {}
for e in entries:
    counts[e["source"]] = counts.get(e["source"], 0) + 1
meta = {"counts": counts, "total": len(entries), "oeisCommit": os.popen(f"git -C {OEIS} rev-parse HEAD").read().strip(),
        "note": "Long tail: conjectures stated in the OEIS and open questions from MathOverflow and Math.SE, ranked by how well known they are."}
# Compact rows (the site inflates them): id, title, source index, fields, statement, ref, authors, fame, difficulty, tags, area
sources = sorted(counts)
rows = [[e["id"], e["title"], sources.index(e["source"]), e["fields"], e["statement"], e["ref"], e.get("authors", []), e["fame"],
         e["difficulty"], e.get("tags", []), e.get("area", ""), e.get("forumPosts", 0)] for e in entries]
licenses = {s: next(e["license"] for e in entries if e["source"] == s) for s in sources}
json.dump({"meta": meta, "sources": sources, "licenses": licenses, "rows": rows}, open(OUT, "w", encoding="utf-8"), ensure_ascii=False, separators=(",", ":"))
print(json.dumps(meta, indent=1))
