#!/usr/bin/env python3
"""Snapshot every upstream Lean file (formal-conjectures, pinned commit) into data/fc_files.json.gz, so each
problem's agent brief can include the definitions, variants and already-proved lemmas of its file.
Usage: python3 -I scripts/pack_sources.py <formal-conjectures checkout>"""
import gzip, json, os, re, sys
FC = sys.argv[1]
out = {}
for dp, _, fs in os.walk(os.path.join(FC, "FormalConjectures")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            t = open(p, encoding="utf-8").read()
            t = re.sub(r"\A/-\nCopyright.*?-/\n", "", t, flags=re.S)  # drop the Apache header (kept in LICENSE)
            out[os.path.relpath(p, FC)] = t
dst = os.path.join(os.path.dirname(__file__), "..", "data", "fc_files.json.gz")
with gzip.open(dst, "wt", encoding="utf-8", compresslevel=9) as g:
    json.dump(out, g, ensure_ascii=False, separators=(",", ":"))
print(len(out), "files ->", os.path.getsize(dst), "bytes")
