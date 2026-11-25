#!/usr/bin/env python3
"""Static gate for a submitted proof file, run BEFORE anything compiles (locally and in CI).

Usage: python3 -I tools/lint.py proofs/<id>.lean data/catalog.json
Prints JSON {ok, problem, decl, polarity, errors}. Exit code 0 only if ok.

Why so strict: Lean can run arbitrary code while it compiles (#eval, macros, elab, initialize,
run_tac ...). A submission must not be able to touch the CI runner or forge its own verdict, so
everything that could execute code at compile time is refused outright.
"""
import json
import os
import re
import sys

path, catalog_path = sys.argv[1], sys.argv[2]
errors = []

if not re.fullmatch(r"proofs/[A-Za-z0-9_.'\-]+\.lean", os.path.relpath(path).replace(os.sep, "/")):
    errors.append("file must be proofs/<problem id>.lean")

pid = os.path.basename(path)[:-5]
cat = json.load(open(catalog_path, encoding="utf-8"))
prob = next((p for p in cat["problems"] if p["id"] == pid), None)
if prob is None:
    print(json.dumps({"ok": False, "problem": pid, "errors": [f"unknown problem id {pid}"]}))
    sys.exit(1)

raw = open(path, "rb").read()
if len(raw) > 512 * 1024:
    errors.append("file larger than 512 KiB")
try:
    src = raw.decode("utf-8")
except UnicodeDecodeError:
    src = ""
    errors.append("file is not UTF-8")


def strip_comments(s):
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s.startswith("--", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
            continue
        if s.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and s.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(s[i])
        i += 1
    if depth:
        errors.append("unterminated block comment")
    return "".join(out)


code = strip_comments(src)

if '"' in code:
    errors.append("no double-quote characters (string literals) allowed")
if "\u0000" in code:
    errors.append("NUL byte")

BANNED = [
    r"\bsorry\b", r"\badmit\b", r"\baxiom\b", r"\baxioms\b", r"\bnative_decide\b", r"\bunsafe\b", r"\bpartial\b",
    r"\bopaque\b", r"\bimplemented_by\b", r"\bextern\b", r"\bmacro\w*", r"\bsyntax\w*", r"\belab\w*", r"\bnotation\w*",
    r"\binfix[lr]?\b", r"\bprefix\b", r"\bpostfix\b", r"\binitialize\b", r"\bbuiltin_initialize\b", r"\brun_cmd\b",
    r"\brun_tac\b", r"\brun_elab\b", r"\bby_elab\b", r"\battribute\b", r"\bdeclare_\w+", r"\bmeta\b", r"\bIO\b",
    r"\bLean\.(Elab|Meta|Compiler|Environment|IR|ofReduceBool|trustCompiler)", r"\bdecide\s*:=\s*true", r"\bimport\s+Lean\b",
    r"#(eval|print|check|reduce|exit|guard|help|lint|find|synth|where|show|time|output|widget|html|norm_num|simp|conv|"
    r"parse|test|explode|long_names|search|loogle|leansearch|moogle|import|min_imports|unused|sample|allow|define|stop|"
    r"count_heartbeats|adaptation_note|align|mathlib|tactic|kernel|compile|leanchecker|version|guard_msgs|trans|redundant)\w*",
]
for pat in BANNED:
    m = re.search(pat, code)
    if m:
        errors.append(f"forbidden: {m.group(0)!r}")

for m in re.finditer(r"@\[([^\]]*)\]", code):
    if m.group(1).strip() not in ("simp", "local simp"):
        errors.append(f"attribute @[{m.group(1)}] not allowed (only @[simp], @[local simp])")

for m in re.finditer(r"\bset_option\s+([\w.]+)\s+(\S+)(\s+in\b)?", code):
    name, val, has_in = m.group(1), m.group(2), m.group(3)
    if name not in ("maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats", "synthInstance.maxSize") or not val.isdigit() or not has_in:
        errors.append(f"set_option {name} {val} not allowed (only numeric maxHeartbeats/maxRecDepth/synthInstance.* with `in`)")

# imports: first the problem's module, then Mathlib only.
lines = [l for l in code.splitlines() if l.strip()]
imports = [l.strip() for l in lines if re.match(r"\s*import\b", l)]
if not imports or imports[0] != f"import {prob['module']}":
    errors.append(f"first line must be: import {prob['module']}")
for l in imports[1:]:
    if not re.fullmatch(r"import Mathlib(\.[A-Za-z0-9_]+)*", l):
        errors.append(f"only Mathlib imports may follow the problem import: {l!r}")
body_started = False
for l in lines:
    if re.match(r"\s*import\b", l):
        if body_started:
            errors.append("imports must come first")
            break
    else:
        body_started = True

decl = prob["decl"]
d = re.escape(decl)
proof = re.findall(r"\btheorem\s+OMA\.solution\s*:\s*type_of%\s*@" + d + r"\s*:=", code)
disproof = re.findall(r"\btheorem\s+OMA\.disproof\s*:\s*¬\s*\(\s*type_of%\s*@" + d + r"\s*\)\s*:=", code)
mentions = re.findall(r"\bOMA\.(solution|disproof)\b", code)
if len(proof) + len(disproof) != 1 or len(mentions) != 1:
    errors.append(
        f"must contain exactly one `theorem OMA.solution : type_of% @{decl} := ...` "
        f"or `theorem OMA.disproof : ¬ (type_of% @{decl}) := ...`, and no other mention of OMA.solution/OMA.disproof"
    )
if re.search(r"(?<![\w.])" + d + r"(?![\w.])", re.sub(r"type_of%\s*@" + d, "", code)):
    errors.append(f"the proof must not use the upstream declaration {decl} itself")

polarity = "disproof" if disproof else "proof"
ok = not errors
print(json.dumps({"ok": ok, "problem": pid, "decl": decl, "module": prob["module"], "kind": prob["kind"], "polarity": polarity,
                  "theorem": "OMA." + ("disproof" if disproof else "solution"), "errors": errors}, ensure_ascii=False))
sys.exit(0 if ok else 1)
