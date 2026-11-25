#!/usr/bin/env bash
# Compile one submitted proof against the pinned formal-conjectures and audit its axioms.
# Usage: tools/check.sh proofs/<id>.lean [verdict.json]
# Needs OMA_FC = a formal-conjectures checkout at the commit in data/catalog.json, with the Mathlib cache.
set -uo pipefail
FILE="$1"; OUT="${2:-/dev/stdout}"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FC="${OMA_FC:-$ROOT/.oma/formal-conjectures}"
LINT="$(python3 -I "$ROOT/tools/lint.py" "$FILE" "$ROOT/data/catalog.json")"; LINT_OK=$?
emit() { python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); d.update(verdict=sys.argv[2], reason=sys.argv[3], log=sys.argv[4][-6000:]); print(json.dumps(d, ensure_ascii=False))' "$LINT" "$1" "$2" "${3:-}" > "$OUT"; }
if [ $LINT_OK -ne 0 ]; then emit rejected "lint: $(python3 -I -c 'import json,sys;print("; ".join(json.loads(sys.argv[1])["errors"]))' "$LINT")"; exit 1; fi
field() { python3 -I -c 'import json,sys;print(json.loads(sys.argv[1])[sys.argv[2]])' "$LINT" "$1"; }
MODULE="$(field module)"; THM="$(field theorem)"
WANT="$(python3 -I -c 'import json;print(json.load(open("'"$ROOT"'/data/catalog.json"))["meta"]["upstreamCommit"])')"
HAVE="$(git -C "$FC" rev-parse HEAD 2>/dev/null || echo none)"
[ "$HAVE" = "$WANT" ] || { emit fault "formal-conjectures checkout is at $HAVE, expected $WANT (run tools/oma.sh setup)"; exit 2; }
cd "$FC"
LOG="$(timeout 2400 lake build "$MODULE" 2>&1)" || { emit fault "could not build upstream module $MODULE" "$LOG"; exit 2; }
SUB="OMASubmission_$$.lean"
{ cat "$ROOT/$FILE" 2>/dev/null || cat "$FILE"; printf '\n#print axioms %s\n' "$THM"; } > "$SUB"
LOG="$(timeout 1800 lake env lean "$SUB" 2>&1)"; RC=$?
rm -f "$SUB"
[ $RC -eq 124 ] && { emit rejected "timeout: over 30 minutes" "$LOG"; exit 1; }
[ $RC -ne 0 ] && { emit rejected "does not compile" "$LOG"; exit 1; }
AX="$(python3 -I - "$LOG" "$THM" <<'PY'
import re, sys
log, thm = sys.argv[1], sys.argv[2]
if re.search(r"'%s' does not depend on any axioms" % re.escape(thm), log):
    print("OK"); sys.exit()
m = re.search(r"'%s' depends on axioms: \[(.*?)\]" % re.escape(thm), log, re.S)
if not m:
    print("NOAX"); sys.exit()
ax = {a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()}
bad = ax - {"propext", "Classical.choice", "Quot.sound"}
print("OK" if not bad else "BAD " + ", ".join(sorted(bad)))
PY
)"
if echo "$LOG" | grep -qE "(^|:)[0-9]+:[0-9]+: error"; then emit rejected "compiler reported errors" "$LOG"; exit 1; fi
case "$AX" in
  OK) emit accepted "kernel accepted; axioms within propext, Classical.choice, Quot.sound" "$LOG"; exit 0 ;;
  NOAX) emit rejected "no axiom report for $THM" "$LOG"; exit 1 ;;
  *) emit rejected "uses forbidden axioms: ${AX#BAD }" "$LOG"; exit 1 ;;
esac
