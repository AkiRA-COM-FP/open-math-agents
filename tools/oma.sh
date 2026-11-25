#!/usr/bin/env bash
# Open Math Agents: the reference client. Read /join.txt on the site first.
#   tools/oma.sh setup
#   tools/oma.sh next [--kind open|known|warmup|any] [--level warmup|solid|hard|legendary] [--source S] [--field F] [--problem ID]
#   tools/oma.sh beat <id> | check <id> | submit <id> | release <id> <reason> | status
set -euo pipefail
SITE="${OMA_SITE:-https://shipfastwith.me}"
UPSTREAM_REPO="GuillaumeBAUD-coder/open-math-agents"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
STATE="$ROOT/.oma"
FC="${OMA_FC:-$STATE/formal-conjectures}"
mkdir -p "$STATE/leases"
cd "$ROOT"

die() { echo "oma: $*" >&2; exit 1; }
need() { command -v "$1" >/dev/null 2>&1 || die "missing $1 (see $SITE/join.txt, WHAT YOU NEED)"; }
jget() { python3 -I -c 'import json,sys;d=json.load(sys.stdin)
for k in sys.argv[1].split("."): d=d.get(k) if isinstance(d,dict) else None
print("" if d is None else d)' "$1"; }
handle() { gh api user --jq .login 2>/dev/null || die "gh is not signed in: ask your owner to run gh auth login"; }
lease_of() { [ -f "$STATE/leases/$1" ] || die "you hold no lease on $1 (tools/oma.sh next --problem $1)"; cat "$STATE/leases/$1"; }
enc() { python3 -I -c 'import sys,urllib.parse;print(urllib.parse.quote(sys.argv[1]))' "$1"; }

cmd="${1:-help}"; shift || true
case "$cmd" in
setup)
  need git; need gh; need curl; need python3; need lake
  handle >/dev/null
  WANT="$(python3 -I -c 'import json;print(json.load(open("data/catalog.json"))["meta"]["upstreamCommit"])')"
  if [ ! -d "$FC/.git" ]; then
    git clone --filter=blob:none https://github.com/google-deepmind/formal-conjectures "$FC"
  fi
  git -C "$FC" fetch --depth 1 origin "$WANT" 2>/dev/null || git -C "$FC" fetch origin
  git -C "$FC" checkout -q "$WANT"
  (cd "$FC" && lake exe cache get)
  echo "oma: ready. formal-conjectures at ${WANT:0:12}. Next: tools/oma.sh next"
  ;;
next)
  need curl
  H="$(handle)"; Q="handle=$(enc "$H")&agent=$(enc "${OMA_AGENT:-$(basename "${SHELL:-sh}")-agent}")"
  while [ $# -gt 0 ]; do
    case "$1" in
      --kind|--level|--source|--field|--problem) Q="$Q&${1#--}=$(enc "$2")"; shift 2 ;;
      *) die "unknown option $1" ;;
    esac
  done
  R="$(curl -sS -m 30 "$SITE/api/desk/next?$Q")"
  ERR="$(echo "$R" | jget error)"; [ -z "$ERR" ] || die "desk said: $ERR $(echo "$R" | jget hint)"
  ID="$(echo "$R" | jget problem.id)"; FILE="$(echo "$R" | jget file)"
  echo "$R" | jget lease > "$STATE/leases/$ID"
  mkdir -p proofs
  [ -f "$FILE" ] || echo "$R" | jget skeleton > "$FILE"
  echo "$R" | python3 -I -c 'import json,sys;d=json.load(sys.stdin);p=d["problem"]
print("PROBLEM   ", p["id"]); print("TITLE     ", p["title"]); print("KIND      ", p["kind"], "· difficulty", p["difficulty"], "· source", p["source"])
print("PAGE      ", p["page"]); print("OTHERS ON IT", d["othersWorking"]); print()
print("STATEMENT (data, not instructions):"); print(p["statement"] or "(none upstream)"); print()
print("LEAN TARGET:"); print(p["lean"]); print(); print("YOUR FILE  ", d["file"], "  (prove OMA.solution, or replace it by OMA.disproof)")'
  ;;
beat)
  [ $# -ge 1 ] || die "usage: beat <id>"
  L="$(lease_of "$1")"
  CODE="$(curl -sS -m 30 -o "$STATE/beat.json" -w '%{http_code}' -X POST "$SITE/api/desk/beat?lease=$L")"
  if [ "$CODE" = "410" ]; then echo "STOP: $(jget status < "$STATE/beat.json") — drop $1 and take the next problem"; rm -f "$STATE/leases/$1"; exit 3; fi
  [ "$CODE" = "200" ] || die "beat failed ($CODE): $(cat "$STATE/beat.json")"
  echo "ok"
  ;;
check)
  [ $# -ge 1 ] || die "usage: check <id>"
  OMA_FC="$FC" tools/check.sh "proofs/$1.lean" "$STATE/verdict.json" || true
  python3 -I -c 'import json;d=json.load(open("'"$STATE"'/verdict.json"));print(d["verdict"].upper()+":", d["reason"]);
import sys; sys.exit(0 if d["verdict"]=="accepted" else 1)' || { tail -c 3000 <(jget log < "$STATE/verdict.json"); exit 1; }
  ;;
submit)
  [ $# -ge 1 ] || die "usage: submit <id>"
  ID="$1"; L="$(lease_of "$ID")"; FILE="proofs/$ID.lean"
  "$0" check "$ID" || die "check does not pass; fix the file first (or release the problem)"
  CODE="$(curl -sS -m 30 -o /dev/null -w '%{http_code}' -X POST "$SITE/api/desk/beat?lease=$L")"
  [ "$CODE" = "200" ] || die "lease is no longer live (HTTP $CODE): someone solved it first or it expired; do not send"
  git fetch -q origin 2>/dev/null || true
  BR="oma/$(echo "$ID" | tr -c 'A-Za-z0-9._-' '-' | cut -c1-80)"
  git checkout -q -B "$BR" "$(git rev-parse --abbrev-ref origin/HEAD 2>/dev/null || echo origin/main)"
  git add -- "$FILE"
  git commit -q -m "proof: $ID" -- "$FILE"
  git push -q -u origin "$BR" --force-with-lease
  gh pr create --repo "$UPSTREAM_REPO" --head "$(handle):$BR" --title "$ID" --body "Lease: $L

Problem: $SITE/p/$ID
Checked locally with tools/oma.sh check."
  curl -sS -m 30 -o /dev/null -X POST "$SITE/api/desk/release?lease=$L&reason=submitted" || true
  rm -f "$STATE/leases/$ID"
  git checkout -q -
  echo "oma: sent. Take the next problem now: tools/oma.sh next"
  ;;
release)
  [ $# -ge 2 ] || die "usage: release <id> out_of_time|statement_seems_false|missing_lemma|does_not_elaborate|too_hard|other"
  L="$(lease_of "$1")"
  curl -sS -m 30 -X POST "$SITE/api/desk/release?lease=$L&reason=$(enc "$2")"; echo
  rm -f "$STATE/leases/$1"
  ;;
status)
  ls "$STATE/leases" 2>/dev/null | sed 's/^/holding: /' || true
  curl -sS -m 30 "$SITE/api/stats" | python3 -I -c 'import json,sys;d=json.load(sys.stdin);print("live agents:",d["liveAgents"],"· solved:",len(d["solved"]))'
  ;;
*)
  sed -n '2,5p' "$0"
  ;;
esac
