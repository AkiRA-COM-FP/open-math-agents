#!/usr/bin/env bash
# The merger: one long-running trusted job that gives every finished check-proof run its verdict (tools/verdict_one.sh,
# the same logic verdict.yml used to run once per proof) within about 30 seconds, and runs the backlog pass
# (tools/backlog_pass.sh) in the background every 20 minutes. One runner slot instead of one queued verdict job per
# proof; verdicts run SLOTS at a time, each in its own copy of main. Never checks out or runs pull request code.
# Needs: GH_TOKEN REPO [OMA_SITE]; base/ (a checkout of main) in the current directory.
set -uo pipefail
ROOT="$PWD"; mkdir -p "$ROOT/done"; : > "$ROOT/watch.txt"
START=$(date -u +%s); END=$(( START + ${MERGER_SECONDS:-20400} ))   # 5 h 40 min, under the 6 h job limit
LAST_BACKLOG=0; BPID=""; SLOTS=${SLOTS:-4}; declare -A SPID
iso() { date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ; }
SINCE="$(iso $(( START - 3*3600 )))"   # first pass catches up on the last 3 hours
budget() {  # keep well inside the GITHUB_TOKEN budget (1000 requests an hour per repository)
  local rem reset
  read -r rem reset < <(gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset)"' 2>/dev/null || echo "999 0")
  if [ "${rem:-999}" -lt 120 ]; then echo "rate budget low ($rem left), waiting for the reset"; sleep $(( reset - $(date -u +%s) + 5 )); fi
}
refresh() {  # main moved on (merges): pull it and give each verdict slot and the backlog pass a fresh copy
  git -C "$ROOT/base" fetch -q --depth 1 origin main && git -C "$ROOT/base" reset -q --hard FETCH_HEAD; git -C "$ROOT/base" clean -fdq
  for d in $(seq 1 "$SLOTS") b; do rm -rf "$ROOT/base_$d"; cp -a "$ROOT/base" "$ROOT/base_$d"; done
}
verdict() {  # $1 run id, $2 head sha, $3 attempt, $4 url, $5 completed before this loop started (1/0), $6 slot
  local ID="$1" SHA="$2" ATT="$3" URL="$4" OLD="$5" B="$ROOT/base_$6" W="$ROOT/work_$6" PR STATE
  rm -rf "$W"; mkdir -p "$W"; ln -s "$B" "$W/base"
  if ! gh run download "$ID" --repo "$REPO" -n verdict -D "$W/artifact" >/dev/null 2>&1; then return 0; fi
  PR=$(head -c 12 "$W/artifact/pr.txt" 2>/dev/null | tr -cd '0-9'); [ -n "$PR" ] || return 0
  STATE=$(gh api "repos/$REPO/pulls/$PR" --jq .state 2>/dev/null || echo unknown)
  [ "$STATE" = open ] || return 0                       # merged or closed meanwhile: nothing to say
  if [ "$OLD" = 1 ] && gh api "repos/$REPO/issues/$PR/comments?per_page=100" --jq '.[].body' 2>/dev/null | grep -qF "$URL"; then
    return 0                                            # already reported (by verdict.yml or an earlier merger)
  fi
  budget
  ( cd "$W" && RELINT="$W/relint.json" RUN_ID="$ID" RUN_ATTEMPT="$ATT" HEAD_SHA="$SHA" RUN_URL="$URL" \
      bash "$B/tools/verdict_one.sh" ) > "$W/log.txt" 2>&1
  echo "#$PR run $ID.$ATT: exit $? $(grep -m1 -oE 'ACCEPTED|REJECTED|FAULT|merged|already on main' "$W/log.txt" || true)"
  git -C "$B" clean -fdq -- proofs reductions statements 2>/dev/null || true
  # a fault or a refused merge re-runs the check: watch the same run id for its next attempt
  [ "$(gh api "repos/$REPO/actions/runs/$ID" --jq .status 2>/dev/null)" = completed ] || echo "$ID" >> "$ROOT/watch.txt"
}
refresh
while [ "$(date -u +%s)" -lt "$END" ]; do
  NOW=$(date -u +%s)
  gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=completed&per_page=100&created=>$SINCE" \
    --jq '.workflow_runs[] | select(.conclusion != "cancelled") | [.id, .head_sha, .run_attempt, .html_url, .updated_at] | @tsv' > runs.tsv 2>/dev/null || : > runs.tsv
  for WID in $(sort -u "$ROOT/watch.txt"); do         # re-run checks created earlier than the window
    gh api "repos/$REPO/actions/runs/$WID" --jq 'select(.status == "completed" and .conclusion != "cancelled") | [.id, .head_sha, .run_attempt, .html_url, .updated_at] | @tsv' >> runs.tsv 2>/dev/null || true
  done
  while IFS=$'\t' read -r ID SHA ATT URL UPD; do
    [ -n "$ID" ] || continue
    [ -e "$ROOT/done/$ID.$ATT" ] && continue
    touch "$ROOT/done/$ID.$ATT"; sed -i "/^$ID\$/d" "$ROOT/watch.txt"
    OLD=0; [ "$(date -u -d "$UPD" +%s 2>/dev/null || echo 0)" -lt "$START" ] && OLD=1
    while :; do                                         # first free slot
      FREE=""; for i in $(seq 1 "$SLOTS"); do { [ -z "${SPID[$i]:-}" ] || ! kill -0 "${SPID[$i]}" 2>/dev/null; } && { FREE=$i; break; }; done
      [ -n "$FREE" ] && break; sleep 1
    done
    verdict "$ID" "$SHA" "$ATT" "$URL" "$OLD" "$FREE" & SPID[$FREE]=$!
  done < runs.tsv
  for i in $(seq 1 "$SLOTS"); do [ -n "${SPID[$i]:-}" ] && wait "${SPID[$i]}" 2>/dev/null; SPID[$i]=""; done
  SINCE="$(iso $(( NOW - 2*3600 )))"                   # afterwards a 2-hour window; done/ remembers the rest
  if { [ -z "$BPID" ] || ! kill -0 "$BPID" 2>/dev/null; } && [ $(( NOW - LAST_BACKLOG )) -ge 1200 ]; then
    LAST_BACKLOG=$NOW; refresh
    B="$ROOT/backlog"; rm -rf "$B"; mkdir -p "$B"; ln -s "$ROOT/base_b" "$B/base"
    ( cd "$B" && RELINT="$B/relint.json" timeout 2400 bash "$ROOT/base_b/tools/backlog_pass.sh" 2>&1 | grep -E "merged|batch|done:" | sed 's/^/backlog: /' ) &
    BPID=$!
  fi
  sleep 30
done
wait
echo "merger: time is up; the next scheduled run takes over"
