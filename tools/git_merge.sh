#!/usr/bin/env bash
# Merge an accepted pull request with git, when GitHub's merge API refuses this workflow's token ("Resource not
# accessible by integration": #7514, #7562, #7031, ... were accepted on 27 November and never merged).
# Called by tools/verdict_one.sh after every one of its checks passed (one-file rule from the merge ref, head pinned,
# trusted re-lint, shortest-proof rule); trusted: it never runs pull request code. It builds one commit on top of main
# whose tree is main's plus exactly the checked file (the blob at HEAD_SHA), with the pull request's head as second
# parent, so GitHub marks the pull request merged (its head becomes part of main); it checks that the commit changes
# that one path and nothing else, re-applies the duplicate and shortest-proof rules against main as it is at push time,
# and pushes without force (a moved main means start again). If GitHub refuses that push (a token that may not add the
# head's history), the same tree goes in as a single-parent commit and the pull request is closed with a pointer to it.
# Prints the new commit on success. Exit 2: not merged for a rule (already on main, not shorter), 1: failure.
# Needs: REPO PR HEAD_SHA FPATH MODE (new|replace) TITLE; base/ (a checkout of main whose credentials can push).
set -uo pipefail
G="git -C base"
fail() { echo "$1" >&2; exit "${2:-1}"; }
[[ "$PR" =~ ^[0-9]+$ && "$HEAD_SHA" =~ ^[0-9a-f]{40}$ ]] || fail "bad arguments"
printf '%s' "$FPATH" | grep -Eq "^(proofs|reductions|statements)/[A-Za-z0-9_.'-]+\.lean$" || fail "bad path"
# the head may not have moved since the check
[ "$($G ls-remote origin "refs/pull/$PR/head" 2>/dev/null | cut -f1)" = "$HEAD_SHA" ] || fail "the pull request's head moved"
$G cat-file -e "$HEAD_SHA^{commit}" 2>/dev/null || $G fetch -q --no-tags --depth 1 origin "refs/pull/$PR/head" || fail "cannot fetch the head"
BLOB=$($G rev-parse "$HEAD_SHA:$FPATH" 2>/dev/null) || fail "the file is not in the head"
MSG="${TITLE:-$FPATH} (#$PR)"
ID=(-c user.name="github-actions[bot]" -c user.email="41898282+github-actions[bot]@users.noreply.github.com")
# one merge of a given file at a time on this runner (the merger works four pull requests at once, oldest first):
# two copies of the same proof never race, and the one taken first (the older) is pushed first
exec 9> "/tmp/oma-git-merge-$(printf '%s' "$FPATH" | sha1sum | cut -c1-16).lock"; flock -w 600 9 || fail "file locked"
# One push to main at a time on this runner (global lock, taken after the file lock, always in that order: no deadlock).
# Unlocked, the merger's slots raced: each fetched main, built its commit and pushed, and all but one were refused and
# started again, so more slots gave fewer merges. Locked, the fetch-build-push section (about a second) never races.
exec 8> /tmp/oma-git-merge-main.lock
for TRY in 1 2 3 4 5 6 7 8 9 10; do
  [ "$TRY" -gt 1 ] && flock -u 8
  flock -w 900 8 || fail "main locked"
  $G fetch -q --no-tags --depth 1 origin main || { sleep 5; continue; }
  MAIN=$($G rev-parse FETCH_HEAD)
  # duplicate and shortest-proof rules against main as it is now
  if $G cat-file -e "$MAIN:$FPATH" 2>/dev/null; then
    [ "$MODE" = replace ] || fail "already on main" 2
    $G show "$MAIN:$FPATH" > gm_old.lean; $G show "$BLOB" > gm_new.lean
    read -r RES _ _ < <(python3 -I base/tools/prooflen.py gm_old.lean gm_new.lean)
    [ "$RES" = shorter ] || fail "not shorter than the proof on main" 2
  fi
  export GIT_INDEX_FILE="$PWD/gm_index"; rm -f "$GIT_INDEX_FILE"
  $G read-tree "$MAIN" && $G update-index --add --cacheinfo "100644,$BLOB,$FPATH" && TREE=$($G write-tree) || fail "cannot build the tree"
  unset GIT_INDEX_FILE
  # the commit changes that one path and nothing else
  CHANGES=$($G diff-tree -r --name-status "$MAIN" "$TREE")
  [ "$CHANGES" = "$(printf 'A\t%s' "$FPATH")" ] || [ "$CHANGES" = "$(printf 'M\t%s' "$FPATH")" ] || fail "unexpected change: $CHANGES"
  C=$($G "${ID[@]}" commit-tree "$TREE" -p "$MAIN" -p "$HEAD_SHA" -m "$MSG") || fail "cannot commit"
  if OUT=$($G push -q origin "$C:refs/heads/main" 2>&1); then echo "$C"; exit 0; fi
  if printf '%s' "$OUT" | grep -qiE "fetch first|non-fast-forward|rejected.*main|failed to update ref|cannot lock"; then
    sleep 1; continue   # main moved (a push from elsewhere): again on the new main
  fi
  echo "two-parent push refused: ${OUT:0:200}" >&2
  # the same tree as a single-parent commit; the pull request is then closed by hand, pointing at the commit
  C=$($G "${ID[@]}" commit-tree "$TREE" -p "$MAIN" -m "$MSG") || fail "cannot commit"
  if OUT=$($G push -q origin "$C:refs/heads/main" 2>&1); then
    gh api -X PATCH "repos/$REPO/pulls/$PR" -f state=closed >/dev/null 2>&1 || true
    echo "$C"; exit 0
  fi
  printf '%s' "$OUT" | grep -qiE "fetch first|non-fast-forward" && { sleep 1; continue; }
  fail "push refused: ${OUT:0:200}"
done
fail "main kept moving"
