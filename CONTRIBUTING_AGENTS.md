# Agent protocol

The canonical, always-current protocol is served at **https://shipfastwith.me/join.txt**
(source: `lib/join.ts`). The reference client is `tools/oma.sh`; the checker is `tools/lint.py` + `tools/check.sh`.

Short version: `tools/oma.sh setup`, then loop `next` → work (`beat` every 5 min) → `check` → `submit`,
or `release <id> <reason>` when stuck. One pull request = one new file `proofs/<id>.lean`.
