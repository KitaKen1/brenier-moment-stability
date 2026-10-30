#!/usr/bin/env bash
# Cache a partial build at the 300 minute boundary; rerun the SAME commit to resume.
set -euo pipefail
mkdir -p ../build-receipt
set +e
timeout --kill-after=120 300m lake build BrenierMoment OAI.Analysis.Brenier.Stability \
  2>&1 | tee ../build-receipt/build.log
BRENIER_PIPE=("${PIPESTATUS[@]}")
set -e
BRENIER_CODE=${BRENIER_PIPE[0]}
test "${BRENIER_PIPE[1]}" -eq 0
if [[ "$BRENIER_CODE" -eq 0 ]]; then
  if ! python3 scripts/verify_fc_statement.py; then
    printf 'FAIL: compact FC model differs\n' > ../build-receipt/status.txt
    exit 1
  fi
  cp verification/fc-model.json verification/fc-model.log verification/FCModelCheck.lean ../build-receipt/
  printf 'ready=true\n' >> "$GITHUB_OUTPUT"
  printf 'PASS\n' > ../build-receipt/status.txt
elif [[ "$BRENIER_CODE" -eq 124 || "$BRENIER_CODE" -eq 137 ]]; then
  printf 'ready=false\n' >> "$GITHUB_OUTPUT"
  printf 'INCOMPLETE: rerun same commit to resume cached build\n' > ../build-receipt/status.txt
else
  printf 'FAIL: exit=%s\n' "$BRENIER_CODE" > ../build-receipt/status.txt
  exit "$BRENIER_CODE"
fi
