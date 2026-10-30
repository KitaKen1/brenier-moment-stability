#!/usr/bin/env bash
set -euo pipefail
BRENIER_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
: "${COMPARATOR_TOOLS:?Run install-tools.sh first}"
BRENIER_RECEIPT="$BRENIER_ROOT/comparator-receipt"
BRENIER_CONFIG=ComparatorChallenges/BrenierMomentStability.json
mkdir -p "$BRENIER_RECEIPT"
printf 'NOT_RUN\n' > "$BRENIER_RECEIPT/status.txt"
trap 'code=$?; if [[ $code -ne 0 ]]; then printf "FAIL: exit=%s\n" "$code" > "$BRENIER_RECEIPT/status.txt"; fi' EXIT
python3 "$BRENIER_ROOT/comparator/check-inputs.py" --receipt-dir "$BRENIER_RECEIPT"
test "$(uname -s)" = Linux
python3 - "$BRENIER_ROOT/comparator/pins.json" "$COMPARATOR_TOOLS" "$BRENIER_ROOT/lean/lean-toolchain" <<'PY'
from pathlib import Path
import json, subprocess, sys
pins=json.load(open(sys.argv[1])); tools=Path(sys.argv[2])
for tool,key in [('comparator','comparator_commit'),('landrun','landrun_commit'),('lean4export','lean4export_commit')]:
    actual=subprocess.check_output(['git','-C',str(tools/tool),'rev-parse','HEAD'],text=True).strip()
    if actual!=pins[key]: raise SystemExit('Tool commit differs: '+tool)
if (tools/'lean4export/lean-toolchain').read_bytes()!=Path(sys.argv[3]).read_bytes():
    raise SystemExit('Exporter toolchain differs from proof')
PY
for BRENIER_FILE in "lean/$BRENIER_CONFIG" comparator/pins.json .github/workflows/comparator.yml \
    lean/BrenierMoment/FCPresentation.lean lean/BrenierMoment/Presentation/Model.lean; do
  cp "$BRENIER_ROOT/$BRENIER_FILE" "$BRENIER_RECEIPT/$(basename "$BRENIER_FILE")"
done
{
  printf 'run_url=%s/%s/actions/runs/%s\n' "${GITHUB_SERVER_URL:-https://github.com}" "${GITHUB_REPOSITORY:-local}" "${GITHUB_RUN_ID:-local}"
  printf 'run_attempt=%s\ntested_commit=%s\n' "${GITHUB_RUN_ATTEMPT:-local}" "$(git -C "$BRENIER_ROOT" rev-parse HEAD)"
  date -u +started_utc=%FT%TZ
  uname -a; id
  (cd "$BRENIER_ROOT/lean" && lake env lean --version)
  for BRENIER_TOOL in comparator landrun lean4export; do
    printf '%s_commit=%s\n' "$BRENIER_TOOL" "$(git -C "$COMPARATOR_TOOLS/$BRENIER_TOOL" rev-parse HEAD)"
  done
  git -C "$COMPARATOR_TOOLS/lean4export" diff -- lean-toolchain
  printf 'sandbox: unprivileged uid/gid, RestrictAddressFamilies=~AF_UNIX, NoNewPrivileges=yes\n'
} > "$BRENIER_RECEIPT/environment.txt"
set +e
sudo systemd-run --wait --collect --pipe \
  --uid="$(id -u)" --gid="$(id -g)" \
  --property='RestrictAddressFamilies=~AF_UNIX' --property=NoNewPrivileges=yes \
  --property=RuntimeMaxSec=240min --working-directory="$BRENIER_ROOT/lean" \
  --setenv="PATH=$PATH" --setenv="HOME=$HOME" \
  --setenv="COMPARATOR_LANDRUN=$COMPARATOR_TOOLS/bin/landrun" \
  --setenv="COMPARATOR_LEAN4EXPORT=$COMPARATOR_TOOLS/lean4export/.lake/build/bin/lean4export" \
  -- "$HOME/.elan/bin/lake" env "$COMPARATOR_TOOLS/comparator/.lake/build/bin/comparator" "$BRENIER_CONFIG" \
  2>&1 | tee "$BRENIER_RECEIPT/comparator.log"
BRENIER_PIPE=("${PIPESTATUS[@]}")
set -e
test "${BRENIER_PIPE[0]}" -eq 0
test "${BRENIER_PIPE[1]}" -eq 0
grep -Fxq 'Lean default kernel accepts the solution' "$BRENIER_RECEIPT/comparator.log"
grep -Fxq 'Your solution is okay!' "$BRENIER_RECEIPT/comparator.log"
python3 "$BRENIER_ROOT/comparator/check-inputs.py" --receipt-dir "$BRENIER_RECEIPT/after"
# Inspect the solution only after the sandboxed Comparator has accepted it.
(cd "$BRENIER_ROOT/lean" && lake env lean FCAudit.lean) 2>&1 | tee "$BRENIER_RECEIPT/axioms.log"
python3 - "$BRENIER_RECEIPT/axioms.log" <<'PY'
from pathlib import Path
import sys
text=Path(sys.argv[1]).read_text()
for name in ['BrenierStability.moment_stability', 'BrenierStability.moment_rate_sharp', 'BrenierStability.no_modulus_at_second_moment', 'BrenierMoment.moment_stability', 'BrenierMoment.moment_rate_sharp', 'BrenierMoment.no_modulus_at_second_moment']:
 expected="'"+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
 if text.count(expected)!=1: raise SystemExit('Missing exact axiom receipt for '+name)
if 'sorryAx' in text or 'error:' in text: raise SystemExit('Axiom audit failed')
PY
printf 'PASS\n' > "$BRENIER_RECEIPT/status.txt"
