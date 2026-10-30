# Brenier moment stability proposed FC target verification

Public verification [passed on 30 October 2026](https://github.com/KitaKen1/brenier-moment-stability/actions/runs/40978788813),
testing commit `4871736bc0c348fd9e6a25d2f0e6e28892dbeeba`. The proof build, compact FC-model
check, sandboxed Comparator, six target axiom reports, whole-environment fresh replay and final
gate all passed. The original logs and artifacts are preserved in
[ComparatorLog20261030](../ComparatorLog20261030/40978788813-attempt1/).
The first private attempt exposed a missing build dependency for the original OpenAI comparison
theorem; the CI build target was corrected without changing the proof sources. No
Formal Conjectures PR has been created; the statement was proposed in
[formal-conjectures issue 7197](https://github.com/google-deepmind/formal-conjectures/issues/7197).
The setup follows the verification of
[KitaKen1/smooth-isometric-embeddings-r4](https://github.com/KitaKen1/smooth-isometric-embeddings-r4/tree/main/comparator),
which uses the same Lean and Mathlib versions.

The targets are `BrenierStability.moment_stability`, `BrenierStability.moment_rate_sharp` and
`BrenierStability.no_modulus_at_second_moment`. The complete proposed FC-style file is in
`FClikelean/BrenierMomentStability.lean`; that folder also contains the statement guide.
It restates OpenAI's compact-target result immediately before the moment variant for comparison.
`render-target.py` checks the three shared definitions and expanded variant types against the
proved model, then restores the model's definitions and three statement signatures to generate the trusted
file `lean/ComparatorChallenges/BrenierMomentStability.lean`, with eight pinned Mathlib imports
and the theorems' intended `sorry` holes. The FC import, the module/public declarations and the
review attributes are removed. The challenge retains the model's longer docstrings.
The solution module is `BrenierMoment.FCPresentation`. It imports the definitions from
`BrenierMoment/Presentation/Model.lean`, which imports only the same eight Mathlib modules,
retains the same statements and names, and fills the holes from
`BrenierMoment.moment_stability`, `BrenierMoment.moment_rate_sharp` and
`BrenierMoment.no_modulus_at_second_moment`.

This extraction is explicit: **the challenge is not a byte-for-byte copy of an upstream FC file.**
The full draft is preserved and hashed, and the generated file is checked against it.
`lean/scripts/verify_fc_statement.py` proves equality of the three compact definitions and the
three variant types with the model by `rfl`, and separately derives the original statement
from OpenAI's `one_third_stability`. The FC
file is not submitted, so `fc_target_commit` and `fc_pr` are null rather than invented identifiers.

The challenge and the solution each elaborate their own copy of the thirteen definitions.
Comparator compares the two copies declaration by declaration, and `lean/scripts/verify.py`
checks that their source text is identical. The challenge is a plain Lean file, while the
solution and its definitions use Lean's module system with every definition exposed. The local
declaration comparison, which uses the pinned Comparator's equality and traversal rules, passes
for this combination: [`local-comparison.log`](../lean/verification/local-comparison.log) and
[`local-statement.json`](../lean/verification/local-statement.json). The export through
lean4export and the sandboxed run are what the first private run has to show.

Upstream FC uses Lean 4.33.1. This proof uses Lean 4.34.1 / Mathlib `d13f23b…`.
The current draft's compatibility with a real FC checkout remains pending. Do not describe
this candidate as an accepted FC theorem, a validated upstream FC checkout, or an exact
upstream-target Comparator run. First build the proposed statement and definitions in a real
FC checkout. If incompatibilities are found, determine the smallest changes needed, keep the
submitted and external target definitions aligned, and then freeze the submitted FC head/path
for the final exact-target comparison.

## Fixed inputs

`pins.json` fixes the proof release, the proposed draft, the challenge, the toolchain, Mathlib and
three tool revisions. The proof release is [`leanWithoutComparator/`](../leanWithoutComparator/README.md):
`check-inputs.py` checks that all files listed in its `sources.json` are unchanged in `lean/`
and in the copy, and that no proof source is extra or missing. The proof lakefile only adds the
`ComparatorChallenges` review library; its unchanged original is `leanWithoutComparator/lakefile.toml`.

```bash
python3 comparator/render-target.py --check
python3 comparator/check-inputs.py --receipt-dir input-receipt
```

After a deliberate change of the statement or of the proof, regenerate and repin:

```bash
python3 lean/scripts/make_fc_statement.py
python3 comparator/render-target.py
python3 lean/scripts/make_lean_without_comparator.py
python3 comparator/refresh-pins.py
```

For a built proof workspace, the local preflight is:

```bash
python3 comparator/local-precheck.py --receipt-dir local-precheck-receipt
```

It builds the challenge and the solution as separate modules, checks the compact FC model by
`rfl`, compares the three theorems and
all reachable declarations using the pinned Comparator's equality/traversal rules, and audits the
solution's axioms. Its success status is `LOCAL_PRECHECK_PASS`, **not** `PASS` for a Linux
Comparator run.

## Private CI first, then public main CI

First run `.github/workflows/comparator.yml` in a private verification repository. Check the
three FC targets, permitted axioms and kernel acceptance; repair setup or target issues there.
Freeze the successful proof and verification configuration, publish them to public `main`, and
rerun this same workflow in the public repository. Private success alone is not public-run evidence.

The workflow is manual (`workflow_dispatch`), with read-only repository
permissions and three substantive jobs:

1. Build the complete proof and check the compact FC model by `rfl` on a separate runner.
   Save the complete or partial build under the
   exact tested commit; if the 300-minute build window expires, rerun the same commit to resume.
   An incomplete round fails the final gate rather than appearing verified.
2. On a fresh checker runner, compile the trusted extracted challenge, install pinned tools,
   restore proof products, restore the separately compiled challenge, and run Comparator through
   landrun under an unprivileged systemd service. AF_UNIX is restricted. The checking job does
   not compile the solution outside the sandbox before Comparator acceptance.
3. Independently replay the whole proof environment using `leanchecker --fresh`.

Comparator success additionally requires exact success lines and exact axiom lines for the three
FC targets and for the original theorems `BrenierMoment.moment_stability`,
`BrenierMoment.moment_rate_sharp` and `BrenierMoment.no_modulus_at_second_moment`. Failed
receipts are also uploaded. All artifact retention is 90 days. The final gate requires all three
jobs to succeed. Runner preparation and swap helpers live in `comparator/prepare-runner.sh` and
`comparator/add-swap.sh`.

To build and inspect the proof locally, from the repository root:

```bash
cd lean
lake exe cache get
lake build BrenierMoment
lake env lean FCAudit.lean
LEAN_BIN=$(dirname "$(elan which lean)")
lake env "$LEAN_BIN/leanchecker" --fresh BrenierMoment
```

## Preserve a completed public run

Only after public `main` CI succeeds, archive the completed attempt using its actual IDs:

```bash
python3 comparator/archive-run.py \
  --repo KitaKen1/brenier-moment-stability \
  --run RUN_ID --attempt ATTEMPT --expected-commit TESTED_COMMIT \
  --public-success-only \
  --output ComparatorLogYYYYMMDD/RUN_ID-attemptATTEMPT
```

Authentication uses `GH_TOKEN` or the existing Git credential helper; credentials are not saved.
The archive preserves original artifact ZIPs, all extracted receipts, original complete workflow
log ZIP, complete job logs, API metadata, artifact IDs/digests/expiry, and `SHA256SUMS`.
The downloaded ZIP digest must equal the GitHub artifact digest. A successful run must contain
`status.txt: PASS`, both Comparator success messages, target axiom lines, and the tested commit.
Existing archive directories are not overwritten. `--public-success-only` rejects a private,
failed or non-main run before writing evidence.

Keep three identities separate: the proof commit, the tested CI commit, and the later archive
commit. The last cannot be embedded as its own commit hash; record it in the README/PR after
committing the archive. Local hashes are file identities, not signed GitHub attestations.

Official references: [Comparator at the pinned revision](https://github.com/leanprover/comparator/blob/ca04cfc72b550331658ec314bf47685281bfd4bf/README.md),
[FC contribution guidance](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md).
