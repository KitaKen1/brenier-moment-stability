# Verification scope

Each check has a separate result. A successful local build does not imply that
an external service or a separate kernel has run. The last column says what has
actually been run on the files of this package.

Public CI [passed on 30 October 2026](https://github.com/KitaKen1/brenier-moment-stability/actions/runs/40978788813),
testing commit `4871736bc0c348fd9e6a25d2f0e6e28892dbeeba`. Every required job succeeded:
the Lake proof build and compact FC-model check, sandboxed Comparator and six target axiom
reports, whole-environment fresh replay, and final gate. The original evidence is preserved in
[ComparatorLog20261030](../ComparatorLog20261030/40978788813-attempt1/).
An upstream Formal Conjectures checkout remains a separate compatibility check.

| Check | Evidence / command | Scope | Run |
|---|---|---|---|
| Module-by-module build and axiom audit | `lean/verification/local-build.json` | Every module compiled separately by `lean` against a prebuilt cache of the pinned Mathlib, without Lake; `#print axioms` for the declarations of `Audit.lean` and `FCAudit.lean` | Run on 12 and 13 October 2026, passed |
| Lake build and axiom audit | `lean/verification/result.json`, `python3 lean/scripts/verify.py` | Lake build, the challenge, all listed transitive axiom closures, statement comparison | Not run |
| Public Lake proof build and target audit | Public run 40978788813, build and comparator artifacts | `lake build BrenierMoment OAI.Analysis.Brenier.Stability`; separately compiled challenge; `FCAudit.lean` for six target axiom reports | Passed on 30 October 2026; the broader `verify.py` workflow above has not been run as a whole |
| Source-level guards | `python3 lean/scripts/verify.py --static` | Hashes of the adapted upstream files, one vocabulary and three statements in model and challenge, no hole or axiom in the proof sources | Run, passed |
| Mathematical dependency ledger | `python3 lean/scripts/check_blueprint.py` | Acyclic ledger, real source files, witnesses declared in their source and listed for the axiom audit | Run, passed |
| Compiled statement comparison | `lean/verification/statement.log`; local run: `lean/verification/local-statement.json` | Types and recursively dependent definitions of the three targets in the two compiled environments, and the axioms of the solution | Run locally with `lean --run` on the module-by-module build, passed. Not run through `lake env` |
| Compact FC statement | `lean/verification/fc-model.json`, `python3 lean/scripts/verify_fc_statement.py`; public build artifact | Three compact definitions and three expanded variant types equal the proved model by Lean's `rfl`; the original compact-target statement is derived from OpenAI's `one_third_stability`. FC import and metadata omitted | Passed locally on 13 October and in public Linux CI on 30 October 2026. FC checkout compatibility remains pending |
| Fresh Lean environment | `lean/verification/replay.json`, `lake env lean --run scripts/Replay.lean` | Same installed Lean kernel, all imported and defined constants | Not run |
| Single-file edition | `lean4web/verification.json`; local run: `lean4web/local-verification.json` | Complete generated file with no project imports, pinned Mathlib; its three targets against the challenge | Compiled locally by `lean` against the Mathlib cache on 13 October 2026: no error, seven axiom reports with the three axioms; the targets agree with the challenge up to the names of auxiliary proofs (`lean/scripts/CompareSingleFile.lean`). Not run through `lake env` |
| Copy without Comparator files | `leanWithoutComparator/sources.json`, `python3 lean/scripts/make_lean_without_comparator.py --check` | Every copied file has the bytes of its `lean/` original | Identity: run, passed. Build of the copy: not run |
| Publication copies | `python3 lean/scripts/check_publication.py` | FC vocabulary and signatures equal to the proved ones, pinned dependencies, hole-free single file | Run, passed |
| Comparator inputs | `python3 comparator/check-inputs.py`, `comparator/pins.json` | Targets, challenge generated from the FC draft with its four helpers expanded, proof files identical to `leanWithoutComparator/`, toolchain, Mathlib and tool revisions | Run, passed |
| Local Comparator precheck | `python3 comparator/local-precheck.py --receipt-dir DIR`; local run of its comparison: `lean/verification/local-comparison.log` | Declaration equality of challenge and solution with the pinned Comparator's rules, and the solution's axioms; no sandbox, not a Comparator run | The comparison `comparator/LocalCompare.lean` was run with `lean --run` on the module-by-module build: no mismatch. The script, which builds with Lake, has not been run |
| Lean Comparator | `.github/workflows/comparator.yml`, `comparator/run-check.sh`; public comparator artifact | Pinned Comparator in a sandbox on a fresh GitHub runner: the three targets, permitted axioms and kernel acceptance, followed by six axiom reports | Passed in public run 40978788813 on 30 October 2026 |
| Whole-environment fresh replay | `.github/workflows/comparator.yml`, replay job | `lake env leanchecker --fresh BrenierMoment` | Passed in the public run on 30 October 2026 |
| GitHub Actions | `.github/workflows/` | Manual workflows; success requires a hosted run | Public Comparator workflow passed, including the final gate. The separate `lean.yml` workflow has not run |
| Hosted Lean4Web | `lean4web/hosted-status.json` | Manual browser run on the public server | Not run |
| Formal Conjectures submission | `FClikelean/README.md` | Draft; compile and lint inside the destination checkout before submitting | Not done |

## What the local build is

The proof was developed and compiled outside this directory layout, with the adapted upstream
files in `OAI/` next to `BrenierMoment/`. Each module was compiled by `lean -o` in dependency
order against a cache of compiled Mathlib at the pinned revision; a module was accepted only if
the compiler reported no error and no `sorry`. `lean/verification/local-build.json` lists a
module only if the file in this package has the SHA-256 of the source that was compiled.

That original build did not use Lake. The subsequent private CI run on 30 October 2026 built
the files in this package's layout using its `lakefile.toml` and `lake-manifest.json`. It also
built `OAI.Analysis.Brenier.Stability` explicitly for the original-result comparison.

## Axioms and holes

`propext`, `Classical.choice` and `Quot.sound` are the only permitted axioms for
the proved theorems. The challenge and the FC draft have intentional proof holes;
they are excluded from the proof-source scan and never imported by the solution.

## Module system

The proof sources use Lean's module system. Every file opens with
`@[expose] public section`, so all definitions are exposed. The Comparator challenge is a plain
Lean file. The single-file edition is a plain Lean file as well: the generator removes the
module headers. Its compilation is a separate check from the modular build: in one file a
module sees every earlier source, not only its imports. The first compilation failed for this
reason at two references to a name that exists in two namespaces; the generator now writes
these references with the full name, and records the change in `lean4web/sources.json`.

## Upstream sources

The files under `lean/vendor/openai/` are adapted from OpenAI math; see
[third-party.md](third-party.md). `lean/VENDOR.json` records the hash of each adapted file.
The package does not contain the upstream originals and does not compare against them.
