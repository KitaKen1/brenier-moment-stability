# Modular Lean proof

Entry point: [`BrenierMoment.lean`](BrenierMoment.lean).
Final theorems: [`UpperBound.lean`](BrenierMoment/UpperBound.lean),
[`Sharpness.lean`](BrenierMoment/Sharpness.lean) and
[`TwoSided.lean`](BrenierMoment/TwoSided.lean).
Public Mathlib-only statements: [`FCPresentation.lean`](BrenierMoment/FCPresentation.lean).

```sh
lake exe cache get
python3 scripts/verify.py
lake env lean --run scripts/Replay.lean
```

`Audit.lean` prints the transitive axiom dependencies of the principal declarations, and
`FCAudit.lean` those of the Mathlib-only statements and of the theorems they are derived from.
The standard-three axiom whitelist is enforced by `scripts/verify.py`, which also checks that
no proof source contains `sorry`, `admit`, `axiom` or `native_decide`.
`scripts/CompareStatement.lean` compares the separately compiled Mathlib-only challenge and
solution, including all the definitions their types use. `scripts/CompareSingleFile.lean` makes the same comparison for the single-file
edition, after replacing auxiliary proof constants by their proof terms. The challenge in
`ComparatorChallenges/` is generated from the Formal Conjectures draft. Comparator
instructions are in [`../comparator/`](../comparator/README.md).

[`blueprint/dependencies.json`](blueprint/dependencies.json) is a mathematical dependency
ledger of the proof. `scripts/check_blueprint.py` checks that it is acyclic and that each of
its witnesses is declared in the named source and covered by the axiom audit. Its edges are
authored; it is not an extracted Lean import graph.

The sources under [`vendor/openai/`](vendor/openai/) are adapted from
`lean/OAI/Analysis/Brenier/` of [openai/math](https://github.com/openai/math) at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. They are not verbatim: every file has a module
header, and three further changes are listed in [`VENDOR.json`](VENDOR.json) together with the
SHA-256 of each file as included here. `scripts/verify.py` checks these hashes.

All files use Lean's module system, with `@[expose] public section`, and are compiled with
`autoImplicit` off.

Use the committed `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`
without running `lake update`. Mathlib caches accelerate external dependencies.
The project and the adapted upstream modules still build from their sources.
See the [root README](../README.md) for scope, public statements and status, and
[`../docs/verification.md`](../docs/verification.md) for the checks that have been run.
