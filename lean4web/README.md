# Complete single-file proof

[`BrenierMomentStabilityLean4Web.lean`](BrenierMomentStabilityLean4Web.lean) includes
the complete project proof and the adapted OpenAI math sources it needs. It imports
`Mathlib` and nothing else. No locally compiled `BrenierMoment` or `OAI` module is
imported.

```sh
python3 ../lean/scripts/make_lean4web.py --check
lake exe cache get
python3 ../lean/scripts/verify_lean4web.py
```

The environment is pinned to Lean `v4.34.1` and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Source ordering, hashes and the output
hash are recorded in [`sources.json`](sources.json). The generator removes the
import and module-system header lines of each original module and encloses the
module in a section, which isolates its local options, instances, variables and
namespaces. Definitions and theorem statements are retained. The umbrella
`import Mathlib` is kept because the upstream modules rely on it.

Two kinds of change to the text of a source are possible, and the manifest lists
each one per source:

- **Qualified references.** In the modular build a module sees only what it
  imports. In one file it also sees every earlier source, so a short name can
  resolve to a declaration of a deeper namespace that the module never imported.
  This happens for `eventually_injective_sites`, which exists both in
  `OAI.Problem358` and in `OAI.Problem358.CellGeometry`: its three references in
  the proofs of `CellContinuity.lean` and `CanonicalLaplacian.lean` are written
  with the full name `_root_.OAI.Problem358.eventually_injective_sites`. Two of
  them lie inside the namespace `CellGeometry` and do not compile otherwise.
  See `proof_adjustments` in the manifest.
- **Renamed private identifiers.** A private identifier is renamed only if two
  sources declare the same name. There are none at present.

The file is not in Lean's module system, while the sources in `../lean/` are. In
the sources every definition is exposed, so nothing changes in what later
declarations can unfold.

The seven final `#print axioms` commands must list only `propext`,
`Classical.choice` and `Quot.sound`. The verification script records the source
hash, result and axiom reports in `verification.json` and the compiler output in
`build.log`. `lake build` is also available for a normal library build.

<!-- BEGIN SINGLE FILE STATUS -->
**Status.** On 13 October 2026 the file was compiled on the author's machine by `lean`, against
a cache of the pinned Mathlib: no error and no warning, and the seven axiom reports list only
the three axioms ([local-verification.json](local-verification.json),
[local-build.log](local-build.log)). The three Mathlib-only targets of the file, with all the
definitions their statements use, were compared with the compiled Comparator challenge and
agree ([local-statement.log](local-statement.log)); see below. This run did not go through
`lake env`, so `lakefile.toml` and `lake-manifest.json` of this directory are not exercised, and
no `verification.json` is included: `verify_lean4web.py` and the `single-file` job of
[`lean.yml`](../.github/workflows/lean.yml) produce it.
<!-- END SINGLE FILE STATUS -->

## Comparison with the challenge

The statements of the single file can be compared with the Comparator challenge, but not
constant by constant. When a definition contains a proof, Lean stores it in an auxiliary
theorem `Foo._proof_n`, and it reuses an auxiliary theorem that already has the same statement
and proof. In one file the statement vocabulary comes after the whole development, so its
definitions refer to auxiliary theorems created earlier, for example
`BrenierMoment.tailEnvelope._proof_1` where the challenge has
`BrenierStability.modulus._proof_1`. [`CompareSingleFile.lean`](../lean/scripts/CompareSingleFile.lean)
replaces every such auxiliary theorem by its proof term and then makes the comparison of
[`CompareStatement.lean`](../lean/scripts/CompareStatement.lean). It needs the compiled
challenge and the compiled single file on the search path:

```sh
lean --run ../lean/scripts/CompareSingleFile.lean CONFIG.json
```

where `CONFIG.json` has the fields of
[`BrenierMomentStability.json`](../lean/ComparatorChallenges/BrenierMomentStability.json) with
`"solution_module": "BrenierMomentStabilityLean4Web"`.

<!-- BEGIN PUBLICATION LINKS -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fbrenier-moment-stability%2Fmain%2Flean4web%2FBrenierMomentStabilityLean4Web.lean) (Lean **v4.34**).
<!-- END PUBLICATION LINKS -->

For a hosted editor, open [Lean4Web](https://live.lean-lang.org/), select the
project **Stable Release (v4.34.0 with mathlib, cslib)** (`project=mathlib-stable`),
then load the complete file. That project is the closest to the pinned
environment: Mathlib's `v4.34.1` tag, pinned here, differs from its `v4.34.0`
tag only in the toolchain file. The server's projects are not pinned by this
repository and are replaced as new releases appear, so a later server project may
require a separate port and revalidation. The
[server's URL documentation](https://github.com/leanprover-community/lean4web/blob/main/doc/Usage.md)
describes `#url=...` and `project=...`.

This edition is much larger than a small Lean4Web example, and it has not been
run on the server. [`hosted-status.json`](hosted-status.json) records this. The
local compilation took about twenty minutes.
A local build is the reproducible check; server resource limits and version
compatibility are separate from proof correctness.
