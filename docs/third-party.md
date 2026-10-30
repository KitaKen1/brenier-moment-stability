# Third-party sources

The exact list of the included upstream files and their SHA-256 hashes are in
[`../lean/VENDOR.json`](../lean/VENDOR.json).

| Project | Commit | Use |
|---|---|---|
| [Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612) | `d13f23b723b8a846827a245b89c10fc7d3f11612` | Measure theory, convexity, analysis and Lean tactics |
| [OpenAI math](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb) | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` | Finite transport cells, potentials, optimal couplings and map distances, from `lean/OAI/Analysis/Brenier/` |

OpenAI math is Apache-2.0. Its license is retained in `lean/vendor/openai/LICENSE`.

The files under `lean/vendor/openai/` are **adapted**, not verbatim:

- Every file has a Lean module header (`module`, `public import`, `@[expose] public section`)
  in place of its plain imports.
- The bodies of `Basic`, `Atomic`, `Optimality` and `Wasserstein` are compiled together in the
  added file `TransportCore.lean`, which uses targeted Mathlib imports. The four original paths
  re-export it, together with the omnibus Mathlib import on which the other upstream files rely.
- In `Quantiles.lean` the import precedes the leading comment block.
- In `PrefixSections.lean` the definition `scalarBlock` is public instead of private.

The adaptation record in `VENDOR.json` lists every change; the mathematical statements and
proof bodies are those of the upstream files. The upstream originals are not included in this
package, and no script here compares the adapted files with them. The recorded hashes are those
of the adapted files.

From the upstream development the upper bound uses the transport definitions, the finite
optimal coupling with non-colliding interpolation, the restricted conjugate, the completeness
and limit lemmas for maps, and the potential estimate for uniform sources. The upstream
interpolation, existence and uniqueness results for compact targets are not used. The sharpness
example uses the finite-affine optimality certificate.

The statement vocabulary of `lean/BrenierMoment/Presentation/Model.lean` follows the definitions
of `OAI.Problem358` (couplings, quadratic cost, Wasserstein distance, optimal maps, distance of
maps), restated with Mathlib alone.

The generated Lean4Web file includes the adapted sources. Its file header documents
import/module-header removal and section isolation, and its manifest records every included
source hash.

Comparator, lean4export and landrun are downloaded only when the tool installer or CI is run;
their source repositories are not vendored here.
