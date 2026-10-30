# Statement in the format of Formal Conjectures

[BrenierMomentStability.lean](BrenierMomentStability.lean) places the original compact-target
result and the moment variant consecutively, using three shared definitions:

- **Original:** `original_compact_stability`, OpenAI's solved compact-target problem with the
  sharp $`W_2^{1/3}`$ bound. The earlier square-root conjecture was disproved.
- **Variant:** `moment_stability` and its sharpness and endpoint statements, proved in this work.

The changes are visible directly in the statements:

| Part of the statement | `Original` | `Variant` |
|---|---|---|
| Source | `let ρ := (volume K)⁻¹ • volume.restrict K` | Density proportional to `Real.exp (-V x)`, with `hV : ConvexOn ℝ U V` |
| Target conditions | `μ (Yᶜ) = 0 → ν (Yᶜ) = 0`, with `hY : IsCompact Y` | `moment p β μ ≤ 1 → moment 2 0 ν < ∞` |
| Bound | `C * wasserstein μ ν ^ (1 / 3 : ℝ)` | `C * (δ ^ ((p - 2) / (3 * p - 2)) * Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2)))` |
| Distance range | All target pairs in `Y` | `0 < δ` and `δ ≤ δ₀`, where `let δ := wasserstein μ ν` |
| Dimension | `hd : 2 ≤ d` | Any `d : ℕ` for the upper bound |

`μ (Yᶜ) = 0` says that no mass lies outside `Y`. In the variant, a common target set `Y`
is replaced by the one-sided moment condition. Both statements write the map error directly
as `Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ)`.

For the variant, a log-concave source on a bounded convex set, a target $`\mu`$ with
$`\int|y|^p[\log(e+|y|)]^\beta\,d\mu\le1`$ and a target $`\nu`$ with finite second moment,
$`\|T_\mu-T_\nu\|_{L^2(\rho)}\le C\,\delta^{(p-2)/(3p-2)}[\log(e/\delta)]^{-2\beta/(3p-2)}`$
for small $`\delta=W_2(\mu,\nu)`$, and this modulus cannot be improved. All three variant
statements are proved.

- **Upper bound:** `BrenierStability.moment_stability`, for the probability measure with density
  proportional to $`e^{-V}`$ on a bounded open convex set `U`, with `V` convex on `U`, and for
  all $`p\ge2`$, $`\beta\ge0`$. The statement includes the existence and uniqueness of the two
  Brenier maps.
- **Sharpness:** `BrenierStability.moment_rate_sharp`, on the uniform source on
  $`[0,1]\times[-1,1]^{d+1}`$, for two four-atom targets at every small distance $`\delta`$.
- **Endpoint:** `BrenierStability.no_modulus_at_second_moment`: at $`p=2`$, $`\beta=0`$ the
  distance of the maps stays at least $`1/20`$ while $`W_2\to0`$.
- **Definitions:** just `wasserstein`, `IsBrenierMap` and `moment`. The Euclidean space is written
  directly as `EuclideanSpace ℝ (Fin d)`. The source, map
  error and rate are written inside the statements. The box and four-atom predicate are local
  to the sharpness and endpoint statements.
  [verify_fc_statement.py](../lean/scripts/verify_fc_statement.py) checks all three definitions
  and the three variant types against the proved model by Lean's `rfl`, and derives
  `original_compact_stability` directly from OpenAI's `one_third_stability`.
- **Proof links:** the four statements use `by sorry`, with `formal_proof` links to the
  complete Lean proofs. The original links to the pinned OpenAI theorem; run `fill_links.py`
  with a public commit to pin the three variant links.

`python3 lean/scripts/check_publication.py` checks the original statement and that the definitions
and three expanded variant statements agree with the complete proof.
`python3 lean/scripts/make_fc_statement.py` regenerates this file from the proof sources,
retaining the original/variant comparison, compact definitions and short docstrings.

The statement differs from the issue text in three ways, each of which makes it stronger or
equivalent. The dimension is arbitrary in the upper bound, where the issue has $`d\ge2`$. The
case $`p=2`$, $`\beta=0`$ is not excluded from the upper bound; there the modulus is $`1`$. The
source is given by a bounded open convex set and a convex function on it, which covers every
log-concave density whose support is a compact convex body.

This file has not been compiled inside a Formal Conjectures checkout, which pins another Lean
version than the proof (`v4.33.1`). Its definitions and three variant statements, without the Formal
Conjectures import and attributes, and with the helper definitions expanded, are the Comparator challenge
[lean/ComparatorChallenges/BrenierMomentStability.lean](../lean/ComparatorChallenges/BrenierMomentStability.lean),
which compiles with the pinned Mathlib.
