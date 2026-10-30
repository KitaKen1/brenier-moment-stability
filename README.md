# Lean proof of sharp moment stability of Brenier maps

> [!NOTE]
> **Tentative version.** The Lean proofs have [passed public CI](https://github.com/KitaKen1/brenier-moment-stability/actions/runs/40978788813).
> The statement and documentation are being refined; a finalized version will be available soon.

For the Brenier maps of a log-concave source, the stability problem under a moment bound on one
target is the following.

> **Conjecture.** Let $`d\ge2`$ and let $`\rho`$ be a probability measure on $`\mathbb R^d`$
> with a log-concave density whose support is a compact convex body. For a probability measure
> $`\mu`$ with finite second moment, let $`T_\mu`$ be the Brenier map from $`\rho`$ to
> $`\mu`$, that is, the optimal transport map for the quadratic cost. Let $`p>2`$ and
> $`\beta\ge0`$, or $`p=2`$ and $`\beta>0`$, and put
>
> ```math
> M_{p,\beta}(\mu)=\int|y|^p[\log(e+|y|)]^\beta\,d\mu(y),\qquad
> \omega_{p,\beta}(\delta)=\delta^{(p-2)/(3p-2)}[\log(e/\delta)]^{-2\beta/(3p-2)}.
> ```
>
> **1. Upper bound.** There are $`C>0`$ and $`0<\delta_0<1`$, depending only on
> $`\rho,p,\beta`$, such that
>
> ```math
> \|T_\mu-T_\nu\|_{L^2(\rho)}\le C\,\omega_{p,\beta}(\delta)
> ```
>
> whenever $`M_{p,\beta}(\mu)\le1`$, $`\nu`$ has finite second moment and
> $`0<\delta=W_2(\mu,\nu)\le\delta_0`$.
>
> **2. Sharpness.** For the uniform source $`\rho_0`$ on $`[0,1]\times[-1,1]^{d-1}`$ there is
> $`c>0`$ such that for every sufficiently small $`\delta>0`$ there are two targets
> $`\mu,\nu`$ with four atoms, both with $`M_{p,\beta}\le1`$, with $`W_2(\mu,\nu)=\delta`$
> and $`\|T_\mu-T_\nu\|_{L^2(\rho_0)}\ge c\,\omega_{p,\beta}(\delta)`$.
>
> **3. Endpoint.** At $`p=2`$, $`\beta=0`$ there is no modulus: for $`\rho_0`$ there are
> four-atom targets with second moments at most $`1`$, with $`W_2(\mu,\nu)`$ arbitrarily
> small and $`\|T_\mu-T_\nu\|_{L^2(\rho_0)}\ge1/20`$.
>
> Here $`W_2`$ is the quadratic Wasserstein distance and logarithms are natural. The moment
> bound is imposed on $`\mu`$ only, and no positive lower bound on the density of $`\rho`$ is
> assumed.

This repository presents a complete Lean proof of this conjecture.

The earlier result of this form requires both targets in a fixed compact set:

| Result | Source $`\rho`$ | Targets | Modulus |
|---|---|---|---|
| [OpenAI (2026)](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/374.md) | uniform on a convex body | both in a fixed compact set | $`\delta^{1/3}`$, sharp |
| **This repository** | **log-concave on a convex body** | **one with $`M_{p,\beta}\le1`$, the other with finite second moment** | **$`\omega_{p,\beta}(\delta)`$, sharp** |

Note that the exponent $`(p-2)/(3p-2)`$ tends to $`1/3`$ as $`p\to\infty`$.

**Main contribution.**

1. **Formal Conjectures statement.**
2. **Lean proof of the conjecture.**

**Subcontribution** (see [Further statements](#further-statements)):

1. **Lean proof that the rate is attained:** on $`\rho_0`$, the same pairs of targets satisfy
   the upper and the lower bound.

<!-- BEGIN PUBLICATION LINKS -->
**Try it in Lean4Web:** [open the complete proof in one file](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fbrenier-moment-stability%2Fmain%2Flean4web%2FBrenierMomentStabilityLean4Web.lean) (Lean **v4.34**).
<!-- END PUBLICATION LINKS -->

## Formal Conjectures target

[FClikelean/BrenierMomentStability.lean](FClikelean/BrenierMomentStability.lean) states the
conjecture with `category research solved, AMS 49 60`. It places OpenAI's compact-target result
immediately before the moment variant, so their changed assumptions and bounds can be compared
directly in Lean. It keeps three shared definitions and writes the source, error and rate inside
the theorem statements.
[BrenierMoment/FCPresentation.lean](lean/BrenierMoment/FCPresentation.lean) proves the three
theorems below. The quotations below use the proof's named definitions; the compact FC file
expands the auxiliary definitions, with equivalent statement types checked by Lean's `rfl`.

### Target theorem: the upper bound

```lean
theorem moment_stability {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUn : U.Nonempty) {V : Space d → ℝ} (hV : ConvexOn ℝ U V)
    {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ μ ν : Measure (Space d), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        moment p β μ ≤ 1 → moment 2 0 ν < ∞ →
        ∃ Tμ Tν : Space d → Space d,
          IsBrenierMap (logConcaveSource U V) μ Tμ ∧
          IsBrenierMap (logConcaveSource U V) ν Tν ∧
          (0 < wasserstein μ ν → wasserstein μ ν ≤ δ₀ →
            mapDist (logConcaveSource U V) Tμ Tν ≤ C * modulus p β (wasserstein μ ν))
```

The source is given by a bounded open convex set `U` and a function `V` that is convex on `U`:
`logConcaveSource U V` is the probability measure on `U` with density proportional to
$`e^{-V}`$. Every log-concave density with bounded support has this form, with `U` the interior
of its support, and the density may tend to zero at the boundary of `U`.
`IsBrenierMap ρ μ T` says that `T` is measurable, pushes `ρ` forward to `μ`, that its graph has
the least quadratic cost among all couplings of `ρ` and `μ`, and that every coupling of no
larger cost is that graph. So the theorem also gives existence and uniqueness of the two maps.
`moment p β μ` is $`M_{p,\beta}(\mu)`$, and `moment 2 0 ν < ∞` says that $`\nu`$ has finite
second moment. `wasserstein` is $`W_2`$, `mapDist ρ` is the distance in $`L^2(\rho)`$ and
`modulus p β` is $`\omega_{p,\beta}`$.

The statement holds in every dimension. The case $`p=2`$, $`\beta=0`$ is included; there
$`\omega_{2,0}=1`$ and the statement is a bound by a constant.

### Target theorem: sharpness

```lean
theorem moment_rate_sharp (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
        HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment p β μ ≤ 1 ∧ moment p β ν ≤ 1 ∧
        IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
        wasserstein μ ν = δ ∧ c * modulus p β δ ≤ mapDist (boxSource d) Tμ Tν
```

`boxSource d` is the uniform probability measure on
$`[0,1]\times[-1,1]^{d+1}\subset\mathbb R^{d+2}`$, so the dimension $`d+2`$ runs over all
dimensions at least two. `HasFourAtoms μ` says that $`\mu`$ is a probability measure with
exactly four atoms. The distance of the two targets is exactly $`\delta`$, for every small
$`\delta`$.

### Target theorem: the endpoint

```lean
theorem no_modulus_at_second_moment (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
      HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment 2 0 μ ≤ 1 ∧ moment 2 0 ν ≤ 1 ∧
      IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
      0 < wasserstein μ ν ∧ wasserstein μ ν < ε ∧ 1 / 20 ≤ mapDist (boxSource d) Tμ Tν
```

### Further statements

These are proved in [lean/](lean/) and are not part of the Formal Conjectures statement.

- `BrenierMoment.moment_rate_two_sided`
  ([TwoSided.lean](lean/BrenierMoment/TwoSided.lean)): on the box source, the pairs of targets
  of the sharpness theorem satisfy
  $`c\,\omega_{p,\beta}(\delta)\le\|T_\mu-T_\nu\|_{L^2(\rho_0)}\le C\,\omega_{p,\beta}(\delta)`$.
  The uniform source on a convex set is the log-concave source with $`V=0`$ on its interior, so
  the upper bound applies to $`\rho_0`$ (`uniformMeasure_eq_logConcaveSource`,
  `moment_stability_uniform`).
- `BrenierMoment.moment_stability_of_goodSource`
  ([MomentStability.lean](lean/BrenierMoment/MomentStability.lean)): the upper bound with the
  constant $`\sqrt{(12dP^2+72dB)\,2^{4/3}+12(3p-2)^\beta+16}`$, where $`P`$ and $`B`$ are the
  constants of steps 2 and 3 below, and with the range
  $`\delta\le\exp(1-(6\beta+2)^2)`$.

## Mathematical explanation (AI generated)

This sketch follows the Lean proof.

**Setting.** A *finite potential* is $`u(x)=\max_i\{\langle x,y_i\rangle+a_i\}`$ with sites
$`y_i\in\mathbb R^d`$. An *active map* of $`u`$ sends every $`x`$ to a site $`y_i`$ at which
the maximum is attained. If an active map pushes $`\rho`$ forward to
$`\mu=\sum_im_i\delta_{y_i}`$, it is the Brenier map from $`\rho`$ to $`\mu`$. The proof first
treats such targets and then passes to limits. Throughout, the source is concentrated on a
bounded open convex set $`U\subset B(0,R)`$.

**1. Potentials for uniform sources.** Let two targets have common masses $`m_i`$ at sites
$`y_i`$ and $`z_i`$, with the points $`(1-t)y_i+tz_i`$ distinct for $`0<t<1`$. For the uniform
source on a convex body of radius $`R`$ there are finite potentials $`u`$ and $`v`$ whose active
maps push the source forward to the two targets, with

```math
\|u-v\|_{L^2(\rho)}^2\le326\,R^2\sum_im_i|y_i-z_i|^2 .
```

The constant depends on neither the dimension nor the body. This is the potential estimate of
OpenAI math: the sites move along the segments, the intercepts follow from the cell-mass
equations, and their velocities are controlled by the cell moments.
[UniformBase.lean](lean/BrenierMoment/UniformBase.lean) repeats that chain so that the
intercepts and the active maps are part of the statement
([PotentialBound.lean](lean/BrenierMoment/PotentialBound.lean)).

**2. Potentials for log-concave sources.** The same estimate holds for the source with density
proportional to $`e^{-V}`$ on $`U`$, with $`326\,(R^2+1)`$ in place of $`326\,R^2`$
(`atomicPotentialBound_logConcave` in [LogConcave.lean](lean/BrenierMoment/LogConcave.lean)).
The steps are:
- **One more coordinate.** For a concave $`h>0`$ on $`U`$, the density $`h^{r+1}`$ on $`U`$ is
  the marginal of the density $`h^r`$ on the region $`\{(x,t):x\in U,\ 0<t<h(x)\}`$, which is
  convex and one dimension higher. A finite potential whose sites have last coordinate zero does
  not depend on the last coordinate, so the estimate descends to the marginal
  ([LastCoordinate.lean](lean/BrenierMoment/LastCoordinate.lean), `of_marginal` in
  [PotentialBound.lean](lean/BrenierMoment/PotentialBound.lean)).
- **Induction.** By induction on $`r`$, the estimate for uniform sources gives the estimate for
  the density $`h^r`$. The source does not change when $`h`$ is multiplied by a constant. If
  $`h\le1/\sqrt r`$, the region after $`r`$ steps lies in $`B(0,\sqrt{R^2+1})`$, so the
  constant does not depend on $`r`$ ([PowerSource.lean](lean/BrenierMoment/PowerSource.lean)).
- **Limit.** Take $`h=1-V/n`$ on $`\{V<n\}`$ and $`r=n`$. Then
  $`(1-V/n)^n\le e^{-V}`$ and $`(1-V/n)^n\to e^{-V}`$, so each of these sources is at most a
  multiple $`c_n`$ of the log-concave source, with $`c_n\to1`$. This gives convergence in total
  variation, and the estimate passes to the limit
  ([PotentialBoundLimit.lean](lean/BrenierMoment/PotentialBoundLimit.lean)). A convex function
  on a bounded open convex set is bounded below, so $`V\ge0`$ can be assumed.

**3. Interpolation with tails.** Write $`\mathrm{clip}_H`$ for the truncation of a real number
to $`[-H,H]`$, applied to each coordinate of a vector. Let $`T`$ and $`S`$ be active maps of
finite potentials $`u`$ and $`v`$. For every $`H\ge0`$ and $`h>0`$,

```math
\int|\mathrm{clip}_H T-\mathrm{clip}_H S|^2\,d\rho
\le\frac{4d}{h^2}\int(u-v)^2\,d\rho+24\,d\,H^2h\,B
```

(`clipped_interpolation_of_active` in [ActiveMaps.lean](lean/BrenierMoment/ActiveMaps.lean)).
Here $`B`$ depends only on the source. The steps are:
- **A pointwise inequality.** The slope of a convex function lies between its backward and
  forward difference quotients. The clipped slopes of $`u`$ and $`v`$ therefore differ by at
  most the difference quotient of $`u-v`$, up to the variation of the clipped quotients over one
  step. The slopes are clipped inside this inequality, so no bound on $`T`$ or $`S`$ is used
  ([Clip.lean](lean/BrenierMoment/Clip.lean),
  [ClipSlack.lean](lean/BrenierMoment/ClipSlack.lean)).
- **On a line.** Integrated over an interval, the variations telescope and contribute at most
  $`24H^2h`$, whatever the length of the interval
  ([LineInterpolation.lean](lean/BrenierMoment/LineInterpolation.lean)).
- **By slices.** A set whose slices along a coordinate are intervals is treated slice by slice
  ([CoordSlices.lean](lean/BrenierMoment/CoordSlices.lean)).
- **With the density.** The weighted source is the marginal of Lebesgue measure on the region
  under the graph of $`e^{-V}`$. The slices of this region along a coordinate of $`U`$ are
  slices of the convex sets $`\{e^{-V}>s\}`$, hence intervals. The density is never compared at
  two points ([SourceInterpolation.lean](lean/BrenierMoment/SourceInterpolation.lean),
  [StripInterpolation.lean](lean/BrenierMoment/StripInterpolation.lean)).

**4. Brenier maps for targets with finite second moment.** Every target $`\mu`$ with finite
second moment has a Brenier map from $`\rho`$, and this map is a limit in $`L^2(\rho)`$ of
active maps (`exists_optimal_map_with_approximation` in
[MomentStability.lean](lean/BrenierMoment/MomentStability.lean)). No limit potential is
constructed. The steps are:
**Couplings against an active map.** Let $`T`$ be an active map of $`u`$ and let $`\pi`$ be a
coupling with first marginal $`\rho`$. The cost of comparing $`\pi`$ with the graph of $`T`$
is controlled by the Fenchel gap of $`u`$ integrated over $`\pi`$:

```math
\int|\mathrm{clip}_H y-\mathrm{clip}_H T(x)|^2\,d\pi(x,y)
\le24\,d\,H^2h\,B+\frac{4dH}{h}\int\bigl(u(x)+u^*(y)-\langle x,y\rangle\bigr)\,d\pi(x,y),
```

where $`u^*`$ is the conjugate of $`u`$ over the closure of $`U`$. This is step 3 with the
supporting slope $`y`$ in place of a second active map, applied to the conditional laws of
$`\pi`$ ([PlanComparison.lean](lean/BrenierMoment/PlanComparison.lean)).

**Uniqueness.** Let active maps $`T_n`$ converge to $`T`$ in $`L^2(\rho)`$. A coupling of
$`\rho`$ and $`T_\#\rho`$ whose cost is at most that of the graph of $`T`$ has integrated gap
at most that of the graph, which tends to zero. Letting $`n\to\infty`$ and then $`h\to0`$
shows that the coupling is the graph of $`T`$. Hence $`T`$ is the Brenier map onto its law
([LimitCertificate.lean](lean/BrenierMoment/LimitCertificate.lean)).

**Existence.** The images of $`\mu`$ under simple functions that converge to the identity are
finite targets. Their Brenier maps are active maps
([FiniteTargets.lean](lean/BrenierMoment/FiniteTargets.lean)). By steps 2 and 3 and a tail
bound they form a Cauchy sequence in $`L^2(\rho)`$, and the limit pushes $`\rho`$ forward to
$`\mu`$ ([GeneralTargets.lean](lean/BrenierMoment/GeneralTargets.lean)).

**5. The rate.** Put $`\delta=W_2(\mu,\nu)`$ and
$`\tau_\mu(H)=\int_{|y|>H}|y|^2\,d\mu(y)`$. Steps 2 to 4 give, for every $`H>0`$ and $`h>0`$,

```math
\|T_\mu-T_\nu\|_{L^2(\rho)}^2
\le3\Bigl(\frac{4dP^2}{h^2}\,\delta^2+24\,d\,H^2h\,B\Bigr)+3\bigl(\tau_\mu(H)+\tau_\nu(H)\bigr),
```

with $`P^2=326\,(R^2+1)`$ (`sq_mapL2Dist_le_of_limits`). The remaining steps are scalar:
- **The step.** With $`h=(\delta/H)^{2/3}`$ the first bracket is
  $`(4dP^2+24dB)\,\delta^{2/3}H^{4/3}`$.
- **One-sided tails.** A coupling of the targets gives
  $`\tau_\nu(2H)\le4\delta^2+2\tau_\mu(H)`$, so only the tail of $`\mu`$ remains
  ([Tails.lean](lean/BrenierMoment/Tails.lean),
  [OneSided.lean](lean/BrenierMoment/OneSided.lean)).
- **The moment.** $`M_{p,\beta}(\mu)\le1`$ gives
  $`\tau_\mu(H)\le H^{2-p}[\log(e+H)]^{-\beta}`$
  ([MomentTail.lean](lean/BrenierMoment/MomentTail.lean)).
- **The threshold.** The value $`H=\delta^{-2/D}\ell^{-3\beta/D}`$ with $`D=3p-2`$ and
  $`\ell=\log(e/\delta)`$ is substituted, and the powers are compared after taking logarithms
  ([Threshold.lean](lean/BrenierMoment/Threshold.lean)).

This proves the upper bound ([UpperBound.lean](lean/BrenierMoment/UpperBound.lean)).

**6. Sharpness.** On the box source, take the maximum of four affine functions with slopes
$`0,R_*,2R_*,3R_*`$ in the first coordinate, and tilt the third one in the second coordinate.
The four cells have masses $`1-3a,a,a,a`$ with and without the tilt, and the tilt moves one
atom of the target. The steps are:
- **Cells.** The active plane is given by an explicit selector, and the cell masses are
  computed by slices ([FourCellGeometry.lean](lean/BrenierMoment/FourCellGeometry.lean),
  [FourCellSlices.lean](lean/BrenierMoment/FourCellSlices.lean),
  [CoordBox.lean](lean/BrenierMoment/CoordBox.lean)).
- **Distances.** The two maps are Brenier maps by the finite potential. The distance of the
  targets is computed exactly, and the distance of the maps is bounded below on the strip where
  the two selectors differ ([FourAtomSharp.lean](lean/BrenierMoment/FourAtomSharp.lean)).
- **Parameters.** For a given $`\delta`$ the cell mass is set to
  $`a=\kappa\,\delta^{2p/D}\ell^{2\beta/D}`$ and the slope to $`R_*=4\delta/a^{3/2}`$. Then
  $`W_2=\delta`$ holds identically, the lower bound is $`2\delta/a=(2/\kappa)\,\omega_{p,\beta}(\delta)`$,
  and it remains to check the two moments. No intermediate value argument is needed
  ([SharpRate.lean](lean/BrenierMoment/SharpRate.lean),
  [Sharpness.lean](lean/BrenierMoment/Sharpness.lean)).

At $`p=2`$, $`\beta=0`$ the same family with $`R_*=1/(10\sqrt a)`$ has $`W_2=a/40`$ and map
distance at least $`1/20`$.

**7. The Mathlib-only statements.** The definitions of
[Presentation/Model.lean](lean/BrenierMoment/Presentation/Model.lean) use Mathlib alone. They
unfold to the definitions used in the proof, and the box of the statement is the box of step 6
([FCPresentation.lean](lean/BrenierMoment/FCPresentation.lean)).

**In Lean.** The main choices are:
- the potential estimate with the potentials and maps as data, so that it descends to marginals;
- lifting by one coordinate, for the potential estimate and for the interpolation, instead of a
  weighted midpoint coupling and weighted cell calculus;
- Brenier maps as limits of active maps, with uniqueness from the Fenchel gap of couplings,
  instead of limits of potentials;
- explicit values of the step, the threshold and the sharpness parameters;
- a statement that uses only Mathlib.

Step 1 and the finite optimal couplings of step 4 rest on the development of OpenAI math. The
proof imports 76 of its files, next to the 36 modules of this project.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.34.1` | Complete proof: Mathlib `d13f23b7`, with the adapted files of OpenAI math `fd4aeeb2` that it uses. Includes the Comparator challenge |
| [leanWithoutComparator/](leanWithoutComparator/) | `v4.34.1` | The same proof files without the Comparator challenge, checked byte for byte against `lean/` |
| [lean4web/](lean4web/) | `v4.34.1` | Complete proof in one Mathlib-only file, including the files of OpenAI math |
| [FClikelean/](FClikelean/) | FC `v4.33.1` | Formal Conjectures statement |
| [PDF/](PDF/) | — | Manuscript, with an OpenTimestamps proof (`.ots`) |
| [comparator/](comparator/) | Checks the proof with `v4.34.1` | Input pins, comparison scripts, runner preparation and verification guide |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Comparator verification workflow |
| [docs/](docs/) | — | Scope of each check and third-party sources |

Inside [lean/BrenierMoment/](lean/BrenierMoment/):

| Path | Content |
|---|---|
| `UpperBound.lean`, `Sharpness.lean`, `TwoSided.lean` | The final theorems |
| `Presentation/Model.lean`, `FCPresentation.lean` | Definitions of the Formal Conjectures statement and its proof from the final theorems |
| `UniformBase.lean`, `PotentialBound.lean` | The potential estimate for uniform sources, in explicit form |
| `LastCoordinate.lean`, `PowerSource.lean`, `PotentialBoundLimit.lean`, `LogConcave.lean` | The potential estimate for log-concave sources |
| `Clip.lean`, `ClipSlack.lean`, `LineInterpolation.lean`, `CoordSlices.lean`, `SourceInterpolation.lean`, `StripInterpolation.lean`, `ActiveMaps.lean` | Interpolation with tails |
| `PlanComparison.lean`, `LimitCertificate.lean`, `FiniteTargets.lean`, `GeneralTargets.lean` | Brenier maps for targets with finite second moment |
| `Tails.lean`, `MomentTail.lean`, `Threshold.lean`, `OneSided.lean`, `MomentStability.lean` | The rate |
| `FourCellGeometry.lean`, `FourCellSlices.lean`, `CoordBox.lean`, `FourAtomTargets.lean`, `FourAtomSharp.lean`, `SharpRate.lean` | The four-atom example |
| `MomentP4.lean`, `BalanceP4.lean` | Earlier special cases at $`p=4`$ |

The project has 36 modules, about 8,800 lines. The adapted sources in
[lean/vendor/](lean/vendor/) are 90 files, about 33,400 lines: the 89 files of the Brenier
development of OpenAI math and one file that combines four of them. The proof imports 76 of
the 90.

## Verification

```bash
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

The final theorems depend only on `[propext, Classical.choice, Quot.sound]`.
`python3 lean/scripts/verify.py` runs the build, checks this for every theorem listed in
[Audit.lean](lean/Audit.lean) and [FCAudit.lean](lean/FCAudit.lean), compares the three
statements and their definitions with the Comparator challenge, and records its results in
[lean/verification/](lean/verification/).

Further checks, run from the repository root unless noted:

```bash
(cd lean && lake env lean --run scripts/Replay.lean)
python3 lean/scripts/verify_lean4web.py
python3 lean/scripts/verify_lean_without_comparator.py
python3 lean/scripts/check_publication.py
```

They replay every declaration in a fresh environment, compile the one-file proof, check the
copy without Comparator files, and check that the Formal Conjectures statement agrees with the
proof. [lean4web/README.md](lean4web/README.md) describes how the one-file proof is compared
with the challenge.

<!-- BEGIN VERIFICATION STATUS -->
**Checks run so far (12 and 13 October 2026).** The 129 Lean files of `lean/` outside
`scripts/` have been compiled, one module at a time, by `lean` against a cache of the pinned
Mathlib; only the challenge contains `sorry`. The reports of
`Audit.lean` (52 declarations) and `FCAudit.lean` (6 declarations) list only the three axioms
([local-build.json](lean/verification/local-build.json)). The three targets and all the
definitions they use are equal in the compiled challenge and the compiled solution
([local-statement.json](lean/verification/local-statement.json)). The one-file proof has been
compiled in the same way, without error, and its three targets agree with the challenge
([local-verification.json](lean4web/local-verification.json)). The source-level checks, the
copy check, the publication check and the Comparator input check pass.

**Public CI (30 October 2026): passed.** The proof build, compact FC-model comparison,
sandboxed Lean Comparator, six target axiom reports and whole-environment fresh replay all
passed in [run 40978788813](https://github.com/KitaKen1/brenier-moment-stability/actions/runs/40978788813),
testing commit `4871736bc0c348fd9e6a25d2f0e6e28892dbeeba`.
The proof source commit is `c028b1a002da7ef4bf9177a3b4abcf596a6ab1b3`.
The original logs and artifacts are preserved in
[ComparatorLog20261030](ComparatorLog20261030/40978788813-attempt1/).

**Separate checks still pending:** the complete standalone verification workflows, hosted
Lean4Web and upstream FC checkout compatibility; see the
[Appendix](#appendix-verification-by-lean-comparator-on-github-ci-runner).
<!-- END VERIFICATION STATUS -->

[docs/verification.md](docs/verification.md) lists what each check covers and which checks
have been run.

## Status boundary

Proved here, for every bounded nonempty open convex set $`U\subset\mathbb R^d`$, every convex
$`V`$ on $`U`$, and all $`p\ge2`$, $`\beta\ge0`$:

```text
Existence and uniqueness of the Brenier map from the source to every target with finite second moment.
The upper bound C ω(δ) for δ = W₂(μ, ν) ≤ exp(1 − (6β + 2)²), with the moment bound on μ only.
The lower bound c ω(δ) on the box source, for every small δ, with W₂ = δ exactly.
Both bounds for the same pairs of targets on the box source.
No modulus at p = 2, β = 0: map distance at least 1/20 with W₂ arbitrarily small.
```

The following are not claimed or not formalized:
- **Constants.** The constant of the upper bound is explicit in terms of the dimension, the
  radius of $`U`$ and a constant $`B`$ of the source, but it is not optimized, and the lower
  bound is not proved for each individual source.
- **Manuscript.** The Lean proof follows the strategy of the manuscript in [PDF/](PDF/), but it
  does not formalize the manuscript statement by statement. The weighted midpoint coupling and
  the limit potentials of the manuscript are replaced by steps 2 and 4. The tail estimate of the
  manuscript for every threshold appears with an explicit step in step 5, its corollary for
  compactly supported targets is not stated, and the trivial upper bound at $`p=2`$,
  $`\beta=0`$ is not stated.
- **Regularity.** Nothing is proved about the regularity of Brenier maps, and they are not
  identified with gradients of convex functions.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from AI tools, including Claude Code using Claude Opus 5.5.

## Sources

- [Br91] Y. Brenier, Polar factorization and monotone rearrangement of vector-valued functions,
  Comm. Pure Appl. Math. 44 (1991), 375–417: existence and uniqueness of the optimal map.
- [MDC20] Q. Mérigot, A. Delalande and F. Chazal,
  [Quantitative stability of optimal transport maps and linearization of the 2-Wasserstein space](https://proceedings.mlr.press/v108/merigot20a.html),
  AISTATS 2020: dimension-independent stability; Remark 3.1 leaves the optimal exponent open.
- [DM23] A. Delalande and Q. Mérigot,
  [Quantitative stability of optimal transport maps under variations of the target measure](https://arxiv.org/abs/2103.05934),
  Duke Math. J. 172 (2023): quantitative stability of optimal transport maps with respect to
  the target.
- [LM24] C. Letrouit and Q. Mérigot,
  [Gluing methods for quantitative stability of optimal transport maps](https://arxiv.org/abs/2411.04908),
  arXiv:2411.04908 (2024).
- [L26] C. Letrouit,
  [Unstable optimal transport maps](https://comptes-rendus.academie-sciences.fr/mathematique/articles/10.5802/crmath.834/),
  Comptes Rendus. Mathématique 364 (2026), 333–344: Conjecture 3 states uniform square-root
  stability in $`W_2`$ for a uniform convex source and compact targets.
- [Ruan26] Y. Ruan,
  [Sharp conditioning and quantitative stability of optimal transport](https://arxiv.org/abs/2610.07577),
  arXiv:2610.07577 (2026).
- [OpenAI math](https://github.com/openai/math) (revision `fd4aeeb2`, Apache 2.0): stability
  with exponent $`1/3`$ for uniform sources and compact targets
  ([result 374](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/374.md)).
  The proof depends on its Lean development of finite transport cells, potentials and optimal
  couplings, and the Lean4Web file includes it.
- [Mathlib](https://github.com/leanprover-community/mathlib4).
- [Lean Comparator](https://github.com/leanprover/comparator/tree/ca04cfc72b550331658ec314bf47685281bfd4bf),
  at the pinned revision.

The files of OpenAI math are adapted, not verbatim; the changes and the original license are in
[lean/vendor/](lean/vendor/) and [lean/VENDOR.json](lean/VENDOR.json); see [NOTICE](NOTICE) and
[docs/third-party.md](docs/third-party.md).

## Appendix: timeline

The stability problem predates OpenAI's result. Letrouit's Conjecture 3 is the explicit
square-root conjecture used here as the reference problem.

| Date | Contributor | Problem or result |
|---|---|---|
| 2020 | Quentin Mérigot, Alex Delalande and Frédéric Chazal | **Progress and open question:** proved a target-uniform $`W_1^{2/15}`$ stability bound for a uniform convex source and compact targets. The optimal exponent remained open ([Remark 3.1](https://proceedings.mlr.press/v108/merigot20a/merigot20a.pdf#page=4)). |
| 2023 | Alex Delalande and Quentin Mérigot | **Progress:** obtained a $`W_1^{1/6}`$ map bound for compact targets, and treated unbounded targets under moment bounds, for source densities bounded above and below on a compact convex set ([paper](https://arxiv.org/abs/2103.05934v2)). |
| May 2026 | Cyril Letrouit | **Explicit conjecture:** for a uniform convex source and targets in a fixed compact set, asked whether $`\|T_\mu-T_\nu\|_{L^2(\rho)}\le C W_2(\mu,\nu)^{1/2}`$ holds uniformly ([Conjecture 3, §1.2, p. 335](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.5802/crmath.834.pdf#page=4)). |
| September 2026 (manuscript date) | OpenAI | **Resolution:** disproved the square-root conjecture using three-atom targets on a fixed cube, and proved the matching uniform $`W_2^{1/3}`$ bound. Thus $`1/3`$ is the optimal exponent in this source class ([manuscript](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf), [Lean result 374](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/374.md)). |
| October 2026 | This work | **Moment extension:** replaces the common compact target set by a power-logarithmic moment bound on one target, allows log-concave sources, and formalizes the upper bound, matching four-atom examples and the second-moment endpoint ([Lean statements and proofs](lean/BrenierMoment/FCPresentation.lean)). |

The original conjecture was resolved by a counterexample, together with a sharp replacement
bound. The moment statement at the start of this README is the extension treated in this work.

## Appendix: comparison of the problem settings

Both settings fix a source distribution and ask how its optimal transport map changes when
the **target distribution** changes. The source and target assumptions are compared first;
the two statements are then placed side by side.

| Setting | Original problem: Letrouit's Conjecture 3 | This work |
|---|---|---|
| Source distribution | Uniform on a compact convex body | Log-concave density with bounded convex support, including uniform densities; no positive lower bound on the density is required |
| Target distributions | Both lie in one fixed compact set $`Y`$ | May have unbounded supports; one satisfies $`M_{p,\beta}\le1`$, the other has finite second moment |
| Control on distant mass | All mass must stay inside the prescribed set $`Y`$ | Distant mass is allowed, with a bound on its weighted average distance for one target |
| Quantity being compared | The difference of the two Brenier maps in $`L^2(\rho)`$ | The same difference, measured in the same way |
| Uniformity | One constant for every pair of targets in $`Y`$ | One constant and one distance threshold for every pair satisfying the moment conditions |
| Question | Does the square-root bound hold uniformly? | What is the optimal uniform bound under the moment conditions, and when does it tend to zero? |

Write $`\delta=W_2(\mu,\nu)`$ for the quadratic Wasserstein distance between the targets.
For $`p\ge2`$ and $`\beta\ge0`$, the moment and the scale of the bound in this work are

```math
M_{p,\beta}(\mu)=\int |y|^p[\log(e+|y|)]^\beta\,d\mu(y),\qquad
\omega_{p,\beta}(\delta)=\delta^{(p-2)/(3p-2)}[\log(e/\delta)]^{-2\beta/(3p-2)}.
```

### Problem statements in natural language

Here, an optimal map minimizes the mean squared transport distance. Its change is the
root mean square of the difference between the two destinations of each source point.

| Original statement: the square-root conjecture | This work: the upper-bound theorem |
|---|---|
| Fix the uniform probability distribution on a compact convex body of positive volume, and fix a compact set for the targets. Then there is a positive constant, depending only on the source and this target set, such that for **any two probability distributions supported in that set**, the difference of their optimal maps is at most the constant times the **square root of the Wasserstein distance between the targets**. Thus the same square-root estimate holds for every target pair. | Fix a probability distribution with a log-concave density on a bounded convex support, and fix the moment orders $`p\ge2`$ and $`\beta\ge0`$. Then there are a positive constant and a positive distance threshold below one, depending only on the source and these orders. For **any two target probability distributions**, if **one has power-logarithmic moment at most one** and **the other has finite second moment**, their optimal maps exist. Whenever their Wasserstein distance $`\delta`$ is positive and at most the threshold, the difference of the maps is at most the constant times $`\omega_{p,\beta}(\delta)`$. Thus the same moment-dependent estimate holds for every admissible target pair, without a common bound on their support radius. |

The original statement is [Letrouit's Conjecture 3](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.5802/crmath.834.pdf#page=4).
OpenAI disproved it and established the sharp replacement $`C\delta^{1/3}`$ in the original
setting. The statement on the right is proved by
[`moment_stability`](lean/BrenierMoment/FCPresentation.lean). This work also proves matching
four-atom examples on a fixed box source and shows that a second-moment bound alone gives no
vanishing uniform modulus.

**Scope of the extension.** This work treats a broader class of sources and targets: uniform
convex sources are log-concave, and compactly supported targets have bounded power-logarithmic
moments. After normalizing a fixed moment budget, these targets fit the moment framework, which
also permits unbounded supports. The conclusion changes with this broader setting: for finite
$`p`$, the power exponent $`(p-2)/(3p-2)`$ is below $`1/3`$. It tends to $`1/3`$ as
$`p\to\infty`$. At $`p=2,\beta=0`$ there is no vanishing uniform modulus; a positive logarithmic
weight $`\beta>0`$ restores one.

## Appendix: Verification by Lean Comparator on GitHub CI runner

Lean Comparator checks the theorem statements and dependent definitions against the challenge,
audits permitted axioms and verifies kernel acceptance.

GitHub CI runs checks in a fresh environment and records their results;
pinned inputs support reproducibility.

The verification target is in
[ComparatorChallenges/BrenierMomentStability.lean](lean/ComparatorChallenges/BrenierMomentStability.lean),
and the proof is in [BrenierMoment/FCPresentation.lean](lean/BrenierMoment/FCPresentation.lean).
The challenge states `BrenierStability.moment_stability`, `BrenierStability.moment_rate_sharp`
and `BrenierStability.no_modulus_at_second_moment` with the definitions of the Formal
Conjectures statement, and it imports only Mathlib.

Lean Comparator and GitHub CI enable the following:

- **Verification in a web browser (within 90 days):** see [CI results](#certification-within-90-days-ci-results).
- **Verification from an archive (after 90 days):** see [archived records](#certification-after-90-days-archive).
- **Regenerate and verify the results yourself:** see [how to run the checks on your own CI runner](#reproduce-the-verification).

### Certification Within 90 days: CI results

The public verification workflow [passed on 30 October 2026](https://github.com/KitaKen1/brenier-moment-stability/actions/runs/40978788813),
testing commit `4871736bc0c348fd9e6a25d2f0e6e28892dbeeba`. All required jobs succeeded:
the proof build, Comparator, whole-environment fresh replay and final verification gate.

Readers can inspect the Comparator execution and the axiom audit in the public CI logs.
The `#print axioms` reports contain the three axioms for each target:

```text
'BrenierStability.moment_stability' depends on axioms: [propext, Classical.choice, Quot.sound]
'BrenierStability.moment_rate_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'BrenierStability.no_modulus_at_second_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Certification After 90 days: archive

After the [90-day retention period](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/download-workflow-artifacts)
for CI logs and artifacts expires, readers can inspect the same results in
[ComparatorLog20261030/40978788813-attempt1](ComparatorLog20261030/40978788813-attempt1/).
The archive contains the original logs and artifact ZIPs, extracted receipts, API metadata and
SHA-256 checksums. Each artifact ZIP was checked against its GitHub digest before extraction.
The archive was added in [commit `ab8cd03a`](https://github.com/KitaKen1/brenier-moment-stability/commit/ab8cd03a24bc5ddd30e0e5c6c9c49ac181afcbdc).

### Reproduce the verification

To run the verification yourself, clone the repository, push it to a GitHub repository
you control, and run the [verification workflow](.github/workflows/comparator.yml) from
**Actions → Run workflow**. Your CI runner executes the same checks; compare the Comparator
result and the three-axiom output with the lines above.
Setup and commands are in [comparator/README.md](comparator/README.md).
