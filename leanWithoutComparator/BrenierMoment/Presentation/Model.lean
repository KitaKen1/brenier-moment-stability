module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

/-!
# Moment stability of Brenier maps: a Mathlib-only statement vocabulary

Self-contained definitions for the statements of `FCPresentation.lean`: couplings, the
quadratic Wasserstein distance, Brenier maps, log-concave sources, the power-logarithmic
moment and the modulus. Nothing here depends on the proof or on the upstream development.

The definitions of couplings, the quadratic cost, the Wasserstein distance, optimal maps and the
distance of maps follow `OAI.Problem358` in openai/math, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0; see vendor/openai/LICENSE).

The block between the two markers is the whole statement vocabulary. It is repeated verbatim in
`ComparatorChallenges/BrenierMomentStability.lean`; `scripts/verify.py` checks the two copies.
-/

namespace BrenierStability

noncomputable section
open MeasureTheory
open scoped ENNReal

-- BEGIN MODEL
/-- The Euclidean space $\mathbb{R}^d$. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A coupling of $\mu$ and $\nu$: a probability measure on the product with marginals $\mu$
and $\nu$. -/
def IsCoupling {d : ℕ} (μ ν : Measure (Space d)) (π : Measure (Space d × Space d)) : Prop :=
  IsProbabilityMeasure π ∧ Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν

/-- The quadratic cost $\int |x - y|^2 \, d\pi(x, y)$ of a measure on the product. -/
def cost {d : ℕ} (π : Measure (Space d × Space d)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π

/-- The quadratic Wasserstein distance $W_2(\mu, \nu)$: the square root of the infimum of the
quadratic cost over all couplings of $\mu$ and $\nu$. -/
def wasserstein {d : ℕ} (μ ν : Measure (Space d)) : ℝ :=
  Real.sqrt (ENNReal.toReal (sInf {r : ℝ≥0∞ |
    ∃ π : Measure (Space d × Space d), IsCoupling μ ν π ∧ cost π = r}))

/-- The measure $(\mathrm{id}, T)_\# \rho$ carried by the graph of $T$. -/
def graph {d : ℕ} (ρ : Measure (Space d)) (T : Space d → Space d) : Measure (Space d × Space d) :=
  Measure.map (fun x => (x, T x)) ρ

/-- $T$ is the Brenier map from $\rho$ to $\mu$: it is measurable, it pushes $\rho$ forward to
$\mu$, its graph has the least quadratic cost among all couplings of $\rho$ and $\mu$, and every
coupling of no larger cost is that graph. -/
def IsBrenierMap {d : ℕ} (ρ μ : Measure (Space d)) (T : Space d → Space d) : Prop :=
  (Measurable T ∧ Measure.map T ρ = μ ∧
    ∀ π : Measure (Space d × Space d), IsCoupling ρ μ π → cost (graph ρ T) ≤ cost π) ∧
  ∀ π : Measure (Space d × Space d), IsCoupling ρ μ π → cost π ≤ cost (graph ρ T) → π = graph ρ T

/-- The distance $\|T - S\|_{L^2(\rho)}$ of two maps. -/
def mapDist {d : ℕ} (ρ : Measure (Space d)) (T S : Space d → Space d) : ℝ :=
  Real.sqrt (∫ x, ‖T x - S x‖ ^ 2 ∂ρ)

/-- The probability measure on $U$ whose density with respect to Lebesgue measure is
proportional to $e^{-V}$. -/
def logConcaveSource {d : ℕ} (U : Set (Space d)) (V : Space d → ℝ) : Measure (Space d) :=
  let m : Measure (Space d) :=
    (volume.restrict U).withDensity fun x => ENNReal.ofReal (Real.exp (-V x))
  (m Set.univ)⁻¹ • m

/-- The power-logarithmic moment
$M_{p,\beta}(\mu) = \int |y|^p [\log(e + |y|)]^\beta \, d\mu(y)$. In particular
$M_{2,0}(\mu)$ is the second moment of $\mu$. -/
def moment {d : ℕ} (p β : ℝ) (μ : Measure (Space d)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖y‖ ^ p * Real.log (Real.exp 1 + ‖y‖) ^ β) ∂μ

/-- The modulus
$\omega_{p,\beta}(\delta) = \delta^{(p-2)/(3p-2)} [\log(e/\delta)]^{-2\beta/(3p-2)}$. -/
def modulus (p β δ : ℝ) : ℝ :=
  δ ^ ((p - 2) / (3 * p - 2)) * Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2))

/-- The box $[0,1] \times [-1,1]^{d+1}$ in $\mathbb{R}^{d+2}$. -/
def box (d : ℕ) : Set (Space (d + 2)) :=
  {x | x 0 ∈ Set.Icc 0 1 ∧ ∀ i, x i ∈ Set.Icc (-1) 1}

/-- The uniform probability measure on the box $[0,1] \times [-1,1]^{d+1}$. -/
def boxSource (d : ℕ) : Measure (Space (d + 2)) :=
  (volume (box d))⁻¹ • volume.restrict (box d)

/-- A probability measure with exactly four atoms. -/
def HasFourAtoms {d : ℕ} (μ : Measure (Space d)) : Prop :=
  ∃ y : Fin 4 → Space d, Function.Injective y ∧
    ∃ w : Fin 4 → ℝ≥0∞, (∀ k, 0 < w k) ∧ (∑ k, w k) = 1 ∧
      μ = ∑ k, w k • Measure.dirac (y k)
-- END MODEL

end

end BrenierStability
