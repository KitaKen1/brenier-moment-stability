import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity

namespace BrenierStability

noncomputable section
open MeasureTheory
open scoped ENNReal

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

/-- Moment stability of Brenier maps. Let $U \subset \mathbb{R}^d$ be bounded, open, convex and
nonempty, let $V$ be convex on $U$, and let $\rho$ be the probability measure on $U$ with density
proportional to $e^{-V}$. Let $p \ge 2$ and $\beta \ge 0$. There are $C > 0$ and
$0 < \delta_0 < 1$ such that, for every probability measure $\mu$ with $M_{p,\beta}(\mu) \le 1$
and every probability measure $\nu$ with finite second moment, there are Brenier maps $T_\mu$
and $T_\nu$ from $\rho$ to $\mu$ and to $\nu$, and
$\|T_\mu - T_\nu\|_{L^2(\rho)} \le C\,\omega_{p,\beta}(\delta)$ whenever
$0 < \delta = W_2(\mu, \nu) \le \delta_0$. -/
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
            mapDist (logConcaveSource U V) Tμ Tν ≤ C * modulus p β (wasserstein μ ν)) := by
  sorry

/-- Sharpness of the modulus. Let $\rho_0$ be the uniform probability measure on
$[0,1] \times [-1,1]^{d+1} \subset \mathbb{R}^{d+2}$, and let $p \ge 2$, $\beta \ge 0$. There are
$c > 0$ and $\delta_1 > 0$ such that for every $0 < \delta \le \delta_1$ there are two measures
$\mu$ and $\nu$ with four atoms, with $M_{p,\beta}(\mu) \le 1$, $M_{p,\beta}(\nu) \le 1$ and
$W_2(\mu, \nu) = \delta$, whose Brenier maps from $\rho_0$ satisfy
$\|T_\mu - T_\nu\|_{L^2(\rho_0)} \ge c\,\omega_{p,\beta}(\delta)$. -/
theorem moment_rate_sharp (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
        HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment p β μ ≤ 1 ∧ moment p β ν ≤ 1 ∧
        IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
        wasserstein μ ν = δ ∧ c * modulus p β δ ≤ mapDist (boxSource d) Tμ Tν := by
  sorry

/-- No modulus at the second moment. Let $\rho_0$ be the uniform probability measure on
$[0,1] \times [-1,1]^{d+1} \subset \mathbb{R}^{d+2}$. For every $\varepsilon > 0$ there are two
measures $\mu$ and $\nu$ with four atoms and second moments at most $1$ such that
$0 < W_2(\mu, \nu) < \varepsilon$ and the Brenier maps from $\rho_0$ satisfy
$\|T_\mu - T_\nu\|_{L^2(\rho_0)} \ge 1/20$. -/
theorem no_modulus_at_second_moment (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
      HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment 2 0 μ ≤ 1 ∧ moment 2 0 ν ≤ 1 ∧
      IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
      0 < wasserstein μ ν ∧ wasserstein μ ν < ε ∧ 1 / 20 ≤ mapDist (boxSource d) Tμ Tν := by
  sorry

end

end BrenierStability
