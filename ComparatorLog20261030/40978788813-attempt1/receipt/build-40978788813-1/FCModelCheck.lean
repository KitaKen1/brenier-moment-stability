import BrenierMoment.Presentation.Model
import OAI.Analysis.Brenier.Stability

namespace BrenierFCCheck
noncomputable section
open MeasureTheory
open scoped ENNReal

/-- The quadratic Wasserstein distance $W_2(\mu,\nu)$. -/
def wasserstein {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d))) : ℝ :=
  Real.sqrt (ENNReal.toReal (sInf {r : ℝ≥0∞ |
    ∃ π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)), (IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν) ∧
      (∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π) = r}))

/-- A measurable transport map whose graph is the unique optimal quadratic coupling. -/
def IsBrenierMap {d : ℕ} (ρ μ : Measure (EuclideanSpace ℝ (Fin d))) (T : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  let cost (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
    ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π
  let graph := Measure.map (fun x => (x, T x)) ρ
  let coupling (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d))) : Prop :=
    IsProbabilityMeasure π ∧ Measure.map Prod.fst π = ρ ∧ Measure.map Prod.snd π = μ
  (Measurable T ∧ Measure.map T ρ = μ ∧
    ∀ π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)), coupling π → cost graph ≤ cost π) ∧
  ∀ π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)), coupling π → cost π ≤ cost graph → π = graph

/-- The moment $\int |y|^p[\log(e+|y|)]^\beta\,d\mu(y)$. -/
def moment {d : ℕ} (p β : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖y‖ ^ p * Real.log (Real.exp 1 + ‖y‖) ^ β) ∂μ


def fcCheck_moment_stability {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUn : U.Nonempty) {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ConvexOn ℝ U V)
    {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) : Prop :=
    let m : Measure (EuclideanSpace ℝ (Fin d)) :=
      (volume.restrict U).withDensity fun x => ENNReal.ofReal (Real.exp (-V x))
    let ρ := (m Set.univ)⁻¹ • m
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ μ ν : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        moment p β μ ≤ 1 → moment 2 0 ν < ∞ →
        ∃ Tμ Tν : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          IsBrenierMap ρ μ Tμ ∧
          IsBrenierMap ρ ν Tν ∧
          (let δ := wasserstein μ ν
           0 < δ → δ ≤ δ₀ →
            Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ) ≤ C * (δ ^ ((p - 2) / (3 * p - 2)) *
              Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2))))

def fcCheck_moment_rate_sharp (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) : Prop :=
    let B : Set (EuclideanSpace ℝ (Fin (d + 2))) := {x | x 0 ∈ Set.Icc 0 1 ∧ ∀ i, x i ∈ Set.Icc (-1) 1}
    let ρ : Measure (EuclideanSpace ℝ (Fin (d + 2))) := (volume B)⁻¹ • volume.restrict B
    let fourAtoms (μ : Measure (EuclideanSpace ℝ (Fin (d + 2)))) : Prop :=
      ∃ y : Fin 4 → EuclideanSpace ℝ (Fin (d + 2)), Function.Injective y ∧
        ∃ w : Fin 4 → ℝ≥0∞, (∀ k, 0 < w k) ∧ (∑ k, w k) = 1 ∧
          μ = ∑ k, w k • Measure.dirac (y k)
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (EuclideanSpace ℝ (Fin (d + 2)))) (Tμ Tν : EuclideanSpace ℝ (Fin (d + 2)) → EuclideanSpace ℝ (Fin (d + 2))),
        fourAtoms μ ∧ fourAtoms ν ∧ moment p β μ ≤ 1 ∧ moment p β ν ≤ 1 ∧
        IsBrenierMap ρ μ Tμ ∧ IsBrenierMap ρ ν Tν ∧
        wasserstein μ ν = δ ∧ c * (δ ^ ((p - 2) / (3 * p - 2)) *
              Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2))) ≤ Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ)

def fcCheck_no_modulus_at_second_moment (d : ℕ) {ε : ℝ} (hε : 0 < ε) : Prop :=
    let B : Set (EuclideanSpace ℝ (Fin (d + 2))) := {x | x 0 ∈ Set.Icc 0 1 ∧ ∀ i, x i ∈ Set.Icc (-1) 1}
    let ρ : Measure (EuclideanSpace ℝ (Fin (d + 2))) := (volume B)⁻¹ • volume.restrict B
    let fourAtoms (μ : Measure (EuclideanSpace ℝ (Fin (d + 2)))) : Prop :=
      ∃ y : Fin 4 → EuclideanSpace ℝ (Fin (d + 2)), Function.Injective y ∧
        ∃ w : Fin 4 → ℝ≥0∞, (∀ k, 0 < w k) ∧ (∑ k, w k) = 1 ∧
          μ = ∑ k, w k • Measure.dirac (y k)
    ∃ (μ ν : Measure (EuclideanSpace ℝ (Fin (d + 2)))) (Tμ Tν : EuclideanSpace ℝ (Fin (d + 2)) → EuclideanSpace ℝ (Fin (d + 2))),
      fourAtoms μ ∧ fourAtoms ν ∧ moment 2 0 μ ≤ 1 ∧ moment 2 0 ν ≤ 1 ∧
      IsBrenierMap ρ μ Tμ ∧ IsBrenierMap ρ ν Tν ∧
      0 < wasserstein μ ν ∧ wasserstein μ ν < ε ∧ 1 / 20 ≤ Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ)

theorem fcCheck_original_compact_stability {d : ℕ} (hd : 2 ≤ d) {K Y : Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsCompact K) (hKc : Convex ℝ K) (hKn : (interior K).Nonempty)
    (hY : IsCompact Y) (hYn : Y.Nonempty) :
    let ρ : Measure (EuclideanSpace ℝ (Fin d)) := (volume K)⁻¹ • volume.restrict K
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ μ ν : Measure (EuclideanSpace ℝ (Fin d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        μ (Yᶜ) = 0 → ν (Yᶜ) = 0 →
        ∃ Tμ Tν : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          IsBrenierMap ρ μ Tμ ∧ IsBrenierMap ρ ν Tν ∧
          Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ) ≤
            C * wasserstein μ ν ^ (1 / 3 : ℝ) := by
  exact OAI.Problem358.one_third_stability d K Y hd hK hKc hKn hY hYn

end
end BrenierFCCheck

namespace BrenierStability
noncomputable section
open MeasureTheory
open scoped ENNReal

def fcCheck_moment_stability {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUn : U.Nonempty) {V : Space d → ℝ} (hV : ConvexOn ℝ U V)
    {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) : Prop :=
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ μ ν : Measure (Space d), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        moment p β μ ≤ 1 → moment 2 0 ν < ∞ →
        ∃ Tμ Tν : Space d → Space d,
          IsBrenierMap (logConcaveSource U V) μ Tμ ∧
          IsBrenierMap (logConcaveSource U V) ν Tν ∧
          (0 < wasserstein μ ν → wasserstein μ ν ≤ δ₀ →
            mapDist (logConcaveSource U V) Tμ Tν ≤ C * modulus p β (wasserstein μ ν))

def fcCheck_moment_rate_sharp (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) : Prop :=
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
        HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment p β μ ≤ 1 ∧ moment p β ν ≤ 1 ∧
        IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
        wasserstein μ ν = δ ∧ c * modulus p β δ ≤ mapDist (boxSource d) Tμ Tν

def fcCheck_no_modulus_at_second_moment (d : ℕ) {ε : ℝ} (hε : 0 < ε) : Prop :=
    ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
      HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment 2 0 μ ≤ 1 ∧ moment 2 0 ν ≤ 1 ∧
      IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
      0 < wasserstein μ ν ∧ wasserstein μ ν < ε ∧ 1 / 20 ≤ mapDist (boxSource d) Tμ Tν

end
end BrenierStability

example : @BrenierFCCheck.wasserstein = @BrenierStability.wasserstein := rfl
example : @BrenierFCCheck.IsBrenierMap = @BrenierStability.IsBrenierMap := rfl
example : @BrenierFCCheck.moment = @BrenierStability.moment := rfl
example : @BrenierFCCheck.fcCheck_moment_stability = @BrenierStability.fcCheck_moment_stability := rfl
example : @BrenierFCCheck.fcCheck_moment_rate_sharp = @BrenierStability.fcCheck_moment_rate_sharp := rfl
example : @BrenierFCCheck.fcCheck_no_modulus_at_second_moment = @BrenierStability.fcCheck_no_modulus_at_second_moment := rfl
#print axioms BrenierFCCheck.fcCheck_original_compact_stability
