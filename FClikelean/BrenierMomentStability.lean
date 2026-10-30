/-
Copyright 2026 Kenta Kitamura (KitaKen1).
Licensed under the Apache License, Version 2.0; see LICENSE.
-/
module

public import FormalConjecturesUtil

/-!
# Sharp moment stability of Brenier maps

For a log-concave source with bounded support, a power-logarithmic moment bound on one
target gives a sharp modulus of continuity for Brenier maps. A second-moment bound alone
gives no modulus. `original_compact_stability` is OpenAI's result [OAI26];
`moment_stability` is its moment variant [Ki26]. The square-root conjecture [L26] is false.

*References:*
- [L26] C. Letrouit, *Unstable optimal transport maps*, Conjecture 3 (2026).
  https://doi.org/10.5802/crmath.834
- [OAI26] OpenAI, *Sharp One-Third Stability of Brenier Maps* (2026), result 374.
  https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/374.md
- [Ki26] K. Kitamura, *Sharp moment stability of Brenier maps* (2026).
  https://github.com/KitaKen1/brenier-moment-stability
-/

@[expose] public section

namespace BrenierStability

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

/-- OpenAI's sharp compact-target bound, replacing the false square-root conjecture [OAI26]. -/
@[category research solved, AMS 49 60,
    formal_proof using lean4 at "https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Analysis/Brenier/Stability.lean#L19"]
theorem original_compact_stability {d : ℕ} (hd : 2 ≤ d) {K Y : Set (EuclideanSpace ℝ (Fin d))}
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
  sorry

/-- Variant of `original_compact_stability`: log-concave source, one-sided moment bound,
and moment-dependent rate [Ki26]. -/
@[category research solved, AMS 49 60,
    formal_proof using lean4 at "https://github.com/KitaKen1/brenier-moment-stability/blob/COMMIT_OF_THE_PUBLIC_REPOSITORY/lean/BrenierMoment/FCPresentation.lean#L198"]
theorem moment_stability {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUn : U.Nonempty) {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ConvexOn ℝ U V)
    {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
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
              Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2)))) := by
  sorry

/-- The modulus is sharp, already for four-atom targets and a uniform box source [Ki26]. -/
@[category research solved, AMS 49 60,
    formal_proof using lean4 at "https://github.com/KitaKen1/brenier-moment-stability/blob/COMMIT_OF_THE_PUBLIC_REPOSITORY/lean/BrenierMoment/FCPresentation.lean#L217"]
theorem moment_rate_sharp (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
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
              Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2))) ≤ Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ) := by
  sorry

/-- A second-moment bound alone gives no modulus of continuity for Brenier maps [Ki26]. -/
@[category research solved, AMS 49 60,
    formal_proof using lean4 at "https://github.com/KitaKen1/brenier-moment-stability/blob/COMMIT_OF_THE_PUBLIC_REPOSITORY/lean/BrenierMoment/FCPresentation.lean#L230"]
theorem no_modulus_at_second_moment (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    let B : Set (EuclideanSpace ℝ (Fin (d + 2))) := {x | x 0 ∈ Set.Icc 0 1 ∧ ∀ i, x i ∈ Set.Icc (-1) 1}
    let ρ : Measure (EuclideanSpace ℝ (Fin (d + 2))) := (volume B)⁻¹ • volume.restrict B
    let fourAtoms (μ : Measure (EuclideanSpace ℝ (Fin (d + 2)))) : Prop :=
      ∃ y : Fin 4 → EuclideanSpace ℝ (Fin (d + 2)), Function.Injective y ∧
        ∃ w : Fin 4 → ℝ≥0∞, (∀ k, 0 < w k) ∧ (∑ k, w k) = 1 ∧
          μ = ∑ k, w k • Measure.dirac (y k)
    ∃ (μ ν : Measure (EuclideanSpace ℝ (Fin (d + 2)))) (Tμ Tν : EuclideanSpace ℝ (Fin (d + 2)) → EuclideanSpace ℝ (Fin (d + 2))),
      fourAtoms μ ∧ fourAtoms ν ∧ moment 2 0 μ ≤ 1 ∧ moment 2 0 ν ≤ 1 ∧
      IsBrenierMap ρ μ Tμ ∧ IsBrenierMap ρ ν Tν ∧
      0 < wasserstein μ ν ∧ wasserstein μ ν < ε ∧ 1 / 20 ≤ Real.sqrt (∫ x, ‖Tμ x - Tν x‖ ^ 2 ∂ρ) := by
  sorry

end

end BrenierStability
