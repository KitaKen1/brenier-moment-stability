module

public import BrenierMoment.MomentStability
public import BrenierMoment.UniformBase

@[expose] public section

/-!
# The upper bound

The statement of `MomentStability.lean` for log-concave sources, with the
atomic potential estimate for uniform sources supplied by `UniformBase.lean`
and without the measurability assumption on the exponent: a convex function
on an open set is continuous there, and the source only sees it on that set.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The log-concave source depends on the exponent only through its values on `U`. -/
lemma logConcaveSource_congr {U : Set (E d)} (hU : MeasurableSet U) {V W : E d → ℝ}
    (h : Set.EqOn V W U) : logConcaveSource U V = logConcaveSource U W := by
  have he : expMeasure U V = expMeasure U W := by
    unfold expMeasure
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [h hx]
  unfold logConcaveSource
  rw [he]

/-- **Sharp moment stability of Brenier maps: the upper bound.** Let `U` be a
bounded nonempty open convex subset of `ℝ^d`, let `V` be convex on `U`, and let
the source have density proportional to `exp (-V)` on `U`. Let `2 ≤ p` and
`0 ≤ β`. There is a constant `C` such that, for every probability `μ` with
`∫ |y|^p log(e + |y|)^β dμ ≤ 1` and every probability `ν` with finite second
moment, both targets have unique optimal maps and, if
`δ = W₂(μ, ν) ≤ exp (1 - (6β + 2)²)`,
`‖T_μ - T_ν‖_{L²(ρ)} ≤ C δ ^ ((p - 2) / (3p - 2)) * log (e / δ) ^ (-2β / (3p - 2))`. -/
theorem moment_stability {U : Set (E d)} {V : E d → ℝ} {R : ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hV : ConvexOn ℝ U V) {p β : ℝ} (hp : 2 ≤ p)
    (hβ : 0 ≤ β) :
    ∃ C : ℝ, ∀ (μ ν : Measure (E d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) < ∞ →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (logConcaveSource U V) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (logConcaveSource U V) ν Tν ∧
        (wasserstein2 μ ν ≤ smallDistance β →
          mapL2Dist (logConcaveSource U V) Tμ Tν ≤
            C * momentModulus p β (wasserstein2 μ ν)) := by
  classical
  have hcont : ContinuousOn V U := hV.continuousOn hU
  obtain ⟨W, hW⟩ : ∃ W : E d → ℝ, W = U.piecewise V fun _ => 0 := ⟨_, rfl⟩
  have hWm : Measurable W := by
    rw [hW]
    exact hcont.measurable_piecewise continuousOn_const hU.measurableSet
  have heq : Set.EqOn V W U := by
    intro x hx
    rw [hW, Set.piecewise_eq_of_mem _ _ _ hx]
  have hWc : ConvexOn ℝ U W := hV.congr heq
  rw [logConcaveSource_congr hU.measurableSet heq]
  exact moment_stability_logConcave uniformPotentialBound hU hne hR hWc hWm hp hβ

end

end BrenierMoment
