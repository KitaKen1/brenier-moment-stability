module

public import BrenierMoment.SourceInterpolation

@[expose] public section

/-!
# The interpolation property of a source

`StripInterpolation ρ U B` records the estimate of
`SourceInterpolation.lean` as a property of the source alone: along every
coordinate, a pointwise secant bound on the triples of points of `U` at
distance `h` integrates to the same bound, at the cost of `24 H² h B`. The
log-concave sources have this property. Everything proved later about maps
and plans uses the source only through this property and through the atomic
potential estimate.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The interpolation estimate along every coordinate, for a source concentrated on `U`,
with strip constant `B`. -/
def StripInterpolation (ρ : Measure (E d)) (U : Set (E d)) (B : ℝ) : Prop :=
  ∀ (j : Fin d) (H h : ℝ), 0 ≤ H → 0 < h →
    ∀ (Φ Γ : E d → ℝ≥0∞) (D cu cv : E d → ℝ), Measurable Φ → Measurable Γ → Measurable D →
      Measurable cu → Measurable cv → (∀ x, |cu x| ≤ H) → (∀ x, |cv x| ≤ H) →
      (∀ x, cu (x - EuclideanSpace.single j h) ≤ cu x) →
      (∀ x, cv (x - EuclideanSpace.single j h) ≤ cv x) →
      (∀ x ∈ U, Φ x ≤ ENNReal.ofReal (4 * H ^ 2)) →
      (∀ x, x ∈ U → x + EuclideanSpace.single j h ∈ U → x - EuclideanSpace.single j h ∈ U →
        Φ x ≤ ENNReal.ofReal (((D (x + EuclideanSpace.single j h) - D x) / h) ^ 2) +
          ENNReal.ofReal (4 * H) *
            (ENNReal.ofReal (cu x - cu (x - EuclideanSpace.single j h)) +
              ENNReal.ofReal (cv x - cv (x - EuclideanSpace.single j h))) + Γ x) →
      (∫⁻ x, Φ x ∂ρ) ≤
        ENNReal.ofReal (4 / h ^ 2) * (∫⁻ x, ENNReal.ofReal (D x ^ 2) ∂ρ) +
          ENNReal.ofReal (24 * H ^ 2 * h * B) + ∫⁻ x, Γ x ∂ρ

/-- The strict superlevel sets of `exp (-V)` on `U` are convex when `V` is convex. -/
lemma convex_superlevel_exp_neg {U : Set (E d)} {V : E d → ℝ} (hV : ConvexOn ℝ U V) (s : ℝ) :
    Convex ℝ {y | y ∈ U ∧ s < Real.exp (-V y)} := by
  rcases le_or_gt s 0 with hs | hs
  · have hset : {y | y ∈ U ∧ s < Real.exp (-V y)} = U := by
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, hs.trans_lt (Real.exp_pos _)⟩⟩
    rw [hset]
    exact hV.1
  · have hset : {y | y ∈ U ∧ s < Real.exp (-V y)} = {y | y ∈ U ∧ V y < -Real.log s} := by
      ext y
      change (y ∈ U ∧ s < Real.exp (-V y)) ↔ (y ∈ U ∧ V y < -Real.log s)
      refine and_congr_right fun _ => ?_
      rw [← Real.log_lt_iff_lt_exp hs]
      constructor <;> intro h <;> linarith
    rw [hset]
    exact hV.convex_lt _

lemma expMeasure_univ_ne_zero {U : Set (E d)} {V : E d → ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hVm : Measurable V) : expMeasure U V Set.univ ≠ 0 := by
  rw [expMeasure_eq_powerMeasure]
  exact (powerMeasure_univ_pos hU.measurableSet (Real.measurable_exp.comp hVm.neg)
    (hU.measure_pos volume hne).ne' (fun x _ => Real.exp_pos _) 1).ne'

/-- **Log-concave sources have the interpolation property.** -/
theorem stripInterpolation_logConcave {U : Set (E d)} {V : E d → ℝ} {R : ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hV : ConvexOn ℝ U V) (hVm : Measurable V) :
    ∃ B : ℝ, 0 ≤ B ∧ StripInterpolation (logConcaveSource U V) U B := by
  obtain ⟨m, hm⟩ := exists_lower_bound_of_convexOn hU hne hR hV
  have hη : ∀ x ∈ U, Real.exp (-V x) ≤ Real.exp (-m) :=
    fun x hx => Real.exp_le_exp.mpr (neg_le_neg (hm x hx))
  have hZ0 := expMeasure_univ_ne_zero hU hne hVm
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0∞, c =
      volume (Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + Real.exp (-m) ^ 2))) /
        expMeasure U V Set.univ := ⟨_, rfl⟩
  have hctop : c ≠ ∞ := by
    rw [hc]
    exact ENNReal.div_ne_top measure_closedBall_lt_top.ne hZ0
  refine ⟨c.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro j H h hH hh Φ Γ D cu cv hΦ hΓ hD hcu hcv hcuH hcvH hcu_mono hcv_mono ha hb
  have key := logConcaveSource_interpolation hU.measurableSet hVm hR hη
    (convex_superlevel_exp_neg hV) j hH hh hΦ hΓ hD hcu hcv hcuH hcvH hcu_mono hcv_mono ha hb
  rw [← hc] at key
  have hconst : ENNReal.ofReal (24 * H ^ 2 * h) * c =
      ENNReal.ofReal (24 * H ^ 2 * h * c.toReal) := by
    rw [ENNReal.ofReal_mul (p := 24 * H ^ 2 * h) (q := c.toReal) (by positivity),
      ENNReal.ofReal_toReal hctop]
  rw [hconst] at key
  exact key

end

end BrenierMoment
