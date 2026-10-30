module

public import BrenierMoment.UpperBound
public import BrenierMoment.Sharpness

@[expose] public section

/-!
# The upper bound on uniform sources, and the two-sided rate

The uniform source on a convex set is the log-concave source with zero
exponent on its interior, so the upper bound applies to it. On the fixed box
source of the sharpness statements this gives both bounds for the same pairs
of targets.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The uniform source on a convex set is the log-concave source with zero
exponent on its interior. -/
theorem uniformMeasure_eq_logConcaveSource {K : Set (E d)} (hK : Convex ℝ K) :
    uniformMeasure K = logConcaveSource (interior K) fun _ => 0 := by
  have hres : (volume : Measure (E d)).restrict (interior K) = volume.restrict K :=
    Measure.restrict_congr_set (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))
  have hexp : expMeasure (interior K) (fun _ => 0) = volume.restrict K := by
    have h : expMeasure (interior K) (fun _ => 0) =
        ((volume : Measure (E d)).restrict (interior K)).withDensity 1 := by
      unfold expMeasure
      refine congrArg (Measure.withDensity _) (funext fun x => ?_)
      simp
    rw [h, withDensity_one, hres]
  unfold logConcaveSource uniformMeasure
  rw [hexp, Measure.restrict_apply_univ]

/-- **The upper bound for uniform sources.** The statement of `moment_stability`
for the uniform source on a convex body. -/
theorem moment_stability_uniform {K : Set (E d)} (hK : IsCompact K) (hKconv : Convex ℝ K)
    (hKint : (interior K).Nonempty) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ C : ℝ, ∀ (μ ν : Measure (E d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) < ∞ →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (uniformMeasure K) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (uniformMeasure K) ν Tν ∧
        (wasserstein2 μ ν ≤ smallDistance β →
          mapL2Dist (uniformMeasure K) Tμ Tν ≤
            C * momentModulus p β (wasserstein2 μ ν)) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  rw [uniformMeasure_eq_logConcaveSource hKconv]
  exact moment_stability isOpen_interior hKint (fun x hx => hR x (interior_subset hx))
    (convexOn_const 0 hKconv.interior) hp hβ

/-- **The rate is attained.** On the uniform source on `[0,1] × [-1,1]^(d-1)`,
for `2 ≤ p` and `0 ≤ β`, there are at every small distance `δ` two four-atom
targets with power-logarithmic moments at most one and `W₂ = δ` whose unique
optimal maps are at `L²` distance between `c ω(δ)` and `C ω(δ)`, where
`ω(δ) = δ ^ ((p - 2) / (3p - 2)) * log (e / δ) ^ (-2β / (3p - 2))`. -/
theorem moment_rate_two_sided (d : ℕ) (hd : 2 ≤ d) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ c C δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (E d)) (Tμ Tν : E d → E d),
        Sharp.HasFourAtoms μ ∧ Sharp.HasFourAtoms ν ∧
        (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1 ∧
        (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂ν) ≤ 1 ∧
        IsUniqueQuadraticOptimalMap (sharpSource d hd) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (sharpSource d hd) ν Tν ∧
        wasserstein2 μ ν = δ ∧
        c * momentModulus p β δ ≤ mapL2Dist (sharpSource d hd) Tμ Tν ∧
        mapL2Dist (sharpSource d hd) Tμ Tν ≤ C * momentModulus p β δ := by
  obtain ⟨c, hc, δ₁, hδ₁, hsharp⟩ := moment_rate_sharp d hd hp hβ
  have hprob : IsProbabilityMeasure (sharpSource d hd) :=
    Sharp.sourceBox_isProbabilityMeasure _
  have hconv : Convex ℝ (Sharp.sourceBox (Sharp.axis0 d hd)) := convex_coordBox _ _
  have hint : (interior (Sharp.sourceBox (Sharp.axis0 d hd))).Nonempty :=
    interior_coordBox_nonempty (Sharp.sourceLo_lt_sourceHi _)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ (μ ν : Measure (E d)), IsProbabilityMeasure μ →
      IsProbabilityMeasure ν →
      (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) < ∞ →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (sharpSource d hd) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (sharpSource d hd) ν Tν ∧
        (wasserstein2 μ ν ≤ smallDistance β →
          mapL2Dist (sharpSource d hd) Tμ Tν ≤
            C * momentModulus p β (wasserstein2 μ ν)) :=
    moment_stability_uniform (Sharp.isCompact_sourceBox (Sharp.axis0 d hd)) hconv hint hp hβ
  refine ⟨c, C, min δ₁ (smallDistance β), hc, lt_min hδ₁ (smallDistance_pos β), ?_⟩
  intro δ hδ0 hδ
  obtain ⟨μ, ν, Tμ, Tν, hμ4, hν4, hμM, hνM, hTμ, hTν, hW, hlow⟩ :=
    hsharp δ hδ0 (hδ.trans (min_le_left _ _))
  have hμp : IsProbabilityMeasure μ := by
    rw [← hTμ.1.2.1]
    exact (Measure.isProbabilityMeasure_map_iff hTμ.1.1.aemeasurable).mpr hprob
  have hνp : IsProbabilityMeasure ν := by
    rw [← hTν.1.2.1]
    exact (Measure.isProbabilityMeasure_map_iff hTν.1.1.aemeasurable).mpr hprob
  -- the second moment of `ν` is finite
  have hwm := measurable_momentWeight (d := d) p β
  have hνint : Integrable (momentWeight p β : E d → ℝ) ν :=
    ⟨hwm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y =>
        momentWeight_nonneg p β y)).mpr (hνM.trans_lt ENNReal.one_lt_top)⟩
  have hν2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) < ∞ :=
    (lintegral_sq_norm_ne_top (integrable_sq_norm_of_moment hp hβ hνint)).lt_top
  obtain ⟨Sμ, Sν, hSμ, hSν, hup⟩ := hC μ ν hμp hνp hμM hν2
  have hWle : wasserstein2 μ ν ≤ smallDistance β := by
    rw [hW]
    exact hδ.trans (min_le_right _ _)
  have hupper := hup hWle
  rw [hW] at hupper
  refine ⟨μ, ν, Tμ, Tν, hμ4, hν4, hμM, hνM, hTμ, hTν, hW, hlow, ?_⟩
  rw [mapL2Dist_eq_of_optimal_maps hTμ hTν hSμ.1 hSν.1]
  exact hupper

end

end BrenierMoment
