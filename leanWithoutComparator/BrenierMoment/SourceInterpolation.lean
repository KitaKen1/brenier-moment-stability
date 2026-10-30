module

public import BrenierMoment.CoordSlices
public import BrenierMoment.LogConcave

@[expose] public section

/-!
# The interpolation estimate for a log-concave source

The density `exp (-V)` on `U` is the marginal of the Lebesgue measure on the
region under its graph. The slices of that region along a coordinate of `E d`
are slices of the convex sets `{y ∈ U | s < exp (-V y)}`, hence
order-connected. The estimate of `CoordSlices.lean` for the Lebesgue measure
on the region therefore becomes an estimate for the weighted source, for
functions of the base point only. No weight is ever compared at two points.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

variable {d : ℕ}

lemma powerMeasure_zero (U : Set (E d)) (h : E d → ℝ) :
    powerMeasure U h 0 = volume.restrict U := by
  unfold powerMeasure
  simp only [pow_zero, ENNReal.ofReal_one]
  exact withDensity_one

/-- The exponential density is the marginal of the Lebesgue measure under its graph. -/
lemma map_dropLast_restrict_subgraph {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) :
    Measure.map dropLast (volume.restrict (subgraph U fun x => Real.exp (-V x))) =
      expMeasure U V := by
  have hh : Measurable fun x => Real.exp (-V x) := Real.measurable_exp.comp hV.neg
  have h := map_dropLast_powerMeasure hU hh (fun x _ => (Real.exp_pos _).le) 0
  rw [powerMeasure_zero] at h
  rw [h, expMeasure_eq_powerMeasure]

lemma lintegral_expMeasure {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) {F : E d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, F x ∂(expMeasure U V) =
      ∫⁻ w in subgraph U (fun x => Real.exp (-V x)), F (dropLast w) := by
  rw [← map_dropLast_restrict_subgraph hU hV, lintegral_map hF measurable_dropLast]

lemma dropLast_single_castSucc (j : Fin d) (a : ℝ) :
    dropLast (EuclideanSpace.single j.castSucc a) = EuclideanSpace.single j a := by
  ext k
  simp [PiLp.single_apply, Fin.castSucc_inj]

/-- The slices of the region under a graph along a base coordinate are convex,
if the strict superlevel sets of the function are convex. -/
lemma convex_slice_subgraph {U : Set (E d)} {h : E d → ℝ}
    (hqc : ∀ s : ℝ, Convex ℝ {y | y ∈ U ∧ s < h y}) (j : Fin d) (x : E d) :
    Convex ℝ (slice j.castSucc (subgraph U h) x) := by
  intro t₁ ht₁ t₂ ht₂ a b ha hb hab
  change coordJoin j.castSucc (t₁, x) ∈ subgraph U h at ht₁
  change coordJoin j.castSucc (t₂, x) ∈ subgraph U h at ht₂
  obtain ⟨h1U, h10, h1h⟩ := ht₁
  obtain ⟨h2U, -, h2h⟩ := ht₂
  have hne : Fin.last d ≠ j.castSucc := (Fin.castSucc_lt_last j).ne'
  -- the last coordinate is constant along the slice
  have hlast : ∀ t, coordJoin j.castSucc (t, x) (Fin.last d) =
      coordJoin j.castSucc (t₁, x) (Fin.last d) :=
    fun t => coordJoin_apply_of_ne j.castSucc hne t t₁ x
  have hcombo : coordJoin j.castSucc (a • t₁ + b • t₂, x) =
      a • coordJoin j.castSucc (t₁, x) + b • coordJoin j.castSucc (t₂, x) := by
    rw [smul_eq_mul, smul_eq_mul]
    exact coordJoin_combo j.castSucc hab t₁ t₂ x
  have h2h' : coordJoin j.castSucc (t₁, x) (Fin.last d) <
      h (dropLast (coordJoin j.castSucc (t₂, x))) := by
    rw [← hlast t₂]
    exact h2h
  have hmem : dropLast (coordJoin j.castSucc (a • t₁ + b • t₂, x)) ∈
      {y | y ∈ U ∧ coordJoin j.castSucc (t₁, x) (Fin.last d) < h y} := by
    rw [hcombo, map_add, map_smul, map_smul]
    exact hqc _ ⟨h1U, h1h⟩ ⟨h2U, h2h'⟩ ha hb hab
  change dropLast (coordJoin j.castSucc (a • t₁ + b • t₂, x)) ∈ U ∧
    0 < coordJoin j.castSucc (a • t₁ + b • t₂, x) (Fin.last d) ∧
    coordJoin j.castSucc (a • t₁ + b • t₂, x) (Fin.last d) <
      h (dropLast (coordJoin j.castSucc (a • t₁ + b • t₂, x)))
  rw [hlast (a • t₁ + b • t₂)]
  exact ⟨hmem.1, h10, hmem.2⟩

lemma slice_subgraph_subset_Icc {U : Set (E d)} {h : E d → ℝ} {R : ℝ}
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) (j : Fin d) (x : E d) :
    slice j.castSucc (subgraph U h) x ⊆ Set.Icc (-R) R := by
  intro t ht
  change coordJoin j.castSucc (t, x) ∈ subgraph U h at ht
  obtain ⟨hU', -, -⟩ := ht
  have h1 : dropLast (coordJoin j.castSucc (t, x)) j = t := by
    rw [dropLast_apply, coordJoin_same]
  have h2 := PiLp.norm_apply_le (dropLast (coordJoin j.castSucc (t, x))) j
  rw [h1, Real.norm_eq_abs] at h2
  exact abs_le.mp (h2.trans (hR _ hU'))

lemma mem_closedBall_of_slice_nonempty {U : Set (E d)} {h : E d → ℝ} {R η : ℝ}
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hη : ∀ x ∈ U, h x ≤ η) (j : Fin d) {x : E d}
    (hne : (slice j.castSucc (subgraph U h) x).Nonempty) :
    x ∈ Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + η ^ 2)) := by
  obtain ⟨t, ht⟩ := hne
  have h1 := norm_le_of_mem_subgraph hR hη
    (show coordJoin j.castSucc (t, x) ∈ subgraph U h from ht)
  have h2 : ‖x‖ ≤ ‖coordJoin j.castSucc (t, x)‖ := norm_snd_le_norm_coordJoin j.castSucc (t, x)
  exact mem_closedBall_zero_iff.mpr (h2.trans h1)

/-- **Interpolation for the exponential density**, along the `j`-th coordinate. -/
theorem expMeasure_interpolation {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) {R η : ℝ} (hR : ∀ x ∈ U, ‖x‖ ≤ R)
    (hη : ∀ x ∈ U, Real.exp (-V x) ≤ η)
    (hqc : ∀ s : ℝ, Convex ℝ {y | y ∈ U ∧ s < Real.exp (-V y)})
    (j : Fin d) {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h)
    {Φ Γ : E d → ℝ≥0∞} (hΦ : Measurable Φ) (hΓ : Measurable Γ)
    {D cu cv : E d → ℝ} (hD : Measurable D) (hcu : Measurable cu) (hcv : Measurable cv)
    (hcuH : ∀ x, |cu x| ≤ H) (hcvH : ∀ x, |cv x| ≤ H)
    (hcu_mono : ∀ x, cu (x - EuclideanSpace.single j h) ≤ cu x)
    (hcv_mono : ∀ x, cv (x - EuclideanSpace.single j h) ≤ cv x)
    (ha : ∀ x ∈ U, Φ x ≤ ENNReal.ofReal (4 * H ^ 2))
    (hb : ∀ x, x ∈ U → x + EuclideanSpace.single j h ∈ U → x - EuclideanSpace.single j h ∈ U →
      Φ x ≤ ENNReal.ofReal (((D (x + EuclideanSpace.single j h) - D x) / h) ^ 2) +
        ENNReal.ofReal (4 * H) * (ENNReal.ofReal (cu x - cu (x - EuclideanSpace.single j h)) +
          ENNReal.ofReal (cv x - cv (x - EuclideanSpace.single j h))) + Γ x) :
    (∫⁻ x, Φ x ∂(expMeasure U V)) ≤
      ENNReal.ofReal (4 / h ^ 2) * (∫⁻ x, ENNReal.ofReal (D x ^ 2) ∂(expMeasure U V)) +
        ENNReal.ofReal (24 * H ^ 2 * h) *
          volume (Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + η ^ 2))) +
        ∫⁻ x, Γ x ∂(expMeasure U V) := by
  have hhm : Measurable fun x => Real.exp (-V x) := Real.measurable_exp.comp hV.neg
  have hGm : MeasurableSet (subgraph U fun x => Real.exp (-V x)) :=
    measurableSet_subgraph hU hhm
  have hDsq : Measurable fun x => ENNReal.ofReal (D x ^ 2) :=
    ENNReal.measurable_ofReal.comp (hD.pow_const 2)
  have hshift_add : ∀ w : E (d + 1), dropLast (w + EuclideanSpace.single j.castSucc h) =
      dropLast w + EuclideanSpace.single j h := by
    intro w
    rw [map_add, dropLast_single_castSucc]
  have hshift_sub : ∀ w : E (d + 1), dropLast (w - EuclideanSpace.single j.castSucc h) =
      dropLast w - EuclideanSpace.single j h := by
    intro w
    rw [map_sub, dropLast_single_castSucc]
  have key := sliced_interpolation j.castSucc hGm
    (fun x => convex_iff_ordConnected.mp (convex_slice_subgraph hqc j x))
    (fun x => ((measure_mono (slice_subgraph_subset_Icc hR j x)).trans_lt
      measure_Icc_lt_top).ne)
    (N := Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + η ^ 2))) measurableSet_closedBall
    (fun x hne => mem_closedBall_of_slice_nonempty hR hη j hne) hH hh
    (Φ := fun w => Φ (dropLast w)) (Γ := fun w => Γ (dropLast w))
    (hΦ.comp measurable_dropLast) (hΓ.comp measurable_dropLast)
    (D := fun w => D (dropLast w)) (cu := fun w => cu (dropLast w))
    (cv := fun w => cv (dropLast w))
    (hD.comp measurable_dropLast) (hcu.comp measurable_dropLast)
    (hcv.comp measurable_dropLast) (fun w => hcuH _) (fun w => hcvH _)
    (fun w => by
      rw [hshift_sub]
      exact hcu_mono _)
    (fun w => by
      rw [hshift_sub]
      exact hcv_mono _)
    (fun w hw => ha _ hw.1)
    (fun w hw hp hm => by
      have hp' : dropLast w + EuclideanSpace.single j h ∈ U := by
        rw [← hshift_add]
        exact hp.1
      have hm' : dropLast w - EuclideanSpace.single j h ∈ U := by
        rw [← hshift_sub]
        exact hm.1
      have h1 := hb (dropLast w) hw.1 hp' hm'
      rw [← hshift_add, ← hshift_sub] at h1
      exact h1)
  rw [lintegral_expMeasure hU hV hΦ, lintegral_expMeasure hU hV hDsq,
    lintegral_expMeasure hU hV hΓ]
  exact key

/-- **Interpolation for the log-concave source**, along the `j`-th coordinate.
The constant term is divided by the total mass of the exponential density. -/
theorem logConcaveSource_interpolation {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) {R η : ℝ} (hR : ∀ x ∈ U, ‖x‖ ≤ R)
    (hη : ∀ x ∈ U, Real.exp (-V x) ≤ η)
    (hqc : ∀ s : ℝ, Convex ℝ {y | y ∈ U ∧ s < Real.exp (-V y)})
    (j : Fin d) {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h)
    {Φ Γ : E d → ℝ≥0∞} (hΦ : Measurable Φ) (hΓ : Measurable Γ)
    {D cu cv : E d → ℝ} (hD : Measurable D) (hcu : Measurable cu) (hcv : Measurable cv)
    (hcuH : ∀ x, |cu x| ≤ H) (hcvH : ∀ x, |cv x| ≤ H)
    (hcu_mono : ∀ x, cu (x - EuclideanSpace.single j h) ≤ cu x)
    (hcv_mono : ∀ x, cv (x - EuclideanSpace.single j h) ≤ cv x)
    (ha : ∀ x ∈ U, Φ x ≤ ENNReal.ofReal (4 * H ^ 2))
    (hb : ∀ x, x ∈ U → x + EuclideanSpace.single j h ∈ U → x - EuclideanSpace.single j h ∈ U →
      Φ x ≤ ENNReal.ofReal (((D (x + EuclideanSpace.single j h) - D x) / h) ^ 2) +
        ENNReal.ofReal (4 * H) * (ENNReal.ofReal (cu x - cu (x - EuclideanSpace.single j h)) +
          ENNReal.ofReal (cv x - cv (x - EuclideanSpace.single j h))) + Γ x) :
    (∫⁻ x, Φ x ∂(logConcaveSource U V)) ≤
      ENNReal.ofReal (4 / h ^ 2) * (∫⁻ x, ENNReal.ofReal (D x ^ 2) ∂(logConcaveSource U V)) +
        ENNReal.ofReal (24 * H ^ 2 * h) *
          (volume (Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + η ^ 2))) /
            expMeasure U V Set.univ) +
        ∫⁻ x, Γ x ∂(logConcaveSource U V) := by
  have key := expMeasure_interpolation hU hV hR hη hqc j hH hh hΦ hΓ hD hcu hcv hcuH hcvH
    hcu_mono hcv_mono ha hb
  unfold logConcaveSource
  rw [lintegral_smul_measure, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul,
    smul_eq_mul, smul_eq_mul]
  calc (expMeasure U V Set.univ)⁻¹ * ∫⁻ x, Φ x ∂(expMeasure U V)
      ≤ (expMeasure U V Set.univ)⁻¹ *
          (ENNReal.ofReal (4 / h ^ 2) * (∫⁻ x, ENNReal.ofReal (D x ^ 2) ∂(expMeasure U V)) +
            ENNReal.ofReal (24 * H ^ 2 * h) *
              volume (Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + η ^ 2))) +
            ∫⁻ x, Γ x ∂(expMeasure U V)) := by gcongr
    _ = ENNReal.ofReal (4 / h ^ 2) *
          ((expMeasure U V Set.univ)⁻¹ * ∫⁻ x, ENNReal.ofReal (D x ^ 2) ∂(expMeasure U V)) +
        ENNReal.ofReal (24 * H ^ 2 * h) *
          (volume (Metric.closedBall (0 : E d) (Real.sqrt (R ^ 2 + η ^ 2))) /
            expMeasure U V Set.univ) +
        (expMeasure U V Set.univ)⁻¹ * ∫⁻ x, Γ x ∂(expMeasure U V) := by
        rw [ENNReal.div_eq_inv_mul]
        ring

end

end BrenierMoment
