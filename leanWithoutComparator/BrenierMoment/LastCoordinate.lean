module

public import OAI.Analysis.Brenier.TransportCore
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Splitting off the last coordinate

`E (k + 1)` is identified with `ℝ × E k` by `w ↦ (w_last, dropLast w)`, and
this identification preserves volume. With it a source whose density is a
power `h ^ (r + 1)` is the marginal of the density `h ^ r` on the region under
the graph of `h`, one dimension higher. Only this one-coordinate form of
Fubini's theorem is needed.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

variable {k : ℕ}

/-- Forget the last coordinate. -/
def dropLast : E (k + 1) →ₗ[ℝ] E k where
  toFun w := WithLp.toLp 2 fun i : Fin k => w i.castSucc
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl

/-- Append a zero last coordinate. -/
def appendZero : E k →ₗ[ℝ] E (k + 1) where
  toFun y := WithLp.toLp 2 (Fin.snoc (α := fun _ : Fin (k + 1) => ℝ) (fun i => y i) 0)
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

@[simp] lemma dropLast_apply (w : E (k + 1)) (i : Fin k) : dropLast w i = w i.castSucc := rfl

@[simp] lemma appendZero_castSucc (y : E k) (i : Fin k) : appendZero y i.castSucc = y i := by
  simp [appendZero]

@[simp] lemma appendZero_last (y : E k) : appendZero y (Fin.last k) = 0 := by
  simp [appendZero]

@[simp] lemma dropLast_appendZero (y : E k) : dropLast (appendZero y) = y := by
  ext i
  simp

/-- A site with vanishing last coordinate does not see the last coordinate. -/
lemma inner_appendZero (w : E (k + 1)) (y : E k) : ⟪w, appendZero y⟫ = ⟪dropLast w, y⟫ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fin.sum_univ_castSucc]
  simp

lemma norm_appendZero (y : E k) : ‖appendZero y‖ = ‖y‖ := by
  have h : ‖appendZero y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
    simp
  calc ‖appendZero y‖ = Real.sqrt (‖appendZero y‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖y‖ ^ 2) := by rw [h]
    _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)

lemma measurable_dropLast : Measurable (dropLast : E (k + 1) → E k) :=
  (LinearMap.continuous_of_finiteDimensional dropLast).measurable

lemma measurable_appendZero : Measurable (appendZero : E k → E (k + 1)) :=
  (LinearMap.continuous_of_finiteDimensional appendZero).measurable

lemma continuous_dropLast : Continuous (dropLast : E (k + 1) → E k) :=
  LinearMap.continuous_of_finiteDimensional dropLast

lemma continuous_last : Continuous fun w : E (k + 1) => w (Fin.last k) :=
  PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) (Fin.last k)

/-- The squared norm splits into the first `k` coordinates and the last one. -/
lemma norm_sq_eq_dropLast_add (w : E (k + 1)) :
    ‖w‖ ^ 2 = ‖dropLast w‖ ^ 2 + w (Fin.last k) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp

/-! ### The volume-preserving splitting -/

/-- Split off the last coordinate: `w ↦ (w_last, dropLast w)`. -/
def lastSplit (k : ℕ) : E (k + 1) → ℝ × E k :=
  Prod.map id (WithLp.toLp 2) ∘
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)) ∘ WithLp.ofLp

lemma lastSplit_fst (w : E (k + 1)) : (lastSplit k w).1 = w (Fin.last k) := rfl

lemma lastSplit_snd (w : E (k + 1)) : (lastSplit k w).2 = dropLast w := by
  ext j
  change w ((Fin.last k).succAbove j) = w j.castSucc
  rw [Fin.succAbove_last_apply]

theorem measurePreserving_lastSplit (k : ℕ) :
    MeasurePreserving (lastSplit k) volume
      ((volume : Measure ℝ).prod (volume : Measure (E k))) := by
  have h1 : MeasurePreserving (WithLp.ofLp : E (k + 1) → Fin (k + 1) → ℝ) volume volume :=
    PiLp.volume_preserving_ofLp (Fin (k + 1))
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k))
      volume ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
  have h3 : MeasurePreserving (Prod.map id (WithLp.toLp 2) : ℝ × (Fin k → ℝ) → ℝ × E k)
      ((volume : Measure ℝ).prod (volume : Measure (Fin k → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (E k))) :=
    (MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin k))
  exact h3.comp (h2.comp h1)

/-- Integration over `E (k + 1)` in split coordinates: the last coordinate is integrated first. -/
theorem lintegral_comp_lastSplit {G : ℝ × E k → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ w, G (lastSplit k w) = ∫⁻ x, ∫⁻ t, G (t, x) := by
  rw [(measurePreserving_lastSplit k).lintegral_comp hG,
    lintegral_prod_symm _ hG.aemeasurable]

/-! ### Power densities as marginals -/

/-- The unnormalized source with density `h ^ r` on `U`. -/
def powerMeasure (U : Set (E k)) (h : E k → ℝ) (r : ℕ) : Measure (E k) :=
  (volume.restrict U).withDensity fun x => ENNReal.ofReal (h x ^ r)

/-- The region under the graph of `h` over `U`. -/
def subgraph (U : Set (E k)) (h : E k → ℝ) : Set (E (k + 1)) :=
  {w | dropLast w ∈ U ∧ 0 < w (Fin.last k) ∧ w (Fin.last k) < h (dropLast w)}

lemma measurableSet_subgraph {U : Set (E k)} (hU : MeasurableSet U) {h : E k → ℝ}
    (hh : Measurable h) : MeasurableSet (subgraph U h) :=
  (measurable_dropLast hU).inter
    ((measurableSet_lt measurable_const continuous_last.measurable).inter
      (measurableSet_lt continuous_last.measurable (hh.comp measurable_dropLast)))

/-- **One-coordinate Fubini for power densities.** The density `h ^ r` on the
region under the graph of `h` has marginal density `h ^ (r + 1)`. -/
theorem map_dropLast_powerMeasure {U : Set (E k)} (hU : MeasurableSet U) {h : E k → ℝ}
    (hh : Measurable h) (hpos : ∀ x ∈ U, 0 ≤ h x) (r : ℕ) :
    Measure.map dropLast (powerMeasure (subgraph U h) (fun w => h (dropLast w)) r) =
      powerMeasure U h (r + 1) := by
  ext A hA
  have hsub := measurableSet_subgraph hU hh
  have hpre : MeasurableSet (dropLast ⁻¹' A : Set (E (k + 1))) := measurable_dropLast hA
  rw [Measure.map_apply measurable_dropLast hA, powerMeasure, powerMeasure,
    withDensity_apply _ hpre, withDensity_apply _ hA,
    Measure.restrict_restrict hpre, Measure.restrict_restrict hA,
    ← lintegral_indicator (hpre.inter hsub), ← lintegral_indicator (hA.inter hU)]
  -- the planar integrand
  obtain ⟨S, hS⟩ : ∃ S : Set (ℝ × E k),
      S = {p | p.2 ∈ A ∧ p.2 ∈ U ∧ 0 < p.1 ∧ p.1 < h p.2} := ⟨_, rfl⟩
  have hSm : MeasurableSet S := by
    rw [hS]
    exact (measurable_snd hA).inter ((measurable_snd hU).inter
      ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst (hh.comp measurable_snd))))
  obtain ⟨F, hF⟩ : ∃ F : ℝ × E k → ℝ≥0∞, F = fun p => ENNReal.ofReal (h p.2 ^ r) := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact ENNReal.measurable_ofReal.comp ((hh.comp measurable_snd).pow_const r)
  have hleft : ∀ w : E (k + 1),
      (dropLast ⁻¹' A ∩ subgraph U h).indicator
        (fun w => ENNReal.ofReal (h (dropLast w) ^ r)) w =
      S.indicator F (lastSplit k w) := by
    intro w
    have hmem : w ∈ dropLast ⁻¹' A ∩ subgraph U h ↔ lastSplit k w ∈ S := by
      rw [hS]
      change (dropLast w ∈ A ∧ dropLast w ∈ U ∧ 0 < w (Fin.last k) ∧
          w (Fin.last k) < h (dropLast w)) ↔
        ((lastSplit k w).2 ∈ A ∧ (lastSplit k w).2 ∈ U ∧ 0 < (lastSplit k w).1 ∧
          (lastSplit k w).1 < h (lastSplit k w).2)
      rw [lastSplit_snd, lastSplit_fst]
    by_cases hw : w ∈ dropLast ⁻¹' A ∩ subgraph U h
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hmem.mp hw), hF]
      change ENNReal.ofReal (h (dropLast w) ^ r) = ENNReal.ofReal (h (lastSplit k w).2 ^ r)
      rw [lastSplit_snd]
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun hc => hw (hmem.mpr hc))]
  simp_rw [hleft]
  rw [lintegral_comp_lastSplit (hFm.indicator hSm)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A ∩ U
  · have hslice : ∀ t : ℝ, S.indicator F (t, x) =
        (Set.Ioo 0 (h x)).indicator (fun _ => ENNReal.ofReal (h x ^ r)) t := by
      intro t
      by_cases ht : t ∈ Set.Ioo 0 (h x)
      · have hin : (t, x) ∈ S := by
          rw [hS]
          exact ⟨hx.1, hx.2, ht.1, ht.2⟩
        rw [Set.indicator_of_mem hin, Set.indicator_of_mem ht, hF]
      · have hout : (t, x) ∉ S := by
          rw [hS]
          intro hc
          exact ht ⟨hc.2.2.1, hc.2.2.2⟩
        rw [Set.indicator_of_notMem hout, Set.indicator_of_notMem ht]
    simp_rw [hslice]
    rw [lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero,
      Set.indicator_of_mem hx, ← ENNReal.ofReal_mul (pow_nonneg (hpos x hx.2) r), pow_succ]
  · have hslice : ∀ t : ℝ, S.indicator F (t, x) = 0 := by
      intro t
      apply Set.indicator_of_notMem
      rw [hS]
      intro hc
      exact hx ⟨hc.1, hc.2.1⟩
    simp_rw [hslice]
    rw [lintegral_zero, Set.indicator_of_notMem hx]

/-! ### Geometry of the region under a concave graph -/

/-- The point with first coordinates `x` and last coordinate `t`. -/
def appendLast (x : E k) (t : ℝ) : E (k + 1) :=
  WithLp.toLp 2 (Fin.snoc (α := fun _ : Fin (k + 1) => ℝ) (fun i => x i) t)

@[simp] lemma dropLast_appendLast (x : E k) (t : ℝ) : dropLast (appendLast x t) = x := by
  ext i
  simp [appendLast]

@[simp] lemma appendLast_last (x : E k) (t : ℝ) : appendLast x t (Fin.last k) = t := by
  simp [appendLast]

lemma subgraph_nonempty {U : Set (E k)} {h : E k → ℝ} (hU : U.Nonempty)
    (hpos : ∀ x ∈ U, 0 < h x) : (subgraph U h).Nonempty := by
  obtain ⟨x, hx⟩ := hU
  refine ⟨appendLast x (h x / 2), ?_⟩
  change dropLast (appendLast x (h x / 2)) ∈ U ∧ 0 < appendLast x (h x / 2) (Fin.last k) ∧
    appendLast x (h x / 2) (Fin.last k) < h (dropLast (appendLast x (h x / 2)))
  rw [dropLast_appendLast, appendLast_last]
  exact ⟨hx, by linarith [hpos x hx], by linarith [hpos x hx]⟩

lemma norm_le_of_mem_subgraph {U : Set (E k)} {h : E k → ℝ} {R η : ℝ}
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hη : ∀ x ∈ U, h x ≤ η) {w : E (k + 1)}
    (hw : w ∈ subgraph U h) : ‖w‖ ≤ Real.sqrt (R ^ 2 + η ^ 2) := by
  obtain ⟨hwU, h0, h1⟩ := hw
  have hsq := norm_sq_eq_dropLast_add w
  have h2 : ‖dropLast w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hR _ hwU) 2
  have h3 : w (Fin.last k) ^ 2 ≤ η ^ 2 :=
    pow_le_pow_left₀ h0.le (h1.le.trans (hη _ hwU)) 2
  exact (le_abs_self _).trans (Real.abs_le_sqrt (by linarith))

lemma convex_subgraph {U : Set (E k)} {h : E k → ℝ} (hconc : ConcaveOn ℝ U h) :
    Convex ℝ (subgraph U h) := by
  intro w hw w' hw' a b ha hb hab
  obtain ⟨hwU, h0, h1⟩ := hw
  obtain ⟨hwU', h0', h1'⟩ := hw'
  have hlast : (a • w + b • w') (Fin.last k) = a * w (Fin.last k) + b * w' (Fin.last k) := rfl
  have hdrop : dropLast (a • w + b • w') = a • dropLast w + b • dropLast w' := by
    rw [map_add, map_smul, map_smul]
  have hc := hconc.2 hwU hwU' ha hb hab
  simp only [smul_eq_mul] at hc
  change dropLast (a • w + b • w') ∈ U ∧ 0 < (a • w + b • w') (Fin.last k) ∧
    (a • w + b • w') (Fin.last k) < h (dropLast (a • w + b • w'))
  rw [hdrop, hlast]
  refine ⟨hconc.1 hwU hwU' ha hb hab, ?_, ?_⟩
  · rcases ha.eq_or_lt with ha0 | ha0
    · have hb1 : b = 1 := by linarith
      rw [← ha0, hb1]
      simpa using h0'
    · linarith [mul_pos ha0 h0, mul_nonneg hb h0'.le]
  · have hlt : a * w (Fin.last k) + b * w' (Fin.last k) <
        a * h (dropLast w) + b * h (dropLast w') := by
      rcases ha.eq_or_lt with ha0 | ha0
      · have hb1 : b = 1 := by linarith
        rw [← ha0, hb1]
        simpa using h1'
      · linarith [mul_lt_mul_of_pos_left h1 ha0, mul_le_mul_of_nonneg_left h1'.le hb]
    linarith

lemma isOpen_subgraph {U : Set (E k)} {h : E k → ℝ} (hU : IsOpen U)
    (hh : ContinuousOn h U) : IsOpen (subgraph U h) := by
  have hV : IsOpen (dropLast ⁻¹' U : Set (E (k + 1))) := hU.preimage continuous_dropLast
  have hcont : ContinuousOn (fun w : E (k + 1) => h (dropLast w) - w (Fin.last k))
      (dropLast ⁻¹' U) :=
    (hh.comp continuous_dropLast.continuousOn fun w hw => hw).sub continuous_last.continuousOn
  have h1 : IsOpen ((dropLast ⁻¹' U : Set (E (k + 1))) ∩
      (fun w : E (k + 1) => h (dropLast w) - w (Fin.last k)) ⁻¹' Set.Ioi 0) :=
    hcont.isOpen_inter_preimage hV isOpen_Ioi
  have h2 : IsOpen {w : E (k + 1) | 0 < w (Fin.last k)} :=
    isOpen_lt continuous_const continuous_last
  have heq : subgraph U h = ((dropLast ⁻¹' U : Set (E (k + 1))) ∩
      (fun w : E (k + 1) => h (dropLast w) - w (Fin.last k)) ⁻¹' Set.Ioi 0) ∩
      {w | 0 < w (Fin.last k)} := by
    ext w
    constructor
    · rintro ⟨hw, h0, h1⟩
      exact ⟨⟨hw, sub_pos.mpr h1⟩, h0⟩
    · rintro ⟨⟨hw, h1⟩, h0⟩
      exact ⟨hw, h0, sub_pos.mp h1⟩
  rw [heq]
  exact h1.inter h2

/-! ### Normalized power sources -/

/-- The probability source with density proportional to `h ^ r` on `U`. -/
def powerSource (U : Set (E k)) (h : E k → ℝ) (r : ℕ) : Measure (E k) :=
  (powerMeasure U h r Set.univ)⁻¹ • powerMeasure U h r

/-- The normalized form of the one-coordinate Fubini theorem. -/
theorem map_dropLast_powerSource {U : Set (E k)} (hU : MeasurableSet U) {h : E k → ℝ}
    (hh : Measurable h) (hpos : ∀ x ∈ U, 0 ≤ h x) (r : ℕ) :
    Measure.map dropLast (powerSource (subgraph U h) (fun w => h (dropLast w)) r) =
      powerSource U h (r + 1) := by
  have hmap := map_dropLast_powerMeasure hU hh hpos r
  have hmass : powerMeasure (subgraph U h) (fun w => h (dropLast w)) r Set.univ =
      powerMeasure U h (r + 1) Set.univ := by
    rw [← hmap, Measure.map_apply measurable_dropLast MeasurableSet.univ, Set.preimage_univ]
  unfold powerSource
  rw [Measure.map_smul _ measurable_dropLast.aemeasurable, hmap, hmass]

lemma powerMeasure_univ (U : Set (E k)) (h : E k → ℝ) (r : ℕ) :
    powerMeasure U h r Set.univ = ∫⁻ x in U, ENNReal.ofReal (h x ^ r) := by
  rw [powerMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

lemma powerMeasure_univ_ne_top {U : Set (E k)} {h : E k → ℝ}
    {η : ℝ} (hvol : volume U ≠ ∞) (hpos : ∀ x ∈ U, 0 ≤ h x) (hη : ∀ x ∈ U, h x ≤ η) (r : ℕ) :
    powerMeasure U h r Set.univ ≠ ∞ := by
  rw [powerMeasure_univ]
  have hle : (∫⁻ x in U, ENNReal.ofReal (h x ^ r)) ≤ ∫⁻ _ in U, ENNReal.ofReal (η ^ r) := by
    apply setLIntegral_mono measurable_const
    intro x hx
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hpos x hx) (hη x hx) r)
  rw [setLIntegral_const] at hle
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvol) hle

lemma powerMeasure_univ_pos {U : Set (E k)} (hU : MeasurableSet U) {h : E k → ℝ}
    (hh : Measurable h) (hvol : volume U ≠ 0) (hpos : ∀ x ∈ U, 0 < h x) (r : ℕ) :
    0 < powerMeasure U h r Set.univ := by
  rw [powerMeasure_univ, pos_iff_ne_zero]
  intro hzero
  have hm : Measurable fun x => ENNReal.ofReal (h x ^ r) :=
    ENNReal.measurable_ofReal.comp (hh.pow_const r)
  rw [lintegral_eq_zero_iff hm] at hzero
  have hnull : (volume.restrict U) {x | ¬ ENNReal.ofReal (h x ^ r) = 0} = 0 := ae_iff.mp hzero
  have hsub : U ⊆ {x | ¬ ENNReal.ofReal (h x ^ r) = 0} := by
    intro x hx
    change ¬ ENNReal.ofReal (h x ^ r) = 0
    rw [ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (hpos x hx) r
  have hU0 : (volume.restrict U) U = 0 := measure_mono_null hsub hnull
  rw [Measure.restrict_apply hU, Set.inter_self] at hU0
  exact hvol hU0

lemma powerSource_isProbabilityMeasure {U : Set (E k)} (hU : MeasurableSet U) {h : E k → ℝ}
    (hh : Measurable h) {η : ℝ} (hvol0 : volume U ≠ 0) (hvol : volume U ≠ ∞)
    (hpos : ∀ x ∈ U, 0 < h x) (hη : ∀ x ∈ U, h x ≤ η) (r : ℕ) :
    IsProbabilityMeasure (powerSource U h r) := by
  refine ⟨?_⟩
  rw [powerSource, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (powerMeasure_univ_pos hU hh hvol0 hpos r).ne'
    (powerMeasure_univ_ne_top hvol (fun x hx => (hpos x hx).le) hη r)

lemma powerSource_absolutelyContinuous (U : Set (E k)) (h : E k → ℝ) (r : ℕ) :
    powerSource U h r ≪ volume := by
  unfold powerSource powerMeasure
  exact (Measure.AbsolutelyContinuous.smul_left
    ((withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous) _)

lemma ae_mem_powerSource {U : Set (E k)} (hU : MeasurableSet U) (h : E k → ℝ) (r : ℕ) :
    ∀ᵐ x ∂powerSource U h r, x ∈ U := by
  unfold powerSource powerMeasure
  apply Measure.ae_smul_measure
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hU)

end

end BrenierMoment
