module

public import OAI.Analysis.Brenier.TransportCore
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

/-!
# Uniform laws on coordinate boxes

The cube computations of the upstream development are repeated for a box whose
sides are arbitrary intervals. The fixed source of the sharpness example,
`[0,1] × [-1,1]^(d-1)`, is such a box. Planar events are evaluated by slices,
so only one-dimensional integrals of explicit functions remain.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-- The closed coordinate box with sides `[lo k, hi k]`. -/
def coordBox (lo hi : Fin d → ℝ) : Set (E d) :=
  {x | ∀ k, x k ∈ Set.Icc (lo k) (hi k)}

theorem coordBox_eq_preimage_pi (lo hi : Fin d → ℝ) :
    coordBox lo hi = (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
      (Set.univ.pi fun k => Set.Icc (lo k) (hi k)) := by
  ext x
  exact ⟨fun h k _ => h k, fun h k => h k (Set.mem_univ k)⟩

theorem isCompact_coordBox (lo hi : Fin d → ℝ) : IsCompact (coordBox lo hi) := by
  have h : coordBox lo hi = (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      {x | ∀ k, x k ∈ Set.Icc (lo k) (hi k)} := by
    ext x
    exact Iff.rfl
  rw [h]
  exact (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isCompact_preimage.mpr
    (isCompact_pi_infinite fun _ => isCompact_Icc)

theorem convex_coordBox (lo hi : Fin d → ℝ) : Convex ℝ (coordBox lo hi) := by
  intro x hx y hy a b ha hb hab k
  have hxk := hx k
  have hyk := hy k
  have hlo : (a + b) * lo k = lo k := by rw [hab, one_mul]
  have hhi : (a + b) * hi k = hi k := by rw [hab, one_mul]
  change a * x k + b * y k ∈ Set.Icc (lo k) (hi k)
  constructor
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxk.1), mul_nonneg hb (sub_nonneg.mpr hyk.1)]
  · nlinarith [mul_nonneg ha (sub_nonneg.mpr hxk.2), mul_nonneg hb (sub_nonneg.mpr hyk.2)]

theorem interior_coordBox_nonempty {lo hi : Fin d → ℝ} (h : ∀ k, lo k < hi k) :
    (interior (coordBox lo hi)).Nonempty := by
  refine ⟨WithLp.toLp 2 (fun k => (lo k + hi k) / 2),
    mem_interior.mpr ⟨(PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) ⁻¹'
      (Set.univ.pi fun k => Set.Ioo (lo k) (hi k)), ?_, ?_, ?_⟩⟩
  · intro x hx k
    exact Set.Ioo_subset_Icc_self (hx k (Set.mem_univ k))
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).preimage
      (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).continuous
  · intro k _
    change (lo k + hi k) / 2 ∈ Set.Ioo (lo k) (hi k)
    constructor <;> linarith [h k]

theorem volume_coordBox (lo hi : Fin d → ℝ) :
    volume (coordBox lo hi) = ∏ k, ENNReal.ofReal (hi k - lo k) := by
  rw [coordBox_eq_preimage_pi,
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)).nullMeasurableSet,
    volume_pi_pi]
  simp only [Real.volume_Icc]

lemma volume_coordBox_ne_zero {lo hi : Fin d → ℝ} (h : ∀ k, lo k < hi k) :
    volume (coordBox lo hi) ≠ 0 := by
  rw [volume_coordBox]
  exact Finset.prod_ne_zero_iff.mpr fun k _ =>
    (ENNReal.ofReal_pos.mpr (sub_pos.mpr (h k))).ne'

lemma volume_coordBox_ne_top (lo hi : Fin d → ℝ) :
    volume (coordBox lo hi) ≠ ∞ := by
  rw [volume_coordBox]
  exact ENNReal.prod_ne_top fun k _ => ENNReal.ofReal_ne_top

theorem uniformMeasure_coordBox_isProbabilityMeasure {lo hi : Fin d → ℝ}
    (h : ∀ k, lo k < hi k) :
    IsProbabilityMeasure (uniformMeasure (coordBox lo hi)) := by
  refine ⟨?_⟩
  rw [uniformMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (volume_coordBox_ne_zero h) (volume_coordBox_ne_top lo hi)

/-- The uniform probability law on `[a, b]`. -/
def intervalLaw (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Set.Icc a b)

lemma intervalLaw_isProbabilityMeasure {a b : ℝ} (h : a < b) :
    IsProbabilityMeasure (intervalLaw a b) := by
  refine ⟨?_⟩
  rw [intervalLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Real.volume_Icc, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (sub_pos.mpr h)).ne'
    ENNReal.ofReal_ne_top

instance intervalLaw_sFinite (a b : ℝ) : SFinite (intervalLaw a b) := by
  unfold intervalLaw
  infer_instance

lemma ae_mem_intervalLaw (a b : ℝ) : ∀ᵐ t ∂intervalLaw a b, t ∈ Set.Icc a b :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

/-- Restricting Euclidean volume to the box gives the product of the interval restrictions. -/
theorem map_ofLp_volume_restrict_coordBox (lo hi : Fin d → ℝ) :
    Measure.map (@WithLp.ofLp 2 (Fin d → ℝ)) (volume.restrict (coordBox lo hi)) =
      Measure.pi (fun k : Fin d => volume.restrict (Set.Icc (lo k) (hi k))) := by
  rw [coordBox_eq_preimage_pi,
    (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
      (MeasurableSet.univ_pi (fun _ => measurableSet_Icc)) |>.map_eq,
    volume_pi, Measure.restrict_pi_pi]

/-- The normalized box law is the product of the normalized interval laws. -/
theorem map_ofLp_uniformMeasure_coordBox {lo hi : Fin d → ℝ} (h : ∀ k, lo k < hi k) :
    Measure.map (@WithLp.ofLp 2 (Fin d → ℝ)) (uniformMeasure (coordBox lo hi)) =
      Measure.pi (fun k : Fin d => intervalLaw (lo k) (hi k)) := by
  have hinv : (∏ k, ENNReal.ofReal (hi k - lo k))⁻¹ =
      ∏ k, (ENNReal.ofReal (hi k - lo k))⁻¹ :=
    ENNReal.prod_inv_distrib fun i _ j _ _ =>
      Or.inl (ENNReal.ofReal_pos.mpr (sub_pos.mpr (h i))).ne'
  have hprob : ∀ k, IsProbabilityMeasure (intervalLaw (lo k) (hi k)) :=
    fun k => intervalLaw_isProbabilityMeasure (h k)
  rw [uniformMeasure,
    Measure.map_smul _ (PiLp.volume_preserving_ofLp (Fin d)).measurable.aemeasurable,
    volume_coordBox, map_ofLp_volume_restrict_coordBox]
  apply (Measure.pi_eq fun s hs => ?_).symm
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, intervalLaw]
  rw [Finset.prod_mul_distrib, hinv]

theorem measurePreserving_ofLp_uniformMeasure_coordBox {lo hi : Fin d → ℝ}
    (h : ∀ k, lo k < hi k) :
    MeasurePreserving (@WithLp.ofLp 2 (Fin d → ℝ)) (uniformMeasure (coordBox lo hi))
      (Measure.pi (fun k : Fin d => intervalLaw (lo k) (hi k))) :=
  ⟨(PiLp.volume_preserving_ofLp (Fin d)).measurable, map_ofLp_uniformMeasure_coordBox h⟩

/-- Two distinct coordinates of the uniform box have the product interval law. -/
theorem measurePreserving_coordPair_uniformMeasure_coordBox {lo hi : Fin d → ℝ}
    (h : ∀ k, lo k < hi k) (i j : Fin d) (hij : i ≠ j) :
    MeasurePreserving (fun x : E d => (x i, x j)) (uniformMeasure (coordBox lo hi))
      ((intervalLaw (lo i) (hi i)).prod (intervalLaw (lo j) (hi j))) := by
  have hprob : ∀ k, IsProbabilityMeasure (intervalLaw (lo k) (hi k)) :=
    fun k => intervalLaw_isProbabilityMeasure (h k)
  have hind : ProbabilityTheory.iIndepFun
      (fun i : Fin d => fun x : Fin d → ℝ => x i)
      (Measure.pi (fun k : Fin d => intervalLaw (lo k) (hi k))) :=
    ProbabilityTheory.iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hp : MeasurePreserving (fun x : Fin d → ℝ => (x i, x j))
      (Measure.pi (fun k : Fin d => intervalLaw (lo k) (hi k)))
      ((intervalLaw (lo i) (hi i)).prod (intervalLaw (lo j) (hi j))) := by
    refine ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), ?_⟩
    rw [(hind.indepFun hij).map_prod_eq_prod_map_map
      (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable,
      (measurePreserving_eval (fun k : Fin d => intervalLaw (lo k) (hi k)) i).map_eq,
      (measurePreserving_eval (fun k : Fin d => intervalLaw (lo k) (hi k)) j).map_eq]
  exact hp.comp (measurePreserving_ofLp_uniformMeasure_coordBox h)

/-- A planar event in two distinct coordinates is evaluated in the product law. -/
theorem uniformMeasure_coordBox_coordPair_preimage {lo hi : Fin d → ℝ}
    (h : ∀ k, lo k < hi k) (i j : Fin d) (hij : i ≠ j)
    (s : Set (ℝ × ℝ)) (hs : MeasurableSet s) :
    uniformMeasure (coordBox lo hi) ((fun x : E d => (x i, x j)) ⁻¹' s) =
      ((intervalLaw (lo i) (hi i)).prod (intervalLaw (lo j) (hi j))) s :=
  (measurePreserving_coordPair_uniformMeasure_coordBox h i j hij).measure_preimage
    hs.nullMeasurableSet

/-- Slice formula for a planar event whose slices over the first factor have known mass. -/
theorem prod_intervalLaw_of_slices {a b a' b' : ℝ} {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    {len : ℝ → ℝ}
    (hslice : ∀ s ∈ Set.Icc a b,
      intervalLaw a' b' (Prod.mk s ⁻¹' S) = ENNReal.ofReal (len s)) :
    ((intervalLaw a b).prod (intervalLaw a' b')) S =
      ∫⁻ s, ENNReal.ofReal (len s) ∂intervalLaw a b := by
  rw [Measure.prod_apply hS]
  apply lintegral_congr_ae
  filter_upwards [ae_mem_intervalLaw a b] with s hs
  exact hslice s hs

lemma intervalLaw_unit_Ioc {g h : ℝ} (h0 : 0 ≤ g) (_hgh : g ≤ h) (h1 : h ≤ 1) :
    intervalLaw 0 1 (Set.Ioc g h) = ENNReal.ofReal (h - g) := by
  have hsub : Set.Ioc g h ⊆ Set.Icc 0 1 :=
    fun t ht => ⟨h0.trans ht.1.le, ht.2.trans h1⟩
  rw [intervalLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.mpr hsub, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, inv_one,
    smul_eq_mul, one_mul]

lemma intervalLaw_unit_Iic {c : ℝ} (_h0 : 0 ≤ c) (h1 : c ≤ 1) :
    intervalLaw 0 1 (Set.Iic c) = ENNReal.ofReal c := by
  have hset : Set.Iic c ∩ Set.Icc 0 1 = Set.Icc 0 c := by
    ext t
    constructor
    · rintro ⟨htc, ht0, -⟩
      exact ⟨ht0, htc⟩
    · rintro ⟨ht0, htc⟩
      exact ⟨htc, ht0, htc.trans h1⟩
  rw [intervalLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hset,
    Real.volume_Icc, sub_zero, sub_zero, ENNReal.ofReal_one, inv_one, smul_eq_mul, one_mul]

lemma intervalLaw_unit_Ioi {c : ℝ} (h0 : 0 ≤ c) (_h1 : c ≤ 1) :
    intervalLaw 0 1 (Set.Ioi c) = ENNReal.ofReal (1 - c) := by
  have hset : Set.Ioi c ∩ Set.Icc 0 1 = Set.Ioc c 1 := by
    ext t
    constructor
    · rintro ⟨htc, -, ht1⟩
      exact ⟨htc, ht1⟩
    · rintro ⟨htc, ht1⟩
      exact ⟨htc, h0.trans htc.le, ht1⟩
  rw [intervalLaw, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi, hset,
    Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, inv_one, smul_eq_mul, one_mul]

/-- Slice formula: the region between two graphs over the first factor, when the
second factor is uniform on `[0, 1]` and the graphs stay inside it. -/
theorem prod_intervalLaw_region {a b : ℝ} {g h : ℝ → ℝ}
    (hg : Measurable g) (hh : Measurable h)
    (hbd : ∀ s ∈ Set.Icc a b, 0 ≤ g s ∧ g s ≤ h s ∧ h s ≤ 1) :
    ((intervalLaw a b).prod (intervalLaw 0 1)) {p : ℝ × ℝ | g p.1 < p.2 ∧ p.2 ≤ h p.1} =
      ∫⁻ s, ENNReal.ofReal (h s - g s) ∂intervalLaw a b := by
  have hS : MeasurableSet {p : ℝ × ℝ | g p.1 < p.2 ∧ p.2 ≤ h p.1} :=
    (measurableSet_lt (hg.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (hh.comp measurable_fst))
  rw [prod_intervalLaw_of_slices hS (len := fun s => h s - g s)]
  intro s hs
  obtain ⟨h0, hgh, h1⟩ := hbd s hs
  have hpre : Prod.mk s ⁻¹' {p : ℝ × ℝ | g p.1 < p.2 ∧ p.2 ≤ h p.1} =
      Set.Ioc (g s) (h s) := by
    ext t
    exact Iff.rfl
  rw [hpre, intervalLaw_unit_Ioc h0 hgh h1]

/-! ### One-dimensional integrals against the uniform law on `[-1, 1]` -/

lemma integrable_intervalLaw_of_continuous {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f (intervalLaw a b) :=
  hf.continuousOn.integrableOn_Icc.smul_measure
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne')

lemma integral_intervalLaw_symm (f : ℝ → ℝ) :
    (∫ t, f t ∂intervalLaw (-1) 1) = (1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, f t := by
  rw [intervalLaw, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by norm_num), smul_eq_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num

lemma integral_affine_intervalLaw_symm (α β : ℝ) :
    (∫ t, α + β * t ∂intervalLaw (-1) 1) = α := by
  have hconst : IntervalIntegrable (fun _ : ℝ => α) volume (-1) 1 :=
    continuous_const.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun t : ℝ => β * t) volume (-1) 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [integral_intervalLaw_symm, intervalIntegral.integral_add hconst hlin,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

lemma intervalIntegral_abs_symm : (∫ t in (-1 : ℝ)..1, |t|) = 1 := by
  have hn : (∫ t in (-1 : ℝ)..0, |t|) = ∫ t in (-1 : ℝ)..0, -t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
    exact abs_of_nonpos ht.2
  have hp : (∫ t in (0 : ℝ)..1, |t|) = ∫ t in (0 : ℝ)..1, t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact abs_of_nonneg ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (continuous_abs.intervalIntegrable (-1) 0) (continuous_abs.intervalIntegrable 0 1),
    hn, hp, intervalIntegral.integral_neg, integral_id, integral_id]
  norm_num

lemma integral_mul_abs_intervalLaw_symm (β : ℝ) :
    (∫ t, β * |t| ∂intervalLaw (-1) 1) = β / 2 := by
  rw [integral_const_mul, integral_intervalLaw_symm, intervalIntegral_abs_symm]
  ring

lemma lintegral_affine_intervalLaw_symm {α β : ℝ} (hαβ : |β| ≤ α) :
    (∫⁻ t, ENNReal.ofReal (α + β * t) ∂intervalLaw (-1) 1) = ENNReal.ofReal α := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_intervalLaw_of_continuous (by norm_num) (f := fun t : ℝ => α + β * t)
      (continuous_const.add (continuous_const.mul continuous_id)))]
  · rw [integral_affine_intervalLaw_symm]
  · filter_upwards [ae_mem_intervalLaw (-1) 1] with t ht
    have ht' : |t| ≤ 1 := abs_le.mpr ht
    have hbt : |β * t| ≤ α := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left ht' (abs_nonneg β)).trans (by simpa using hαβ)
    have := neg_abs_le (β * t)
    change 0 ≤ α + β * t
    linarith

lemma lintegral_mul_abs_intervalLaw_symm {β : ℝ} (hβ : 0 ≤ β) :
    (∫⁻ t, ENNReal.ofReal (β * |t|) ∂intervalLaw (-1) 1) = ENNReal.ofReal (β / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_intervalLaw_of_continuous (by norm_num) (f := fun t : ℝ => β * |t|)
      (continuous_const.mul continuous_abs))]
  · rw [integral_mul_abs_intervalLaw_symm]
  · exact Filter.Eventually.of_forall fun t => mul_nonneg hβ (abs_nonneg t)

end

end BrenierMoment
