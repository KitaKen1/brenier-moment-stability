module

public import BrenierMoment.FiniteTargets
public import OAI.Analysis.Brenier.MapLimits

@[expose] public section

/-!
# Targets with finite second moment

A target with finite second moment is approximated by its images under a
fixed sequence of simple functions converging to the identity. The active
maps of the finite approximations form a Cauchy sequence in `L²` of the
source: the clipped estimate controls the clipped maps, and the part removed
by the clipping is small uniformly along the sequence. The limit is a map
onto the target, and it is the unique optimal map by
`LimitCertificate.lean`. The clipped estimate passes to the limit maps of two
targets, with the cost of any coupling of the targets on the right.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358 Filter
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

variable {d : ℕ}

/-! ### Quantizers -/

/-- Simple functions approximating the identity of `E d`. -/
def quantizer (d : ℕ) (n : ℕ) : E d → E d :=
  ⇑(SimpleFunc.approxOn (id : E d → E d) measurable_id Set.univ 0 (Set.mem_univ 0) n)

lemma measurable_quantizer (n : ℕ) : Measurable (quantizer d n) :=
  SimpleFunc.measurable _

lemma finite_range_quantizer (n : ℕ) : (Set.range (quantizer d n)).Finite :=
  SimpleFunc.finite_range _

lemma tendsto_quantizer (y : E d) : Tendsto (fun n => quantizer d n y) atTop (𝓝 y) :=
  SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ (0 : E d)) (by simp)

lemma norm_quantizer_sub_le (n : ℕ) (y : E d) : ‖quantizer d n y - y‖ ≤ ‖y‖ := by
  have h := SimpleFunc.edist_approxOn_le (f := (id : E d → E d)) measurable_id
    (Set.mem_univ (0 : E d)) y n
  rw [edist_dist, edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg, dist_eq_norm,
    dist_eq_norm, zero_sub, norm_neg] at h
  exact h

lemma isSupported_map_quantizer (μ : Measure (E d)) (n : ℕ) :
    IsSupported (Measure.map (quantizer d n) μ) (Set.range (quantizer d n)) := by
  have hpre : quantizer d n ⁻¹' (Set.range (quantizer d n))ᶜ = ∅ := by
    ext y
    constructor
    · intro hy
      exact (hy ⟨y, rfl⟩).elim
    · intro hy
      exact hy.elim
  unfold IsSupported
  rw [Measure.map_apply (measurable_quantizer n)
    (finite_range_quantizer n).measurableSet.compl, hpre, measure_empty]

/-- The quantizers converge to the identity in `L²` of a law with finite second moment. -/
lemma tendsto_lintegral_quantizer {μ : Measure (E d)}
    (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞) :
    Tendsto (fun n => ∫⁻ y, ENNReal.ofReal (‖quantizer d n y - y‖ ^ 2) ∂μ) atTop (𝓝 0) := by
  have hpt : ∀ y : E d,
      Tendsto (fun n => ENNReal.ofReal (‖quantizer d n y - y‖ ^ 2)) atTop (𝓝 0) := by
    intro y
    have h1 : Tendsto (fun n => ‖quantizer d n y - y‖ ^ 2) atTop (𝓝 (‖y - y‖ ^ 2)) :=
      (((tendsto_quantizer y).sub tendsto_const_nhds).norm).pow 2
    rw [sub_self, norm_zero] at h1
    have h2 : Tendsto (fun n => ENNReal.ofReal (‖quantizer d n y - y‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) := (ENNReal.continuous_ofReal.tendsto _).comp h1
    rw [zero_pow two_ne_zero, ENNReal.ofReal_zero] at h2
    exact h2
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun n y => ENNReal.ofReal (‖quantizer d n y - y‖ ^ 2)) (f := fun _ => 0)
    (fun y => ENNReal.ofReal (‖y‖ ^ 2))
    (fun n => ENNReal.measurable_ofReal.comp
      (((measurable_quantizer n).sub measurable_id).norm.pow_const 2))
    (fun n => Eventually.of_forall fun y =>
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_quantizer_sub_le n y) 2))
    hμ2 (Eventually.of_forall hpt)
  rw [lintegral_zero] at h
  exact h

/-- The part of a law removed by clipping at level `k` vanishes as `k → ∞`. -/
lemma tendsto_lintegral_sub_clipVec {μ : Measure (E d)}
    (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞) :
    Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (‖y - clipVec (k : ℝ) y‖ ^ 2) ∂μ) atTop (𝓝 0) := by
  have hpt : ∀ y : E d,
      Tendsto (fun k : ℕ => ENNReal.ofReal (‖y - clipVec (k : ℝ) y‖ ^ 2)) atTop (𝓝 0) := by
    intro y
    obtain ⟨N, hN⟩ := exists_nat_ge ‖y‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : ‖y‖ ≤ (k : ℝ) := hN.trans (by exact_mod_cast hk)
    rw [clipVec_eq_self hk', sub_self, norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero]
  have hbound : ∀ (k : ℕ) (y : E d),
      ENNReal.ofReal (‖y - clipVec (k : ℝ) y‖ ^ 2) ≤ ENNReal.ofReal (‖y‖ ^ 2) := by
    intro k y
    apply ENNReal.ofReal_le_ofReal
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    have h := sq_sub_clip_le (Nat.cast_nonneg k) (y j)
    simpa using h
  have h := tendsto_lintegral_of_dominated_convergence (μ := μ)
    (F := fun (k : ℕ) y => ENNReal.ofReal (‖y - clipVec (k : ℝ) y‖ ^ 2)) (f := fun _ => 0)
    (fun y => ENNReal.ofReal (‖y‖ ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp
      ((measurable_id.sub (measurable_clipVec _)).norm.pow_const 2))
    (fun k => Eventually.of_forall fun y => hbound k y) hμ2 (Eventually.of_forall hpt)
  rw [lintegral_zero] at h
  exact h

/-! ### Squared distances -/

/-- The squared `L²` distance of two maps, with values in `[0, ∞]`. -/
def sqDist (ρ : Measure (E d)) (T S : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖T x - S x‖ ^ 2) ∂ρ

lemma measurable_sq_norm_sub {α : Type*} [MeasurableSpace α] {A B : α → E d}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => ENNReal.ofReal (‖A x - B x‖ ^ 2) :=
  ENNReal.measurable_ofReal.comp ((hA.sub hB).norm.pow_const 2)

lemma mapL2Dist_sq_eq_toReal (ρ : Measure (E d)) {T S : E d → E d} (hT : Measurable T)
    (hS : Measurable S) : mapL2Dist ρ T S ^ 2 = (sqDist ρ T S).toReal := by
  rw [mapL2Dist_sq]
  exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
    ((hT.sub hS).norm.pow_const 2).aestronglyMeasurable

lemma sqDist_ne_top_of_memLp {ρ : Measure (E d)} {T S : E d → E d} (hT : MemLp T 2 ρ)
    (hS : MemLp S 2 ρ) : sqDist ρ T S ≠ ∞ := by
  have hint : Integrable (fun x => ‖T x - S x‖ ^ 2) ρ := (hT.sub hS).norm.integrable_sq
  unfold sqDist
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
  exact ENNReal.ofReal_ne_top

private lemma sq_le_slack_real {θ n p r s : ℝ} (hθ : 0 < θ) (hn0 : 0 ≤ n)
    (hn : n ≤ p + (r + s)) :
    n ^ 2 ≤ (1 + θ) * p ^ 2 + (1 + 1 / θ) * (2 * (r ^ 2 + s ^ 2)) := by
  have h1 : n ^ 2 ≤ (p + (r + s)) ^ 2 := pow_le_pow_left₀ hn0 hn 2
  have h2 : 2 * p * (r + s) ≤ θ * p ^ 2 + (r + s) ^ 2 / θ := by
    rw [← sub_nonneg]
    have e : θ * p ^ 2 + (r + s) ^ 2 / θ - 2 * p * (r + s) = (θ * p - (r + s)) ^ 2 / θ := by
      field_simp
      ring
    rw [e]
    positivity
  have h3 : (r + s) ^ 2 ≤ 2 * (r ^ 2 + s ^ 2) := by nlinarith [sq_nonneg (r - s)]
  have hθ' : 0 ≤ 1 + 1 / θ := by positivity
  have h4 : (1 + 1 / θ) * (r + s) ^ 2 ≤ (1 + 1 / θ) * (2 * (r ^ 2 + s ^ 2)) :=
    mul_le_mul_of_nonneg_left h3 hθ'
  have h5 : (r + s) ^ 2 / θ = 1 / θ * (r + s) ^ 2 := by ring
  nlinarith [h1, h2, h4, h5]

/-- The square of a distance, compared with the square of another distance up
to a factor `1 + θ`. -/
lemma norm_sq_sub_le_slack {θ : ℝ} (hθ : 0 < θ) (a b c e : E d) :
    ‖a - b‖ ^ 2 ≤
      (1 + θ) * ‖c - e‖ ^ 2 + (1 + 1 / θ) * (2 * (‖a - c‖ ^ 2 + ‖b - e‖ ^ 2)) := by
  have hsplit : a - b = (c - e) + ((a - c) - (b - e)) := by abel
  have hn : ‖a - b‖ ≤ ‖c - e‖ + (‖a - c‖ + ‖b - e‖) := by
    calc ‖a - b‖ = ‖(c - e) + ((a - c) - (b - e))‖ := by rw [← hsplit]
      _ ≤ ‖c - e‖ + ‖(a - c) - (b - e)‖ := norm_add_le _ _
      _ ≤ ‖c - e‖ + (‖a - c‖ + ‖b - e‖) := by linarith [norm_sub_le (a - c) (b - e)]
  exact sq_le_slack_real hθ (norm_nonneg _) hn

/-- The integrated form of `norm_sq_sub_le_slack`. -/
lemma lintegral_sq_sub_le_slack {α : Type*} [MeasurableSpace α] (ν : Measure α) {θ : ℝ}
    (hθ : 0 < θ) {A B C D : α → E d} (hA : Measurable A) (hB : Measurable B)
    (hC : Measurable C) (hD : Measurable D) :
    (∫⁻ x, ENNReal.ofReal (‖A x - B x‖ ^ 2) ∂ν) ≤
      ENNReal.ofReal (1 + θ) * (∫⁻ x, ENNReal.ofReal (‖C x - D x‖ ^ 2) ∂ν) +
        ENNReal.ofReal ((1 + 1 / θ) * 2) *
          ((∫⁻ x, ENNReal.ofReal (‖A x - C x‖ ^ 2) ∂ν) +
            ∫⁻ x, ENNReal.ofReal (‖B x - D x‖ ^ 2) ∂ν) := by
  have h1 : (0 : ℝ) ≤ 1 + θ := by positivity
  have h2 : (0 : ℝ) ≤ (1 + 1 / θ) * 2 := by positivity
  have hpt : ∀ x, ENNReal.ofReal (‖A x - B x‖ ^ 2) ≤
      ENNReal.ofReal (1 + θ) * ENNReal.ofReal (‖C x - D x‖ ^ 2) +
        ENNReal.ofReal ((1 + 1 / θ) * 2) *
          (ENNReal.ofReal (‖A x - C x‖ ^ 2) + ENNReal.ofReal (‖B x - D x‖ ^ 2)) := by
    intro x
    have h := norm_sq_sub_le_slack hθ (A x) (B x) (C x) (D x)
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul h1,
      ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    linarith [h]
  have hCD := measurable_sq_norm_sub hC hD
  have hAC := measurable_sq_norm_sub hA hC
  have hBD := measurable_sq_norm_sub hB hD
  have hsum : Measurable fun x =>
      ENNReal.ofReal (‖A x - C x‖ ^ 2) + ENNReal.ofReal (‖B x - D x‖ ^ 2) := hAC.add hBD
  calc (∫⁻ x, ENNReal.ofReal (‖A x - B x‖ ^ 2) ∂ν)
      ≤ ∫⁻ x, (ENNReal.ofReal (1 + θ) * ENNReal.ofReal (‖C x - D x‖ ^ 2) +
          ENNReal.ofReal ((1 + 1 / θ) * 2) *
            (ENNReal.ofReal (‖A x - C x‖ ^ 2) + ENNReal.ofReal (‖B x - D x‖ ^ 2))) ∂ν :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (1 + θ) * (∫⁻ x, ENNReal.ofReal (‖C x - D x‖ ^ 2) ∂ν) +
          ENNReal.ofReal ((1 + 1 / θ) * 2) *
            ((∫⁻ x, ENNReal.ofReal (‖A x - C x‖ ^ 2) ∂ν) +
              ∫⁻ x, ENNReal.ofReal (‖B x - D x‖ ^ 2) ∂ν) := by
        rw [lintegral_add_left (hCD.const_mul _), lintegral_const_mul _ hCD,
          lintegral_const_mul _ hsum, lintegral_add_left hAC]

/-- The squared distance of two maps is at most twice the sum of their squared
distances to a third map. -/
lemma lintegral_sq_sub_le_two {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {A B C : α → E d} (hA : Measurable A) (hB : Measurable B) (hC : Measurable C) :
    (∫⁻ x, ENNReal.ofReal (‖A x - B x‖ ^ 2) ∂ν) ≤
      2 * (∫⁻ x, ENNReal.ofReal (‖A x - C x‖ ^ 2) ∂ν) +
        2 * ∫⁻ x, ENNReal.ofReal (‖B x - C x‖ ^ 2) ∂ν := by
  have e : ∀ r : ℝ, ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
    intro r
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hpt : ∀ x, ENNReal.ofReal (‖A x - B x‖ ^ 2) ≤
      2 * ENNReal.ofReal (‖A x - C x‖ ^ 2) + 2 * ENNReal.ofReal (‖B x - C x‖ ^ 2) := by
    intro x
    have hn : ‖A x - B x‖ ≤ ‖A x - C x‖ + ‖B x - C x‖ := by
      have h0 : A x - B x = (A x - C x) - (B x - C x) := by abel
      rw [h0]
      exact norm_sub_le _ _
    have hsq := mul_self_le_mul_self (norm_nonneg (A x - B x)) hn
    have h3 : ‖A x - B x‖ ^ 2 ≤ 2 * ‖A x - C x‖ ^ 2 + 2 * ‖B x - C x‖ ^ 2 := by
      nlinarith [hsq, sq_nonneg (‖A x - C x‖ - ‖B x - C x‖)]
    rw [← e, ← e, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal h3
  have hAC := measurable_sq_norm_sub hA hC
  have hBC := measurable_sq_norm_sub hB hC
  calc (∫⁻ x, ENNReal.ofReal (‖A x - B x‖ ^ 2) ∂ν)
      ≤ ∫⁻ x, (2 * ENNReal.ofReal (‖A x - C x‖ ^ 2) +
          2 * ENNReal.ofReal (‖B x - C x‖ ^ 2)) ∂ν := lintegral_mono hpt
    _ = 2 * (∫⁻ x, ENNReal.ofReal (‖A x - C x‖ ^ 2) ∂ν) +
          2 * ∫⁻ x, ENNReal.ofReal (‖B x - C x‖ ^ 2) ∂ν := by
        rw [lintegral_add_left (hAC.const_mul _), lintegral_const_mul _ hAC,
          lintegral_const_mul _ hBC]

/-! ### Wasserstein distance of images -/

/-- The Wasserstein distance of the images of the two marginals of a coupling. -/
lemma ofReal_wasserstein2_sq_map_le {μ ν : Measure (E d)} {π : Measure (E d × E d)}
    (hπ : IsCoupling μ ν π) {A B : E d → E d} (hA : Measurable A) (hB : Measurable B)
    (hfin : (∫⁻ p, ENNReal.ofReal (‖A p.1 - B p.2‖ ^ 2) ∂π) ≠ ∞) :
    ENNReal.ofReal (wasserstein2 (Measure.map A μ) (Measure.map B ν) ^ 2) ≤
      ∫⁻ p, ENNReal.ofReal (‖A p.1 - B p.2‖ ^ 2) ∂π := by
  have hprob : IsProbabilityMeasure π := hπ.1
  have hpair : Measurable fun p : E d × E d => (A p.1, B p.2) :=
    (hA.comp measurable_fst).prodMk (hB.comp measurable_snd)
  have hcm : Measurable fun q : E d × E d => ENNReal.ofReal (‖q.1 - q.2‖ ^ 2) :=
    measurable_sq_norm_sub measurable_fst measurable_snd
  have hπ' : IsCoupling (Measure.map A μ) (Measure.map B ν)
      (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π) := by
    refine ⟨(Measure.isProbabilityMeasure_map_iff hpair.aemeasurable).mpr hprob, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hpair, ← hπ.2.1,
        Measure.map_map hA measurable_fst]
      rfl
    · rw [Measure.map_map measurable_snd hpair, ← hπ.2.2,
        Measure.map_map hB measurable_snd]
      rfl
  have hcost : quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π) =
      ∫⁻ p, ENNReal.ofReal (‖A p.1 - B p.2‖ ^ 2) ∂π := by
    unfold quadraticPlanCost
    rw [lintegral_map hcm hpair]
  have hfin' : quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π) ≠ ∞ := by
    rw [hcost]
    exact hfin
  have hW := wasserstein2_le_of_coupling hπ' hfin'
  have hsq : wasserstein2 (Measure.map A μ) (Measure.map B ν) ^ 2 ≤
      (quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π)).toReal := by
    calc wasserstein2 (Measure.map A μ) (Measure.map B ν) ^ 2
        ≤ Real.sqrt
            (quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π)).toReal ^ 2 :=
          pow_le_pow_left₀ (wasserstein2_nonneg _ _) hW 2
      _ = (quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π)).toReal :=
          Real.sq_sqrt ENNReal.toReal_nonneg
  calc ENNReal.ofReal (wasserstein2 (Measure.map A μ) (Measure.map B ν) ^ 2)
      ≤ ENNReal.ofReal
          (quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π)).toReal :=
        ENNReal.ofReal_le_ofReal hsq
    _ = quadraticPlanCost (Measure.map (fun p : E d × E d => (A p.1, B p.2)) π) :=
        ENNReal.ofReal_toReal hfin'
    _ = ∫⁻ p, ENNReal.ofReal (‖A p.1 - B p.2‖ ^ 2) ∂π := hcost

/-- The diagonal coupling of a law with itself. -/
lemma isCoupling_diagonal (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    IsCoupling μ μ (Measure.map (fun x : E d => (x, x)) μ) := by
  have hdiag : Measurable fun x : E d => (x, x) := measurable_id.prodMk measurable_id
  refine ⟨(Measure.isProbabilityMeasure_map_iff hdiag.aemeasurable).mpr inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  · rw [Measure.map_map measurable_snd hdiag]
    exact Measure.map_id

/-- The Wasserstein distance of two images of the same law. -/
lemma ofReal_wasserstein2_sq_map_self_le {μ : Measure (E d)} [IsProbabilityMeasure μ]
    {A B : E d → E d} (hA : Measurable A) (hB : Measurable B) (hfin : sqDist μ A B ≠ ∞) :
    ENNReal.ofReal (wasserstein2 (Measure.map A μ) (Measure.map B μ) ^ 2) ≤ sqDist μ A B := by
  have hdiag : Measurable fun x : E d => (x, x) := measurable_id.prodMk measurable_id
  have hF : Measurable fun p : E d × E d => ENNReal.ofReal (‖A p.1 - B p.2‖ ^ 2) :=
    measurable_sq_norm_sub (hA.comp measurable_fst) (hB.comp measurable_snd)
  have heq : (∫⁻ p, ENNReal.ofReal (‖A p.1 - B p.2‖ ^ 2)
      ∂(Measure.map (fun x : E d => (x, x)) μ)) = sqDist μ A B := by
    rw [lintegral_map hF hdiag]
    rfl
  have h := ofReal_wasserstein2_sq_map_le (isCoupling_diagonal μ) hA hB
    (by rw [heq]; exact hfin)
  rw [heq] at h
  exact h

/-! ### The errors of the approximation -/

/-- The squared `L²` error of the `n`-th quantizer under `μ`. -/
def quantErr (μ : Measure (E d)) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖quantizer d n y - y‖ ^ 2) ∂μ

/-- The part of `μ` removed by clipping at level `H`. -/
def clipErr (μ : Measure (E d)) (H : ℝ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (‖y - clipVec H y‖ ^ 2) ∂μ

lemma tendsto_quantErr {μ : Measure (E d)} (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞) :
    Tendsto (quantErr μ) atTop (𝓝 0) :=
  tendsto_lintegral_quantizer hμ2

lemma tendsto_clipErr {μ : Measure (E d)} (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞) :
    Tendsto (fun k : ℕ => clipErr μ (k : ℝ)) atTop (𝓝 0) :=
  tendsto_lintegral_sub_clipVec hμ2

lemma quantErr_ne_top {μ : Measure (E d)} (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞)
    (n : ℕ) : quantErr μ n ≠ ∞ :=
  ne_top_of_le_ne_top hμ2 (lintegral_mono fun y =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (norm_quantizer_sub_le n y) 2))

/-- A numerical inequality between extended nonnegative reals, proved for real numbers. -/
private lemma ennreal_combo_le {κ a b e η : ℝ} (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hη : 0 ≤ η)
    (h : 3 * (κ * (2 * a + 2 * a) + e + (8 * a + 2 * b) + (8 * a + 2 * b)) ≤ η) :
    3 * (ENNReal.ofReal κ * (2 * ENNReal.ofReal a + 2 * ENNReal.ofReal a) + ENNReal.ofReal e +
        (8 * ENNReal.ofReal a + 2 * ENNReal.ofReal b) +
        (8 * ENNReal.ofReal a + 2 * ENNReal.ofReal b)) ≤ ENNReal.ofReal η := by
  lift κ to NNReal using hκ
  lift a to NNReal using ha
  lift b to NNReal using hb
  lift e to NNReal using he
  lift η to NNReal using hη
  simp only [ENNReal.ofReal_coe_nnreal]
  exact_mod_cast h

/-! ### Existence -/

/-- The bound that makes the active maps of the quantized targets a Cauchy sequence. -/
lemma sqDist_quantized_le {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {μ : Measure (E d)} [IsProbabilityMeasure μ]
    (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞)
    {Tn : ℕ → E d → E d} (hTnm : ∀ n, Measurable (Tn n))
    (hTn : ∀ n, IsFinitePotentialMap (Tn n))
    (hpush : ∀ n, Measure.map (Tn n) ρ = Measure.map (quantizer d n) μ) (m n : ℕ) {H h : ℝ}
    (hH : 0 ≤ H) (hh : 0 < h) :
    sqDist ρ (Tn m) (Tn n) ≤
      3 * (ENNReal.ofReal (4 * d * P ^ 2 / h ^ 2) * (2 * quantErr μ m + 2 * quantErr μ n) +
        ENNReal.ofReal (24 * d * H ^ 2 * h * B) + (8 * quantErr μ m + 2 * clipErr μ H) +
        (8 * quantErr μ n + 2 * clipErr μ H)) := by
  have hprob := hρ.prob
  have hB := hρ.strip_nonneg
  have hcl : ∀ k, Measurable fun x => clipVec H (Tn k x) := fun k =>
    (measurable_clipVec H).comp (hTnm k)
  -- remove the clipping
  have h3 : sqDist ρ (Tn m) (Tn n) ≤
      3 * (∫⁻ x, ENNReal.ofReal (‖clipVec H (Tn m x) - clipVec H (Tn n x)‖ ^ 2) ∂ρ) +
        3 * ((∫⁻ x, ENNReal.ofReal (‖Tn m x - clipVec H (Tn m x)‖ ^ 2) ∂ρ) +
          ∫⁻ x, ENNReal.ofReal (‖Tn n x - clipVec H (Tn n x)‖ ^ 2) ∂ρ) := by
    have h := lintegral_sq_sub_le_slack ρ (θ := 2) (by norm_num) (hTnm m) (hTnm n) (hcl m) (hcl n)
    have e1 : ENNReal.ofReal ((1 : ℝ) + 2) = 3 := by
      rw [show (1 : ℝ) + 2 = 3 by norm_num, ENNReal.ofReal_ofNat]
    have e2 : ENNReal.ofReal (((1 : ℝ) + 1 / 2) * 2) = 3 := by
      rw [show ((1 : ℝ) + 1 / 2) * 2 = 3 by norm_num, ENNReal.ofReal_ofNat]
    rw [e1, e2] at h
    exact h
  -- the part removed by the clipping, moved to the target
  have hY : ∀ k, (∫⁻ x, ENNReal.ofReal (‖Tn k x - clipVec H (Tn k x)‖ ^ 2) ∂ρ) ≤
      8 * quantErr μ k + 2 * clipErr μ H := by
    intro k
    have hG : Measurable fun z : E d => ENNReal.ofReal (‖z - clipVec H z‖ ^ 2) :=
      measurable_sq_norm_sub measurable_id (measurable_clipVec H)
    have hmove : (∫⁻ x, ENNReal.ofReal (‖Tn k x - clipVec H (Tn k x)‖ ^ 2) ∂ρ) =
        ∫⁻ y, ENNReal.ofReal (‖quantizer d k y - clipVec H (quantizer d k y)‖ ^ 2) ∂μ := by
      rw [← lintegral_map hG (hTnm k), hpush k, lintegral_map hG (measurable_quantizer k)]
    have e8 : ∀ r : ℝ, ENNReal.ofReal (8 * r) = 8 * ENNReal.ofReal r := by
      intro r
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have e2 : ∀ r : ℝ, ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
      intro r
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    have hpt : ∀ y : E d,
        ENNReal.ofReal (‖quantizer d k y - clipVec H (quantizer d k y)‖ ^ 2) ≤
          8 * ENNReal.ofReal (‖quantizer d k y - y‖ ^ 2) +
            2 * ENNReal.ofReal (‖y - clipVec H y‖ ^ 2) := by
      intro y
      have hn : ‖quantizer d k y - clipVec H (quantizer d k y)‖ ≤
          2 * ‖quantizer d k y - y‖ + ‖y - clipVec H y‖ := by
        have h0 : quantizer d k y - clipVec H (quantizer d k y) =
            (quantizer d k y - y) + (y - clipVec H y) +
              (clipVec H y - clipVec H (quantizer d k y)) := by abel
        have h1 := norm_clipVec_sub_le H y (quantizer d k y)
        rw [norm_sub_rev y] at h1
        calc ‖quantizer d k y - clipVec H (quantizer d k y)‖
            = ‖(quantizer d k y - y) + (y - clipVec H y) +
                (clipVec H y - clipVec H (quantizer d k y))‖ := by rw [← h0]
          _ ≤ ‖(quantizer d k y - y) + (y - clipVec H y)‖ +
                ‖clipVec H y - clipVec H (quantizer d k y)‖ := norm_add_le _ _
          _ ≤ 2 * ‖quantizer d k y - y‖ + ‖y - clipVec H y‖ := by
              linarith [norm_add_le (quantizer d k y - y) (y - clipVec H y)]
      have hsq := mul_self_le_mul_self (norm_nonneg _) hn
      have hreal : ‖quantizer d k y - clipVec H (quantizer d k y)‖ ^ 2 ≤
          8 * ‖quantizer d k y - y‖ ^ 2 + 2 * ‖y - clipVec H y‖ ^ 2 := by
        nlinarith [hsq, sq_nonneg (2 * ‖quantizer d k y - y‖ - ‖y - clipVec H y‖)]
      rw [← e8, ← e2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal hreal
    have hq : Measurable fun y : E d => ENNReal.ofReal (‖quantizer d k y - y‖ ^ 2) :=
      measurable_sq_norm_sub (measurable_quantizer k) measurable_id
    rw [hmove]
    calc (∫⁻ y, ENNReal.ofReal (‖quantizer d k y - clipVec H (quantizer d k y)‖ ^ 2) ∂μ)
        ≤ ∫⁻ y, (8 * ENNReal.ofReal (‖quantizer d k y - y‖ ^ 2) +
            2 * ENNReal.ofReal (‖y - clipVec H y‖ ^ 2)) ∂μ := lintegral_mono hpt
      _ = 8 * quantErr μ k + 2 * clipErr μ H := by
          rw [lintegral_add_left (hq.const_mul _), lintegral_const_mul _ hq,
            lintegral_const_mul _ hG]
          rfl
  -- the clipped maps
  have hX : (∫⁻ x, ENNReal.ofReal (‖clipVec H (Tn m x) - clipVec H (Tn n x)‖ ^ 2) ∂ρ) ≤
      ENNReal.ofReal (4 * d * P ^ 2 / h ^ 2) * (2 * quantErr μ m + 2 * quantErr μ n) +
        ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by
    have hb := clipped_estimate_of_finitePotential hρ (hTn m) (hTn n) (hTnm m) (hTnm n) hH hh
    rw [hpush m, hpush n] at hb
    have hqq : sqDist μ (quantizer d m) (quantizer d n) ≤
        2 * quantErr μ m + 2 * quantErr μ n :=
      lintegral_sq_sub_le_two μ (measurable_quantizer m) (measurable_quantizer n)
        (C := fun y : E d => y) measurable_id
    have hfin : sqDist μ (quantizer d m) (quantizer d n) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top (quantErr_ne_top hμ2 m),
          ENNReal.mul_ne_top ENNReal.ofNat_ne_top (quantErr_ne_top hμ2 n)⟩) hqq
    have hW := ofReal_wasserstein2_sq_map_self_le (measurable_quantizer m)
      (measurable_quantizer n) hfin
    have h4 : (0 : ℝ) ≤ 4 * d * P ^ 2 / h ^ 2 := by positivity
    have esplit : ENNReal.ofReal
        (4 * d * P ^ 2 *
            wasserstein2 (Measure.map (quantizer d m) μ) (Measure.map (quantizer d n) μ) ^ 2 /
          h ^ 2 + 24 * d * H ^ 2 * h * B) =
        ENNReal.ofReal (4 * d * P ^ 2 / h ^ 2) * ENNReal.ofReal
          (wasserstein2 (Measure.map (quantizer d m) μ) (Measure.map (quantizer d n) μ) ^ 2) +
          ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by
      rw [← ENNReal.ofReal_mul h4, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [esplit] at hb
    refine hb.trans ?_
    gcongr
    exact hW.trans hqq
  calc sqDist ρ (Tn m) (Tn n)
      ≤ 3 * (∫⁻ x, ENNReal.ofReal (‖clipVec H (Tn m x) - clipVec H (Tn n x)‖ ^ 2) ∂ρ) +
          3 * ((∫⁻ x, ENNReal.ofReal (‖Tn m x - clipVec H (Tn m x)‖ ^ 2) ∂ρ) +
            ∫⁻ x, ENNReal.ofReal (‖Tn n x - clipVec H (Tn n x)‖ ^ 2) ∂ρ) := h3
    _ ≤ 3 * (ENNReal.ofReal (4 * d * P ^ 2 / h ^ 2) * (2 * quantErr μ m + 2 * quantErr μ n) +
            ENNReal.ofReal (24 * d * H ^ 2 * h * B)) +
          3 * ((8 * quantErr μ m + 2 * clipErr μ H) + (8 * quantErr μ n + 2 * clipErr μ H)) := by
        gcongr
        · exact hY m
        · exact hY n
    _ = 3 * (ENNReal.ofReal (4 * d * P ^ 2 / h ^ 2) * (2 * quantErr μ m + 2 * quantErr μ n) +
          ENNReal.ofReal (24 * d * H ^ 2 * h * B) + (8 * quantErr μ m + 2 * clipErr μ H) +
          (8 * quantErr μ n + 2 * clipErr μ H)) := by ring

/-- **Existence.** A target with finite second moment is the law of a limit in
`L²` of active maps of finite potentials, which push the source to the
quantized targets. -/
theorem exists_limit_map {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {μ : Measure (E d)} [IsProbabilityMeasure μ]
    (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞) :
    ∃ (T : E d → E d) (Tn : ℕ → E d → E d), Measurable T ∧ MemLp T 2 ρ ∧
      (∀ n, Measurable (Tn n)) ∧ (∀ n, IsFinitePotentialMap (Tn n)) ∧
      (∀ n, Measure.map (Tn n) ρ = Measure.map (quantizer d n) μ) ∧
      Tendsto (fun n => sqDist ρ T (Tn n)) atTop (𝓝 0) ∧ Measure.map T ρ = μ := by
  have hprob := hρ.prob
  have hB := hρ.strip_nonneg
  -- the active maps of the quantized targets
  have hex : ∀ n : ℕ, ∃ T : E d → E d, Measurable T ∧ IsFinitePotentialMap T ∧
      Measure.map T ρ = Measure.map (quantizer d n) μ := by
    intro n
    have hp : IsProbabilityMeasure (Measure.map (quantizer d n) μ) :=
      (Measure.isProbabilityMeasure_map_iff (measurable_quantizer n).aemeasurable).mpr
        inferInstance
    exact exists_finitePotentialMap_of_finite hρ (finite_range_quantizer n)
      (isSupported_map_quantizer μ n)
  choose Tn hTnm hTn hpush using hex
  have hTnL2 : ∀ n, MemLp (Tn n) 2 ρ := by
    intro n
    obtain ⟨C, hC⟩ := (hTn n).bounded
    exact MemLp.of_bound (hTnm n).aestronglyMeasurable C (Eventually.of_forall hC)
  have hq := tendsto_quantErr hμ2
  have hc := tendsto_clipErr hμ2
  -- the sequence is Cauchy
  have hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, mapL2Dist ρ (Tn m) (Tn n) < ε := by
    intro ε hε
    obtain ⟨η, hη⟩ : ∃ η : ℝ, η = ε ^ 2 / 4 := ⟨_, rfl⟩
    have hη0 : 0 < η := by
      rw [hη]
      positivity
    -- the level of the clipping
    obtain ⟨k, hk⟩ := (ENNReal.tendsto_atTop_zero.mp hc) (ENNReal.ofReal (η / 36))
      (ENNReal.ofReal_pos.mpr (by positivity))
    have hck := hk k le_rfl
    -- the step
    obtain ⟨Dn, hDn⟩ : ∃ Dn : ℝ, Dn = 72 * d * (k : ℝ) ^ 2 * B + 1 := ⟨_, rfl⟩
    have hDn0 : 0 < Dn := by
      rw [hDn]
      positivity
    obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = η / (3 * Dn) := ⟨_, rfl⟩
    have hh : 0 < h := by
      rw [hh_def]
      positivity
    -- the index
    obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 4 * d * P ^ 2 / h ^ 2 := ⟨_, rfl⟩
    have hκ0 : 0 ≤ κ := by
      rw [hκ]
      positivity
    obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = 6 * κ + 24 := ⟨_, rfl⟩
    have hA : 0 < A := by
      rw [hA_def]
      positivity
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp hq) (ENNReal.ofReal (η / (6 * A)))
      (ENNReal.ofReal_pos.mpr (by positivity))
    refine ⟨N, fun m hm n hn => ?_⟩
    have hbound := sqDist_quantized_le hρ hμ2 hTnm hTn hpush m n (Nat.cast_nonneg k) hh
    rw [← hκ] at hbound
    have hqm := hN m hm
    have hqn := hN n hn
    -- the three parts are at most `η / 3` each
    have hreal : 3 * (κ * (2 * (η / (6 * A)) + 2 * (η / (6 * A))) + 24 * d * (k : ℝ) ^ 2 * h * B +
        (8 * (η / (6 * A)) + 2 * (η / 36)) + (8 * (η / (6 * A)) + 2 * (η / 36))) ≤ η := by
      have e1 : 3 * (κ * (2 * (η / (6 * A)) + 2 * (η / (6 * A))) + 24 * d * (k : ℝ) ^ 2 * h * B +
          (8 * (η / (6 * A)) + 2 * (η / 36)) + (8 * (η / (6 * A)) + 2 * (η / 36))) =
          (2 * A) * (η / (6 * A)) + (72 * d * (k : ℝ) ^ 2 * B) * h + η / 3 := by
        rw [hA_def]
        ring
      have e2 : (2 * A) * (η / (6 * A)) = η / 3 := by
        field_simp
        ring
      have e3 : (72 * d * (k : ℝ) ^ 2 * B) * h ≤ η / 3 := by
        have hle : 72 * d * (k : ℝ) ^ 2 * B ≤ Dn := by
          rw [hDn]
          linarith
        have h1 : (72 * d * (k : ℝ) ^ 2 * B) * h ≤ Dn * h :=
          mul_le_mul_of_nonneg_right hle hh.le
        have h2 : Dn * h = η / 3 := by
          rw [hh_def]
          field_simp
        linarith
      rw [e1, e2]
      linarith
    have hsq : sqDist ρ (Tn m) (Tn n) ≤ ENNReal.ofReal η := by
      refine hbound.trans (le_trans ?_ (ennreal_combo_le hκ0
        (by positivity : (0 : ℝ) ≤ η / (6 * A)) (by positivity : (0 : ℝ) ≤ η / 36)
        (by positivity : (0 : ℝ) ≤ 24 * d * (k : ℝ) ^ 2 * h * B) hη0.le hreal))
      gcongr
    have htoReal : mapL2Dist ρ (Tn m) (Tn n) ^ 2 ≤ η := by
      rw [mapL2Dist_sq_eq_toReal ρ (hTnm m) (hTnm n)]
      exact ENNReal.toReal_le_of_le_ofReal hη0.le hsq
    refine lt_of_pow_lt_pow_left₀ 2 hε.le (lt_of_le_of_lt htoReal ?_)
    rw [hη]
    nlinarith [sq_pos_of_pos hε]
  -- the limit
  obtain ⟨T, hTm, hT2, hlim⟩ := exists_mapL2Dist_limit hTnL2 hC
  have hsq : Tendsto (fun n => sqDist ρ T (Tn n)) atTop (𝓝 0) := by
    have heq : ∀ n, sqDist ρ T (Tn n) = ENNReal.ofReal (mapL2Dist ρ (Tn n) T ^ 2) := by
      intro n
      rw [mapL2Dist_comm, mapL2Dist_sq_eq_toReal ρ hTm (hTnm n),
        ENNReal.ofReal_toReal (sqDist_ne_top_of_memLp hT2 (hTnL2 n))]
    have h1 : Tendsto (fun n => mapL2Dist ρ (Tn n) T ^ 2) atTop (𝓝 ((0 : ℝ) ^ 2)) :=
      hlim.pow 2
    have h2 : Tendsto (fun n => ENNReal.ofReal (mapL2Dist ρ (Tn n) T ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) := (ENNReal.continuous_ofReal.tendsto _).comp h1
    rw [zero_pow two_ne_zero, ENNReal.ofReal_zero] at h2
    simp only [heq]
    exact h2
  -- the law of the limit
  have hlaw : Measure.map T ρ = μ := by
    obtain ⟨ns, hns, hae⟩ :=
      exists_subseq_tendsto_ae_of_mapL2Dist_tendsto_zero hTnL2 hT2 hlim
    exact map_eq_of_ae_tendsto_quantized (Tn := fun n => Tn (ns n))
      (Qn := fun n => quantizer d (ns n)) (fun n => hTnm (ns n)) hTm
      (fun n => measurable_quantizer (ns n)) (fun n => hpush (ns n)) hae
      (Eventually.of_forall fun y => (tendsto_quantizer y).comp hns.tendsto_atTop)
  exact ⟨T, Tn, hTm, hT2, hTnm, hTn, hpush, hsq, hlaw⟩

/-! ### The clipped estimate for limit maps -/

private lemma slack_algebra {t k c D u : ℝ} (ht : 0 ≤ t) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hD : 0 ≤ D) {X Xn W Ee F : ℝ≥0∞}
    (h1 : X ≤ ENNReal.ofReal t * Xn + ENNReal.ofReal u * F)
    (h2 : Xn ≤ ENNReal.ofReal k * W + ENNReal.ofReal D)
    (h3 : W ≤ ENNReal.ofReal t * ENNReal.ofReal c + ENNReal.ofReal u * Ee) :
    X ≤ ENNReal.ofReal (t * (k * (t * c) + D)) + ENNReal.ofReal (t * k * u) * Ee +
      ENNReal.ofReal u * F := by
  have h4 : X ≤ ENNReal.ofReal t *
      (ENNReal.ofReal k * (ENNReal.ofReal t * ENNReal.ofReal c + ENNReal.ofReal u * Ee) +
        ENNReal.ofReal D) + ENNReal.ofReal u * F := by
    refine h1.trans ?_
    gcongr
    refine h2.trans ?_
    gcongr
  have e1 : ENNReal.ofReal (t * (k * (t * c) + D)) =
      ENNReal.ofReal t * (ENNReal.ofReal k * (ENNReal.ofReal t * ENNReal.ofReal c) +
        ENNReal.ofReal D) := by
    rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_add (by positivity) hD, ENNReal.ofReal_mul hk,
      ENNReal.ofReal_mul ht]
  have e2 : ENNReal.ofReal (t * k * u) = ENNReal.ofReal t * ENNReal.ofReal k * ENNReal.ofReal u := by
    rw [ENNReal.ofReal_mul (mul_nonneg ht hk), ENNReal.ofReal_mul ht]
  refine h4.trans (le_of_eq ?_)
  rw [e1, e2]
  ring

/-- **The clipped estimate for two limit maps**, with the cost of an arbitrary
coupling of the two targets. -/
theorem clipped_estimate_of_limits {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {μ ν : Measure (E d)}
    (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞)
    (hν2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) ≠ ∞)
    {T S : E d → E d} {Tn Sn : ℕ → E d → E d} (hTm : Measurable T) (hSm : Measurable S)
    (hTnm : ∀ n, Measurable (Tn n)) (hSnm : ∀ n, Measurable (Sn n))
    (hTn : ∀ n, IsFinitePotentialMap (Tn n)) (hSn : ∀ n, IsFinitePotentialMap (Sn n))
    (hTpush : ∀ n, Measure.map (Tn n) ρ = Measure.map (quantizer d n) μ)
    (hSpush : ∀ n, Measure.map (Sn n) ρ = Measure.map (quantizer d n) ν)
    (hTlim : Tendsto (fun n => sqDist ρ T (Tn n)) atTop (𝓝 0))
    (hSlim : Tendsto (fun n => sqDist ρ S (Sn n)) atTop (𝓝 0))
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π) (hπfin : quadraticPlanCost π ≠ ∞)
    {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h) :
    (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
      ENNReal.ofReal
        (4 * d * P ^ 2 / h ^ 2 * (quadraticPlanCost π).toReal + 24 * d * H ^ 2 * h * B) := by
  have hprob := hρ.prob
  have hB := hρ.strip_nonneg
  have hqμ := tendsto_quantErr hμ2
  have hqν := tendsto_quantErr hν2
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (quadraticPlanCost π).toReal := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact ENNReal.toReal_nonneg
  have hcost : (∫⁻ p : E d × E d, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π) = ENNReal.ofReal c := by
    rw [hc, ENNReal.ofReal_toReal hπfin]
    rfl
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 4 * d * P ^ 2 / h ^ 2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 24 * d * H ^ 2 * h * B := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  -- the estimate with slack `θ`, through the `n`-th approximations
  have hstep : ∀ θ : ℝ, 0 < θ → ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
        ENNReal.ofReal ((1 + θ) * (κ * ((1 + θ) * c) + D)) +
          ENNReal.ofReal ((1 + θ) * κ * ((1 + 1 / θ) * 2)) * (quantErr μ n + quantErr ν n) +
          ENNReal.ofReal ((1 + 1 / θ) * 2) * (sqDist ρ T (Tn n) + sqDist ρ S (Sn n)) := by
    intro θ hθ n
    have ht0 : (0 : ℝ) ≤ 1 + θ := by positivity
    -- from the limit maps to the approximations
    have ha := lintegral_sq_sub_le_slack ρ hθ
      (A := fun x => clipVec H (T x)) (B := fun x => clipVec H (S x))
      (C := fun x => clipVec H (Tn n x)) (D := fun x => clipVec H (Sn n x))
      ((measurable_clipVec H).comp hTm) ((measurable_clipVec H).comp hSm)
      ((measurable_clipVec H).comp (hTnm n)) ((measurable_clipVec H).comp (hSnm n))
    have hcT : (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (Tn n x)‖ ^ 2) ∂ρ) ≤
        sqDist ρ T (Tn n) :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (norm_clipVec_sub_le H _ _) 2)
    have hcS : (∫⁻ x, ENNReal.ofReal (‖clipVec H (S x) - clipVec H (Sn n x)‖ ^ 2) ∂ρ) ≤
        sqDist ρ S (Sn n) :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (pow_le_pow_left₀ (norm_nonneg _) (norm_clipVec_sub_le H _ _) 2)
    have h1 : (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
        ENNReal.ofReal (1 + θ) *
            (∫⁻ x, ENNReal.ofReal (‖clipVec H (Tn n x) - clipVec H (Sn n x)‖ ^ 2) ∂ρ) +
          ENNReal.ofReal ((1 + 1 / θ) * 2) * (sqDist ρ T (Tn n) + sqDist ρ S (Sn n)) := by
      refine ha.trans ?_
      gcongr
    -- the approximations
    have hb := clipped_estimate_of_finitePotential hρ (hTn n) (hSn n) (hTnm n) (hSnm n) hH hh
    rw [hTpush n, hSpush n] at hb
    have h2 : (∫⁻ x, ENNReal.ofReal (‖clipVec H (Tn n x) - clipVec H (Sn n x)‖ ^ 2) ∂ρ) ≤
        ENNReal.ofReal κ * ENNReal.ofReal
          (wasserstein2 (Measure.map (quantizer d n) μ) (Measure.map (quantizer d n) ν) ^ 2) +
          ENNReal.ofReal D := by
      refine hb.trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_mul hκ0, ← ENNReal.ofReal_add (by positivity) hD0, hκ, hD]
      congr 1
      ring
    -- the distance of the quantized targets
    have hslack := lintegral_sq_sub_le_slack π hθ
      (A := fun p : E d × E d => quantizer d n p.1) (B := fun p : E d × E d => quantizer d n p.2)
      (C := fun p : E d × E d => p.1) (D := fun p : E d × E d => p.2)
      ((measurable_quantizer n).comp measurable_fst) ((measurable_quantizer n).comp measurable_snd)
      measurable_fst measurable_snd
    have hqm : Measurable fun y : E d => ENNReal.ofReal (‖quantizer d n y - y‖ ^ 2) :=
      measurable_sq_norm_sub (measurable_quantizer n) measurable_id
    have hm1 : (∫⁻ p : E d × E d, ENNReal.ofReal (‖quantizer d n p.1 - p.1‖ ^ 2) ∂π) =
        quantErr μ n := by
      unfold quantErr
      rw [← hπ.2.1, lintegral_map hqm measurable_fst]
    have hm2 : (∫⁻ p : E d × E d, ENNReal.ofReal (‖quantizer d n p.2 - p.2‖ ^ 2) ∂π) =
        quantErr ν n := by
      unfold quantErr
      rw [← hπ.2.2, lintegral_map hqm measurable_snd]
    rw [hm1, hm2, hcost] at hslack
    have hfin : (∫⁻ p : E d × E d,
        ENNReal.ofReal (‖quantizer d n p.1 - quantizer d n p.2‖ ^ 2) ∂π) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.mpr
            ⟨quantErr_ne_top hμ2 n, quantErr_ne_top hν2 n⟩)⟩) hslack
    have hW := ofReal_wasserstein2_sq_map_le hπ (measurable_quantizer n)
      (measurable_quantizer n) hfin
    exact slack_algebra ht0 hκ0 hc0 hD0 h1 h2 (hW.trans hslack)
  -- let `n → ∞`
  have hlimit : ∀ θ : ℝ, 0 < θ →
      (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
        ENNReal.ofReal ((1 + θ) * (κ * ((1 + θ) * c) + D)) := by
    intro θ hθ
    have hE : Tendsto (fun n => quantErr μ n + quantErr ν n) atTop (𝓝 0) := by
      have h := hqμ.add hqν
      rw [add_zero] at h
      exact h
    have hF : Tendsto (fun n => sqDist ρ T (Tn n) + sqDist ρ S (Sn n)) atTop (𝓝 0) := by
      have h := hTlim.add hSlim
      rw [add_zero] at h
      exact h
    have hK1 : ENNReal.ofReal ((1 + θ) * κ * ((1 + 1 / θ) * 2)) ≠ ∞ := ENNReal.ofReal_ne_top
    have hK2 : ENNReal.ofReal ((1 + 1 / θ) * 2) ≠ ∞ := ENNReal.ofReal_ne_top
    have ht := ((tendsto_const_nhds (f := atTop)
        (x := ENNReal.ofReal ((1 + θ) * (κ * ((1 + θ) * c) + D)))).add
      (ENNReal.Tendsto.const_mul hE (Or.inr hK1))).add
      (ENNReal.Tendsto.const_mul hF (Or.inr hK2))
    rw [mul_zero, mul_zero, add_zero, add_zero] at ht
    exact ge_of_tendsto' ht (hstep θ hθ)
  -- let `θ → 0`
  have hg : Continuous fun θ : ℝ => (1 + θ) * (κ * ((1 + θ) * c) + D) := by fun_prop
  have hθlim : Tendsto
      (fun k : ℕ => (1 + 1 / ((k : ℝ) + 1)) * (κ * ((1 + 1 / ((k : ℝ) + 1)) * c) + D)) atTop
      (𝓝 ((1 + 0) * (κ * ((1 + 0) * c) + D))) :=
    (hg.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hfinal := ge_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp hθlim)
    (fun k : ℕ => hlimit (1 / ((k : ℝ) + 1)) (by positivity))
  have e : (1 + 0) * (κ * ((1 + 0) * c) + D) =
      4 * d * P ^ 2 / h ^ 2 * (quadraticPlanCost π).toReal + 24 * d * H ^ 2 * h * B := by
    rw [hκ, hD, hc]
    ring
  rw [e] at hfinal
  exact hfinal

end

end BrenierMoment
