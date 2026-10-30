module

public import BrenierMoment.GeneralTargets
public import BrenierMoment.OneSided
public import BrenierMoment.MomentTail

@[expose] public section

/-!
# Moment stability of Brenier maps

For a source with the atomic potential estimate and the interpolation
property, every probability with finite second moment has a unique optimal
map, and the maps of two such targets satisfy the interpolation estimate with
tails. With the scalar end of `OneSided.lean` this is the rate
`δ ^ ((p - 2) / (3 p - 2)) * log (e / δ) ^ (-2 β / (3 p - 2))` under the
power-logarithmic moment bound on one of the two targets. Log-concave sources
on bounded open convex sets are covered, given the atomic potential estimate
for uniform sources.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358 Filter
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

variable {d : ℕ}

/-! ### Second moments -/

lemma measurable_momentWeight (p β : ℝ) : Measurable (momentWeight p β : E d → ℝ) :=
  (measurable_norm.pow_const p).mul
    ((Real.measurable_log.comp (measurable_const.add measurable_norm)).pow_const β)

lemma lintegral_sq_norm_ne_top {μ : Measure (E d)}
    (hint : Integrable (fun y : E d => ‖y‖ ^ 2) μ) :
    (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => sq_nonneg _)]
  exact ENNReal.ofReal_ne_top

lemma integrable_sq_norm_of_lintegral {μ : Measure (E d)}
    (h : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) < ∞) :
    Integrable (fun y : E d => ‖y‖ ^ 2) μ :=
  ⟨(measurable_norm.pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)).mpr h⟩

/-- A power-logarithmic moment with `p ≥ 2` controls the second moment. -/
lemma integrable_sq_norm_of_moment {μ : Measure (E d)} [IsFiniteMeasure μ] {p β : ℝ}
    (hp : 2 ≤ p) (hβ : 0 ≤ β) (hint : Integrable (momentWeight p β : E d → ℝ) μ) :
    Integrable (fun y : E d => ‖y‖ ^ 2) μ := by
  have hbound : ∀ y : E d, ‖y‖ ^ 2 ≤ 1 + tailEnvelope p β 1 * momentWeight p β y := by
    intro y
    have h1 := quadraticTailTerm_le_envelope hp hβ one_pos y
    unfold quadraticTailTerm at h1
    split_ifs at h1 with hy
    · linarith
    · have h2 : ‖y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg y, not_lt.mp hy]
      linarith
  have hdom : Integrable (fun y : E d => 1 + tailEnvelope p β 1 * momentWeight p β y) μ :=
    (integrable_const (1 : ℝ)).add (hint.const_mul _)
  refine hdom.mono' (measurable_norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hbound y

/-! ### Unique optimal maps -/

/-- **Existence and uniqueness.** A target with finite second moment has a unique
optimal map, which is a limit in `L²` of active maps of finite potentials. -/
theorem exists_optimal_map_with_approximation {ρ : Measure (E d)} {U : Set (E d)}
    {R P B : ℝ} (hρ : GoodSource ρ U R P B) {μ : Measure (E d)} [IsProbabilityMeasure μ]
    (hμ2 : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≠ ∞) :
    ∃ (T : E d → E d) (Tn : ℕ → E d → E d), Measurable T ∧ MemLp T 2 ρ ∧
      (∀ n, Measurable (Tn n)) ∧ (∀ n, IsFinitePotentialMap (Tn n)) ∧
      (∀ n, Measure.map (Tn n) ρ = Measure.map (quantizer d n) μ) ∧
      Tendsto (fun n => sqDist ρ T (Tn n)) atTop (𝓝 0) ∧ Measure.map T ρ = μ ∧
      IsUniqueQuadraticOptimalMap ρ μ T := by
  have hprob := hρ.prob
  obtain ⟨T, Tn, hTm, hT2, hTnm, hTn, hpush, hlim, hlaw⟩ := exists_limit_map hρ hμ2
  have hT2' : (∫⁻ x, ENNReal.ofReal (‖T x‖ ^ 2) ∂ρ) ≠ ∞ := by
    have hint : Integrable (fun x => ‖T x‖ ^ 2) ρ := hT2.norm.integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have huniq := isUniqueQuadraticOptimalMap_of_tendsto_active hρ.nonempty hρ.norm_le hρ.ae_mem
    hρ.strip_nonneg hρ.strip hTn hTnm hTm hT2' hlim
  rw [hlaw] at huniq
  exact ⟨T, Tn, hTm, hT2, hTnm, hTn, hpush, hlim, hlaw, huniq⟩

/-! ### The interpolation estimate with tails -/

private lemma toReal_le_three {s : ℝ≥0∞} {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : s ≤ 3 * ENNReal.ofReal a + 3 * ENNReal.ofReal b + 3 * ENNReal.ofReal c) :
    s.toReal ≤ 3 * a + 3 * b + 3 * c := by
  have e : ∀ r : ℝ, ENNReal.ofReal (3 * r) = 3 * ENNReal.ofReal r := by
    intro r
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h.trans (le_of_eq ?_))
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), e, e, e]

/-- **The interpolation estimate with tails**, with a free step `h`. -/
theorem sq_mapL2Dist_le_of_limits {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {μ ν : Measure (E d)}
    (hμi : Integrable (fun y : E d => ‖y‖ ^ 2) μ) (hνi : Integrable (fun y : E d => ‖y‖ ^ 2) ν)
    {T S : E d → E d} {Tn Sn : ℕ → E d → E d} (hTm : Measurable T) (hSm : Measurable S)
    (hT2 : MemLp T 2 ρ) (hS2 : MemLp S 2 ρ)
    (hTnm : ∀ n, Measurable (Tn n)) (hSnm : ∀ n, Measurable (Sn n))
    (hTn : ∀ n, IsFinitePotentialMap (Tn n)) (hSn : ∀ n, IsFinitePotentialMap (Sn n))
    (hTpush : ∀ n, Measure.map (Tn n) ρ = Measure.map (quantizer d n) μ)
    (hSpush : ∀ n, Measure.map (Sn n) ρ = Measure.map (quantizer d n) ν)
    (hTlim : Tendsto (fun n => sqDist ρ T (Tn n)) atTop (𝓝 0))
    (hSlim : Tendsto (fun n => sqDist ρ S (Sn n)) atTop (𝓝 0))
    (hTlaw : Measure.map T ρ = μ) (hSlaw : Measure.map S ρ = ν)
    {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h) :
    mapL2Dist ρ T S ^ 2 ≤
      3 * (4 * d * P ^ 2 / h ^ 2 * wasserstein2 μ ν ^ 2 + 24 * d * H ^ 2 * h * B) +
        3 * (quadraticTail μ H + quadraticTail ν H) := by
  have hprob := hρ.prob
  have hB := hρ.strip_nonneg
  have hμ2 := lintegral_sq_norm_ne_top hμi
  have hν2 := lintegral_sq_norm_ne_top hνi
  -- a coupling of the two targets with finite cost
  have hpair : Measurable fun x : E d => (T x, S x) := hTm.prodMk hSm
  have hπ₀ : IsCoupling μ ν (Measure.map (fun x : E d => (T x, S x)) ρ) := by
    refine ⟨(Measure.isProbabilityMeasure_map_iff hpair.aemeasurable).mpr hprob, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hpair, ← hTlaw]
      rfl
    · rw [Measure.map_map measurable_snd hpair, ← hSlaw]
      rfl
  have hπ₀fin : quadraticPlanCost (Measure.map (fun x : E d => (T x, S x)) ρ) ≠ ∞ := by
    rw [quadraticPlanCost_map_pair hTm hSm]
    exact sqDist_ne_top_of_memLp hT2 hS2
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 4 * d * P ^ 2 / h ^ 2 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by
    rw [hκ]
    positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 24 * d * H ^ 2 * h * B := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hD]
    positivity
  -- the clipped maps, with the cost of every coupling
  have hclip : ∀ π : Measure (E d × E d), IsCoupling μ ν π → quadraticPlanCost π ≠ ∞ →
      (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
        ENNReal.ofReal (κ * (quadraticPlanCost π).toReal + D) := by
    intro π hπ hfin
    have h1 := clipped_estimate_of_limits hρ hμ2 hν2 hTm hSm hTnm hSnm hTn hSn hTpush hSpush
      hTlim hSlim hπ hfin hH hh
    rw [← hκ, ← hD] at h1
    exact h1
  have hXfin : (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hclip _ hπ₀ hπ₀fin)
  -- with the Wasserstein distance
  have hXW : (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ).toReal ≤
      κ * wasserstein2 μ ν ^ 2 + D := by
    have hb : ∀ π : Measure (E d × E d), IsCoupling μ ν π → quadraticPlanCost π ≠ ∞ →
        (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ).toReal - D ≤
          κ * Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) 2 := by
      intro π hπ hfin
      have h1 := ENNReal.toReal_le_of_le_ofReal
        (add_nonneg (mul_nonneg hκ0 ENNReal.toReal_nonneg) hD0) (hclip π hπ hfin)
      have h3 : Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) 2 =
          (quadraticPlanCost π).toReal := by
        rw [Real.rpow_eq_pow, Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg]
      rw [h3]
      linarith
    have h2 := le_mul_rpow_wasserstein2_of_coupling_bound hπ₀ hπ₀fin hκ0
      (by norm_num : (0 : ℝ) ≤ 2) hb
    rw [Real.rpow_eq_pow, Real.rpow_two] at h2
    linarith
  -- the tails of the two maps are the tails of the targets
  have htailm : Measurable fun y : E d => ENNReal.ofReal (quadraticTailTerm H y) :=
    ENNReal.measurable_ofReal.comp (measurable_quadraticTailTerm H)
  have htail : ∀ (σ : Measure (E d)) (F : E d → E d), Measurable F → Measure.map F ρ = σ →
      Integrable (fun y : E d => ‖y‖ ^ 2) σ →
      (∫⁻ x, ENNReal.ofReal (quadraticTailTerm H (F x)) ∂ρ) =
        ENNReal.ofReal (quadraticTail σ H) := by
    intro σ F hF hlaw hσ
    have hint : Integrable (fun y : E d => quadraticTailTerm H y) σ :=
      integrable_quadraticTailTerm aemeasurable_id hσ H
    rw [← lintegral_map htailm hF, hlaw]
    unfold quadraticTail
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun y => quadraticTailTerm_nonneg H y)]
  -- remove the clipping
  have e3 : ∀ r : ℝ, ENNReal.ofReal (3 * r) = 3 * ENNReal.ofReal r := by
    intro r
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hpt : ∀ x, ENNReal.ofReal (‖T x - S x‖ ^ 2) ≤
      3 * ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) +
        3 * ENNReal.ofReal (quadraticTailTerm H (T x)) +
        3 * ENNReal.ofReal (quadraticTailTerm H (S x)) := by
    intro x
    have h1 := norm_sq_sub_le_clipVec hH (T x) (S x)
    have ht1 := quadraticTailTerm_nonneg H (T x)
    have ht2 := quadraticTailTerm_nonneg H (S x)
    rw [← e3, ← e3, ← e3, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  have hcm : Measurable fun x => ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) :=
    measurable_sq_norm_sub ((measurable_clipVec H).comp hTm) ((measurable_clipVec H).comp hSm)
  have htT : Measurable fun x => ENNReal.ofReal (quadraticTailTerm H (T x)) := htailm.comp hTm
  have htS : Measurable fun x => ENNReal.ofReal (quadraticTailTerm H (S x)) := htailm.comp hSm
  have hsum : sqDist ρ T S ≤
      3 * ENNReal.ofReal
          (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ).toReal +
        3 * ENNReal.ofReal (quadraticTail μ H) + 3 * ENNReal.ofReal (quadraticTail ν H) := by
    rw [ENNReal.ofReal_toReal hXfin, ← htail μ T hTm hTlaw hμi, ← htail ν S hSm hSlaw hνi]
    calc sqDist ρ T S
        ≤ ∫⁻ x, (3 * ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) +
            3 * ENNReal.ofReal (quadraticTailTerm H (T x)) +
            3 * ENNReal.ofReal (quadraticTailTerm H (S x))) ∂ρ := lintegral_mono hpt
      _ = 3 * (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) +
            3 * (∫⁻ x, ENNReal.ofReal (quadraticTailTerm H (T x)) ∂ρ) +
            3 * ∫⁻ x, ENNReal.ofReal (quadraticTailTerm H (S x)) ∂ρ := by
          rw [lintegral_add_right _ (htS.const_mul _), lintegral_add_right _ (htT.const_mul _),
            lintegral_const_mul _ hcm, lintegral_const_mul _ htT, lintegral_const_mul _ htS]
  have hτμ : 0 ≤ quadraticTail μ H := integral_nonneg fun y => quadraticTailTerm_nonneg H y
  have hτν : 0 ≤ quadraticTail ν H := integral_nonneg fun y => quadraticTailTerm_nonneg H y
  have hreal := toReal_le_three ENNReal.toReal_nonneg hτμ hτν hsum
  rw [mapL2Dist_sq_eq_toReal ρ hTm hSm, ← hκ, ← hD]
  linarith

/-- The step that balances the two terms of the interpolation estimate. -/
lemma exists_balanced_step {δ H K L : ℝ} (hδ : 0 < δ) (hH : 0 < H) :
    ∃ h : ℝ, 0 < h ∧
      K * δ ^ 2 / h ^ 2 + L * H ^ 2 * h = (K + L) * (δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = δ ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = H ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]
    exact Real.rpow_pos_of_pos hδ _
  have hv0 : 0 < v := by
    rw [hv]
    exact Real.rpow_pos_of_pos hH _
  have hu3 : u ^ 3 = δ := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  have hv3 : v ^ 3 = H := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hH.le]
    norm_num
  have hu2 : δ ^ (2 / 3 : ℝ) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  have hv4 : H ^ (4 / 3 : ℝ) = v ^ 4 := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul hH.le]
    norm_num
  have hune : u ≠ 0 := hu0.ne'
  have hvne : v ≠ 0 := hv0.ne'
  refine ⟨u ^ 2 / v ^ 2, by positivity, ?_⟩
  rw [hu2, hv4, ← hu3, ← hv3]
  field_simp

/-! ### The theorem -/

lemma momentModulus_nonneg (p β : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    0 ≤ momentModulus p β δ := by
  unfold momentModulus
  refine mul_nonneg (Real.rpow_nonneg hδ0 _) (Real.rpow_nonneg ?_ _)
  rcases hδ0.eq_or_lt with h0 | h0
  · rw [← h0, div_zero, Real.log_zero]
  · apply Real.log_nonneg
    rw [le_div_iff₀ h0]
    linarith [Real.exp_one_gt_two]

/-- **Moment stability for a good source.** Let `μ` have power-logarithmic
moment at most one, with `p ≥ 2` and `β ≥ 0`, and let `ν` have finite second
moment. Both have unique optimal maps, and for `W₂(μ, ν) ≤ exp (1 - (6β + 2)²)`
the maps differ in `L²` of the source by at most a constant times the
modulus of `W₂(μ, ν)`. -/
theorem moment_stability_of_goodSource {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β)
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμM : (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1)
    (hν : (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) < ∞) :
    ∃ Tμ Tν : E d → E d,
      IsUniqueQuadraticOptimalMap ρ μ Tμ ∧ IsUniqueQuadraticOptimalMap ρ ν Tν ∧
      (wasserstein2 μ ν ≤ smallDistance β →
        mapL2Dist ρ Tμ Tν ≤
          Real.sqrt ((12 * d * P ^ 2 + 72 * d * B) * (2 : ℝ) ^ (4 / 3 : ℝ) +
            12 * (3 * p - 2) ^ β + 16) * momentModulus p β (wasserstein2 μ ν)) := by
  have hprob := hρ.prob
  have hB := hρ.strip_nonneg
  -- the moment bound in integral form
  have hwm := measurable_momentWeight (d := d) p β
  have hμint : Integrable (momentWeight p β : E d → ℝ) μ :=
    ⟨hwm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => momentWeight_nonneg p β y)).mpr
        (hμM.trans_lt ENNReal.one_lt_top)⟩
  have hμM' : (∫ y, momentWeight p β y ∂μ) ≤ 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun y => momentWeight_nonneg p β y) hwm.aestronglyMeasurable]
    have h := ENNReal.toReal_mono ENNReal.one_ne_top hμM
    rw [ENNReal.toReal_one] at h
    exact h
  have hμi := integrable_sq_norm_of_moment hp hβ hμint
  have hνi := integrable_sq_norm_of_lintegral hν
  -- the two optimal maps
  obtain ⟨T, Tn, hTm, hT2, hTnm, hTn, hTpush, hTlim, hTlaw, huT⟩ :=
    exists_optimal_map_with_approximation hρ (lintegral_sq_norm_ne_top hμi)
  obtain ⟨S, Sn, hSm, hS2, hSnm, hSn, hSpush, hSlim, hSlaw, huS⟩ :=
    exists_optimal_map_with_approximation hρ (lintegral_sq_norm_ne_top hνi)
  refine ⟨T, S, huT, huS, fun hsmall => ?_⟩
  -- a coupling of the two targets with finite cost
  have hpair : Measurable fun x : E d => (T x, S x) := hTm.prodMk hSm
  have hπ₀ : IsCoupling μ ν (Measure.map (fun x : E d => (T x, S x)) ρ) := by
    refine ⟨(Measure.isProbabilityMeasure_map_iff hpair.aemeasurable).mpr hprob, ?_, ?_⟩
    · rw [Measure.map_map measurable_fst hpair, ← hTlaw]
      rfl
    · rw [Measure.map_map measurable_snd hpair, ← hSlaw]
      rfl
  have hπ₀fin : quadraticPlanCost (Measure.map (fun x : E d => (T x, S x)) ρ) ≠ ∞ := by
    rw [quadraticPlanCost_map_pair hTm hSm]
    exact sqDist_ne_top_of_memLp hT2 hS2
  have hδ0 := wasserstein2_nonneg μ ν
  have hδ1 : wasserstein2 μ ν ≤ 1 := hsmall.trans (smallDistance_lt_one hβ).le
  have hmod := momentModulus_nonneg p β hδ0 hδ1
  rcases hδ0.eq_or_lt with hzero | hpos
  · -- equal targets
    have heq : μ = ν := measure_eq_of_wasserstein2_eq_zero ⟨_, hπ₀, hπ₀fin⟩ hzero.symm
    have hSopt : IsQuadraticOptimalMap ρ μ S := by
      rw [heq]
      exact huS.1
    have hae : T =ᵐ[ρ] S := huT.ae_eq_of_optimal hSopt
    rw [mapL2Dist_eq_zero_of_ae_eq hae]
    exact mul_nonneg (Real.sqrt_nonneg _) hmod
  · -- distinct targets
    have hA : 0 ≤ 12 * d * P ^ 2 + 72 * d * B := by positivity
    have hinterp : ∀ H : ℝ, 0 < H →
        mapL2Dist ρ T S ^ 2 ≤
          (12 * d * P ^ 2 + 72 * d * B) *
              (wasserstein2 μ ν ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) +
            3 * (quadraticTail μ H + quadraticTail ν H) := by
      intro H hH
      obtain ⟨h, hh, hbal⟩ := exists_balanced_step (K := 12 * d * P ^ 2) (L := 72 * d * B) hpos hH
      have h1 := sq_mapL2Dist_le_of_limits hρ hμi hνi hTm hSm hT2 hS2 hTnm hSnm hTn hSn hTpush
        hSpush hTlim hSlim hTlaw hSlaw hH.le hh
      have e : 3 * (4 * d * P ^ 2 / h ^ 2 * wasserstein2 μ ν ^ 2 + 24 * d * H ^ 2 * h * B) =
          12 * d * P ^ 2 * wasserstein2 μ ν ^ 2 / h ^ 2 + 72 * d * B * H ^ 2 * h := by ring
      rw [e, hbal] at h1
      exact h1
    have hmono : ∀ H : ℝ, 0 < H → quadraticTail μ (2 * H) ≤ quadraticTail μ H := by
      intro H hH
      apply integral_mono (integrable_quadraticTailTerm aemeasurable_id hμi _)
        (integrable_quadraticTailTerm aemeasurable_id hμi _)
      intro y
      change quadraticTailTerm (2 * H) y ≤ quadraticTailTerm H y
      unfold quadraticTailTerm
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (by linarith : H < ‖y‖) h2
      · positivity
      · exact le_rfl
    have htransfer : ∀ H : ℝ, 0 < H →
        quadraticTail ν (2 * H) ≤ 4 * wasserstein2 μ ν ^ 2 + 2 * quadraticTail μ H := by
      intro H hH
      have hb : ∀ π : Measure (E d × E d), IsCoupling μ ν π → quadraticPlanCost π ≠ ∞ →
          quadraticTail ν (2 * H) - 2 * quadraticTail μ H ≤
            4 * Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) 2 := by
        intro π hπ hfin
        have h1 := quadraticTail_transfer_of_coupling (π := π) hπ.2.1 hπ.2.2 hμi hνi hH.le
        have hm : Measurable fun q : E d × E d => ‖q.2 - q.1‖ ^ 2 :=
          (measurable_snd.sub measurable_fst).norm.pow_const 2
        have h2 : (∫ q : E d × E d, ‖q.2 - q.1‖ ^ 2 ∂π) = (quadraticPlanCost π).toReal := by
          rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => sq_nonneg _)
            hm.aestronglyMeasurable]
          unfold quadraticPlanCost
          congr 1
          exact lintegral_congr fun q => by rw [norm_sub_rev]
        have h3 : Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) 2 =
            (quadraticPlanCost π).toReal := by
          rw [Real.rpow_eq_pow, Real.rpow_two, Real.sq_sqrt ENNReal.toReal_nonneg]
        rw [h3, ← h2]
        linarith
      have h4 := le_mul_rpow_wasserstein2_of_coupling_bound hπ₀ hπ₀fin
        (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 2) hb
      rw [Real.rpow_eq_pow, Real.rpow_two] at h4
      linarith
    have henv : ∀ H : ℝ, 0 < H → quadraticTail μ H ≤ tailEnvelope p β H :=
      fun H hH => quadraticTail_le_envelope hp hβ hμint hμM' hH
    exact rate_of_interpolation hp hβ hA (mapL2Dist_nonneg ρ T S) hpos hsmall hinterp hmono
      htransfer henv

/-! ### Log-concave sources -/

/-- A log-concave source on a bounded open convex set is a good source, given
the atomic potential estimate for uniform sources. -/
theorem goodSource_logConcave {c₀ : ℝ} (hc₀ : UniformPotentialBound c₀) {U : Set (E d)}
    {V : E d → ℝ} {R : ℝ} (hU : IsOpen U) (hne : U.Nonempty) (hR : ∀ x ∈ U, ‖x‖ ≤ R)
    (hV : ConvexOn ℝ U V) (hVm : Measurable V) :
    ∃ B : ℝ, GoodSource (logConcaveSource U V) U R (c₀ * Real.sqrt (R ^ 2 + 1)) B := by
  obtain ⟨B, hB, hstrip⟩ := stripInterpolation_logConcave hU hne hR hV hVm
  obtain ⟨m, hm⟩ := exists_lower_bound_of_convexOn hU hne hR hV
  have hUm := hU.measurableSet
  have hvol0 : volume U ≠ 0 := (hU.measure_pos volume hne).ne'
  have hvol : volume U ≠ ∞ := volume_ne_top_of_norm_le hR
  have hexp_meas : Measurable fun x => Real.exp (-V x) := Real.measurable_exp.comp hVm.neg
  have hexp_pos : ∀ x ∈ U, 0 < Real.exp (-V x) := fun x _ => Real.exp_pos _
  have hexp_le : ∀ x ∈ U, Real.exp (-V x) ≤ Real.exp (-m) :=
    fun x hx => Real.exp_le_exp.mpr (neg_le_neg (hm x hx))
  have hprob : IsProbabilityMeasure (logConcaveSource U V) := by
    rw [logConcaveSource_eq_powerSource]
    exact powerSource_isProbabilityMeasure hUm hexp_meas hvol0 hvol hexp_pos hexp_le 1
  have hmem : ∀ᵐ x ∂logConcaveSource U V, x ∈ U := by
    rw [logConcaveSource_eq_powerSource]
    exact ae_mem_powerSource hUm _ 1
  exact ⟨B, hprob, hne, hR, hmem, atomicPotentialBound_logConcave hc₀ hU hne hR hV hVm,
    hstrip, hB⟩

/-- **Moment stability for log-concave sources**, given the atomic potential
estimate for uniform sources. The source has density proportional to
`exp (-V)` on the bounded open convex set `U`, with `V` convex. -/
theorem moment_stability_logConcave {c₀ : ℝ} (hc₀ : UniformPotentialBound c₀) {U : Set (E d)}
    {V : E d → ℝ} {R : ℝ} (hU : IsOpen U) (hne : U.Nonempty) (hR : ∀ x ∈ U, ‖x‖ ≤ R)
    (hV : ConvexOn ℝ U V) (hVm : Measurable V) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ C : ℝ, ∀ (μ ν : Measure (E d)), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) < ∞ →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap (logConcaveSource U V) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (logConcaveSource U V) ν Tν ∧
        (wasserstein2 μ ν ≤ smallDistance β →
          mapL2Dist (logConcaveSource U V) Tμ Tν ≤
            C * momentModulus p β (wasserstein2 μ ν)) := by
  obtain ⟨B, hgood⟩ := goodSource_logConcave hc₀ hU hne hR hV hVm
  refine ⟨Real.sqrt ((12 * d * (c₀ * Real.sqrt (R ^ 2 + 1)) ^ 2 + 72 * d * B) *
    (2 : ℝ) ^ (4 / 3 : ℝ) + 12 * (3 * p - 2) ^ β + 16), ?_⟩
  intro μ ν hμ hν hμM hν2
  exact moment_stability_of_goodSource hgood hp hβ μ ν hμM hν2

end

end BrenierMoment
