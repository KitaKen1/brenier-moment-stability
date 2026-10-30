module

public import BrenierMoment.PlanComparison
public import OAI.Analysis.Brenier.Conjugacy
public import OAI.Analysis.Brenier.MapDistance

@[expose] public section

/-!
# Limits of active maps are unique optimal maps

Let the source have the interpolation property. If a map `T` is a limit in
`L²` of active maps of finite potentials, then `T` is the unique optimal map
from the source to its law: every plan with the same marginals that costs no
more than the graph of `T` is the graph of `T`.

No limit potential is constructed. For the `n`-th finite potential, the
Fenchel gap integrated against a competing plan is at most the gap integrated
against the graph of `T`, which tends to zero. The comparison of
`PlanComparison.lean` then bounds the clipped distance between the plan and
the graph of the `n`-th active map by `24 d H² h B` plus a term that vanishes
with the gap. Letting first `n → ∞` and then `h → 0` puts the plan on the
graph of `T`.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358 Filter
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

variable {d : ℕ}

/-! ### The Fenchel gap of a finite potential -/

section Gap

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Twice the Fenchel gap of a finite potential, the conjugate being taken over `K`. -/
def gap2 (K : Set (E d)) (y : ι → E d) (a : ι → ℝ) (p : E d × E d) : ℝ :=
  ‖p.1 - p.2‖ ^ 2 - (‖p.1‖ ^ 2 - 2 * FiniteAffine.potential y a p.1) -
    (‖p.2‖ ^ 2 - 2 * restrictedConjugate K (FiniteAffine.potential y a) p.2)

lemma gap2_nonneg {K : Set (E d)} (hK : IsCompact K) (y : ι → E d) (a : ι → ℝ)
    {p : E d × E d} (hp : p.1 ∈ K) : 0 ≤ gap2 K y a p := by
  have h := restrictedConjugate_quadratic_dual_le hK
    (FiniteAffine.continuous_potential y a).continuousOn hp p.2
  unfold gap2
  linarith

lemma measurable_gap2 {K : Set (E d)} (hK : IsCompact K) (hne : K.Nonempty) (y : ι → E d)
    (a : ι → ℝ) : Measurable (gap2 K y a) := by
  have hφ := FiniteAffine.continuous_potential y a
  have hc := restrictedConjugate_continuous hK hne hφ.continuousOn
  have hcont : Continuous fun p : E d × E d =>
      ‖p.1 - p.2‖ ^ 2 - (‖p.1‖ ^ 2 - 2 * FiniteAffine.potential y a p.1) -
        (‖p.2‖ ^ 2 - 2 * restrictedConjugate K (FiniteAffine.potential y a) p.2) :=
    (((continuous_fst.sub continuous_snd).norm.pow 2).sub
      ((continuous_fst.norm.pow 2).sub (continuous_const.mul (hφ.comp continuous_fst)))).sub
      ((continuous_snd.norm.pow 2).sub (continuous_const.mul (hc.comp continuous_snd)))
  exact hcont.measurable

/-- The second variable supports the potential on `K` up to half the gap. -/
lemma gap2_support {K : Set (E d)} (hK : IsCompact K) (y : ι → E d) (a : ι → ℝ) (x : E d)
    {z : E d} (hz : z ∈ K) (y' : E d) :
    FiniteAffine.potential y a x + ⟪z - x, y'⟫ - gap2 K y a (x, y') / 2 ≤
      FiniteAffine.potential y a z := by
  have h := restrictedConjugate_fenchel hK
    (FiniteAffine.continuous_potential y a).continuousOn hz y'
  have hn : ‖x - y'‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y'⟫ + ‖y'‖ ^ 2 := norm_sub_sq_real x y'
  unfold gap2
  dsimp only
  rw [inner_sub_left, hn]
  linarith

/-- The gap vanishes on the graph of an active map. -/
lemma gap2_active {K : Set (E d)} (hK : IsCompact K) {y : ι → E d} {a : ι → ℝ}
    {T : E d → E d} (hT : IsActiveMap y a T) {x : E d} (hx : x ∈ K) :
    gap2 K y a (x, T x) = 0 := by
  have h := (restrictedConjugate_quadratic_dual_eq_iff hK
    (FiniteAffine.continuous_potential y a).continuousOn hx (y := T x)).mpr
    (fun z _ => hT.supports x z)
  unfold gap2
  dsimp only
  linarith

/-- The gap is Lipschitz in the second variable, uniformly on `K`. -/
lemma gap2_sub_le {K : Set (E d)} (hK : IsCompact K) (hne : K.Nonempty) {R : ℝ}
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (y : ι → E d) (a : ι → ℝ) {x : E d} (hx : x ∈ K) (y' y'' : E d) :
    gap2 K y a (x, y') - gap2 K y a (x, y'') ≤ 4 * R * ‖y' - y''‖ := by
  have h1 := restrictedConjugate_sub_le hK hne
    (FiniteAffine.continuous_potential y a).continuousOn hR y' y''
  have h2 : -⟪x, y' - y''⟫ ≤ R * ‖y' - y''‖ := by
    have h3 := abs_real_inner_le_norm x (y' - y'')
    have h4 : ‖x‖ * ‖y' - y''‖ ≤ R * ‖y' - y''‖ :=
      mul_le_mul_of_nonneg_right (hR x hx) (norm_nonneg _)
    linarith [neg_abs_le ⟪x, y' - y''⟫]
  rw [inner_sub_right] at h2
  have hn1 : ‖x - y'‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y'⟫ + ‖y'‖ ^ 2 := norm_sub_sq_real x y'
  have hn2 : ‖x - y''‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y''⟫ + ‖y''‖ ^ 2 := norm_sub_sq_real x y''
  unfold gap2
  dsimp only
  rw [hn1, hn2]
  linarith

/-- A plan that costs no more than the graph of `T` has no larger total gap. -/
lemma lintegral_gap2_le {ρ : Measure (E d)} [IsProbabilityMeasure ρ] {K : Set (E d)}
    (hK : IsCompact K) (hne : K.Nonempty) {R : ℝ} (hR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hρK : ∀ᵐ x ∂ρ, x ∈ K) (y : ι → E d) (a : ι → ℝ) {T : E d → E d} (hTm : Measurable T)
    (hcost : quadraticPlanCost (graphPlan ρ T) ≠ ∞)
    {π : Measure (E d × E d)} (hπ : IsCoupling ρ (Measure.map T ρ) π)
    (hle : quadraticPlanCost π ≤ quadraticPlanCost (graphPlan ρ T)) :
    (∫⁻ p, ENNReal.ofReal (gap2 K y a p) ∂π) ≤
      ∫⁻ x, ENNReal.ofReal (gap2 K y a (x, T x)) ∂ρ := by
  have hφ := FiniteAffine.continuous_potential y a
  have hc := restrictedConjugate_continuous hK hne hφ.continuousOn
  -- the two dual functions, shifted to be nonnegative
  obtain ⟨f, hf⟩ : ∃ f : E d → ℝ, f = fun x => ‖x‖ ^ 2 - 2 * FiniteAffine.potential y a x :=
    ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : E d → ℝ, g = fun y' =>
      ‖y'‖ ^ 2 - 2 * restrictedConjugate K (FiniteAffine.potential y a) y' := ⟨_, rfl⟩
  have hfc : Continuous f := by
    rw [hf]
    exact (continuous_norm.pow 2).sub (continuous_const.mul hφ)
  have hgc : Continuous g := by
    rw [hg]
    exact (continuous_norm.pow 2).sub (continuous_const.mul hc)
  have hgap : ∀ p : E d × E d, gap2 K y a p = ‖p.1 - p.2‖ ^ 2 - f p.1 - g p.2 := by
    intro p
    rw [hf, hg]
    rfl
  obtain ⟨m, hm⟩ := hK.bddBelow_image hfc.continuousOn
  have hfm : ∀ x ∈ K, 0 ≤ f x + |m| := by
    intro x hx
    have h1 : m ≤ f x := hm ⟨x, hx, rfl⟩
    linarith [neg_abs_le m]
  obtain ⟨cg, hcg⟩ : ∃ cg : ℝ, cg =
      2 * |restrictedConjugate K (FiniteAffine.potential y a) 0| + R ^ 2 := ⟨_, rfl⟩
  have hgm : ∀ y' : E d, 0 ≤ g y' + cg := by
    intro y'
    have h1 := restrictedConjugate_sub_le hK hne hφ.continuousOn hR y' 0
    rw [sub_zero] at h1
    have h2 := le_abs_self (restrictedConjugate K (FiniteAffine.potential y a) 0)
    rw [hg, hcg]
    change 0 ≤ ‖y'‖ ^ 2 - 2 * restrictedConjugate K (FiniteAffine.potential y a) y' +
      (2 * |restrictedConjugate K (FiniteAffine.potential y a) 0| + R ^ 2)
    nlinarith [sq_nonneg (‖y'‖ - R)]
  have hcg0 : 0 ≤ cg := by
    rw [hcg]
    positivity
  have hFm : Measurable fun x => ENNReal.ofReal (f x + |m|) :=
    ENNReal.measurable_ofReal.comp (hfc.measurable.add_const _)
  have hGm : Measurable fun y' => ENNReal.ofReal (g y' + cg) :=
    ENNReal.measurable_ofReal.comp (hgc.measurable.add_const _)
  have hgapm : Measurable fun p => ENNReal.ofReal (gap2 K y a p) :=
    ENNReal.measurable_ofReal.comp (measurable_gap2 hK hne y a)
  have hFm1 : Measurable fun p : E d × E d => ENNReal.ofReal (f p.1 + |m|) :=
    hFm.comp measurable_fst
  have hpair : Measurable fun x : E d => (x, T x) := measurable_id.prodMk hTm
  -- the identity satisfied by every plan with these marginals
  have hid : ∀ π' : Measure (E d × E d), IsCoupling ρ (Measure.map T ρ) π' →
      (∫⁻ p, ENNReal.ofReal (gap2 K y a p) ∂π') +
        ((∫⁻ x, ENNReal.ofReal (f x + |m|) ∂ρ) +
          ∫⁻ y', ENNReal.ofReal (g y' + cg) ∂(Measure.map T ρ)) =
      quadraticPlanCost π' + ENNReal.ofReal (|m| + cg) := by
    intro π' hπ'
    have hprob : IsProbabilityMeasure π' := hπ'.1
    have hfstK : ∀ᵐ p ∂π', p.1 ∈ K := by
      apply ae_of_ae_map measurable_fst.aemeasurable
      rw [hπ'.2.1]
      exact hρK
    have hpt : ∀ᵐ p ∂π', ENNReal.ofReal (gap2 K y a p) +
        (ENNReal.ofReal (f p.1 + |m|) + ENNReal.ofReal (g p.2 + cg)) =
        ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) + ENNReal.ofReal (|m| + cg) := by
      filter_upwards [hfstK] with p hp
      rw [← ENNReal.ofReal_add (hfm p.1 hp) (hgm p.2),
        ← ENNReal.ofReal_add (gap2_nonneg hK y a hp) (add_nonneg (hfm p.1 hp) (hgm p.2)),
        ← ENNReal.ofReal_add (sq_nonneg _) (add_nonneg (abs_nonneg m) hcg0), hgap p]
      congr 1
      ring
    have h1 : (∫⁻ p, ENNReal.ofReal (f p.1 + |m|) ∂π') = ∫⁻ x, ENNReal.ofReal (f x + |m|) ∂ρ := by
      rw [← hπ'.2.1, lintegral_map hFm measurable_fst]
    have h2 : (∫⁻ p, ENNReal.ofReal (g p.2 + cg) ∂π') =
        ∫⁻ y', ENNReal.ofReal (g y' + cg) ∂(Measure.map T ρ) := by
      rw [← hπ'.2.2, lintegral_map hGm measurable_snd]
    calc (∫⁻ p, ENNReal.ofReal (gap2 K y a p) ∂π') +
          ((∫⁻ x, ENNReal.ofReal (f x + |m|) ∂ρ) +
            ∫⁻ y', ENNReal.ofReal (g y' + cg) ∂(Measure.map T ρ))
        = ∫⁻ p, (ENNReal.ofReal (gap2 K y a p) +
            (ENNReal.ofReal (f p.1 + |m|) + ENNReal.ofReal (g p.2 + cg))) ∂π' := by
          rw [lintegral_add_left hgapm, lintegral_add_left hFm1, h1, h2]
      _ = ∫⁻ p, (ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) + ENNReal.ofReal (|m| + cg)) ∂π' :=
          lintegral_congr_ae hpt
      _ = quadraticPlanCost π' + ENNReal.ofReal (|m| + cg) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
          rfl
  have hid0 := hid (graphPlan ρ T) (graphPlan_isCoupling hTm rfl)
  have hid1 := hid π hπ
  -- the dual part is finite
  have hWfin : (∫⁻ x, ENNReal.ofReal (f x + |m|) ∂ρ) +
      ∫⁻ y', ENNReal.ofReal (g y' + cg) ∂(Measure.map T ρ) ≠ ∞ := by
    have hle0 : (∫⁻ x, ENNReal.ofReal (f x + |m|) ∂ρ) +
        ∫⁻ y', ENNReal.ofReal (g y' + cg) ∂(Measure.map T ρ) ≤
        quadraticPlanCost (graphPlan ρ T) + ENNReal.ofReal (|m| + cg) := by
      rw [← hid0]
      exact le_add_self
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hcost, ENNReal.ofReal_ne_top⟩) hle0
  have hgraph : (∫⁻ p, ENNReal.ofReal (gap2 K y a p) ∂(graphPlan ρ T)) =
      ∫⁻ x, ENNReal.ofReal (gap2 K y a (x, T x)) ∂ρ := by
    unfold graphPlan
    rw [lintegral_map hgapm hpair]
  rw [← hgraph]
  refine ENNReal.le_of_add_le_add_right hWfin ?_
  rw [hid1, hid0]
  gcongr

end Gap

/-! ### The certificate -/

/-- `T` is an active map of some finite potential. -/
def IsFinitePotentialMap (T : E d → E d) : Prop :=
  ∃ (n : ℕ) (y : Fin (n + 1) → E d) (a : Fin (n + 1) → ℝ), IsActiveMap y a T

lemma clipVec_eq_self {H : ℝ} {v : E d} (hv : ‖v‖ ≤ H) : clipVec H v = v := by
  ext j
  rw [clipVec_apply]
  apply clip_eq_self
  have h := PiLp.norm_apply_le v j
  rw [Real.norm_eq_abs] at h
  exact h.trans hv

/-- **Limits of active maps are unique optimal maps.** -/
theorem isUniqueQuadraticOptimalMap_of_tendsto_active {ρ : Measure (E d)}
    [IsProbabilityMeasure ρ] {U : Set (E d)} {R B : ℝ} (hUne : U.Nonempty)
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hρU : ∀ᵐ x ∂ρ, x ∈ U) (hB : 0 ≤ B)
    (hstrip : StripInterpolation ρ U B)
    {Tn : ℕ → E d → E d} {T : E d → E d} (hTn : ∀ n, IsFinitePotentialMap (Tn n))
    (hTnm : ∀ n, Measurable (Tn n)) (hTm : Measurable T)
    (hT2 : (∫⁻ x, ENNReal.ofReal (‖T x‖ ^ 2) ∂ρ) ≠ ∞)
    (hlim : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ) atTop (𝓝 0)) :
    IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  obtain ⟨x₀, hx₀⟩ := hUne
  have hR0 : 0 ≤ R := (norm_nonneg x₀).trans (hR x₀ hx₀)
  -- the compact set carrying the source
  obtain ⟨K, hKdef⟩ : ∃ K : Set (E d), K = closure U := ⟨_, rfl⟩
  have hUK : U ⊆ K := by
    rw [hKdef]
    exact subset_closure
  have hKball : K ⊆ Metric.closedBall (0 : E d) R := by
    rw [hKdef]
    exact closure_minimal (fun x hx => mem_closedBall_zero_iff.mpr (hR x hx))
      Metric.isClosed_closedBall
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact isClosed_closure
  have hK : IsCompact K :=
    (isCompact_closedBall (0 : E d) R).of_isClosed_subset hKclosed hKball
  have hKne : K.Nonempty := ⟨x₀, hUK hx₀⟩
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => mem_closedBall_zero_iff.mp (hKball hx)
  have hρK : ∀ᵐ x ∂ρ, x ∈ K := hρU.mono fun x hx => hUK hx
  -- the graph of `T` has finite cost
  have hcost : quadraticPlanCost (graphPlan ρ T) ≠ ∞ := by
    have hcm : Measurable fun p : E d × E d => ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const 2)
    have hpair : Measurable fun x : E d => (x, T x) := measurable_id.prodMk hTm
    have hgc : quadraticPlanCost (graphPlan ρ T) = ∫⁻ x, ENNReal.ofReal (‖x - T x‖ ^ 2) ∂ρ := by
      unfold quadraticPlanCost graphPlan
      rw [lintegral_map hcm hpair]
    rw [hgc]
    have hbound : ∀ᵐ x ∂ρ, ENNReal.ofReal (‖x - T x‖ ^ 2) ≤
        ENNReal.ofReal (2 * R ^ 2) + 2 * ENNReal.ofReal (‖T x‖ ^ 2) := by
      filter_upwards [hρK] with x hx
      have h1 : ‖x - T x‖ ≤ ‖x‖ + ‖T x‖ := norm_sub_le _ _
      have h2 := hKR x hx
      have h3 : ‖x - T x‖ ^ 2 ≤ 2 * R ^ 2 + 2 * ‖T x‖ ^ 2 := by
        nlinarith [norm_nonneg (x - T x), norm_nonneg x, norm_nonneg (T x),
          sq_nonneg (‖x‖ - ‖T x‖), mul_self_le_mul_self (norm_nonneg (x - T x)) h1,
          mul_self_le_mul_self (norm_nonneg x) h2]
      calc ENNReal.ofReal (‖x - T x‖ ^ 2) ≤ ENNReal.ofReal (2 * R ^ 2 + 2 * ‖T x‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal h3
        _ = ENNReal.ofReal (2 * R ^ 2) + 2 * ENNReal.ofReal (‖T x‖ ^ 2) := by
            have e : ENNReal.ofReal (2 * ‖T x‖ ^ 2) = 2 * ENNReal.ofReal (‖T x‖ ^ 2) := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
            rw [ENNReal.ofReal_add (by positivity) (by positivity), e]
    have hT2m : Measurable fun x => ENNReal.ofReal (‖T x‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp (hTm.norm.pow_const 2)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul _ hT2m]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofNat_ne_top hT2⟩
  -- every plan that costs no more than the graph is the graph
  have key : ∀ π : Measure (E d × E d), IsCoupling ρ (Measure.map T ρ) π →
      quadraticPlanCost π ≤ quadraticPlanCost (graphPlan ρ T) → π = graphPlan ρ T := by
    intro π hπ hle
    have hprob : IsProbabilityMeasure π := hπ.1
    have hfst : Measure.map Prod.fst π = ρ := hπ.2.1
    -- the clipped distance to the graph vanishes at every level
    have hzero : ∀ N : ℕ,
        (∫⁻ p, ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) ∂π) = 0 := by
      intro N
      have hH : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      -- the bound for fixed `h`, `s` and `n`
      have hstep : ∀ (h s : ℝ), 0 < h → 0 < s → ∀ n : ℕ,
          (∫⁻ p, ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) ∂π) ≤
            2 * (ENNReal.ofReal (24 * d * (N : ℝ) ^ 2 * h * B) +
              ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R * s)) +
            (2 * (ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R / s)) + 2) *
              ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by
        intro h s hh hs n
        obtain ⟨k, y, a, hact⟩ := hTn n
        have hen : Measurable fun x => ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) :=
          ENNReal.measurable_ofReal.comp ((hTm.sub (hTnm n)).norm.pow_const 2)
        -- the plan against the `n`-th active map
        have hcmp := clipped_plan_comparison hstrip hact (hTnm n) hfst
          (γ := fun p => gap2 K y a p / 2) ((measurable_gap2 hK hKne y a).div_const 2)
          (fun x hx y' => div_nonneg (gap2_nonneg hK y a (hUK hx)) (by norm_num))
          (fun x _ z hz y' => gap2_support hK y a x (hUK hz) y') hH hh
        -- the gap against the plan, and against the graph of `T`
        have hgap1 : (∫⁻ p, ENNReal.ofReal (gap2 K y a p / 2) ∂π) ≤
            ∫⁻ p, ENNReal.ofReal (gap2 K y a p) ∂π := by
          refine lintegral_mono fun p => ?_
          change ENNReal.ofReal (gap2 K y a p / 2) ≤ ENNReal.ofReal (gap2 K y a p)
          rcases le_total 0 (gap2 K y a p) with h0 | h0
          · exact ENNReal.ofReal_le_ofReal (by linarith)
          · rw [ENNReal.ofReal_eq_zero.mpr (by linarith)]
            exact zero_le
        have hgap2 := lintegral_gap2_le hK hKne hKR hρK y a hTm hcost hπ hle
        have hgap3 : (∫⁻ x, ENNReal.ofReal (gap2 K y a (x, T x)) ∂ρ) ≤
            ENNReal.ofReal (2 * R * s) + ENNReal.ofReal (2 * R / s) *
              ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by
          have hpt : ∀ᵐ x ∂ρ, ENNReal.ofReal (gap2 K y a (x, T x)) ≤
              ENNReal.ofReal (2 * R * s) +
                ENNReal.ofReal (2 * R / s) * ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) := by
            filter_upwards [hρK] with x hx
            have h1 := gap2_sub_le hK hKne hKR y a hx (T x) (Tn n x)
            rw [gap2_active hK hact hx, sub_zero] at h1
            have h2 : 4 * R * ‖T x - Tn n x‖ ≤
                2 * R * s + 2 * R / s * ‖T x - Tn n x‖ ^ 2 := by
              have h3 : 2 * ‖T x - Tn n x‖ ≤ s + ‖T x - Tn n x‖ ^ 2 / s := by
                rw [← sub_nonneg]
                have h4 : s + ‖T x - Tn n x‖ ^ 2 / s - 2 * ‖T x - Tn n x‖ =
                    (‖T x - Tn n x‖ - s) ^ 2 / s := by
                  field_simp
                  ring
                rw [h4]
                positivity
              have h5 : 2 * R * s + 2 * R / s * ‖T x - Tn n x‖ ^ 2 =
                  2 * R * (s + ‖T x - Tn n x‖ ^ 2 / s) := by ring
              rw [h5]
              nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * R)]
            calc ENNReal.ofReal (gap2 K y a (x, T x))
                ≤ ENNReal.ofReal (2 * R * s + 2 * R / s * ‖T x - Tn n x‖ ^ 2) :=
                  ENNReal.ofReal_le_ofReal (h1.trans h2)
              _ = ENNReal.ofReal (2 * R * s) +
                    ENNReal.ofReal (2 * R / s) * ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) := by
                  have e : ENNReal.ofReal (2 * R / s * ‖T x - Tn n x‖ ^ 2) =
                      ENNReal.ofReal (2 * R / s) * ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) :=
                    ENNReal.ofReal_mul (by positivity)
                  rw [ENNReal.ofReal_add (by positivity) (by positivity), e]
          calc (∫⁻ x, ENNReal.ofReal (gap2 K y a (x, T x)) ∂ρ)
              ≤ ∫⁻ x, (ENNReal.ofReal (2 * R * s) +
                  ENNReal.ofReal (2 * R / s) * ENNReal.ofReal (‖T x - Tn n x‖ ^ 2)) ∂ρ :=
                lintegral_mono_ae hpt
            _ = ENNReal.ofReal (2 * R * s) + ENNReal.ofReal (2 * R / s) *
                  ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by
                rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
                  lintegral_const_mul _ hen]
        -- from the `n`-th active map to `T`
        have htri : ∀ p : E d × E d,
            ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) ≤
              2 * ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2) +
                2 * ENNReal.ofReal (‖T p.1 - Tn n p.1‖ ^ 2) := by
          intro p
          have h1 : ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ≤
              ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ +
                ‖clipVec (N : ℝ) (Tn n p.1) - clipVec (N : ℝ) (T p.1)‖ := by
            have h0 : clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1) =
                (clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)) +
                  (clipVec (N : ℝ) (Tn n p.1) - clipVec (N : ℝ) (T p.1)) := by abel
            rw [h0]
            exact norm_add_le _ _
          have h2 : ‖clipVec (N : ℝ) (Tn n p.1) - clipVec (N : ℝ) (T p.1)‖ ≤
              ‖T p.1 - Tn n p.1‖ := by
            rw [norm_sub_rev (T p.1)]
            exact norm_clipVec_sub_le _ _ _
          have h12 : ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ≤
              ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ + ‖T p.1 - Tn n p.1‖ := by
            linarith
          have h3 : ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2 ≤
              2 * ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2 +
                2 * ‖T p.1 - Tn n p.1‖ ^ 2 := by
            nlinarith [norm_nonneg (clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)),
              norm_nonneg (clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)),
              norm_nonneg (clipVec (N : ℝ) (Tn n p.1) - clipVec (N : ℝ) (T p.1)),
              norm_nonneg (T p.1 - Tn n p.1),
              mul_self_le_mul_self
                (norm_nonneg (clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1))) h12,
              sq_nonneg (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ -
                ‖T p.1 - Tn n p.1‖)]
          calc ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2)
              ≤ ENNReal.ofReal (2 * ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2 +
                  2 * ‖T p.1 - Tn n p.1‖ ^ 2) := ENNReal.ofReal_le_ofReal h3
            _ = 2 * ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2) +
                  2 * ENNReal.ofReal (‖T p.1 - Tn n p.1‖ ^ 2) := by
                have e : ∀ r : ℝ, ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
                  intro r
                  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
                rw [ENNReal.ofReal_add (by positivity) (by positivity), e, e]
        have hm1 : Measurable fun p : E d × E d =>
            ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2) :=
          ENNReal.measurable_ofReal.comp
            ((((measurable_clipVec _).comp measurable_snd).sub
              ((measurable_clipVec _).comp ((hTnm n).comp measurable_fst))).norm.pow_const 2)
        have hen1 : Measurable fun p : E d × E d => ENNReal.ofReal (‖T p.1 - Tn n p.1‖ ^ 2) :=
          hen.comp measurable_fst
        have hmarg : (∫⁻ p, ENNReal.ofReal (‖T p.1 - Tn n p.1‖ ^ 2) ∂π) =
            ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by
          rw [← hfst, lintegral_map hen measurable_fst]
        calc (∫⁻ p, ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) ∂π)
            ≤ ∫⁻ p, (2 * ENNReal.ofReal
                  (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2) +
                2 * ENNReal.ofReal (‖T p.1 - Tn n p.1‖ ^ 2)) ∂π := lintegral_mono htri
          _ = 2 * (∫⁻ p, ENNReal.ofReal
                  (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (Tn n p.1)‖ ^ 2) ∂π) +
                2 * ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by
              rw [lintegral_add_left (hm1.const_mul 2), lintegral_const_mul _ hm1,
                lintegral_const_mul _ hen1, hmarg]
          _ ≤ 2 * (ENNReal.ofReal (24 * d * (N : ℝ) ^ 2 * h * B) +
                ENNReal.ofReal (4 * d * (N : ℝ) / h) *
                  (ENNReal.ofReal (2 * R * s) + ENNReal.ofReal (2 * R / s) *
                    ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ)) +
                2 * ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by
              gcongr
              exact hcmp.trans (by gcongr; exact hgap1.trans (hgap2.trans hgap3))
          _ = 2 * (ENNReal.ofReal (24 * d * (N : ℝ) ^ 2 * h * B) +
                ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R * s)) +
              (2 * (ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R / s)) + 2) *
                ∫⁻ x, ENNReal.ofReal (‖T x - Tn n x‖ ^ 2) ∂ρ := by ring
      -- let `n → ∞`
      have hlimit : ∀ (h s : ℝ), 0 < h → 0 < s →
          (∫⁻ p, ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) ∂π) ≤
            2 * (ENNReal.ofReal (24 * d * (N : ℝ) ^ 2 * h * B) +
              ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R * s)) := by
        intro h s hh hs
        have hCfin : 2 * (ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R / s)) + 2
            ≠ ∞ :=
          ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofNat_ne_top
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
            ENNReal.ofNat_ne_top⟩
        have ht := (tendsto_const_nhds (x := 2 * (ENNReal.ofReal (24 * d * (N : ℝ) ^ 2 * h * B) +
            ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R * s)))).add
          (ENNReal.Tendsto.const_mul hlim (Or.inr hCfin))
        rw [mul_zero, add_zero] at ht
        exact ge_of_tendsto' ht (hstep h s hh hs)
      -- let `h → 0` with `s = h²`
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 48 * d * (N : ℝ) ^ 2 * B + 16 * d * (N : ℝ) * R := ⟨_, rfl⟩
      have hc0 : 0 ≤ c := by
        rw [hc]
        positivity
      have hsmall : ∀ h : ℝ, 0 < h →
          (∫⁻ p, ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) ∂π) ≤
            ENNReal.ofReal (h * c) := by
        intro h hh
        have h1 := hlimit h (h ^ 2) hh (by positivity)
        have hne : h ≠ 0 := hh.ne'
        have h2 : 2 * (ENNReal.ofReal (24 * d * (N : ℝ) ^ 2 * h * B) +
            ENNReal.ofReal (4 * d * (N : ℝ) / h) * ENNReal.ofReal (2 * R * h ^ 2)) =
            ENNReal.ofReal (h * c) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), hc]
          congr 1
          field_simp
          ring
        rw [h2] at h1
        exact h1
      refine le_antisymm ?_ zero_le
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
      rw [zero_add]
      have hεr : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
      have h1 := hsmall ((ε : ℝ) / (c + 1)) (div_pos hεr (by linarith))
      refine h1.trans ?_
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [hεr, hc0]
    -- hence the plan is concentrated on the graph
    have hae : ∀ᵐ p ∂π, ∀ N : ℕ, clipVec (N : ℝ) p.2 = clipVec (N : ℝ) (T p.1) := by
      rw [ae_all_iff]
      intro N
      have hm : Measurable fun p : E d × E d =>
          ENNReal.ofReal (‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2) :=
        ENNReal.measurable_ofReal.comp
          ((((measurable_clipVec _).comp measurable_snd).sub
            ((measurable_clipVec _).comp (hTm.comp measurable_fst))).norm.pow_const 2)
      have h0 := (lintegral_eq_zero_iff hm).mp (hzero N)
      filter_upwards [h0] with p hp
      have h1 : ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ ^ 2 ≤ 0 :=
        ENNReal.ofReal_eq_zero.mp hp
      have h2 : ‖clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1)‖ = 0 := by
        nlinarith [norm_nonneg (clipVec (N : ℝ) p.2 - clipVec (N : ℝ) (T p.1))]
      exact sub_eq_zero.mp (norm_eq_zero.mp h2)
    have hgraph : ∀ᵐ p ∂π, p.2 = T p.1 := by
      filter_upwards [hae] with p hp
      obtain ⟨N, hN⟩ := exists_nat_ge (max ‖p.2‖ ‖T p.1‖)
      have h1 := hp N
      rw [clipVec_eq_self ((le_max_left _ _).trans hN),
        clipVec_eq_self ((le_max_right _ _).trans hN)] at h1
      exact h1
    exact eq_graph_map_of_fst_eq_and_ae_on_graph hTm hfst hgraph
  unfold IsUniqueQuadraticOptimalMap IsQuadraticOptimalMap
  refine ⟨⟨hTm, rfl, fun π hπ => ?_⟩, key⟩
  by_contra hlt
  have hlt' := not_le.mp hlt
  have heq := key π hπ hlt'.le
  rw [heq] at hlt'
  exact lt_irrefl _ hlt'

end

end BrenierMoment
