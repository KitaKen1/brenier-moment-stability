module

public import BrenierMoment.ActiveMaps
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel

@[expose] public section

/-!
# A transport plan compared with an active map

Let `T` be an active map of a finite potential and let `π` be any plan whose
first marginal is the source. If the second variable of the plan supports the
potential up to an error `γ` on `U`, the clipped distance between the plan and
the graph of `T` is bounded by `24 d H² h B` plus `4 d H / h` times the
integral of `γ`. The plan enters through its conditional kernel only: the
clipped slack inequality is integrated over the conditional law of the second
variable, and the result is a function of the base point, to which the
interpolation property of the source applies.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358 ProbabilityTheory
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Integration against a plan, through its conditional kernel. -/
lemma lintegral_eq_lintegral_condKernel (π : Measure (E d × E d)) [IsFiniteMeasure π]
    {F : E d × E d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂π = ∫⁻ x, ∫⁻ y', F (x, y') ∂(π.condKernel x) ∂π.fst := by
  have h := Measure.lintegral_compProd (μ := π.fst) (κ := π.condKernel) hF
  rw [π.disintegrate π.condKernel] at h
  exact h

/-- **A plan compared with an active map.** -/
theorem clipped_plan_comparison {ρ : Measure (E d)} {U : Set (E d)} {B : ℝ}
    (hstrip : StripInterpolation ρ U B)
    {y : ι → E d} {a : ι → ℝ} {T : E d → E d} (hT : IsActiveMap y a T) (hTm : Measurable T)
    {π : Measure (E d × E d)} [IsProbabilityMeasure π] (hπ : Measure.map Prod.fst π = ρ)
    {γ : E d × E d → ℝ} (hγm : Measurable γ) (hγ0 : ∀ x ∈ U, ∀ y' : E d, 0 ≤ γ (x, y'))
    (hγ : ∀ x ∈ U, ∀ z ∈ U, ∀ y' : E d,
      FiniteAffine.potential y a x + ⟪z - x, y'⟫ - γ (x, y') ≤ FiniteAffine.potential y a z)
    {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h) :
    (∫⁻ p, ENNReal.ofReal (‖clipVec H p.2 - clipVec H (T p.1)‖ ^ 2) ∂π) ≤
      ENNReal.ofReal (24 * d * H ^ 2 * h * B) +
        ENNReal.ofReal (4 * d * H / h) * ∫⁻ p, ENNReal.ofReal (γ p) ∂π := by
  have hfst : π.fst = ρ := hπ
  have hγo : Measurable fun p : E d × E d => ENNReal.ofReal (γ p) :=
    ENNReal.measurable_ofReal.comp hγm
  have hγint : Measurable fun x => ∫⁻ y', ENNReal.ofReal (γ (x, y')) ∂(π.condKernel x) :=
    hγo.lintegral_kernel_prod_right'
  have hγtot : (∫⁻ x, ∫⁻ y', ENNReal.ofReal (γ (x, y')) ∂(π.condKernel x) ∂ρ) =
      ∫⁻ p, ENNReal.ofReal (γ p) ∂π := by
    rw [← hfst]
    exact (lintegral_eq_lintegral_condKernel π hγo).symm
  -- the error, averaged over the conditional law
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : E d → ℝ≥0∞, Γ = fun x =>
      ENNReal.ofReal (4 * H / h) *
        ∫⁻ y', ENNReal.ofReal (γ (x, y')) ∂(π.condKernel x) := ⟨_, rfl⟩
  have hΓm : Measurable Γ := by
    rw [hΓ]
    exact hγint.const_mul _
  have hΓint : (∫⁻ x, Γ x ∂ρ) =
      ENNReal.ofReal (4 * H / h) * ∫⁻ p, ENNReal.ofReal (γ p) ∂π := by
    have h1 : (∫⁻ x, Γ x ∂ρ) = ∫⁻ x, ENNReal.ofReal (4 * H / h) *
        ∫⁻ y', ENNReal.ofReal (γ (x, y')) ∂(π.condKernel x) ∂ρ := by
      rw [hΓ]
    rw [h1, lintegral_const_mul _ hγint, hγtot]
  -- one coordinate
  have hcoord : ∀ j : Fin d,
      (∫⁻ p, ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) ∂π) ≤
        ENNReal.ofReal (24 * H ^ 2 * h * B) +
          ENNReal.ofReal (4 * H / h) * ∫⁻ p, ENNReal.ofReal (γ p) ∂π := by
    intro j
    have hFm : Measurable fun p : E d × E d =>
        ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) :=
      ENNReal.measurable_ofReal.comp
        ((((measurable_clip H).comp ((measurable_coord j).comp measurable_snd)).sub
          ((measurable_clip H).comp
            ((measurable_coord j).comp (hTm.comp measurable_fst)))).pow_const 2)
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : E d → ℝ≥0∞, Φ = fun x =>
        ∫⁻ y', ENNReal.ofReal ((clip H (y' j) - clip H (T x j)) ^ 2) ∂(π.condKernel x) :=
      ⟨_, rfl⟩
    have hΦm : Measurable Φ := by
      rw [hΦ]
      exact hFm.lintegral_kernel_prod_right'
    have hΦint : (∫⁻ x, Φ x ∂ρ) =
        ∫⁻ p, ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) ∂π := by
      rw [hΦ, ← hfst]
      exact (lintegral_eq_lintegral_condKernel π hFm).symm
    have ha : ∀ x ∈ U, Φ x ≤ ENNReal.ofReal (4 * H ^ 2) := by
      intro x _
      rw [hΦ]
      calc (∫⁻ y', ENNReal.ofReal ((clip H (y' j) - clip H (T x j)) ^ 2) ∂(π.condKernel x))
          ≤ ∫⁻ _, ENNReal.ofReal (4 * H ^ 2) ∂(π.condKernel x) :=
            lintegral_mono fun y' => ENNReal.ofReal_le_ofReal (sq_clip_sub_clip_le hH _ _)
        _ = ENNReal.ofReal (4 * H ^ 2) := by
            rw [lintegral_const, measure_univ, mul_one]
    have hb : ∀ x, x ∈ U → x + EuclideanSpace.single j h ∈ U →
        x - EuclideanSpace.single j h ∈ U →
        Φ x ≤ ENNReal.ofReal ((((0 : ℝ) - 0) / h) ^ 2) +
          ENNReal.ofReal (4 * H) *
            (ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))) +
              ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                clip H (fwdQuot y a j h (x - EuclideanSpace.single j h)))) + Γ x := by
      intro x hx hxp hxm
      have hBu := sub_nonneg.mpr (clip_mono H (hT.fwdQuot_mono j hh x))
      have h4 : 0 ≤ 4 * H / h := div_nonneg (by positivity) hh.le
      have hpt : ∀ y' : E d,
          ENNReal.ofReal ((clip H (y' j) - clip H (T x j)) ^ 2) ≤
            (ENNReal.ofReal ((((0 : ℝ) - 0) / h) ^ 2) +
              ENNReal.ofReal (4 * H) *
                (ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                    clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))) +
                  ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                    clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))))) +
            ENNReal.ofReal (4 * H / h) * ENNReal.ofReal (γ (x, y')) := by
        intro y'
        have hg : 0 ≤ γ (x, y') / h := div_nonneg (hγ0 x hx y') hh.le
        have h1 : y' j ≤ fwdQuot y a j h x + γ (x, y') / h := by
          have h0 := hγ x hx _ hxp y'
          rw [add_sub_cancel_left, EuclideanSpace.inner_single_left] at h0
          simp only [conj_trivial] at h0
          unfold fwdQuot
          rw [← add_div, le_div_iff₀ hh]
          linarith
        have h2 : fwdQuot y a j h (x - EuclideanSpace.single j h) - γ (x, y') / h ≤ y' j := by
          have h0 := hγ x hx _ hxm y'
          rw [sub_sub_cancel_left, inner_neg_left, EuclideanSpace.inner_single_left] at h0
          simp only [conj_trivial] at h0
          rw [fwdQuot_sub, ← sub_div, div_le_iff₀ hh]
          linarith
        have hsl := clipped_slope_sq_le_of_slack hH hg h1 h2 (hT.le_fwdQuot j hh x)
          (hT.fwdQuot_sub_le j hh x) (hT.fwdQuot_mono j hh x)
        have e0 : (fwdQuot y a j h x - fwdQuot y a j h x) ^ 2 = (((0 : ℝ) - 0) / h) ^ 2 := by
          simp
        rw [e0] at hsl
        have hres := ofReal_slope_bound hH hBu hBu
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * H) hg) hsl
        have e1 : ENNReal.ofReal (4 * H * (γ (x, y') / h)) =
            ENNReal.ofReal (4 * H / h) * ENNReal.ofReal (γ (x, y')) := by
          rw [← ENNReal.ofReal_mul h4]
          congr 1
          ring
        rw [e1] at hres
        exact hres
      have hγx : Measurable fun y' : E d => ENNReal.ofReal (γ (x, y')) :=
        hγo.comp measurable_prodMk_left
      rw [hΦ, hΓ]
      calc (∫⁻ y', ENNReal.ofReal ((clip H (y' j) - clip H (T x j)) ^ 2) ∂(π.condKernel x))
          ≤ ∫⁻ y', ((ENNReal.ofReal ((((0 : ℝ) - 0) / h) ^ 2) +
              ENNReal.ofReal (4 * H) *
                (ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                    clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))) +
                  ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                    clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))))) +
              ENNReal.ofReal (4 * H / h) * ENNReal.ofReal (γ (x, y'))) ∂(π.condKernel x) :=
            lintegral_mono hpt
        _ = ENNReal.ofReal ((((0 : ℝ) - 0) / h) ^ 2) +
              ENNReal.ofReal (4 * H) *
                (ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                    clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))) +
                  ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                    clip H (fwdQuot y a j h (x - EuclideanSpace.single j h)))) +
              ENNReal.ofReal (4 * H / h) *
                ∫⁻ y', ENNReal.ofReal (γ (x, y')) ∂(π.condKernel x) := by
            rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
              lintegral_const_mul _ hγx]
    have key := hstrip j H h hH hh Φ Γ (fun _ => 0)
      (fun x => clip H (fwdQuot y a j h x)) (fun x => clip H (fwdQuot y a j h x))
      hΦm hΓm measurable_const
      ((measurable_clip H).comp (measurable_fwdQuot y a j h))
      ((measurable_clip H).comp (measurable_fwdQuot y a j h))
      (fun x => abs_clip_le hH _) (fun x => abs_clip_le hH _)
      (fun x => clip_mono H (hT.fwdQuot_mono j hh x))
      (fun x => clip_mono H (hT.fwdQuot_mono j hh x)) ha hb
    have hz : (∫⁻ _ : E d, ENNReal.ofReal ((0 : ℝ) ^ 2) ∂ρ) = 0 := by simp
    rw [hz, mul_zero, zero_add, hΓint, hΦint] at key
    exact key
  have hΦm : ∀ j : Fin d, Measurable fun p : E d × E d =>
      ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) := fun j =>
    ENNReal.measurable_ofReal.comp
      ((((measurable_clip H).comp ((measurable_coord j).comp measurable_snd)).sub
        ((measurable_clip H).comp
          ((measurable_coord j).comp (hTm.comp measurable_fst)))).pow_const 2)
  have hsum : ∀ p : E d × E d, ENNReal.ofReal (‖clipVec H p.2 - clipVec H (T p.1)‖ ^ 2) =
      ∑ j : Fin d, ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) := by
    intro p
    rw [norm_sq_clipVec_sub, ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := (ENNReal.ofReal_natCast d).symm
  have e1 : (d : ℝ≥0∞) * ENNReal.ofReal (24 * H ^ 2 * h * B) =
      ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by
    rw [hd, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    congr 1
    ring
  have e2 : (d : ℝ≥0∞) * ENNReal.ofReal (4 * H / h) = ENNReal.ofReal (4 * d * H / h) := by
    rw [hd, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    congr 1
    ring
  calc (∫⁻ p, ENNReal.ofReal (‖clipVec H p.2 - clipVec H (T p.1)‖ ^ 2) ∂π)
      = ∫⁻ p, ∑ j : Fin d, ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) ∂π := by
        simp only [hsum]
    _ = ∑ j : Fin d, ∫⁻ p, ENNReal.ofReal ((clip H (p.2 j) - clip H (T p.1 j)) ^ 2) ∂π :=
        lintegral_finsetSum _ fun j _ => hΦm j
    _ ≤ ∑ _j : Fin d, (ENNReal.ofReal (24 * H ^ 2 * h * B) +
          ENNReal.ofReal (4 * H / h) * ∫⁻ p, ENNReal.ofReal (γ p) ∂π) :=
        Finset.sum_le_sum fun j _ => hcoord j
    _ = ENNReal.ofReal (24 * d * H ^ 2 * h * B) +
          ENNReal.ofReal (4 * d * H / h) * ∫⁻ p, ENNReal.ofReal (γ p) ∂π := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
          ← mul_assoc, e1, e2]

end

end BrenierMoment
