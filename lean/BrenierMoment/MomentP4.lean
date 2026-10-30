module

public import BrenierMoment.Tails
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace BrenierMoment

open MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

lemma quadraticTailTerm_le_fourth {H : ℝ} (hH : 0 < H) (y : E) :
    quadraticTailTerm H y ≤ ‖y‖ ^ 4 / H ^ 2 := by
  unfold quadraticTailTerm
  split_ifs with hy
  · apply (le_div_iff₀ (sq_pos_of_pos hH)).mpr
    have hsq : H ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    nlinarith [mul_nonneg (sq_nonneg ‖y‖) (sub_nonneg.mpr hsq)]
  · positivity

variable [MeasurableSpace E] [BorelSpace E]

/-- A fourth-moment bound gives the exact quadratic-tail envelope needed in
the scalar `p4_bound_from_interpolation` lemma. Integrability is explicit so
that the Bochner integral cannot silently take its default value. -/
theorem quadraticTail_le_inv_square_of_fourth_moment {μ : Measure E}
    (hμ4 : Integrable (fun y : E => ‖y‖ ^ 4) μ)
    (hM : (∫ y : E, ‖y‖ ^ 4 ∂μ) ≤ 1) {H : ℝ} (hH : 0 < H) :
    quadraticTail μ H ≤ 1 / H ^ 2 := by
  have hbound : Integrable (fun y : E => ‖y‖ ^ 4 / H ^ 2) μ := hμ4.div_const _
  have htail : Integrable (quadraticTailTerm H : E → ℝ) μ := by
    apply hbound.mono' (measurable_quadraticTailTerm H).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (quadraticTailTerm_nonneg H y)]
    exact quadraticTailTerm_le_fourth hH y
  calc
    quadraticTail μ H ≤ ∫ y : E, ‖y‖ ^ 4 / H ^ 2 ∂μ :=
      integral_mono htail hbound (fun y => quadraticTailTerm_le_fourth hH y)
    _ = (∫ y : E, ‖y‖ ^ 4 ∂μ) / H ^ 2 := integral_div (H ^ 2) (fun y : E => ‖y‖ ^ 4)
    _ ≤ 1 / H ^ 2 := div_le_div_of_nonneg_right hM (sq_nonneg H)

end

end BrenierMoment
