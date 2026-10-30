module

public import BrenierMoment.Tails
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Quadratic tails from a power-logarithmic moment

For `2 ≤ p` and `0 ≤ β`, the weight `‖y‖ ^ p * log (e + ‖y‖) ^ β` dominates
`‖y‖ ^ 2` above a threshold `H` with the explicit factor
`H ^ (2 - p) * log (e + H) ^ (-β)`. No optimization is involved.
-/

namespace BrenierMoment

open MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

/-- The weight of the power-logarithmic moment `M_{p,β}`. -/
def momentWeight (p β : ℝ) (y : E) : ℝ :=
  ‖y‖ ^ p * Real.log (Real.exp 1 + ‖y‖) ^ β

/-- The envelope of the quadratic tail above `H` under `M_{p,β} ≤ 1`. -/
def tailEnvelope (p β H : ℝ) : ℝ :=
  H ^ (2 - p) * Real.log (Real.exp 1 + H) ^ (-β)

lemma one_lt_exp_one_add {t : ℝ} (ht : 0 ≤ t) : 1 < Real.exp 1 + t := by
  linarith [Real.exp_one_gt_two]

lemma log_exp_one_add_pos {t : ℝ} (ht : 0 ≤ t) : 0 < Real.log (Real.exp 1 + t) :=
  Real.log_pos (one_lt_exp_one_add ht)

lemma momentWeight_nonneg (p β : ℝ) (y : E) : 0 ≤ momentWeight p β y :=
  mul_nonneg (Real.rpow_nonneg (norm_nonneg y) p)
    (Real.rpow_nonneg (log_exp_one_add_pos (norm_nonneg y)).le β)

lemma tailEnvelope_nonneg (p β : ℝ) {H : ℝ} (hH : 0 ≤ H) : 0 ≤ tailEnvelope p β H :=
  mul_nonneg (Real.rpow_nonneg hH _) (Real.rpow_nonneg (log_exp_one_add_pos hH).le _)

/-- The pointwise comparison behind the tail bound. -/
theorem quadraticTailTerm_le_envelope {p β H : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β)
    (hH : 0 < H) (y : E) :
    quadraticTailTerm H y ≤ tailEnvelope p β H * momentWeight p β y := by
  unfold quadraticTailTerm
  split_ifs with hy
  · have hy0 : 0 < ‖y‖ := hH.trans hy
    have hLH : 0 < Real.log (Real.exp 1 + H) := log_exp_one_add_pos hH.le
    have hLy : Real.log (Real.exp 1 + H) ≤ Real.log (Real.exp 1 + ‖y‖) :=
      Real.log_le_log (by linarith [one_lt_exp_one_add hH.le]) (by linarith)
    have h1 : ‖y‖ ^ (2 - p) ≤ H ^ (2 - p) :=
      Real.rpow_le_rpow_of_nonpos hH hy.le (by linarith)
    have h2 : Real.log (Real.exp 1 + H) ^ β ≤ Real.log (Real.exp 1 + ‖y‖) ^ β :=
      Real.rpow_le_rpow hLH.le hLy hβ
    have h3 : ‖y‖ ^ 2 = ‖y‖ ^ p * ‖y‖ ^ (2 - p) := by
      rw [← Real.rpow_add hy0, ← Real.rpow_two]
      congr 1
      ring
    have h4 : Real.log (Real.exp 1 + H) ^ (-β) * Real.log (Real.exp 1 + H) ^ β = 1 := by
      rw [← Real.rpow_add hLH, neg_add_cancel, Real.rpow_zero]
    have hyp : 0 ≤ ‖y‖ ^ p := Real.rpow_nonneg hy0.le p
    have hHp : 0 ≤ H ^ (2 - p) := Real.rpow_nonneg hH.le _
    have hLn : 0 ≤ Real.log (Real.exp 1 + H) ^ (-β) := Real.rpow_nonneg hLH.le _
    unfold tailEnvelope momentWeight
    calc ‖y‖ ^ 2 = ‖y‖ ^ p * ‖y‖ ^ (2 - p) := h3
      _ ≤ ‖y‖ ^ p * H ^ (2 - p) := mul_le_mul_of_nonneg_left h1 hyp
      _ = ‖y‖ ^ p * H ^ (2 - p) *
            (Real.log (Real.exp 1 + H) ^ (-β) * Real.log (Real.exp 1 + H) ^ β) := by
          rw [h4, mul_one]
      _ ≤ ‖y‖ ^ p * H ^ (2 - p) *
            (Real.log (Real.exp 1 + H) ^ (-β) * Real.log (Real.exp 1 + ‖y‖) ^ β) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hLn) (mul_nonneg hyp hHp)
      _ = H ^ (2 - p) * Real.log (Real.exp 1 + H) ^ (-β) *
            (‖y‖ ^ p * Real.log (Real.exp 1 + ‖y‖) ^ β) := by ring
  · exact mul_nonneg (tailEnvelope_nonneg p β hH.le) (momentWeight_nonneg p β y)

variable [MeasurableSpace E] [BorelSpace E]

/-- A power-logarithmic moment bound controls the quadratic tail at every
positive threshold. Integrability is explicit so that the Bochner integral
cannot silently take its default value. -/
theorem quadraticTail_le_envelope {μ : Measure E} {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β)
    (hint : Integrable (momentWeight p β : E → ℝ) μ)
    (hM : (∫ y : E, momentWeight p β y ∂μ) ≤ 1) {H : ℝ} (hH : 0 < H) :
    quadraticTail μ H ≤ tailEnvelope p β H := by
  have henv : 0 ≤ tailEnvelope p β H := tailEnvelope_nonneg p β hH.le
  have hbound : Integrable (fun y : E => tailEnvelope p β H * momentWeight p β y) μ :=
    hint.const_mul _
  have htail : Integrable (quadraticTailTerm H : E → ℝ) μ := by
    apply hbound.mono' (measurable_quadraticTailTerm H).aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (quadraticTailTerm_nonneg H y)]
    exact quadraticTailTerm_le_envelope hp hβ hH y
  calc
    quadraticTail μ H ≤ ∫ y : E, tailEnvelope p β H * momentWeight p β y ∂μ :=
      integral_mono htail hbound (fun y => quadraticTailTerm_le_envelope hp hβ hH y)
    _ = tailEnvelope p β H * ∫ y : E, momentWeight p β y ∂μ := integral_const_mul _ _
    _ ≤ tailEnvelope p β H * 1 := mul_le_mul_of_nonneg_left hM henv
    _ = tailEnvelope p β H := mul_one _

end

end BrenierMoment
