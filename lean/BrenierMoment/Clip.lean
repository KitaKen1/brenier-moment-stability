module

public import BrenierMoment.Tails
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Clipped slopes

The gradient interpolation keeps the tails of the maps by clipping only the
scalar slopes, and only inside the secant inequality: a clipped slope lies
between the clipped difference quotients on either side, and the difference
of those two clipped quotients telescopes under translation. The pointwise
inequality below is the scalar core of that argument; it involves no
derivative and no bound on the slopes themselves.
-/

namespace BrenierMoment

noncomputable section

/-- Clipping to `[-H, H]`. -/
def clip (H r : ℝ) : ℝ := max (-H) (min r H)

lemma clip_mono (H : ℝ) {r r' : ℝ} (h : r' ≤ r) : clip H r' ≤ clip H r :=
  max_le_max le_rfl (min_le_min h le_rfl)

lemma neg_le_clip (H r : ℝ) : -H ≤ clip H r := le_max_left _ _

lemma clip_le {H : ℝ} (hH : 0 ≤ H) (r : ℝ) : clip H r ≤ H :=
  max_le (by linarith) (min_le_right _ _)

lemma abs_clip_le {H : ℝ} (hH : 0 ≤ H) (r : ℝ) : |clip H r| ≤ H :=
  abs_le.mpr ⟨neg_le_clip H r, clip_le hH r⟩

/-- Clipping does not increase differences. -/
lemma clip_sub_clip_le (H : ℝ) {r r' : ℝ} (h : r' ≤ r) : clip H r - clip H r' ≤ r - r' := by
  simp only [clip, max_def, min_def]
  split_ifs <;> linarith

lemma clip_sub_clip_le_abs (H r r' : ℝ) : clip H r - clip H r' ≤ |r - r'| := by
  rcases le_total r' r with h | h
  · exact (clip_sub_clip_le H h).trans (le_abs_self _)
  · have h1 := clip_mono H h
    have h2 := abs_nonneg (r - r')
    linarith

lemma clip_eq_self {H r : ℝ} (h : |r| ≤ H) : clip H r = r := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold clip
  rw [min_eq_left h2, max_eq_right h1]

/-- The clipped part is never larger than the number itself. -/
lemma sq_sub_clip_le {H : ℝ} (hH : 0 ≤ H) (r : ℝ) : (r - clip H r) ^ 2 ≤ r ^ 2 := by
  simp only [clip, max_def, min_def]
  split_ifs <;> nlinarith

/-- **Clipping inside the secant inequality.** Let `sT, sS` be slopes of two
convex functions at a point, `qu, qv` their forward difference quotients there
and `qu', qv'` the forward quotients one step behind. Then the squared
difference of the clipped slopes is controlled by the difference of the
quotients and by the increments of the clipped quotients. -/
theorem clipped_slope_sq_le {H sT sS qu qv qu' qv' : ℝ} (hH : 0 ≤ H)
    (h1 : sT ≤ qu) (h2 : qu' ≤ sT) (h3 : sS ≤ qv) (h4 : qv' ≤ sS) :
    (clip H sT - clip H sS) ^ 2 ≤
      (qu - qv) ^ 2 + 4 * H * ((clip H qu - clip H qu') + (clip H qv - clip H qv')) := by
  have hGu : 0 ≤ clip H qu - clip H qu' := sub_nonneg.mpr (clip_mono H (h2.trans h1))
  have hGv : 0 ≤ clip H qv - clip H qv' := sub_nonneg.mpr (clip_mono H (h4.trans h3))
  have hQ0 : 0 ≤ |qu - qv| := abs_nonneg _
  -- upper and lower bounds for the difference of clipped slopes
  have hup : clip H sT - clip H sS ≤ |qu - qv| + (clip H qv - clip H qv') := by
    have a1 := clip_mono H h1
    have a2 := clip_mono H h4
    have a3 := clip_sub_clip_le_abs H qu qv
    linarith
  have hlo : -(clip H sT - clip H sS) ≤ |qu - qv| + (clip H qu - clip H qu') := by
    have a1 := clip_mono H h3
    have a2 := clip_mono H h2
    have a3 := clip_sub_clip_le_abs H qv qu
    rw [abs_sub_comm] at a3
    linarith
  have habs : |clip H sT - clip H sS| ≤
      |qu - qv| + (clip H qu - clip H qu') + (clip H qv - clip H qv') :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have h2H : |clip H sT - clip H sS| ≤ 2 * H := by
    have a1 := abs_clip_le hH sT
    have a2 := abs_clip_le hH sS
    have a3 := abs_sub (clip H sT) (clip H sS)
    linarith
  have hD0 : 0 ≤ |clip H sT - clip H sS| := abs_nonneg _
  -- multiply out
  have m1 : |clip H sT - clip H sS| * |clip H sT - clip H sS| ≤
      |clip H sT - clip H sS| *
        (|qu - qv| + (clip H qu - clip H qu') + (clip H qv - clip H qv')) :=
    mul_le_mul_of_nonneg_left habs hD0
  have m2 : |clip H sT - clip H sS| * ((clip H qu - clip H qu') + (clip H qv - clip H qv')) ≤
      2 * H * ((clip H qu - clip H qu') + (clip H qv - clip H qv')) :=
    mul_le_mul_of_nonneg_right h2H (add_nonneg hGu hGv)
  have m3 : 0 ≤ (|clip H sT - clip H sS| - |qu - qv|) ^ 2 := sq_nonneg _
  have e1 : |clip H sT - clip H sS| * |clip H sT - clip H sS| =
      (clip H sT - clip H sS) ^ 2 := by rw [← sq, sq_abs]
  have e2 : |qu - qv| * |qu - qv| = (qu - qv) ^ 2 := by rw [← sq, sq_abs]
  nlinarith

variable {d : ℕ}

/-- Clipping every coordinate of a vector removes at most its quadratic tail. -/
theorem sum_sq_sub_clip_le {H : ℝ} (hH : 0 ≤ H) (y : EuclideanSpace ℝ (Fin d)) :
    ∑ j, (y j - clip H (y j)) ^ 2 ≤ quadraticTailTerm H y := by
  unfold quadraticTailTerm
  split_ifs with hy
  · rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_le_sum fun j _ => sq_sub_clip_le hH (y j)
  · have hle : ‖y‖ ≤ H := le_of_not_gt hy
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j _
    have hj : |y j| ≤ H := by
      have h := PiLp.norm_apply_le y j
      rw [Real.norm_eq_abs] at h
      exact h.trans hle
    rw [clip_eq_self hj, sub_self]
    norm_num

end

end BrenierMoment
