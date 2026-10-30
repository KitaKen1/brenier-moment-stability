module

public import BrenierMoment.Clip

@[expose] public section

/-!
# Clipped slopes with slack

The secant inequality of `Clip.lean` is extended to a slope that supports its
potential only up to an error: if `sT` lies between the two difference
quotients enlarged by `g ≥ 0`, the clipped inequality holds with the additional
term `4 H g`, which is linear in `g`. This is what allows an arbitrary
transport plan to be compared with the map of a finite potential, the error
being the Fenchel gap of the plan.
-/

namespace BrenierMoment

noncomputable section

private lemma sq_le_of_slack {a A B g H : ℝ} (hH : 0 ≤ H) (hg : 0 ≤ g) (ha0 : 0 ≤ a)
    (ha : a ≤ 2 * H) (hle : a ≤ A + B + g) (hB : 0 ≤ B) (hA : A ≤ 2 * H)
    (hAB : A + B ≤ 2 * H) : a ^ 2 ≤ A ^ 2 + 4 * H * B + 4 * H * g := by
  by_cases ht : A + B ≤ 0
  · have hag : a ≤ g := by linarith
    have h1 : a * a ≤ g * (2 * H) := mul_le_mul hag ha ha0 hg
    nlinarith [sq_nonneg A, mul_nonneg hH hB, mul_nonneg hH hg]
  · have ht' : 0 < A + B := lt_of_not_ge ht
    have h1 : a * a ≤ a * (A + B + g) := mul_le_mul_of_nonneg_left hle ha0
    have h2 : a * (A + B) ≤ (A + B + g) * (A + B) := mul_le_mul_of_nonneg_right hle ht'.le
    have h3 : a * g ≤ 2 * H * g := mul_le_mul_of_nonneg_right ha hg
    have h4 : g * (A + B) ≤ g * (2 * H) := mul_le_mul_of_nonneg_left hAB hg
    have h5 : B * (A + (A + B)) ≤ B * (4 * H) :=
      mul_le_mul_of_nonneg_left (by linarith) hB
    nlinarith [h1, h2, h3, h4, h5]

/-- **Clipped slopes with slack.** Let `qu' ≤ qu` and `qv' ≤ qv` be the lower and
upper difference quotients of two potentials. If `sS` lies between `qv'` and
`qv`, and `sT` lies between `qu' - g` and `qu + g`, then the clipped slopes
satisfy the secant inequality up to `4 H g`. -/
theorem clipped_slope_sq_le_of_slack {H g sT sS qu qv qu' qv' : ℝ} (hH : 0 ≤ H) (hg : 0 ≤ g)
    (h1 : sT ≤ qu + g) (h2 : qu' - g ≤ sT) (h3 : sS ≤ qv) (h4 : qv' ≤ sS)
    (hu : qu' ≤ qu) :
    (clip H sT - clip H sS) ^ 2 ≤
      (qu - qv) ^ 2 +
        4 * H * ((clip H qu - clip H qu') + (clip H qv - clip H qv')) + 4 * H * g := by
  have hv : qv' ≤ qv := h4.trans h3
  -- bounds of the clipped values
  have bT := abs_le.mp (abs_clip_le hH sT)
  have bS := abs_le.mp (abs_clip_le hH sS)
  have bqu := abs_le.mp (abs_clip_le hH qu)
  have bqv := abs_le.mp (abs_clip_le hH qv)
  have bqu' := abs_le.mp (abs_clip_le hH qu')
  have bqv' := abs_le.mp (abs_clip_le hH qv')
  have hBu : 0 ≤ clip H qu - clip H qu' := sub_nonneg.mpr (clip_mono H hu)
  have hBv : 0 ≤ clip H qv - clip H qv' := sub_nonneg.mpr (clip_mono H hv)
  -- the clipped quotients differ by at most the quotients
  have hA1 : clip H qu - clip H qv ≤ |qu - qv| := clip_sub_clip_le_abs H qu qv
  have hA2 : clip H qv - clip H qu ≤ |qu - qv| := by
    rw [abs_sub_comm]
    exact clip_sub_clip_le_abs H qv qu
  have hAsq : (clip H qu - clip H qv) ^ 2 ≤ (qu - qv) ^ 2 := by
    rw [← sq_abs (qu - qv)]
    exact sq_le_sq' (by linarith) hA1
  -- the slack moves a clipped value by at most `g`
  have hup : clip H (qu + g) - clip H qu ≤ g := by
    have := clip_sub_clip_le H (show qu ≤ qu + g by linarith)
    linarith
  have hdown : clip H qu' - clip H (qu' - g) ≤ g := by
    have := clip_sub_clip_le H (show qu' - g ≤ qu' by linarith)
    linarith
  have hT1 : clip H sT ≤ clip H (qu + g) := clip_mono H h1
  have hT2 : clip H (qu' - g) ≤ clip H sT := clip_mono H h2
  have hS1 : clip H sS ≤ clip H qv := clip_mono H h3
  have hS2 : clip H qv' ≤ clip H sS := clip_mono H h4
  rcases le_total 0 (clip H sT - clip H sS) with ha | ha
  · have hmain := sq_le_of_slack (a := clip H sT - clip H sS) (A := clip H qu - clip H qv)
      (B := clip H qv - clip H qv') hH hg ha (by linarith) (by linarith) hBv (by linarith)
      (by linarith)
    nlinarith [mul_nonneg hH hBu]
  · have hmain := sq_le_of_slack (a := clip H sS - clip H sT) (A := clip H qv - clip H qu)
      (B := clip H qu - clip H qu') hH hg (by linarith) (by linarith) (by linarith) hBu
      (by linarith) (by linarith)
    have hsq1 : (clip H sT - clip H sS) ^ 2 = (clip H sS - clip H sT) ^ 2 := by ring
    have hsq2 : (clip H qv - clip H qu) ^ 2 = (clip H qu - clip H qv) ^ 2 := by ring
    nlinarith [mul_nonneg hH hBv]

end

end BrenierMoment
