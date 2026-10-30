module

public import BrenierMoment.MomentTail
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Substituting the threshold

The interpolation estimate holds for every threshold `H`. The optimal `H` is
not searched for: the known value
`H = δ ^ (-2 / D) * log (e / δ) ^ (-3 β / D)`, `D = 3 p - 2`,
is substituted and the three terms are compared after taking logarithms.
Every power becomes an exponential of a linear form in `log δ` and
`log (log (e / δ))`, so the exponent bookkeeping is linear arithmetic.
-/

namespace BrenierMoment

noncomputable section

/-- The modulus `δ ^ ((p - 2) / (3 p - 2)) * log (e / δ) ^ (-2 β / (3 p - 2))`. -/
def momentModulus (p β δ : ℝ) : ℝ :=
  δ ^ ((p - 2) / (3 * p - 2)) * Real.log (Real.exp 1 / δ) ^ (-(2 * β) / (3 * p - 2))

/-- An explicit admissible range of distances. -/
def smallDistance (β : ℝ) : ℝ := Real.exp (1 - (6 * β + 2) ^ 2)

lemma smallDistance_pos (β : ℝ) : 0 < smallDistance β := Real.exp_pos _

lemma smallDistance_lt_one {β : ℝ} (hβ : 0 ≤ β) : smallDistance β < 1 := by
  unfold smallDistance
  have h : 1 - (6 * β + 2) ^ 2 < 0 := by nlinarith [mul_nonneg hβ hβ]
  calc Real.exp (1 - (6 * β + 2) ^ 2) < Real.exp 0 := Real.exp_lt_exp.mpr h
    _ = 1 := Real.exp_zero

lemma momentModulus_pos {p β δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < momentModulus p β δ := by
  have hlog : 0 < Real.log (Real.exp 1 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ0]
    linarith [Real.exp_one_gt_two]
  exact mul_pos (Real.rpow_pos_of_pos hδ0 _) (Real.rpow_pos_of_pos hlog _)

/-- The scalar optimization in closed form. If the squared error is bounded by
the interpolation term, twelve times the tail envelope and `16 δ ^ 2` for every
positive threshold, then it has the power-logarithmic rate, with an explicit
constant, for every `δ ≤ smallDistance β`. The case `p = 2` is included. -/
theorem rate_of_threshold_family {p β A Err δ : ℝ}
    (hp : 2 ≤ p) (hβ : 0 ≤ β) (hA : 0 ≤ A) (hErr : 0 ≤ Err)
    (hδ0 : 0 < δ) (hδ : δ ≤ smallDistance β)
    (h : ∀ H : ℝ, 0 < H →
      Err ^ 2 ≤ A * (δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) +
        12 * tailEnvelope p β H + 16 * δ ^ 2) :
    Err ≤ Real.sqrt (A + 12 * (3 * p - 2) ^ β + 16) * momentModulus p β δ := by
  have hD : 0 < 3 * p - 2 := by linarith
  -- logarithmic variables
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log δ := ⟨_, rfl⟩
  have hℓ : Real.log (Real.exp 1 / δ) = 1 - u := by
    rw [Real.log_div (Real.exp_pos 1).ne' hδ0.ne', Real.log_exp, hu]
  have hu_le : u ≤ 1 - (6 * β + 2) ^ 2 := by
    have h1 := Real.log_le_log hδ0 hδ
    rw [smallDistance, Real.log_exp] at h1
    rw [hu]
    exact h1
  have hℓ_ge : (6 * β + 2) ^ 2 ≤ 1 - u := by linarith
  have hℓ_pos : 0 < 1 - u := by nlinarith [mul_nonneg hβ hβ]
  -- `s` is the square root of `log (e / δ)`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (1 - u) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - u := by rw [hs]; exact Real.sq_sqrt hℓ_pos.le
  have hs_ge : 6 * β + 2 ≤ s := by
    by_contra hc
    have hc' : s < 6 * β + 2 := not_le.mp hc
    nlinarith
  have hs_pos : 0 < s := by linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (1 - u) := ⟨_, rfl⟩
  have hlam_le : lam ≤ 2 * s - 2 := by
    have h1 : Real.log (s ^ 2) = 2 * Real.log s := by
      rw [Real.log_pow]
      norm_num
    have h2 := Real.log_le_sub_one_of_pos hs_pos
    rw [hlam, ← hs_sq, h1]
    linarith
  -- the modulus as an exponential
  have hω : momentModulus p β δ =
      Real.exp ((p - 2) / (3 * p - 2) * u - 2 * β / (3 * p - 2) * lam) := by
    unfold momentModulus
    rw [hℓ, Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hℓ_pos, ← Real.exp_add,
      ← hu, ← hlam]
    congr 1
    ring
  have hω2 : momentModulus p β δ ^ 2 =
      Real.exp (2 * ((p - 2) / (3 * p - 2) * u - 2 * β / (3 * p - 2) * lam)) := by
    rw [hω, sq, ← Real.exp_add]
    congr 1
    ring
  -- the substituted threshold
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ,
      H = Real.exp (-(2 / (3 * p - 2)) * u - 3 * β / (3 * p - 2) * lam) := ⟨_, rfl⟩
  have hHpos : 0 < H := by rw [hHdef]; exact Real.exp_pos _
  have hlogH : Real.log H = -(2 / (3 * p - 2)) * u - 3 * β / (3 * p - 2) * lam := by
    rw [hHdef, Real.log_exp]
  have hβlam : β * lam ≤ β * (2 * s - 2) := mul_le_mul_of_nonneg_left hlam_le hβ
  have hlogH_ge : (1 - u) / (3 * p - 2) ≤ Real.log H := by
    rw [hlogH, div_le_iff₀ hD]
    have h1 : (-(2 / (3 * p - 2)) * u - 3 * β / (3 * p - 2) * lam) * (3 * p - 2) =
        -2 * u - 3 * (β * lam) := by
      field_simp
    rw [h1]
    nlinarith [mul_nonneg hβ hs0]
  -- first term
  have hT1 : δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ) = momentModulus p β δ ^ 2 := by
    rw [hω2, Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hHpos, hlogH, ← hu,
      ← Real.exp_add]
    congr 1
    field_simp
    ring
  -- second term
  have hlogeH : (1 - u) / (3 * p - 2) ≤ Real.log (Real.exp 1 + H) :=
    hlogH_ge.trans (Real.log_le_log hHpos (by linarith [Real.exp_pos 1]))
  have hbase : 0 < (1 - u) / (3 * p - 2) := div_pos hℓ_pos hD
  have hT2a : Real.log (Real.exp 1 + H) ^ (-β) ≤ ((1 - u) / (3 * p - 2)) ^ (-β) :=
    Real.rpow_le_rpow_of_nonpos hbase hlogeH (by linarith)
  have hT2b : ((1 - u) / (3 * p - 2)) ^ (-β) = (3 * p - 2) ^ β * Real.exp (-β * lam) := by
    rw [Real.rpow_def_of_pos hbase, Real.log_div hℓ_pos.ne' hD.ne',
      Real.rpow_def_of_pos hD, ← Real.exp_add, ← hlam]
    congr 1
    ring
  have hT2c : H ^ (2 - p) * Real.exp (-β * lam) = momentModulus p β δ ^ 2 := by
    rw [hω2, Real.rpow_def_of_pos hHpos, hlogH, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have hT2 : tailEnvelope p β H ≤ (3 * p - 2) ^ β * momentModulus p β δ ^ 2 := by
    unfold tailEnvelope
    calc H ^ (2 - p) * Real.log (Real.exp 1 + H) ^ (-β)
        ≤ H ^ (2 - p) * ((1 - u) / (3 * p - 2)) ^ (-β) :=
          mul_le_mul_of_nonneg_left hT2a (Real.rpow_nonneg hHpos.le _)
      _ = (3 * p - 2) ^ β * (H ^ (2 - p) * Real.exp (-β * lam)) := by
          rw [hT2b]
          ring
      _ = (3 * p - 2) ^ β * momentModulus p β δ ^ 2 := by rw [hT2c]
  -- third term
  have hδ2 : δ ^ 2 = Real.exp (2 * u) := by
    rw [hu, two_mul, Real.exp_add, Real.exp_log hδ0, sq]
  have hkey : β * lam ≤ -p * u := by
    have h1 : 0 ≤ (s - 1) * ((p - 2) * (s + 1)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
    have h2 : 0 ≤ (s - 1) * (2 * (s + 1) - 2 * β) :=
      mul_nonneg (by linarith) (by linarith)
    have h3 : -p * u = p * (s ^ 2 - 1) := by rw [hs_sq]; ring
    rw [h3]
    nlinarith
  have hT3 : δ ^ 2 ≤ momentModulus p β δ ^ 2 := by
    rw [hδ2, hω2]
    apply Real.exp_le_exp.mpr
    have ha : (p - 2) / (3 * p - 2) * (3 * p - 2) = p - 2 := div_mul_cancel₀ _ hD.ne'
    have hb : 2 * β / (3 * p - 2) * (3 * p - 2) = 2 * β := div_mul_cancel₀ _ hD.ne'
    have h1 : 2 * ((p - 2) / (3 * p - 2) * u - 2 * β / (3 * p - 2) * lam) - 2 * u =
        4 * (-p * u - β * lam) / (3 * p - 2) := by
      rw [eq_div_iff hD.ne']
      linear_combination (2 * u) * ha - (2 * lam) * hb
    have h2 : 0 ≤ 4 * (-p * u - β * lam) / (3 * p - 2) :=
      div_nonneg (by linarith) hD.le
    linarith
  -- assembly
  have hDβ : 0 ≤ (3 * p - 2 : ℝ) ^ β := Real.rpow_nonneg hD.le β
  have hsum := h H hHpos
  rw [hT1] at hsum
  have hbound : Err ^ 2 ≤ (A + 12 * (3 * p - 2) ^ β + 16) * momentModulus p β δ ^ 2 := by
    have hm : 0 ≤ momentModulus p β δ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hT2 (by norm_num : (0 : ℝ) ≤ 12),
      mul_le_mul_of_nonneg_left hT3 (by norm_num : (0 : ℝ) ≤ 16)]
  have hωpos : 0 < momentModulus p β δ := by rw [hω]; exact Real.exp_pos _
  calc Err = Real.sqrt (Err ^ 2) := (Real.sqrt_sq hErr).symm
    _ ≤ Real.sqrt ((A + 12 * (3 * p - 2) ^ β + 16) * momentModulus p β δ ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (A + 12 * (3 * p - 2) ^ β + 16) * momentModulus p β δ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hωpos.le]

end

end BrenierMoment
