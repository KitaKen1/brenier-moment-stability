module

public import BrenierMoment.Threshold

@[expose] public section

/-!
# Parameters of the sharp four-atom family

For a prescribed distance `δ` the cell mass `a` and the scale `R` are given in
closed form. With these values the target distance is exactly `δ`, the
power-logarithmic moment of both targets is at most one, and the map error is
a fixed multiple of the modulus. No intermediate-value argument is needed.
As in `Threshold`, powers are compared after taking logarithms.
-/

namespace BrenierMoment

noncomputable section

/-- The normalizing constant of the sharp family. -/
def sharpKappa (p β : ℝ) : ℝ :=
  (3 * (12 : ℝ) ^ p * (13 : ℝ) ^ β) ^ (2 / (3 * p - 2))

/-- The common mass of the three small cells. -/
def sharpMass (p β δ : ℝ) : ℝ :=
  sharpKappa p β *
    (δ ^ (2 * p / (3 * p - 2)) * Real.log (Real.exp 1 / δ) ^ (2 * β / (3 * p - 2)))

/-- The slope scale determined by a cell mass and a prescribed target distance. -/
def scaleOf (a δ : ℝ) : ℝ := 4 * δ / (a * Real.sqrt a)

/-- The slope scale of the sharp family. -/
def sharpScale (p β δ : ℝ) : ℝ := scaleOf (sharpMass p β δ) δ

/-- The admissible range of distances for the sharp family. -/
def sharpDistance (p β : ℝ) : ℝ :=
  min (smallDistance β)
    (Real.exp (-((3 * p - 2) / 2) * Real.log (6 * sharpKappa p β)))

lemma sharpKappa_pos (p β : ℝ) : 0 < sharpKappa p β :=
  Real.rpow_pos_of_pos (by positivity) _

lemma sharpDistance_pos (p β : ℝ) : 0 < sharpDistance p β :=
  lt_min (smallDistance_pos β) (Real.exp_pos _)

lemma sharpDistance_lt_one {p β : ℝ} (hβ : 0 ≤ β) : sharpDistance p β < 1 :=
  (min_le_left _ _).trans_lt (smallDistance_lt_one hβ)

lemma scaleOf_pos {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) : 0 < scaleOf a δ :=
  div_pos (by positivity) (mul_pos ha (Real.sqrt_pos.mpr ha))

/-- With the tilt `R * a / 4` the squared target distance `a * b ^ 2` equals `δ ^ 2`. -/
theorem sqrt_mass_tilt_sq {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) :
    Real.sqrt (a * (scaleOf a δ * a / 4) ^ 2) = δ := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have h1 : scaleOf a δ * a / 4 = δ / Real.sqrt a := by
    unfold scaleOf
    calc 4 * δ / (a * Real.sqrt a) * a / 4
        = a * (4 * δ) / (a * Real.sqrt a) / 4 := by
          rw [div_mul_eq_mul_div, mul_comm (4 * δ) a]
      _ = 4 * δ / Real.sqrt a / 4 := by rw [mul_div_mul_left _ _ ha.ne']
      _ = δ / Real.sqrt a := by ring
  have h2 : a * (δ / Real.sqrt a) ^ 2 = δ ^ 2 := by
    rw [div_pow, Real.sq_sqrt ha.le, mul_comm a (δ ^ 2 / a), div_mul_cancel₀ _ ha.ne']
  rw [h1, h2, Real.sqrt_sq hδ]

/-- The lower bound `R * √a / 2` of the map error in terms of `δ` and `a`. -/
theorem scaleOf_mul_sqrt_half {a δ : ℝ} (ha : 0 < a) :
    scaleOf a δ * Real.sqrt a / 2 = 2 * δ / a := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  unfold scaleOf
  calc 4 * δ / (a * Real.sqrt a) * Real.sqrt a / 2
      = 4 * δ * Real.sqrt a / (a * Real.sqrt a) / 2 := by rw [div_mul_eq_mul_div]
    _ = 4 * δ / a / 2 := by rw [mul_div_mul_right _ _ hs.ne']
    _ = 2 * δ / a := by ring

/-- The three analytic facts about the closed-form parameters. -/
theorem sharp_parameters {p β δ : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β)
    (hδ0 : 0 < δ) (hδ : δ ≤ sharpDistance p β) :
    0 < sharpMass p β δ ∧ sharpMass p β δ ≤ 1 / 6 ∧
    2 * δ / sharpMass p β δ = 2 / sharpKappa p β * momentModulus p β δ ∧
    3 * sharpMass p β δ * ((3 * sharpScale p β δ) ^ p *
      Real.log (Real.exp 1 + 3 * sharpScale p β δ) ^ β) ≤ 1 := by
  have hD : 0 < 3 * p - 2 := by linarith
  -- the constant `K = 3 * 12 ^ p * 13 ^ β`
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 3 * (12 : ℝ) ^ p * (13 : ℝ) ^ β := ⟨_, rfl⟩
  have h12 : 1 ≤ (12 : ℝ) ^ p := Real.one_le_rpow (by norm_num) (by linarith)
  have h13 : 1 ≤ (13 : ℝ) ^ β := Real.one_le_rpow (by norm_num) hβ
  have hXY : 1 ≤ (12 : ℝ) ^ p * (13 : ℝ) ^ β := by nlinarith
  have hK3 : 3 ≤ K := by
    rw [hKdef]
    linarith
  have hKpos : 0 < K := by linarith
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hlogK : Real.log K = Real.log 3 + p * Real.log 12 + β * Real.log 13 := by
    rw [hKdef, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)]
  -- logarithmic variables
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = Real.log δ := ⟨_, rfl⟩
  have hδexp : Real.exp u = δ := by rw [hu, Real.exp_log hδ0]
  have hℓ : Real.log (Real.exp 1 / δ) = 1 - u := by
    rw [Real.log_div (Real.exp_pos 1).ne' hδ0.ne', Real.log_exp, hu]
  have hu_le : u ≤ 1 - (6 * β + 2) ^ 2 := by
    have h1 := Real.log_le_log hδ0 (hδ.trans (min_le_left _ _))
    rw [smallDistance, Real.log_exp] at h1
    rw [hu]
    exact h1
  have hu0 : u ≤ 0 := by linarith [mul_nonneg hβ hβ]
  have hℓ_ge : (6 * β + 2) ^ 2 ≤ 1 - u := by linarith
  have hℓ_one : 1 ≤ 1 - u := by linarith
  have hℓ_pos : 0 < 1 - u := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (1 - u) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = 1 - u := by rw [hs]; exact Real.sq_sqrt hℓ_pos.le
  have hs_ge : 6 * β + 2 ≤ s := by
    by_contra hc
    have hc' : s < 6 * β + 2 := not_le.mp hc
    have h1 : s * s < (6 * β + 2) * (6 * β + 2) := mul_self_lt_mul_self hs0 hc'
    linarith
  have hs_pos : 0 < s := by linarith
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = Real.log (1 - u) := ⟨_, rfl⟩
  have hlam0 : 0 ≤ lam := by rw [hlam]; exact Real.log_nonneg hℓ_one
  have hlam_le : lam ≤ 2 * s - 2 := by
    have h1 : Real.log (s ^ 2) = 2 * Real.log s := by
      rw [Real.log_pow]
      norm_num
    have h2 := Real.log_le_sub_one_of_pos hs_pos
    rw [hlam, ← hs_sq, h1]
    linarith
  have hβlam : β * lam ≤ -u := by
    have h1 : β * lam ≤ β * (2 * s - 2) := mul_le_mul_of_nonneg_left hlam_le hβ
    have h2 : 0 ≤ (s - 1) * (s + 1 - 2 * β) := mul_nonneg (by linarith) (by linarith)
    linarith
  -- quotients by `D = 3 p - 2`
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = u / (3 * p - 2) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = lam / (3 * p - 2) := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = Real.log K / (3 * p - 2) := ⟨_, rfl⟩
  have hvD : v * (3 * p - 2) = u := by rw [hv]; exact div_mul_cancel₀ u hD.ne'
  have hwD : w * (3 * p - 2) = lam := by rw [hw]; exact div_mul_cancel₀ lam hD.ne'
  have hkD : k * (3 * p - 2) = Real.log K := by rw [hk]; exact div_mul_cancel₀ _ hD.ne'
  have hw0 : 0 ≤ w := by rw [hw]; exact div_nonneg hlam0 hD.le
  have hk0 : 0 ≤ k := by rw [hk]; exact div_nonneg hlogK0 hD.le
  -- exponential forms
  have hκ : sharpKappa p β = Real.exp (2 * k) := by
    unfold sharpKappa
    rw [← hKdef, Real.rpow_def_of_pos hKpos, hk]
    congr 1
    ring
  have hA : sharpMass p β δ = Real.exp (2 * k + 2 * p * v + 2 * β * w) := by
    unfold sharpMass
    rw [hκ, hℓ, Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hℓ_pos, ← Real.exp_add,
      ← Real.exp_add, ← hu, ← hlam, hv, hw]
    congr 1
    ring
  have hω : momentModulus p β δ = Real.exp ((p - 2) * v - 2 * β * w) := by
    unfold momentModulus
    rw [hℓ, Real.rpow_def_of_pos hδ0, Real.rpow_def_of_pos hℓ_pos, ← Real.exp_add,
      ← hu, ← hlam, hv, hw]
    congr 1
    ring
  have hApos : 0 < sharpMass p β δ := by rw [hA]; exact Real.exp_pos _
  have hsumD : (2 * k + 2 * p * v + 2 * β * w) * (3 * p - 2) =
      2 * Real.log K + 2 * p * u + 2 * β * lam := by
    linear_combination 2 * hkD + 2 * p * hvD + 2 * β * hwD
  refine ⟨hApos, ?_, ?_, ?_⟩
  · -- the mass is at most `1 / 6`
    have h6 : (1 / 6 : ℝ) = Real.exp (-Real.log 6) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [hA, h6]
    apply Real.exp_le_exp.mpr
    have hu2 : u ≤ -((3 * p - 2) / 2) * Real.log (6 * sharpKappa p β) := by
      have h1 := Real.log_le_log hδ0 (hδ.trans (min_le_right _ _))
      rw [Real.log_exp] at h1
      rw [hu]
      exact h1
    have hlog6κ : Real.log (6 * sharpKappa p β) = Real.log 6 + 2 * k := by
      rw [Real.log_mul (by norm_num) (sharpKappa_pos p β).ne', hκ, Real.log_exp]
    rw [hlog6κ] at hu2
    have hu3 : u ≤ -((3 * p - 2) / 2) * Real.log 6 - Real.log K := by
      have e : -((3 * p - 2) / 2) * (Real.log 6 + 2 * k) =
          -((3 * p - 2) / 2) * Real.log 6 - Real.log K := by
        linear_combination (-1 : ℝ) * hkD
      linarith
    have hpu : (p - 2) * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hu0
    apply le_of_mul_le_mul_right _ hD
    rw [hsumD]
    linarith
  · -- the lower bound is a multiple of the modulus
    rw [hA, hκ, hω, ← hδexp]
    have e1 : 2 * Real.exp u / Real.exp (2 * k + 2 * p * v + 2 * β * w) =
        2 * Real.exp (u - (2 * k + 2 * p * v + 2 * β * w)) := by
      rw [Real.exp_sub]
      ring
    have e2 : 2 / Real.exp (2 * k) * Real.exp ((p - 2) * v - 2 * β * w) =
        2 * Real.exp ((p - 2) * v - 2 * β * w - 2 * k) := by
      rw [Real.exp_sub ((p - 2) * v - 2 * β * w) (2 * k)]
      ring
    rw [e1, e2]
    congr 2
    linear_combination (-1 : ℝ) * hvD
  · -- the moment bound
    obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 2 * k + 2 * p * v + 2 * β * w := ⟨_, rfl⟩
    rw [← hAdef] at hA
    have h4 : Real.exp (Real.log 4) = 4 := Real.exp_log (by norm_num)
    have h3 : Real.exp (Real.log 3) = 3 := Real.exp_log (by norm_num)
    have h12log : Real.log 12 = Real.log 3 + Real.log 4 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have hR : sharpScale p β δ = Real.exp (Real.log 4 + u - 3 / 2 * A) := by
      have e1 : Real.exp (Real.log 4 + u - 3 / 2 * A) = 4 * δ / Real.exp (3 / 2 * A) := by
        rw [Real.exp_sub, Real.exp_add, h4, hδexp]
      have e2 : Real.exp A * Real.sqrt (Real.exp A) = Real.exp (3 / 2 * A) := by
        rw [← Real.exp_half, ← Real.exp_add]
        congr 1
        ring
      unfold sharpScale scaleOf
      rw [hA, e2, e1]
    have h3R : 3 * sharpScale p β δ = Real.exp (Real.log 12 + u - 3 / 2 * A) := by
      rw [hR, h12log]
      have e : Real.log 3 + Real.log 4 + u - 3 / 2 * A =
          Real.log 3 + (Real.log 4 + u - 3 / 2 * A) := by ring
      rw [e, Real.exp_add, h3]
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.log 12 + u - 3 / 2 * A := ⟨_, rfl⟩
    rw [← hr] at h3R
    rw [h3R, ← Real.exp_mul]
    -- the prefactor
    have hpre : 3 * sharpMass p β δ * Real.exp (r * p) =
        Real.exp (-(β * (Real.log 13 + lam))) := by
      rw [hA]
      nth_rewrite 1 [← h3]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hr, hAdef]
      linear_combination (-1 : ℝ) * hlogK - hkD - p * hvD - β * hwD
    -- the logarithm
    have hr_le : r ≤ 11 + (1 - u) / 2 := by
      have h12le : Real.log 12 ≤ 11 := by
        have h1 : (12 : ℝ) ≤ Real.exp 11 := by
          have := Real.add_one_le_exp (11 : ℝ)
          linarith
        exact (Real.log_le_log (by norm_num) h1).trans_eq (Real.log_exp 11)
      have hv2 : -2 * v ≤ -u / 2 := by
        apply le_of_mul_le_mul_right _ hD
        have e : -2 * v * (3 * p - 2) = -2 * u := by linear_combination (-2 : ℝ) * hvD
        rw [e]
        linarith [mul_nonneg (neg_nonneg.mpr hu0) (by linarith : (0 : ℝ) ≤ 3 * p - 2 - 4)]
      have e : r = Real.log 12 - 2 * v - 3 * k - 3 * (β * w) := by
        rw [hr, hAdef]
        linear_combination (-1 : ℝ) * hvD
      have hβw : 0 ≤ β * w := mul_nonneg hβ hw0
      rw [e]
      linarith
    have hsum_le : Real.exp 1 + Real.exp r ≤ Real.exp (12 + (1 - u) / 2) := by
      have h1 : Real.exp 1 ≤ Real.exp (11 + (1 - u) / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp r ≤ Real.exp (11 + (1 - u) / 2) := Real.exp_le_exp.mpr hr_le
      have h3' : Real.exp (12 + (1 - u) / 2) =
          Real.exp 1 * Real.exp (11 + (1 - u) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hpos : 0 < Real.exp (11 + (1 - u) / 2) := Real.exp_pos _
      have h5 : 2 * Real.exp (11 + (1 - u) / 2) ≤
          Real.exp 1 * Real.exp (11 + (1 - u) / 2) :=
        mul_le_mul_of_nonneg_right Real.exp_one_gt_two.le hpos.le
      rw [h3']
      linarith
    have hsum_pos : 1 ≤ Real.exp 1 + Real.exp r := by
      linarith [Real.exp_one_gt_two, Real.exp_pos r]
    have hlog0 : 0 ≤ Real.log (Real.exp 1 + Real.exp r) := Real.log_nonneg hsum_pos
    have hlog_le : Real.log (Real.exp 1 + Real.exp r) ≤ 13 * (1 - u) := by
      have h1 := Real.log_le_log (by linarith) hsum_le
      rw [Real.log_exp] at h1
      linarith
    have h13ℓ : 0 < 13 * (1 - u) := by linarith
    have hpow : Real.log (Real.exp 1 + Real.exp r) ^ β ≤
        Real.exp (β * (Real.log 13 + lam)) := by
      have h1 : Real.log (Real.exp 1 + Real.exp r) ^ β ≤ (13 * (1 - u)) ^ β :=
        Real.rpow_le_rpow hlog0 hlog_le hβ
      have h2 : (13 * (1 - u)) ^ β = Real.exp (β * (Real.log 13 + lam)) := by
        rw [Real.rpow_def_of_pos h13ℓ, Real.log_mul (by norm_num) hℓ_pos.ne', ← hlam]
        congr 1
        ring
      rw [h2] at h1
      exact h1
    calc 3 * sharpMass p β δ *
          (Real.exp (r * p) * Real.log (Real.exp 1 + Real.exp r) ^ β)
        = 3 * sharpMass p β δ * Real.exp (r * p) *
            Real.log (Real.exp 1 + Real.exp r) ^ β := by ring
      _ = Real.exp (-(β * (Real.log 13 + lam))) *
            Real.log (Real.exp 1 + Real.exp r) ^ β := by rw [hpre]
      _ ≤ Real.exp (-(β * (Real.log 13 + lam))) *
            Real.exp (β * (Real.log 13 + lam)) :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

end

end BrenierMoment
