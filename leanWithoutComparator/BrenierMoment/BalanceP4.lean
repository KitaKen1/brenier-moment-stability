module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace BrenierMoment

/-- The explicit substitution `δ = t^5`, `H = 1/t`, `h = t^4`
balances the two interpolation terms and the fourth-moment tail.
This scalar lemma is independent of the transport geometry. -/
theorem p4_balance_identity {t A B : ℝ} (ht : t ≠ 0) :
    A * (t ^ 5) ^ 2 / (t ^ 4) ^ 2 + B * (1 / t) ^ 2 * t ^ 4 +
      12 / (1 / t) ^ 2 = (A + B + 12) * t ^ 2 := by
  field_simp [ht]

theorem tenth_power_le_square {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t ^ 10 ≤ t ^ 2 := by
  calc
    t ^ 10 = t ^ 2 * t ^ 8 := by ring
    _ ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1) (sq_nonneg t)
    _ = t ^ 2 := mul_one _

/-- An interpolation estimate with a fourth-moment tail yields the `1/5`
rate after the explicit parameter substitution. The transport estimate itself
must be supplied separately. -/
theorem p4_bound_from_interpolation {E A B t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (h : E ^ 2 ≤ A * (t ^ 5) ^ 2 / (t ^ 4) ^ 2 +
      B * (1 / t) ^ 2 * t ^ 4 + 12 / (1 / t) ^ 2 + 16 * (t ^ 5) ^ 2) :
    E ^ 2 ≤ (A + B + 28) * t ^ 2 := by
  rw [p4_balance_identity ht0.ne'] at h
  have hp := tenth_power_le_square ht0.le ht1
  have he : (t ^ 5) ^ 2 = t ^ 10 := by ring
  rw [he] at h
  nlinarith

end BrenierMoment
