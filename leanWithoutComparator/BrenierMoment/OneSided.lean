module

public import BrenierMoment.Threshold

@[expose] public section

/-!
# From the two-sided interpolation estimate to the one-sided rate

The interpolation estimate carries the quadratic tails of both targets. The
tail of the second target at level `2 H` is bounded by the transport cost and
the tail of the first target at level `H`, so only the first target needs a
moment bound. This file contains the scalar bookkeeping; the tail functions
enter as abstract real functions of the threshold.
-/

namespace BrenierMoment

noncomputable section

/-- The interpolation estimate at threshold `2 H`, the tail transfer and the
moment envelope give the family of bounds required by `rate_of_threshold_family`. -/
theorem one_sided_family {Err δ A p β : ℝ} {τμ τν : ℝ → ℝ}
    (hinterp : ∀ H : ℝ, 0 < H →
      Err ^ 2 ≤ A * (δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) + 3 * (τμ H + τν H))
    (hmono : ∀ H : ℝ, 0 < H → τμ (2 * H) ≤ τμ H)
    (htransfer : ∀ H : ℝ, 0 < H → τν (2 * H) ≤ 4 * δ ^ 2 + 2 * τμ H)
    (henv : ∀ H : ℝ, 0 < H → τμ H ≤ tailEnvelope p β H) :
    ∀ H : ℝ, 0 < H →
      Err ^ 2 ≤ A * (2 : ℝ) ^ (4 / 3 : ℝ) * (δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) +
        12 * tailEnvelope p β H + 16 * δ ^ 2 := by
  intro H hH
  have h2H : 0 < 2 * H := by positivity
  have h1 := hinterp (2 * H) h2H
  have hpow : (2 * H) ^ (4 / 3 : ℝ) = (2 : ℝ) ^ (4 / 3 : ℝ) * H ^ (4 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) hH.le
  rw [hpow] at h1
  have h2 := hmono H hH
  have h3 := htransfer H hH
  have h4 := henv H hH
  have h5 : 0 ≤ tailEnvelope p β H := tailEnvelope_nonneg p β hH.le
  have h6 : 0 ≤ δ ^ 2 := sq_nonneg δ
  have e : A * (δ ^ (2 / 3 : ℝ) * ((2 : ℝ) ^ (4 / 3 : ℝ) * H ^ (4 / 3 : ℝ))) =
      A * (2 : ℝ) ^ (4 / 3 : ℝ) * (δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) := by ring
  rw [e] at h1
  linarith

/-- The scalar end of the proof: an interpolation estimate with both tails,
the tail transfer and a power-logarithmic moment bound on the first target
give the rate, with an explicit constant, for all sufficiently small distances. -/
theorem rate_of_interpolation {p β A Err δ : ℝ} {τμ τν : ℝ → ℝ}
    (hp : 2 ≤ p) (hβ : 0 ≤ β) (hA : 0 ≤ A) (hErr : 0 ≤ Err)
    (hδ0 : 0 < δ) (hδ : δ ≤ smallDistance β)
    (hinterp : ∀ H : ℝ, 0 < H →
      Err ^ 2 ≤ A * (δ ^ (2 / 3 : ℝ) * H ^ (4 / 3 : ℝ)) + 3 * (τμ H + τν H))
    (hmono : ∀ H : ℝ, 0 < H → τμ (2 * H) ≤ τμ H)
    (htransfer : ∀ H : ℝ, 0 < H → τν (2 * H) ≤ 4 * δ ^ 2 + 2 * τμ H)
    (henv : ∀ H : ℝ, 0 < H → τμ H ≤ tailEnvelope p β H) :
    Err ≤ Real.sqrt (A * (2 : ℝ) ^ (4 / 3 : ℝ) + 12 * (3 * p - 2) ^ β + 16) *
      momentModulus p β δ :=
  rate_of_threshold_family hp hβ (mul_nonneg hA (Real.rpow_nonneg (by norm_num) _)) hErr hδ0 hδ
    (one_sided_family hinterp hmono htransfer henv)

end

end BrenierMoment
