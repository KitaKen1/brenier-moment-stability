module

public import BrenierMoment.FourAtomSharp
public import BrenierMoment.SharpRate

@[expose] public section

/-!
# Sharpness of the moment rate

On the fixed source `[0,1] × [-1,1]^(d-1)`, for every sufficiently small `δ`
there are two four-atom targets at distance exactly `δ`, both with
power-logarithmic moment at most one, whose optimal maps differ by a fixed
multiple of the modulus. At `p = 2`, `β = 0` the map error stays above `1 / 20`
while the target distance tends to zero.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

namespace Sharp

/-- The coordinate carrying the slopes. -/
def axis0 (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨0, by omega⟩

/-- The transverse coordinate carrying the tilt. -/
def axis1 (d : ℕ) (hd : 2 ≤ d) : Fin d := ⟨1, by omega⟩

lemma axis_ne (d : ℕ) (hd : 2 ≤ d) : axis0 d hd ≠ axis1 d hd := by
  intro h
  have h1 := congrArg Fin.val h
  simp [axis0, axis1] at h1

end Sharp

/-- The fixed source of the sharpness statements: uniform on `[0,1] × [-1,1]^(d-1)`. -/
def sharpSource (d : ℕ) (hd : 2 ≤ d) : Measure (E d) :=
  uniformMeasure (Sharp.sourceBox (Sharp.axis0 d hd))

/-- **Sharpness.** For `2 ≤ p` and `0 ≤ β` the modulus cannot be improved on the
fixed box source, already for four-atom targets at every small distance. -/
theorem moment_rate_sharp (d : ℕ) (hd : 2 ≤ d) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (E d)) (Tμ Tν : E d → E d),
        Sharp.HasFourAtoms μ ∧ Sharp.HasFourAtoms ν ∧
        (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ) ≤ 1 ∧
        (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂ν) ≤ 1 ∧
        IsUniqueQuadraticOptimalMap (sharpSource d hd) μ Tμ ∧
        IsUniqueQuadraticOptimalMap (sharpSource d hd) ν Tν ∧
        wasserstein2 μ ν = δ ∧
        c * momentModulus p β δ ≤ mapL2Dist (sharpSource d hd) Tμ Tν := by
  refine ⟨2 / sharpKappa p β, div_pos (by norm_num) (sharpKappa_pos p β),
    sharpDistance p β, sharpDistance_pos p β, ?_⟩
  intro δ hδ0 hδ
  obtain ⟨ha0, ha6, hlow, hmom⟩ := sharp_parameters hp hβ hδ0 hδ
  obtain ⟨a, haDef⟩ : ∃ a : ℝ, a = sharpMass p β δ := ⟨_, rfl⟩
  obtain ⟨R, hRDef⟩ : ∃ R : ℝ, R = scaleOf a δ := ⟨_, rfl⟩
  have hRsharp : sharpScale p β δ = R := by rw [hRDef, haDef]; rfl
  rw [hRsharp, ← haDef] at hmom
  rw [← haDef] at ha0 ha6 hlow
  have ha3 : 3 * a ≤ 1 := by linarith
  have ha3' : 3 * a < 1 := by linarith
  have hR : 0 < R := by rw [hRDef]; exact scaleOf_pos ha0 hδ0
  have hij := Sharp.axis_ne d hd
  have hb0 : |Sharp.tilt a R 0| ≤ R := by
    rw [Sharp.tilt_zero, abs_zero]
    exact hR.le
  have hb1 : |Sharp.tilt a R 1| ≤ R := by
    rw [Sharp.tilt_one, abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hR.le (by linarith : (0 : ℝ) ≤ 1 - a / 4)]
  refine ⟨Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R (Sharp.tilt a R 0),
    Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R (Sharp.tilt a R 1),
    Sharp.cellMap (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R 0,
    Sharp.cellMap (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Sharp.target_hasFourAtoms hij _ ha0 ha3' hR
  · exact Sharp.target_hasFourAtoms hij _ ha0 ha3' hR
  · exact (Sharp.lintegral_momentWeight_target_le _ _ ha0.le hR.le hb0 (by linarith) hβ).trans
      (ENNReal.ofReal_le_one.mpr hmom)
  · exact (Sharp.lintegral_momentWeight_target_le _ _ ha0.le hR.le hb1 (by linarith) hβ).trans
      (ENNReal.ofReal_le_one.mpr hmom)
  · exact Sharp.isUniqueOptimal_cellMap hij ha0.le ha3 hR (by norm_num)
  · exact Sharp.isUniqueOptimal_cellMap hij ha0.le ha3 hR (by norm_num)
  · rw [Sharp.tilt_zero, Sharp.wasserstein2_target hij R _ ha0.le ha3, Sharp.tilt_one, hRDef]
    exact sqrt_mass_tilt_sq ha0 hδ0.le
  · calc 2 / sharpKappa p β * momentModulus p β δ = 2 * δ / a := hlow.symm
      _ = R * Real.sqrt a / 2 := by rw [hRDef, scaleOf_mul_sqrt_half ha0]
      _ ≤ mapL2Dist (sharpSource d hd)
            (Sharp.cellMap (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R 0)
            (Sharp.cellMap (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R 1) :=
          Sharp.mapError_lower hij ha0.le ha3

lemma momentWeight_two_zero {F : Type*} [NormedAddCommGroup F] (y : F) :
    momentWeight 2 0 y = ‖y‖ ^ 2 := by
  unfold momentWeight
  rw [Real.rpow_two, Real.rpow_zero, mul_one]

/-- **The endpoint.** A second-moment bound alone gives no vanishing modulus:
the target distance can be made arbitrarily small while the map error stays
at least `1 / 20`. -/
theorem no_modulus_at_second_moment (d : ℕ) (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ ν : Measure (E d)) (Tμ Tν : E d → E d),
      Sharp.HasFourAtoms μ ∧ Sharp.HasFourAtoms ν ∧
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ) ≤ 1 ∧
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂ν) ≤ 1 ∧
      IsUniqueQuadraticOptimalMap (sharpSource d hd) μ Tμ ∧
      IsUniqueQuadraticOptimalMap (sharpSource d hd) ν Tν ∧
      0 < wasserstein2 μ ν ∧ wasserstein2 μ ν < ε ∧
      1 / 20 ≤ mapL2Dist (sharpSource d hd) Tμ Tν := by
  obtain ⟨a, haDef⟩ : ∃ a : ℝ, a = min (1 / 6) (20 * ε) := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [haDef]
    exact lt_min (by norm_num) (by linarith)
  have ha6 : a ≤ 1 / 6 := by rw [haDef]; exact min_le_left _ _
  have haε : a ≤ 20 * ε := by rw [haDef]; exact min_le_right _ _
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha0
  have hss : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  obtain ⟨R, hRDef⟩ : ∃ R : ℝ, R = 1 / (10 * Real.sqrt a) := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRDef]; positivity
  have hRs : R * Real.sqrt a = 1 / 10 := by
    rw [hRDef, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one]
    norm_num
  have hRa : R ^ 2 * a = 1 / 100 := by
    have e : R ^ 2 * a = (R * Real.sqrt a) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha0.le]
    rw [e, hRs]
    norm_num
  have ha3 : 3 * a ≤ 1 := by linarith
  have ha3' : 3 * a < 1 := by linarith
  have hij := Sharp.axis_ne d hd
  have hb0 : |Sharp.tilt a R 0| ≤ R := by
    rw [Sharp.tilt_zero, abs_zero]
    exact hR.le
  have hb1 : |Sharp.tilt a R 1| ≤ R := by
    rw [Sharp.tilt_one, abs_of_nonneg (by positivity)]
    nlinarith [mul_nonneg hR.le (by linarith : (0 : ℝ) ≤ 1 - a / 4)]
  have hmom : 3 * a * ((3 * R) ^ (2 : ℝ) * Real.log (Real.exp 1 + 3 * R) ^ (0 : ℝ)) ≤ 1 := by
    rw [Real.rpow_two, Real.rpow_zero, mul_one]
    nlinarith
  have hmoment : ∀ b : ℝ, |b| ≤ R →
      (∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2)
        ∂Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R b) ≤ 1 := by
    intro b hb
    have h := (Sharp.lintegral_momentWeight_target_le (Sharp.axis0 d hd) (Sharp.axis1 d hd)
      (p := 2) (β := 0) ha0.le hR.le hb (by norm_num) le_rfl).trans
      (ENNReal.ofReal_le_one.mpr hmom)
    simpa only [momentWeight_two_zero] using h
  have hW : wasserstein2
      (Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R (Sharp.tilt a R 0))
      (Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R (Sharp.tilt a R 1)) = a / 40 := by
    rw [Sharp.tilt_zero, Sharp.wasserstein2_target hij R _ ha0.le ha3, Sharp.tilt_one]
    have e : a * (R * a / 4) ^ 2 = (a / 40) ^ 2 := by
      have e1 : a * (R * a / 4) ^ 2 = (R ^ 2 * a) * (a / 4) ^ 2 := by ring
      rw [e1, hRa]
      ring
    rw [e, Real.sqrt_sq (by positivity)]
  refine ⟨Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R (Sharp.tilt a R 0),
    Sharp.target (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R (Sharp.tilt a R 1),
    Sharp.cellMap (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R 0,
    Sharp.cellMap (Sharp.axis0 d hd) (Sharp.axis1 d hd) a R 1,
    Sharp.target_hasFourAtoms hij _ ha0 ha3' hR, Sharp.target_hasFourAtoms hij _ ha0 ha3' hR,
    hmoment _ hb0, hmoment _ hb1,
    Sharp.isUniqueOptimal_cellMap hij ha0.le ha3 hR (by norm_num),
    Sharp.isUniqueOptimal_cellMap hij ha0.le ha3 hR (by norm_num), ?_, ?_, ?_⟩
  · rw [hW]
    positivity
  · rw [hW]
    linarith
  · have h := Sharp.mapError_lower (R := R) hij ha0.le ha3
    have e : R * Real.sqrt a / 2 = 1 / 20 := by
      rw [hRs]
      norm_num
    rw [e] at h
    exact h

end

end BrenierMoment
