module

public import OAI.Analysis.Brenier.TransportCore
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Exact target distance for the four-atom moment-stability example

The second target changes only the transverse coordinate of the third atom.
The coordinate lower bound certifies the atomwise matching as optimal.
-/

namespace BrenierMoment.FourAtom

noncomputable section

open MeasureTheory
open OAI.Problem358
open scoped BigOperators ENNReal

def atoms (R b : ℝ) : Fin 4 → E 2 :=
  ![!₂[0, 0], !₂[R, 0], !₂[2 * R, b], !₂[3 * R, 0]]

def weights (a : ℝ) : Fin 4 → ℝ≥0∞ :=
  ![ENNReal.ofReal (1 - 3 * a), ENNReal.ofReal a,
    ENNReal.ofReal a, ENNReal.ofReal a]

def target (a R b : ℝ) : Measure (E 2) :=
  ∑ i, weights a i • Measure.dirac (atoms R b i)

def HasExactlyFourAtoms (μ : Measure (E 2)) : Prop :=
  ∃ y : Fin 4 → E 2, Function.Injective y ∧
    ∃ w : Fin 4 → ℝ≥0∞, (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧ μ = ∑ i, w i • Measure.dirac (y i)

lemma weights_sum {a : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    ∑ i, weights a i = 1 := by
  have hw : 0 ≤ 1 - 3 * a := by linarith
  rw [Fin.sum_univ_four]
  change ENNReal.ofReal (1 - 3 * a) + ENNReal.ofReal a +
    ENNReal.ofReal a + ENNReal.ofReal a = 1
  rw [← ENNReal.ofReal_add hw ha,
    ← ENNReal.ofReal_add (add_nonneg hw ha) ha,
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg hw ha) ha) ha]
  have hs : 1 - 3 * a + a + a + a = 1 := by ring
  rw [hs, ENNReal.ofReal_one]

lemma weights_pos {a : ℝ} (ha : 0 < a) (ha3 : 3 * a < 1) (i : Fin 4) :
    0 < weights a i := by
  fin_cases i <;> simp [weights, ENNReal.ofReal_pos] <;> linarith

lemma atoms_injective {R b : ℝ} (hR : 0 < R) : Function.Injective (atoms R b) := by
  intro i j h
  have hx := congrArg (fun x : E 2 => x 0) h
  fin_cases i <;> fin_cases j <;> simp [atoms] at hx ⊢ <;> linarith

lemma target_isProbabilityMeasure {a : ℝ} (R b : ℝ)
    (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) : IsProbabilityMeasure (target a R b) := by
  exact finite_atomic_probability (atoms R b) (weights a) (weights_sum ha ha3)

theorem target_hasExactlyFourAtoms {a R : ℝ} (b : ℝ)
    (ha : 0 < a) (ha3 : 3 * a < 1) (hR : 0 < R) :
    HasExactlyFourAtoms (target a R b) := by
  exact ⟨atoms R b, atoms_injective hR, weights a, weights_pos ha ha3,
    weights_sum ha.le ha3.le, rfl⟩

lemma target_ae_second_zero (a R : ℝ) :
    ∀ᵐ x ∂target a R 0, x 1 = 0 := by
  unfold target
  rw [ae_finsetSum_measure_iff]
  intro i hi
  apply Measure.ae_smul_measure
  have hx : atoms R 0 i 1 = 0 := by fin_cases i <;> simp [atoms]
  simpa using hx

lemma target_second_moment (a R b : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((x 1) ^ 2) ∂target a R b) =
      ENNReal.ofReal a * ENNReal.ofReal (b ^ 2) := by
  simp [target, weights, atoms, Fin.sum_univ_succ, lintegral_smul_measure]

lemma matching_cost (a R b : ℝ) :
    quadraticPlanCost (atomicMatchingPlan (weights a) (atoms R 0) (atoms R b)) =
      ENNReal.ofReal a * ENNReal.ofReal (b ^ 2) := by
  rw [quadraticPlanCost_atomicMatchingPlan]
  simp [weights, atoms, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq]

lemma toReal_weighted_three {a x y z : ℝ}
    (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (ENNReal.ofReal a * ENNReal.ofReal x + ENNReal.ofReal a * ENNReal.ofReal y +
      ENNReal.ofReal a * ENNReal.ofReal z).toReal = a * (x + y + z) := by
  rw [← mul_add, ← mul_add, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_ofReal hx, ENNReal.toReal_ofReal hy, ENNReal.toReal_ofReal hz]

/-- The actual quadratic moment of the four-atom target. -/
theorem second_moment_exact {a : ℝ} (R b : ℝ) (ha : 0 ≤ a) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂target a R b).toReal =
      a * (14 * R ^ 2 + b ^ 2) := by
  simp [target, weights, atoms, Fin.sum_univ_succ, EuclideanSpace.real_norm_sq_eq,
    lintegral_smul_measure]
  rw [← add_assoc, toReal_weighted_three ha (by positivity) (by positivity) (by positivity)]
  ring

/-- The fourth moment is an explicit polynomial, so the pure fourth-moment
constraint can be checked without asymptotic or real-power lemmas. -/
theorem fourth_moment_exact {a : ℝ} (R b : ℝ) (ha : 0 ≤ a) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 4) ∂target a R b).toReal =
      a * (98 * R ^ 4 + 8 * R ^ 2 * b ^ 2 + b ^ 4) := by
  have hn : ∀ x : E 2, ‖x‖ ^ 4 = (∑ i, (x i) ^ 2) ^ 2 := by
    intro x
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, EuclideanSpace.real_norm_sq_eq]
  simp [target, weights, atoms, hn, Fin.sum_univ_succ, lintegral_smul_measure]
  rw [← add_assoc, toReal_weighted_three ha (by positivity) (by positivity) (by positivity)]
  ring

theorem fourth_moment_le {a R b : ℝ} (ha : 0 ≤ a) (hb : b ^ 2 ≤ R ^ 2) :
    (∫⁻ x, ENNReal.ofReal (‖x‖ ^ 4) ∂target a R b).toReal ≤ 107 * a * R ^ 4 := by
  have hb4 : b ^ 4 ≤ R ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (add_nonneg (sq_nonneg R) (sq_nonneg b))]
  have hcross : 8 * R ^ 2 * b ^ 2 ≤ 8 * R ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg R) (sub_nonneg.mpr hb)]
  calc
    _ = a * (98 * R ^ 4 + 8 * R ^ 2 * b ^ 2 + b ^ 4) := fourth_moment_exact R b ha
    _ ≤ a * (107 * R ^ 4) := mul_le_mul_of_nonneg_left (by linarith) ha
    _ = 107 * a * R ^ 4 := by ring

/-- An exact Wasserstein formula, certified against all measure-valued couplings. -/
theorem wasserstein2_exact {a : ℝ} (R b : ℝ)
    (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    wasserstein2 (target a R 0) (target a R b) = Real.sqrt (a * b ^ 2) := by
  have hπ : IsCoupling (target a R 0) (target a R b)
      (atomicMatchingPlan (weights a) (atoms R 0) (atoms R b)) :=
    atomicMatchingPlan_isCoupling _ _ _ (weights_sum ha ha3)
  have hc : quadraticPlanCost (atomicMatchingPlan (weights a) (atoms R 0) (atoms R b)) =
      ∫⁻ x, ENNReal.ofReal ((x 1) ^ 2) ∂target a R b := by
    rw [matching_cost, target_second_moment]
  rw [wasserstein2_eq_sqrt_coordinate_moment (1 : Fin 2)
    (target_ae_second_zero a R) hπ hc, target_second_moment,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal (sq_nonneg b)]

theorem wasserstein2_sq_exact {a : ℝ} (R b : ℝ)
    (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    wasserstein2 (target a R 0) (target a R b) ^ 2 = a * b ^ 2 := by
  rw [wasserstein2_exact R b ha ha3, Real.sq_sqrt (mul_nonneg ha (sq_nonneg b))]

theorem wasserstein2_sq_tilt {a : ℝ} (R : ℝ)
    (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    wasserstein2 (target a R 0) (target a R (R * a / 4)) ^ 2 = R ^ 2 * a ^ 3 / 16 := by
  rw [wasserstein2_sq_exact R (R * a / 4) ha ha3]
  ring

end

end BrenierMoment.FourAtom
