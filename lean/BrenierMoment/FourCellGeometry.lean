module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

@[expose] public section

noncomputable section

/-!
# The four affine envelopes in scalar coordinates

These certificates identify the active planes without formalizing a general
polyhedral subdivision algorithm.
-/

namespace BrenierMoment.FourAtom

def basePlane (a t : ℝ) : Fin 4 → ℝ :=
  ![0, t - 1 + 3 * a, 2 * t - 2 + 5 * a, 3 * t - 3 + 6 * a]

def tiltedPlane (a t s : ℝ) : Fin 4 → ℝ :=
  ![0, t - 1 + 3 * a, 2 * t - 2 + 5 * a + a * s / 4,
    3 * t - 3 + 6 * a]

def IsActive (v : Fin 4 → ℝ) (i : Fin 4) : Prop := ∀ j, v j ≤ v i

def boundary01 (a : ℝ) : ℝ := 1 - 3 * a
def boundary12 (a s : ℝ) : ℝ := 1 - 2 * a - a * s / 4
def boundary23 (a s : ℝ) : ℝ := 1 - a + a * s / 4

lemma boundaries_ordered {a s : ℝ} (ha : 0 ≤ a) (hs0 : -1 ≤ s) (hs1 : s ≤ 1) :
    boundary01 a ≤ boundary12 a s ∧ boundary12 a s ≤ boundary23 a s := by
  unfold boundary01 boundary12 boundary23
  constructor <;> nlinarith [mul_nonneg ha (by linarith : 0 ≤ s + 1),
    mul_nonneg ha (by linarith : 0 ≤ 1 - s)]

lemma tilted_active_zero {a t s : ℝ} (ha : 0 ≤ a)
    (_hs0 : -1 ≤ s) (hs1 : s ≤ 1) (ht : t ≤ boundary01 a) :
    IsActive (tiltedPlane a t s) 0 := by
  intro j
  have hs : a * s ≤ a := by nlinarith
  unfold boundary01 at ht
  fin_cases j <;> simp [tiltedPlane] <;> linarith

lemma tilted_active_one {a t s : ℝ} (ha : 0 ≤ a)
    (hs0 : -1 ≤ s) (_hs1 : s ≤ 1)
    (ht0 : boundary01 a ≤ t) (ht1 : t ≤ boundary12 a s) :
    IsActive (tiltedPlane a t s) 1 := by
  intro j
  have hs : -a ≤ a * s := by nlinarith
  simp only [boundary01, boundary12] at ht0 ht1
  fin_cases j <;> simp [tiltedPlane] <;> linarith

lemma tilted_active_two {a t s : ℝ} (ha : 0 ≤ a)
    (hs0 : -1 ≤ s) (hs1 : s ≤ 1)
    (ht0 : boundary12 a s ≤ t) (ht1 : t ≤ boundary23 a s) :
    IsActive (tiltedPlane a t s) 2 := by
  intro j
  have hs : -a ≤ a * s := by nlinarith
  have hs' : a * s ≤ a := by nlinarith
  simp only [boundary12, boundary23] at ht0 ht1
  fin_cases j <;> simp [tiltedPlane] <;> linarith

lemma tilted_active_three {a t s : ℝ} (ha : 0 ≤ a)
    (hs0 : -1 ≤ s) (_hs1 : s ≤ 1) (ht : boundary23 a s ≤ t) :
    IsActive (tiltedPlane a t s) 3 := by
  intro j
  have hs : -a ≤ a * s := by nlinarith
  unfold boundary23 at ht
  fin_cases j <;> simp [tiltedPlane] <;> linarith

lemma tilted_active_iff_base (a t : ℝ) (i : Fin 4) :
    IsActive (tiltedPlane a t 0) i ↔ IsActive (basePlane a t) i := by
  simp [IsActive, tiltedPlane, basePlane]

def activeIndex (a t s : ℝ) : Fin 4 :=
  if t ≤ boundary01 a then 0 else
    if t ≤ boundary12 a s then 1 else
      if t ≤ boundary23 a s then 2 else 3

/-- The explicit selector is genuinely active on every transverse source slice. -/
theorem activeIndex_spec {a t s : ℝ} (ha : 0 ≤ a)
    (hs0 : -1 ≤ s) (hs1 : s ≤ 1) :
    IsActive (tiltedPlane a t s) (activeIndex a t s) := by
  unfold activeIndex
  split_ifs with h0 h1 h2
  · exact tilted_active_zero ha hs0 hs1 h0
  · exact tilted_active_one ha hs0 hs1 (le_of_lt (lt_of_not_ge h0)) h1
  · exact tilted_active_two ha hs0 hs1 (le_of_lt (lt_of_not_ge h1)) h2
  · exact tilted_active_three ha hs0 hs1 (le_of_lt (lt_of_not_ge h2))

lemma middle_width (a s : ℝ) :
    boundary23 a s - boundary12 a s = a + a * s / 2 := by
  unfold boundary23 boundary12
  ring

lemma middle_width_nonneg {a s : ℝ} (ha : 0 ≤ a) (hs : -1 ≤ s) :
    0 ≤ a + a * s / 2 := by
  nlinarith [mul_nonneg ha (by linarith : 0 ≤ s + 1)]

end BrenierMoment.FourAtom
