module

public import BrenierMoment.FourCellGeometry

@[expose] public section

/-!
# Slices of the four cells

On each transverse slice the explicit selector is constant on four consecutive
intervals. The endpoints are the three boundary functions, so every cell mass
is the integral of an affine function of the transverse coordinate.
-/

namespace BrenierMoment.FourAtom

theorem activeIndex_eq_zero_iff (a t s : ℝ) :
    activeIndex a t s = 0 ↔ t ≤ boundary01 a := by
  unfold activeIndex
  split_ifs with h0 h1 h2
  · exact ⟨fun _ => h0, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h0⟩

theorem activeIndex_eq_one_iff (a t s : ℝ) :
    activeIndex a t s = 1 ↔ boundary01 a < t ∧ t ≤ boundary12 a s := by
  unfold activeIndex
  split_ifs with h0 h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h0 (not_le.mpr h.1)⟩
  · exact ⟨fun _ => ⟨lt_of_not_ge h0, h1⟩, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 h1⟩

theorem activeIndex_eq_two_iff {a t s : ℝ} (h01 : boundary01 a ≤ boundary12 a s) :
    activeIndex a t s = 2 ↔ boundary12 a s < t ∧ t ≤ boundary23 a s := by
  unfold activeIndex
  split_ifs with h0 h1 h2
  · exact ⟨fun h => absurd h (by decide),
      fun h => absurd (h0.trans h01) (not_le.mpr h.1)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h1 (not_le.mpr h.1)⟩
  · exact ⟨fun _ => ⟨lt_of_not_ge h1, h2⟩, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 h2⟩

theorem activeIndex_eq_three_iff {a t s : ℝ} (h01 : boundary01 a ≤ boundary12 a s)
    (h12 : boundary12 a s ≤ boundary23 a s) :
    activeIndex a t s = 3 ↔ boundary23 a s < t := by
  unfold activeIndex
  split_ifs with h0 h1 h2
  · exact ⟨fun h => absurd h (by decide),
      fun h => absurd ((h0.trans h01).trans h12) (not_le.mpr h)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd (h1.trans h12) (not_le.mpr h)⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h2 (not_le.mpr h)⟩
  · exact ⟨fun _ => lt_of_not_ge h2, fun _ => rfl⟩

theorem activeIndex_le_one_iff {a t s : ℝ} (h01 : boundary01 a ≤ boundary12 a s) :
    (activeIndex a t s = 0 ∨ activeIndex a t s = 1) ↔ t ≤ boundary12 a s := by
  rw [activeIndex_eq_zero_iff, activeIndex_eq_one_iff]
  constructor
  · rintro (h | h)
    · exact h.trans h01
    · exact h.2
  · intro h
    by_cases h0 : t ≤ boundary01 a
    · exact Or.inl h0
    · exact Or.inr ⟨lt_of_not_ge h0, h⟩

/-- Between the two positions of the last boundary the selectors disagree. -/
theorem activeIndex_ne_of_between23 {a t s s' : ℝ}
    (h : boundary01 a ≤ boundary12 a s ∧ boundary12 a s ≤ boundary23 a s)
    (h' : boundary01 a ≤ boundary12 a s' ∧ boundary12 a s' ≤ boundary23 a s')
    (hlo : min (boundary23 a s) (boundary23 a s') < t)
    (hhi : t ≤ max (boundary23 a s) (boundary23 a s')) :
    activeIndex a t s ≠ activeIndex a t s' := by
  intro heq
  have e1 := activeIndex_eq_three_iff (t := t) h.1 h.2
  have e2 := activeIndex_eq_three_iff (t := t) h'.1 h'.2
  rw [heq] at e1
  have hiff : boundary23 a s < t ↔ boundary23 a s' < t := e1.symm.trans e2
  rcases min_lt_iff.mp hlo with h1 | h1
  · exact absurd hhi (not_le.mpr (max_lt h1 (hiff.mp h1)))
  · exact absurd hhi (not_le.mpr (max_lt (hiff.mpr h1) h1))

/-- Between the two positions of the middle boundary the selectors disagree. -/
theorem activeIndex_ne_of_between12 {a t s s' : ℝ}
    (h : boundary01 a ≤ boundary12 a s) (h' : boundary01 a ≤ boundary12 a s')
    (hlo : min (boundary12 a s) (boundary12 a s') < t)
    (hhi : t ≤ max (boundary12 a s) (boundary12 a s')) :
    activeIndex a t s ≠ activeIndex a t s' := by
  intro heq
  have e1 := activeIndex_le_one_iff (t := t) h
  have e2 := activeIndex_le_one_iff (t := t) h'
  rw [heq] at e1
  have hiff : t ≤ boundary12 a s ↔ t ≤ boundary12 a s' := e1.symm.trans e2
  rcases min_lt_iff.mp hlo with h1 | h1
  · have h2 : boundary12 a s' < t :=
      lt_of_not_ge fun hc => absurd (hiff.mpr hc) (not_le.mpr h1)
    exact absurd hhi (not_le.mpr (max_lt h1 h2))
  · have h2 : boundary12 a s < t :=
      lt_of_not_ge fun hc => absurd (hiff.mp hc) (not_le.mpr h1)
    exact absurd hhi (not_le.mpr (max_lt h2 h1))

/-! ### Slice lengths -/

lemma boundary12_sub_boundary01 (a s : ℝ) :
    boundary12 a s - boundary01 a = a + -(a / 4) * s := by
  unfold boundary12 boundary01
  ring

lemma boundary23_sub_boundary12 (a s : ℝ) :
    boundary23 a s - boundary12 a s = a + a / 2 * s := by
  unfold boundary23 boundary12
  ring

lemma one_sub_boundary23 (a s : ℝ) :
    1 - boundary23 a s = a + -(a / 4) * s := by
  unfold boundary23
  ring

lemma boundary_bounds {a s : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1)
    (hs0 : -1 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ boundary01 a ∧ boundary01 a ≤ boundary12 a s ∧
      boundary12 a s ≤ boundary23 a s ∧ boundary23 a s ≤ 1 := by
  obtain ⟨h1, h2⟩ := boundaries_ordered ha hs0 hs1
  refine ⟨?_, h1, h2, ?_⟩
  · unfold boundary01
    linarith
  · unfold boundary23
    nlinarith [mul_nonneg ha (by linarith : 0 ≤ 1 - s)]

lemma max_sub_min_boundary23 {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    max (boundary23 a s) (boundary23 a 0) - min (boundary23 a s) (boundary23 a 0) =
      a / 4 * |s| := by
  unfold boundary23
  rcases le_total 0 s with hs | hs
  · have h : 1 - a + a * 0 / 4 ≤ 1 - a + a * s / 4 := by nlinarith [mul_nonneg ha hs]
    rw [max_eq_left h, min_eq_right h, abs_of_nonneg hs]
    ring
  · have h : 1 - a + a * s / 4 ≤ 1 - a + a * 0 / 4 := by
      nlinarith [mul_nonneg ha (neg_nonneg.mpr hs)]
    rw [max_eq_right h, min_eq_left h, abs_of_nonpos hs]
    ring

lemma max_sub_min_boundary12 {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    max (boundary12 a s) (boundary12 a 0) - min (boundary12 a s) (boundary12 a 0) =
      a / 4 * |s| := by
  unfold boundary12
  rcases le_total 0 s with hs | hs
  · have h : 1 - 2 * a - a * s / 4 ≤ 1 - 2 * a - a * 0 / 4 := by
      nlinarith [mul_nonneg ha hs]
    rw [max_eq_right h, min_eq_left h, abs_of_nonneg hs]
    ring
  · have h : 1 - 2 * a - a * 0 / 4 ≤ 1 - 2 * a - a * s / 4 := by
      nlinarith [mul_nonneg ha (neg_nonneg.mpr hs)]
    rw [max_eq_left h, min_eq_right h, abs_of_nonpos hs]
    ring

end BrenierMoment.FourAtom
