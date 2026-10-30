module

public import BrenierMoment.PotentialBound
public import OAI.Analysis.Brenier.Argmax
public import OAI.Analysis.Brenier.CompactMeasure

@[expose] public section

/-!
# The atomic potential estimate passes to total-variation limits of sources

Let probability sources `ρN N` on a common ball converge to an absolutely
continuous source `ρ` in total variation. If every `ρN N` satisfies the atomic
potential estimate with the constant `P`, so does `ρ`.

The intercepts in the estimate are not unique: an index whose site is shared
with another index may carry an arbitrarily low intercept, and both potentials
may be shifted by a common constant. Replacing every intercept by the largest
one on its site and shifting the largest to zero gives witnesses bounded in
terms of the radius, the sites and the constant only. A subsequence of
intercepts therefore converges. Off the tie hyperplanes of the limit
configuration the active sites are eventually constant, which identifies the
push-forward of the limit map, and the potentials converge uniformly, which
passes the `L²` bound.
-/

namespace BrenierMoment

open MeasureTheory Filter OAI.Problem358
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

section FiberMax

variable {ι F : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The largest intercept among the indices sharing the site of `i`. -/
def fiberMax (y : ι → F) (a : ι → ℝ) (i : ι) : ℝ := sSup (a '' {j | y j = y i})

omit [Nonempty ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma fiberMax_finite (y : ι → F) (a : ι → ℝ) (i : ι) : (a '' {j | y j = y i}).Finite :=
  (Set.toFinite _).image a

omit [Nonempty ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma le_fiberMax (y : ι → F) (a : ι → ℝ) (i : ι) : a i ≤ fiberMax y a i :=
  le_csSup (fiberMax_finite y a i).bddAbove ⟨i, rfl, rfl⟩

omit [Fintype ι] [Nonempty ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma fiberMax_congr (y : ι → F) (a : ι → ℝ) {i j : ι} (h : y i = y j) :
    fiberMax y a i = fiberMax y a j := by
  unfold fiberMax
  rw [h]

omit [Nonempty ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
lemma exists_fiberMax_eq (y : ι → F) (a : ι → ℝ) (i : ι) :
    ∃ j, y j = y i ∧ fiberMax y a i = a j := by
  have hne : (a '' {j | y j = y i}).Nonempty := ⟨a i, i, rfl, rfl⟩
  obtain ⟨j, hj, hja⟩ := hne.csSup_mem (fiberMax_finite y a i)
  exact ⟨j, hj, hja.symm⟩

omit [Nonempty ι] in
lemma maximizes_fiberMax {y : ι → F} {a : ι → ℝ} {x : F} {i : ι}
    (h : FiniteAffine.Maximizes y a x i) : FiniteAffine.Maximizes y (fiberMax y a) x i := by
  intro j
  obtain ⟨j', hj', hfm⟩ := exists_fiberMax_eq y a j
  have h1 := h j'
  have h2 := le_fiberMax y a i
  rw [hfm, ← hj']
  linarith

omit [Fintype ι] [Nonempty ι] in
lemma maximizes_fiberMax_of_site_eq {y : ι → F} {a : ι → ℝ} {x : F} {i j : ι}
    (h : FiniteAffine.Maximizes y (fiberMax y a) x i) (hij : y j = y i) :
    FiniteAffine.Maximizes y (fiberMax y a) x j := by
  intro k
  have h1 := h k
  rw [hij, fiberMax_congr y a hij]
  exact h1

lemma potential_fiberMax (y : ι → F) (a : ι → ℝ) (x : F) :
    FiniteAffine.potential y (fiberMax y a) x = FiniteAffine.potential y a x := by
  apply le_antisymm
  · apply FiniteAffine.potential_le_of_affine_le
    intro j
    obtain ⟨j', hj', hfm⟩ := exists_fiberMax_eq y a j
    rw [hfm, ← hj']
    exact FiniteAffine.affine_le_potential y a x j'
  · apply FiniteAffine.potential_le_of_affine_le
    intro j
    have h1 := FiniteAffine.affine_le_potential y (fiberMax y a) x j
    have h2 := le_fiberMax y a j
    linarith

omit [Fintype ι] [Nonempty ι] in
lemma maximizes_sub_const {y : ι → F} {a : ι → ℝ} {x : F} {i : ι} (c : ℝ)
    (h : FiniteAffine.Maximizes y a x i) :
    FiniteAffine.Maximizes y (fun j => a j - c) x i := by
  intro j
  have h1 := h j
  change ⟪x, y j⟫ + (a j - c) ≤ ⟪x, y i⟫ + (a i - c)
  linarith

lemma potential_sub_const (y : ι → F) (a : ι → ℝ) (c : ℝ) (x : F) :
    FiniteAffine.potential y (fun j => a j - c) x = FiniteAffine.potential y a x - c := by
  have h := FiniteAffine.potential_add_const y a (-c) x
  simpa only [sub_eq_add_neg] using h

lemma abs_inner_le_mul {x : F} (y : F) {R : ℝ} (hx : ‖x‖ ≤ R) : |⟪x, y⟫| ≤ R * ‖y‖ :=
  (abs_real_inner_le_norm x y).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg y))

lemma potential_le_of_bounds (y : ι → F) (a : ι → ℝ) {x : F} {R L B : ℝ}
    (hx : ‖x‖ ≤ R) (hy : ∀ i, R * ‖y i‖ ≤ L) (ha : ∀ i, a i ≤ B) :
    FiniteAffine.potential y a x ≤ L + B := by
  apply FiniteAffine.potential_le_of_affine_le
  intro i
  have h1 := (le_abs_self _).trans (abs_inner_le_mul (y i) hx)
  linarith [hy i, ha i]

lemma le_potential_of_bounds (y : ι → F) (a : ι → ℝ) {x : F} {R L : ℝ}
    (hx : ‖x‖ ≤ R) (hy : ∀ i, R * ‖y i‖ ≤ L) (i : ι) :
    a i - L ≤ FiniteAffine.potential y a x := by
  have h1 := FiniteAffine.affine_le_potential y a x i
  have h2 : -(R * ‖y i‖) ≤ ⟪x, y i⟫ :=
    (neg_le_neg (abs_inner_le_mul (y i) hx)).trans (neg_abs_le _)
  linarith [hy i]

/-- The finite potential is nonexpansive in the intercepts. -/
lemma potential_le_add_sum_abs (y : ι → F) (a a' : ι → ℝ) (x : F) :
    FiniteAffine.potential y a x ≤ FiniteAffine.potential y a' x + ∑ i, |a i - a' i| := by
  apply FiniteAffine.potential_le_of_affine_le
  intro i
  have h1 := FiniteAffine.affine_le_potential y a' x i
  have h2 : |a i - a' i| ≤ ∑ j, |a j - a' j| :=
    Finset.single_le_sum (f := fun j => |a j - a' j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h3 := le_abs_self (a i - a' i)
  linarith

lemma abs_potential_sub_le_sum_abs (y : ι → F) (a a' : ι → ℝ) (x : F) :
    |FiniteAffine.potential y a x - FiniteAffine.potential y a' x| ≤ ∑ i, |a i - a' i| := by
  have h1 := potential_le_add_sum_abs y a a' x
  have h2 := potential_le_add_sum_abs y a' a x
  have h3 : ∑ i, |a' i - a i| = ∑ i, |a i - a' i| :=
    Finset.sum_congr rfl fun i _ => abs_sub_comm _ _
  rw [h3] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end FiberMax

variable {d n : ℕ}

/-- The data produced by the atomic potential estimate. -/
@[reducible] def IsPotentialWitness (ρ : Measure (E d)) (P : ℝ) (m : Fin (n + 1) → ℝ)
    (y z : Fin (n + 1) → E d) (a b : Fin (n + 1) → ℝ) (T S : E d → E d) : Prop :=
  Measurable T ∧ Measurable S ∧
    (∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i) ∧
    (∀ x, ∃ i, S x = z i ∧ FiniteAffine.Maximizes z b x i) ∧
    Measure.map T ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
    Measure.map S ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (z i) ∧
    (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 ∂ρ) ≤
      P ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2

lemma atomicPotentialBound_iff (ρ : Measure (E d)) (P : ℝ) :
    AtomicPotentialBound ρ P ↔
      ∀ (n : ℕ) (m : Fin (n + 1) → ℝ) (y z : Fin (n + 1) → E d),
        (∀ i, 0 < m i) → (∑ i, m i) = 1 →
        (∀ t : ℝ, 0 < t → t < 1 →
          Function.Injective (fun i => (1 - t) • y i + t • z i)) →
        ∃ (a b : Fin (n + 1) → ℝ) (T S : E d → E d), IsPotentialWitness ρ P m y z a b T S :=
  Iff.rfl

/-- A site of positive mass is selected at some point of the ball carrying the source. -/
lemma exists_active_point {ρ : Measure (E d)} {R : ℝ} (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    {m : Fin (n + 1) → ℝ} (hm : ∀ i, 0 < m i) {y : Fin (n + 1) → E d}
    {a : Fin (n + 1) → ℝ} {T : E d → E d} (hT : Measurable T)
    (hact : ∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i)
    (hpush : Measure.map T ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i))
    (i : Fin (n + 1)) :
    ∃ x, ‖x‖ ≤ R ∧ ∃ i', y i' = y i ∧ FiniteAffine.Maximizes y a x i' := by
  have hpos : 0 < (Measure.map T ρ) {y i} := by
    rw [hpush, Measure.finsetSum_apply]
    have hterm : 0 < (ENNReal.ofReal (m i) • Measure.dirac (y i)) {y i} := by
      rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton _), smul_eq_mul,
        mul_one]
      exact ENNReal.ofReal_pos.mpr (hm i)
    exact lt_of_lt_of_le hterm
      (Finset.single_le_sum
        (f := fun j => (ENNReal.ofReal (m j) • Measure.dirac (y j)) {y i})
        (fun _ _ => by simp) (Finset.mem_univ i))
  rw [Measure.map_apply hT (measurableSet_singleton _)] at hpos
  have hex : ∃ x, T x = y i ∧ ‖x‖ ≤ R := by
    by_contra hc
    have hsub : T ⁻¹' {y i} ⊆ {x | ¬ ‖x‖ ≤ R} := by
      intro x hx hxR
      exact hc ⟨x, hx, hxR⟩
    have hzero : ρ (T ⁻¹' {y i}) = 0 := measure_mono_null hsub (ae_iff.mp hρ)
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨x, hTx, hxR⟩ := hex
  obtain ⟨i', hi', hmax⟩ := hact x
  exact ⟨x, hxR, i', by rw [← hi', hTx], hmax⟩

/-- The uniform bound on normalized intercepts. -/
def witnessBound (R P : ℝ) (m : Fin (n + 1) → ℝ) (y z : Fin (n + 1) → E d) : ℝ :=
  3 * (R * ∑ i, ‖y i‖) + 3 * (R * ∑ i, ‖z i‖) +
    Real.sqrt (P ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2)

/-- **Bounded witnesses.** For a probability source carried by the ball of
radius `R`, the intercepts in the atomic potential estimate can be chosen
bounded by `witnessBound R P m y z`, with the same maps. -/
theorem IsPotentialWitness.exists_bounded {ρ : Measure (E d)} [IsProbabilityMeasure ρ]
    {P R : ℝ} {m : Fin (n + 1) → ℝ} {y z : Fin (n + 1) → E d} {a b : Fin (n + 1) → ℝ}
    {T S : E d → E d} (hR : 0 ≤ R) (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) (hm : ∀ i, 0 < m i)
    (h : IsPotentialWitness ρ P m y z a b T S) :
    ∃ a' b' : Fin (n + 1) → ℝ, IsPotentialWitness ρ P m y z a' b' T S ∧
      (∀ i, |a' i| ≤ witnessBound R P m y z) ∧ (∀ i, |b' i| ≤ witnessBound R P m y z) := by
  obtain ⟨hTm, hSm, hTact, hSact, hTpush, hSpush, hL2⟩ := h
  -- constants
  obtain ⟨Ly, hLy⟩ : ∃ Ly : ℝ, Ly = R * ∑ i, ‖y i‖ := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : ℝ, Lz = R * ∑ i, ‖z i‖ := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑ i, m i * ‖y i - z i‖ ^ 2 := ⟨_, rfl⟩
  have hyL : ∀ i, R * ‖y i‖ ≤ Ly := by
    intro i
    rw [hLy]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => ‖y j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)) hR
  have hzL : ∀ i, R * ‖z i‖ ≤ Lz := by
    intro i
    rw [hLz]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => ‖z j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)) hR
  have hLy0 : 0 ≤ Ly := by
    rw [hLy]
    exact mul_nonneg hR (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hLz0 : 0 ≤ Lz := by
    rw [hLz]
    exact mul_nonneg hR (Finset.sum_nonneg fun i _ => norm_nonneg _)
  -- normalized intercepts: largest on each site, then the largest shifted to zero
  obtain ⟨A, hA⟩ : ∃ A : Fin (n + 1) → ℝ, A = fiberMax y a := ⟨_, rfl⟩
  obtain ⟨Bf, hBf⟩ : ∃ Bf : Fin (n + 1) → ℝ, Bf = fiberMax z b := ⟨_, rfl⟩
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ A Finset.univ_nonempty
  obtain ⟨j₁, -, hj₁⟩ := Finset.exists_max_image Finset.univ Bf Finset.univ_nonempty
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = A j₀ := ⟨_, rfl⟩
  have hTact' : ∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y (fun i => A i - c) x i := by
    intro x
    obtain ⟨i, hi, hmax⟩ := hTact x
    refine ⟨i, hi, maximizes_sub_const c ?_⟩
    rw [hA]
    exact maximizes_fiberMax hmax
  have hSact' : ∀ x, ∃ i, S x = z i ∧ FiniteAffine.Maximizes z (fun i => Bf i - c) x i := by
    intro x
    obtain ⟨i, hi, hmax⟩ := hSact x
    refine ⟨i, hi, maximizes_sub_const c ?_⟩
    rw [hBf]
    exact maximizes_fiberMax hmax
  have hpot : ∀ x, FiniteAffine.potential y (fun i => A i - c) x -
      FiniteAffine.potential z (fun i => Bf i - c) x =
      FiniteAffine.potential y a x - FiniteAffine.potential z b x := by
    intro x
    rw [potential_sub_const, potential_sub_const, hA, hBf, potential_fiberMax,
      potential_fiberMax]
    ring
  have hL2' : (∫ x, (FiniteAffine.potential y (fun i => A i - c) x -
      FiniteAffine.potential z (fun i => Bf i - c) x) ^ 2 ∂ρ) ≤ P ^ 2 * W := by
    simp only [hpot]
    rw [hW]
    exact hL2
  -- every index is active at some point of the ball
  have hptA : ∀ i, ∃ x, ‖x‖ ≤ R ∧ FiniteAffine.Maximizes y (fun i => A i - c) x i := by
    intro i
    obtain ⟨x, hxR, i', hi', hmax⟩ := exists_active_point hρ hm hTm hTact hTpush i
    refine ⟨x, hxR, maximizes_sub_const c ?_⟩
    rw [hA]
    exact maximizes_fiberMax_of_site_eq (maximizes_fiberMax hmax) hi'.symm
  have hptB : ∀ i, ∃ x, ‖x‖ ≤ R ∧ FiniteAffine.Maximizes z (fun i => Bf i - c) x i := by
    intro i
    obtain ⟨x, hxR, i', hi', hmax⟩ := exists_active_point hρ hm hSm hSact hSpush i
    refine ⟨x, hxR, maximizes_sub_const c ?_⟩
    rw [hBf]
    exact maximizes_fiberMax_of_site_eq (maximizes_fiberMax hmax) hi'.symm
  -- oscillation of the intercepts
  have haU : ∀ i, A i - c ≤ 0 := by
    intro i
    have h1 := hj₀ i (Finset.mem_univ i)
    rw [hc]
    linarith
  have haL : ∀ i, -(2 * Ly) ≤ A i - c := by
    intro i
    obtain ⟨x, hxR, hmax⟩ := hptA i
    have h1 := hmax j₀
    change ⟪x, y j₀⟫ + (A j₀ - c) ≤ ⟪x, y i⟫ + (A i - c) at h1
    have h2 : -(R * ‖y j₀‖) ≤ ⟪x, y j₀⟫ :=
      (neg_le_neg (abs_inner_le_mul (y j₀) hxR)).trans (neg_abs_le _)
    have h3 : ⟪x, y i⟫ ≤ R * ‖y i‖ := (le_abs_self _).trans (abs_inner_le_mul (y i) hxR)
    have h4 : A j₀ - c = 0 := by rw [hc]; ring
    linarith [hyL i, hyL j₀]
  have hbU : ∀ i, Bf i - c ≤ Bf j₁ - c := by
    intro i
    have h1 := hj₁ i (Finset.mem_univ i)
    linarith
  have hbL : ∀ i, Bf j₁ - c - 2 * Lz ≤ Bf i - c := by
    intro i
    obtain ⟨x, hxR, hmax⟩ := hptB i
    have h1 := hmax j₁
    change ⟪x, z j₁⟫ + (Bf j₁ - c) ≤ ⟪x, z i⟫ + (Bf i - c) at h1
    have h2 : -(R * ‖z j₁‖) ≤ ⟪x, z j₁⟫ :=
      (neg_le_neg (abs_inner_le_mul (z j₁) hxR)).trans (neg_abs_le _)
    have h3 : ⟪x, z i⟫ ≤ R * ‖z i‖ := (le_abs_self _).trans (abs_inner_le_mul (z i) hxR)
    linarith [hzL i, hzL j₁]
  -- a point of the ball where the two potentials are close
  obtain ⟨G, hG⟩ : ∃ G : E d → ℝ, G = fun x =>
      (FiniteAffine.potential y (fun i => A i - c) x -
        FiniteAffine.potential z (fun i => Bf i - c) x) ^ 2 := ⟨_, rfl⟩
  have hGcont : Continuous G := by
    rw [hG]
    exact ((FiniteAffine.continuous_potential _ _).sub
      (FiniteAffine.continuous_potential _ _)).pow 2
  have hball : ∀ᵐ x ∂ρ, x ∈ Metric.closedBall (0 : E d) R := by
    filter_upwards [hρ] with x hx
    exact mem_closedBall_zero_iff.mpr hx
  have hGint : Integrable G ρ :=
    integrable_of_continuousOn_of_ae_mem_compact (isCompact_closedBall (0 : E d) R) hball
      hGcont.continuousOn
  have hpos := measure_le_integral_pos hGint
  obtain ⟨x, hxG, hxR⟩ : ∃ x, G x ≤ ∫ t, G t ∂ρ ∧ ‖x‖ ≤ R := by
    by_contra hcon
    have hsub : {x | G x ≤ ∫ t, G t ∂ρ} ⊆ {x | ¬ ‖x‖ ≤ R} :=
      fun x hx hxR => hcon ⟨x, hx, hxR⟩
    have hzero : ρ {x | G x ≤ ∫ t, G t ∂ρ} = 0 := measure_mono_null hsub (ae_iff.mp hρ)
    rw [hzero] at hpos
    exact lt_irrefl _ hpos
  have hGle : (∫ t, G t ∂ρ) ≤ P ^ 2 * W := by
    rw [hG]
    exact hL2'
  have hd : |FiniteAffine.potential y (fun i => A i - c) x -
      FiniteAffine.potential z (fun i => Bf i - c) x| ≤ Real.sqrt (P ^ 2 * W) := by
    apply Real.abs_le_sqrt
    have h1 := hxG.trans hGle
    rw [hG] at h1
    exact h1
  obtain ⟨hd1, hd2⟩ := abs_le.mp hd
  have hpy_le : FiniteAffine.potential y (fun i => A i - c) x ≤ Ly + 0 :=
    potential_le_of_bounds y (fun i => A i - c) hxR hyL haU
  have hpy_ge : -(2 * Ly) - Ly ≤ FiniteAffine.potential y (fun i => A i - c) x :=
    (sub_le_sub_right (haL j₀) Ly).trans
      (le_potential_of_bounds y (fun i => A i - c) hxR hyL j₀)
  have hpz_le : FiniteAffine.potential z (fun i => Bf i - c) x ≤ Lz + (Bf j₁ - c) :=
    potential_le_of_bounds z (fun i => Bf i - c) hxR hzL hbU
  have hpz_ge : Bf j₁ - c - Lz ≤ FiniteAffine.potential z (fun i => Bf i - c) x :=
    le_potential_of_bounds z (fun i => Bf i - c) hxR hzL j₁
  have hQ0 : 0 ≤ Real.sqrt (P ^ 2 * W) := Real.sqrt_nonneg _
  have hβU : Bf j₁ - c ≤ Ly + Lz + Real.sqrt (P ^ 2 * W) := by linarith
  have hβL : -(3 * Ly) - Lz - Real.sqrt (P ^ 2 * W) ≤ Bf j₁ - c := by linarith
  refine ⟨fun i => A i - c, fun i => Bf i - c,
    ⟨hTm, hSm, hTact', hSact', hTpush, hSpush, by rw [← hW]; exact hL2'⟩, ?_, ?_⟩
  · intro i
    change |A i - c| ≤ witnessBound R P m y z
    rw [witnessBound, ← hLy, ← hLz, ← hW]
    exact abs_le.mpr ⟨by linarith [haL i], by linarith [haU i]⟩
  · intro i
    change |Bf i - c| ≤ witnessBound R P m y z
    rw [witnessBound, ← hLy, ← hLz, ← hW]
    exact abs_le.mpr ⟨by linarith [hbL i], by linarith [hbU i]⟩


/-- Total-variation closeness of `ρN N` to `ρ`, tested on measurable functions with values in `[0, 1]`. -/
def TVBound (ρN : ℕ → Measure (E d)) (ρ : Measure (E d)) (ε : ℕ → ℝ) : Prop :=
  ∀ N (g : E d → ℝ), Measurable g → (∀ x, 0 ≤ g x ∧ g x ≤ 1) →
    |(∫ x, g x ∂ρN N) - ∫ x, g x ∂ρ| ≤ ε N

/-- If the intercepts converge, active-site maps eventually agree with an
active-site map of the limit configuration, almost everywhere. -/
lemma ae_eventually_eq_of_tendsto_intercepts {ρ : Measure (E d)} (hac : ρ ≪ volume)
    (y : Fin (n + 1) → E d) {aN : ℕ → Fin (n + 1) → ℝ} {a : Fin (n + 1) → ℝ}
    (ha : ∀ i, Tendsto (fun N => aN N i) atTop (𝓝 (a i)))
    {TN : ℕ → E d → E d} {T : E d → E d}
    (hTN : ∀ N x, ∃ i, TN N x = y i ∧ FiniteAffine.Maximizes y (aN N) x i)
    (hT : ∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i) :
    ∀ᵐ x ∂ρ, ∀ᶠ N in atTop, TN N x = T x := by
  filter_upwards [hac.ae_le (ae_affine_tie_implies_slopes_eq volume y a)] with x hx
  obtain ⟨i₀, hTi₀, hact⟩ := hT x
  have hev : ∀ᶠ N in atTop, ∀ j,
      y j = y i₀ ∨ ⟪x, y j⟫ + aN N j < ⟪x, y i₀⟫ + aN N i₀ := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : y j = y i₀
    · exact Eventually.of_forall fun N => Or.inl hj
    · have hlt : ⟪x, y j⟫ + a j < ⟪x, y i₀⟫ + a i₀ := by
        rcases lt_or_eq_of_le (hact j) with h | h
        · exact h
        · exact absurd (hx j i₀ h) hj
      have h1 : Tendsto (fun N => ⟪x, y j⟫ + aN N j) atTop (𝓝 (⟪x, y j⟫ + a j)) :=
        tendsto_const_nhds.add (ha j)
      have h2 : Tendsto (fun N => ⟪x, y i₀⟫ + aN N i₀) atTop (𝓝 (⟪x, y i₀⟫ + a i₀)) :=
        tendsto_const_nhds.add (ha i₀)
      exact (h1.eventually_lt h2 hlt).mono fun N hN => Or.inr hN
  filter_upwards [hev] with N hN
  obtain ⟨k, hTk, hactk⟩ := hTN N x
  rcases hN k with hk | hk
  · rw [hTk, hTi₀, hk]
  · exact absurd (hactk i₀) (not_le.mpr hk)

/-- The push-forward of the limit map is the common push-forward. -/
lemma map_eq_of_tendsto {ρN : ℕ → Measure (E d)} {ρ : Measure (E d)}
    [∀ N, IsProbabilityMeasure (ρN N)] [IsProbabilityMeasure ρ] {ε : ℕ → ℝ}
    (hTV : TVBound ρN ρ ε) (hε : Tendsto ε atTop (𝓝 0))
    {TN : ℕ → E d → E d} {T : E d → E d} (hTNm : ∀ N, Measurable (TN N))
    (hTm : Measurable T) (hev : ∀ᵐ x ∂ρ, ∀ᶠ N in atTop, TN N x = T x)
    {ν : Measure (E d)} (hpush : ∀ N, Measure.map (TN N) (ρN N) = ν) :
    Measure.map T ρ = ν := by
  ext A hA
  rw [Measure.map_apply hTm hA]
  have hνA : ∀ N, (ρN N) (TN N ⁻¹' A) = ν A := by
    intro N
    rw [← hpush N, Measure.map_apply (hTNm N) hA]
  have hmeas : ∀ N, MeasurableSet (TN N ⁻¹' A) := fun N => hTNm N hA
  have hdist : ∀ N, |ρ.real (TN N ⁻¹' A) - ν.real A| ≤ ε N := by
    intro N
    have hg := hTV N ((TN N ⁻¹' A).indicator 1) (measurable_one.indicator (hmeas N))
      (by
        intro x
        by_cases hx : TN N x ∈ A <;> simp [Set.indicator, hx])
    rw [integral_indicator_one (hmeas N), integral_indicator_one (hmeas N)] at hg
    have e : (ρN N).real (TN N ⁻¹' A) = ν.real A := by
      rw [measureReal_def, hνA N, measureReal_def]
    rw [e, abs_sub_comm] at hg
    exact hg
  have h1 : Tendsto (fun N => ρ.real (TN N ⁻¹' A)) atTop (𝓝 (ν.real A)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hε
    rw [Real.dist_eq]
    exact hdist N
  have h2 : Tendsto (fun N => ρ.real (TN N ⁻¹' A)) atTop (𝓝 (ρ.real (T ⁻¹' A))) := by
    have hdct := tendsto_integral_of_dominated_convergence (μ := ρ)
      (F := fun N x => (TN N ⁻¹' A).indicator (1 : E d → ℝ) x)
      (f := fun x => (T ⁻¹' A).indicator (1 : E d → ℝ) x) (fun _ => (1 : ℝ))
      (fun N => (measurable_one.indicator (hmeas N)).aestronglyMeasurable)
      (integrable_const 1)
      (fun N => Eventually.of_forall fun x => by
        by_cases hx : TN N x ∈ A <;> simp [Set.indicator, hx])
      (by
        filter_upwards [hev] with x hx
        apply tendsto_const_nhds.congr'
        filter_upwards [hx] with N hN
        have hiff : x ∈ TN N ⁻¹' A ↔ x ∈ T ⁻¹' A := by
          rw [Set.mem_preimage, Set.mem_preimage, hN]
        change (T ⁻¹' A).indicator (1 : E d → ℝ) x = (TN N ⁻¹' A).indicator (1 : E d → ℝ) x
        by_cases hTx : x ∈ T ⁻¹' A
        · rw [Set.indicator_of_mem hTx, Set.indicator_of_mem (hiff.mpr hTx)]
        · rw [Set.indicator_of_notMem hTx, Set.indicator_of_notMem fun h => hTx (hiff.mp h)])
    simpa only [integral_indicator_one (hmeas _), integral_indicator_one (hTm hA)] using hdct
  have heq : ν.real A = ρ.real (T ⁻¹' A) := tendsto_nhds_unique h1 h2
  have hνfin : ν A ≠ ∞ := by
    rw [← hνA 0]
    exact measure_ne_top _ _
  rw [measureReal_def, measureReal_def] at heq
  exact ((ENNReal.toReal_eq_toReal_iff' hνfin (measure_ne_top _ _)).mp heq).symm

/-- The `L²` bound of the potential difference passes to the limit. -/
lemma integral_sq_le_of_tendsto {ρN : ℕ → Measure (E d)} {ρ : Measure (E d)}
    [∀ N, IsProbabilityMeasure (ρN N)] [IsProbabilityMeasure ρ] {ε : ℕ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hTV : TVBound ρN ρ ε) (hε : Tendsto ε atTop (𝓝 0))
    (hρN : ∀ N, ∀ᵐ x ∂ρN N, ‖x‖ ≤ R) (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R)
    (y z : Fin (n + 1) → E d) {aN bN : ℕ → Fin (n + 1) → ℝ} {a b : Fin (n + 1) → ℝ}
    (ha : ∀ i, Tendsto (fun N => aN N i) atTop (𝓝 (a i)))
    (hb : ∀ i, Tendsto (fun N => bN N i) atTop (𝓝 (b i)))
    {B : ℝ} (haB : ∀ N i, |aN N i| ≤ B) (hbB : ∀ N i, |bN N i| ≤ B) {c : ℝ}
    (hbound : ∀ N, (∫ x, (FiniteAffine.potential y (aN N) x -
      FiniteAffine.potential z (bN N) x) ^ 2 ∂ρN N) ≤ c) :
    (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 ∂ρ) ≤ c := by
  -- notation
  obtain ⟨Ly, hLy⟩ : ∃ Ly : ℝ, Ly = R * ∑ i, ‖y i‖ := ⟨_, rfl⟩
  obtain ⟨Lz, hLz⟩ : ∃ Lz : ℝ, Lz = R * ∑ i, ‖z i‖ := ⟨_, rfl⟩
  have hyL : ∀ i, R * ‖y i‖ ≤ Ly := by
    intro i
    rw [hLy]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => ‖y j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)) hR
  have hzL : ∀ i, R * ‖z i‖ ≤ Lz := by
    intro i
    rw [hLz]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j => ‖z j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)) hR
  obtain ⟨dlim, hdlim⟩ : ∃ f : E d → ℝ,
      f = fun x => FiniteAffine.potential y a x - FiniteAffine.potential z b x := ⟨_, rfl⟩
  obtain ⟨dN, hdN⟩ : ∃ f : ℕ → E d → ℝ, f = fun N x =>
      FiniteAffine.potential y (aN N) x - FiniteAffine.potential z (bN N) x := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℕ → ℝ,
      η = fun N => (∑ i, |a i - aN N i|) + ∑ i, |b i - bN N i| := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Ly + B + (Lz + B) := ⟨_, rfl⟩
  have hη0 : ∀ N, 0 ≤ η N := by
    intro N
    rw [hη]
    exact add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
      (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ∑ i, |a i - aN N i|) atTop (𝓝 (∑ i : Fin (n + 1), (0 : ℝ))) :=
      tendsto_finsetSum _ fun i _ => by
        have := ((tendsto_const_nhds (x := a i)).sub (ha i)).abs
        simpa using this
    have h2 : Tendsto (fun N => ∑ i, |b i - bN N i|) atTop (𝓝 (∑ i : Fin (n + 1), (0 : ℝ))) :=
      tendsto_finsetSum _ fun i _ => by
        have := ((tendsto_const_nhds (x := b i)).sub (hb i)).abs
        simpa using this
    rw [hη]
    simpa using h1.add h2
  -- pointwise comparison
  have hclose : ∀ N x, |dlim x - dN N x| ≤ η N := by
    intro N x
    have h1 := abs_potential_sub_le_sum_abs y a (aN N) x
    have h2 := abs_potential_sub_le_sum_abs z b (bN N) x
    have h3 : dlim x - dN N x =
        (FiniteAffine.potential y a x - FiniteAffine.potential y (aN N) x) -
          (FiniteAffine.potential z b x - FiniteAffine.potential z (bN N) x) := by
      rw [hdlim, hdN]
      ring
    rw [h3, hη]
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hdNbound : ∀ N x, ‖x‖ ≤ R → |dN N x| ≤ D := by
    intro N x hx
    have hy1 := potential_le_of_bounds y (aN N) hx hyL fun i => (le_abs_self _).trans (haB N i)
    have hy2 := le_potential_of_bounds y (aN N) hx hyL 0
    have hz1 := potential_le_of_bounds z (bN N) hx hzL fun i => (le_abs_self _).trans (hbB N i)
    have hz2 := le_potential_of_bounds z (bN N) hx hzL 0
    have ha0 := (neg_abs_le (aN N 0)).trans' (neg_le_neg (haB N 0))
    have hb0 := (neg_abs_le (bN N 0)).trans' (neg_le_neg (hbB N 0))
    rw [hdN, hD]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hD0 : 0 ≤ D := by
    have hLy0 : 0 ≤ Ly := by
      rw [hLy]
      exact mul_nonneg hR (Finset.sum_nonneg fun i _ => norm_nonneg _)
    have hLz0 : 0 ≤ Lz := by
      rw [hLz]
      exact mul_nonneg hR (Finset.sum_nonneg fun i _ => norm_nonneg _)
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (haB 0 0)
    rw [hD]
    linarith
  have hsq : ∀ N x, ‖x‖ ≤ R → dlim x ^ 2 ≤ dN N x ^ 2 + (2 * D * η N + η N ^ 2) := by
    intro N x hx
    have h1 := hclose N x
    have h2 := hdNbound N x hx
    have h3 : |dlim x| ≤ |dN N x| + η N := by
      have := abs_sub_abs_le_abs_sub (dlim x) (dN N x)
      linarith
    have h4 : dlim x ^ 2 = |dlim x| ^ 2 := (sq_abs _).symm
    have h5 : dN N x ^ 2 = |dN N x| ^ 2 := (sq_abs _).symm
    rw [h4, h5]
    nlinarith [abs_nonneg (dlim x), abs_nonneg (dN N x), hη0 N,
      mul_le_mul_of_nonneg_right h2 (hη0 N),
      mul_nonneg (sub_nonneg.mpr h3)
        (add_nonneg (add_nonneg (abs_nonneg (dN N x)) (hη0 N)) (abs_nonneg (dlim x)))]
  -- measurability and integrability
  have hdcont : Continuous dlim := by
    rw [hdlim]
    exact (FiniteAffine.continuous_potential _ _).sub (FiniteAffine.continuous_potential _ _)
  have hdNcont : ∀ N, Continuous (dN N) := by
    intro N
    rw [hdN]
    exact (FiniteAffine.continuous_potential _ _).sub (FiniteAffine.continuous_potential _ _)
  have hball : ∀ (μ : Measure (E d)), (∀ᵐ x ∂μ, ‖x‖ ≤ R) →
      ∀ᵐ x ∂μ, x ∈ Metric.closedBall (0 : E d) R := by
    intro μ hμ
    filter_upwards [hμ] with x hx
    exact mem_closedBall_zero_iff.mpr hx
  have hint : ∀ (μ : Measure (E d)) [IsFiniteMeasure μ], (∀ᵐ x ∂μ, ‖x‖ ≤ R) →
      ∀ f : E d → ℝ, Continuous f → Integrable f μ := by
    intro μ _ hμ f hf
    exact integrable_of_continuousOn_of_ae_mem_compact (isCompact_closedBall (0 : E d) R)
      (hball μ hμ) hf.continuousOn
  -- the limit function is bounded on the ball
  have hdbound : ∀ x, ‖x‖ ≤ R → dlim x ^ 2 ≤ D ^ 2 + 1 := by
    intro x hx
    have hlim1 : Tendsto (fun N => dN N x ^ 2 + (2 * D * η N + η N ^ 2)) atTop
        (𝓝 (dlim x ^ 2 + (2 * D * 0 + 0 ^ 2))) := by
      have hdNx : Tendsto (fun N => dN N x) atTop (𝓝 (dlim x)) := by
        rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) hηlim
        rw [Real.dist_eq, abs_sub_comm]
        exact hclose N x
      exact (hdNx.pow 2).add ((hηlim.const_mul (2 * D)).add (hηlim.pow 2))
    have hle : ∀ N, dN N x ^ 2 + (2 * D * η N + η N ^ 2) ≤ D ^ 2 + (2 * D * η N + η N ^ 2) := by
      intro N
      have h2 := hdNbound N x hx
      have h5 : dN N x ^ 2 = |dN N x| ^ 2 := (sq_abs _).symm
      have h6 : |dN N x| ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      linarith
    have hlim2 : Tendsto (fun N => D ^ 2 + (2 * D * η N + η N ^ 2)) atTop
        (𝓝 (D ^ 2 + (2 * D * 0 + 0 ^ 2))) :=
      tendsto_const_nhds.add ((hηlim.const_mul (2 * D)).add (hηlim.pow 2))
    have := le_of_tendsto_of_tendsto' hlim1 hlim2 hle
    linarith
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = D ^ 2 + 1 := ⟨_, rfl⟩
  have hCpos : 0 < C := by
    rw [hC]
    positivity
  -- total variation applied to the truncated, normalized square
  obtain ⟨g, hg⟩ : ∃ g : E d → ℝ, g = fun x => min (dlim x ^ 2) C / C := ⟨_, rfl⟩
  have hgm : Measurable g := by
    rw [hg]
    exact (((hdcont.pow 2).min continuous_const).div_const C).measurable
  have hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := by
    intro x
    rw [hg]
    constructor
    · exact div_nonneg (le_min (sq_nonneg _) hCpos.le) hCpos.le
    · rw [div_le_one hCpos]
      exact min_le_right _ _
  have hgint : ∀ (μ : Measure (E d)) [IsFiniteMeasure μ], (∀ᵐ x ∂μ, ‖x‖ ≤ R) →
      (∫ x, g x ∂μ) = (∫ x, dlim x ^ 2 ∂μ) / C := by
    intro μ _ hμ
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards [hμ] with x hx
    rw [hg]
    have h1 : dlim x ^ 2 ≤ C := by
      rw [hC]
      exact hdbound x hx
    change min (dlim x ^ 2) C / C = dlim x ^ 2 / C
    rw [min_eq_left h1]
  have hstep1 : ∀ N, (∫ x, dlim x ^ 2 ∂ρ) ≤ (∫ x, dlim x ^ 2 ∂ρN N) + C * ε N := by
    intro N
    have h1 := hTV N g hgm hg01
    rw [hgint (ρN N) (hρN N), hgint ρ hρ] at h1
    have h2 : (∫ x, dlim x ^ 2 ∂ρN N) / C - (∫ x, dlim x ^ 2 ∂ρ) / C =
        ((∫ x, dlim x ^ 2 ∂ρN N) - ∫ x, dlim x ^ 2 ∂ρ) / C := by ring
    rw [h2, abs_div, abs_of_pos hCpos, div_le_iff₀ hCpos] at h1
    have h3 := neg_abs_le ((∫ x, dlim x ^ 2 ∂ρN N) - ∫ x, dlim x ^ 2 ∂ρ)
    linarith
  have hstep2 : ∀ N, (∫ x, dlim x ^ 2 ∂ρN N) ≤ c + (2 * D * η N + η N ^ 2) := by
    intro N
    have hi1 : Integrable (fun x => dlim x ^ 2) (ρN N) :=
      hint (ρN N) (hρN N) _ (hdcont.pow 2)
    have hi2 : Integrable (fun x => dN N x ^ 2) (ρN N) :=
      hint (ρN N) (hρN N) _ ((hdNcont N).pow 2)
    have hi3 : Integrable (fun _ : E d => 2 * D * η N + η N ^ 2) (ρN N) := integrable_const _
    have hmono : (∫ x, dlim x ^ 2 ∂ρN N) ≤
        ∫ x, dN N x ^ 2 + (2 * D * η N + η N ^ 2) ∂ρN N := by
      apply integral_mono_ae hi1 (hi2.add hi3)
      filter_upwards [hρN N] with x hx
      exact hsq N x hx
    have hconst : (∫ _ : E d, (2 * D * η N + η N ^ 2) ∂ρN N) = 2 * D * η N + η N ^ 2 := by
      simp
    rw [integral_add hi2 hi3, hconst] at hmono
    have hb := hbound N
    have e : (∫ x, dN N x ^ 2 ∂ρN N) = ∫ x, (FiniteAffine.potential y (aN N) x -
        FiniteAffine.potential z (bN N) x) ^ 2 ∂ρN N := by
      rw [hdN]
    rw [e] at hmono
    linarith
  have hall : ∀ N, (∫ x, dlim x ^ 2 ∂ρ) ≤ c + (2 * D * η N + η N ^ 2) + C * ε N := by
    intro N
    linarith [hstep1 N, hstep2 N]
  have hlim : Tendsto (fun N => c + (2 * D * η N + η N ^ 2) + C * ε N) atTop
      (𝓝 (c + (2 * D * 0 + 0 ^ 2) + C * 0)) :=
    (tendsto_const_nhds.add ((hηlim.const_mul (2 * D)).add (hηlim.pow 2))).add
      (hε.const_mul C)
  have hfinal := ge_of_tendsto' hlim hall
  have e : (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 ∂ρ) =
      ∫ x, dlim x ^ 2 ∂ρ := by
    rw [hdlim]
  rw [e]
  linarith

/-- **Total-variation limit.** The atomic potential estimate with a fixed
constant is inherited by an absolutely continuous total-variation limit of
probability sources carried by a common ball. -/
theorem AtomicPotentialBound.of_tendsto {ρN : ℕ → Measure (E d)} {ρ : Measure (E d)}
    [∀ N, IsProbabilityMeasure (ρN N)] [IsProbabilityMeasure ρ] {ε : ℕ → ℝ} {R P : ℝ}
    (hR : 0 ≤ R) (hTV : TVBound ρN ρ ε) (hε : Tendsto ε atTop (𝓝 0))
    (hρN : ∀ N, ∀ᵐ x ∂ρN N, ‖x‖ ≤ R) (hρ : ∀ᵐ x ∂ρ, ‖x‖ ≤ R) (hac : ρ ≪ volume)
    (h : ∀ N, AtomicPotentialBound (ρN N) P) : AtomicPotentialBound ρ P := by
  intro n m y z hm hsum hinj
  have hw : ∀ N, ∃ (a b : Fin (n + 1) → ℝ) (T S : E d → E d),
      IsPotentialWitness (ρN N) P m y z a b T S ∧
        (∀ i, |a i| ≤ witnessBound R P m y z) ∧ (∀ i, |b i| ≤ witnessBound R P m y z) := by
    intro N
    obtain ⟨a, b, T, S, hwit⟩ := h N n m y z hm hsum hinj
    obtain ⟨a', b', hwit', ha', hb'⟩ :=
      IsPotentialWitness.exists_bounded hR (hρN N) hm hwit
    exact ⟨a', b', T, S, hwit', ha', hb'⟩
  choose aN bN TN SN hwit haB hbB using hw
  -- a convergent subsequence of intercepts
  have hK : IsCompact
      ((Set.univ.pi fun _ : Fin (n + 1) =>
          Set.Icc (-witnessBound R P m y z) (witnessBound R P m y z)) ×ˢ
        (Set.univ.pi fun _ : Fin (n + 1) =>
          Set.Icc (-witnessBound R P m y z) (witnessBound R P m y z))) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hmem : ∀ N, (aN N, bN N) ∈
      ((Set.univ.pi fun _ : Fin (n + 1) =>
          Set.Icc (-witnessBound R P m y z) (witnessBound R P m y z)) ×ˢ
        (Set.univ.pi fun _ : Fin (n + 1) =>
          Set.Icc (-witnessBound R P m y z) (witnessBound R P m y z))) :=
    fun N => ⟨fun i _ => abs_le.mp (haB N i), fun i _ => abs_le.mp (hbB N i)⟩
  obtain ⟨⟨a, b⟩, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have ha : ∀ i, Tendsto (fun N => aN (φ N) i) atTop (𝓝 (a i)) := fun i =>
    (tendsto_pi_nhds.mp ((continuous_fst.tendsto (a, b)).comp hlim)) i
  have hb : ∀ i, Tendsto (fun N => bN (φ N) i) atTop (𝓝 (b i)) := fun i =>
    (tendsto_pi_nhds.mp ((continuous_snd.tendsto (a, b)).comp hlim)) i
  -- active-site maps of the limit configuration
  obtain ⟨T, hTm, hTact0⟩ := exists_measurable_affine_maximizer y a
  obtain ⟨S, hSm, hSact0⟩ := exists_measurable_affine_maximizer z b
  have hTact : ∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i := by
    intro x
    obtain ⟨i, hi, hmax⟩ := hTact0 x
    refine ⟨i, hi, fun j => ?_⟩
    have h1 := hmax j
    rwa [real_inner_comm x (y j), real_inner_comm x (y i)] at h1
  have hSact : ∀ x, ∃ i, S x = z i ∧ FiniteAffine.Maximizes z b x i := by
    intro x
    obtain ⟨i, hi, hmax⟩ := hSact0 x
    refine ⟨i, hi, fun j => ?_⟩
    have h1 := hmax j
    rwa [real_inner_comm x (z j), real_inner_comm x (z i)] at h1
  -- the subsequence of sources
  have hprob : ∀ N, IsProbabilityMeasure ((fun N => ρN (φ N)) N) := fun N => inferInstance
  have hTV' : TVBound (fun N => ρN (φ N)) ρ (fun N => ε (φ N)) :=
    fun N g hg hg01 => hTV (φ N) g hg hg01
  have hε' : Tendsto (fun N => ε (φ N)) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  have hpushT : Measure.map T ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) :=
    map_eq_of_tendsto hTV' hε' (fun N => (hwit (φ N)).1) hTm
      (ae_eventually_eq_of_tendsto_intercepts hac y ha
        (fun N x => (hwit (φ N)).2.2.1 x) hTact)
      (fun N => (hwit (φ N)).2.2.2.2.1)
  have hpushS : Measure.map S ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (z i) :=
    map_eq_of_tendsto hTV' hε' (fun N => (hwit (φ N)).2.1) hSm
      (ae_eventually_eq_of_tendsto_intercepts hac z hb
        (fun N x => (hwit (φ N)).2.2.2.1 x) hSact)
      (fun N => (hwit (φ N)).2.2.2.2.2.1)
  have hL2 := integral_sq_le_of_tendsto hR hTV' hε' (fun N => hρN (φ N)) hρ y z ha hb
    (fun N i => haB (φ N) i) (fun N i => hbB (φ N) i)
    (fun N => (hwit (φ N)).2.2.2.2.2.2)
  exact ⟨a, b, T, S, hTm, hSm, hTact, hSact, hpushT, hpushS, hL2⟩

end

end BrenierMoment
