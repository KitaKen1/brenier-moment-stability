module

public import BrenierMoment.StripInterpolation
public import BrenierMoment.ClipSlack

@[expose] public section

/-!
# Active maps of finite potentials

A map is active for a finite potential if it selects, at every point, a site
at which the potential is attained. Such a map supports the potential
everywhere, so each of its coordinates lies between the backward and the
forward difference quotient of the potential. With the interpolation property
of the source this gives the clipped estimate for two active maps: the
squared distance of the coordinatewise clipped maps is bounded by the squared
distance of the potentials divided by `h²`, plus `24 d H² h B`.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-! ### Coordinatewise clipping -/

lemma measurable_clip (H : ℝ) : Measurable (clip H) := by
  have h : Continuous fun r : ℝ => max (-H) (min r H) :=
    continuous_const.max (continuous_id.min continuous_const)
  exact h.measurable

lemma measurable_coord (j : Fin d) : Measurable fun v : E d => v j :=
  (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)

lemma sq_clip_sub_clip_le {H : ℝ} (hH : 0 ≤ H) (r s : ℝ) :
    (clip H r - clip H s) ^ 2 ≤ 4 * H ^ 2 := by
  have h1 := abs_le.mp (abs_clip_le hH r)
  have h2 := abs_le.mp (abs_clip_le hH s)
  have h3 : (clip H r - clip H s) ^ 2 ≤ (2 * H) ^ 2 := sq_le_sq' (by linarith) (by linarith)
  linarith [h3, show (2 * H) ^ 2 = 4 * H ^ 2 by ring]

/-- Coordinatewise clipping of a vector. -/
def clipVec (H : ℝ) (v : E d) : E d := WithLp.toLp 2 fun j => clip H (v j)

@[simp] lemma clipVec_apply (H : ℝ) (v : E d) (j : Fin d) : clipVec H v j = clip H (v j) := rfl

lemma measurable_clipVec (H : ℝ) : Measurable (clipVec H : E d → E d) :=
  (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun j => (measurable_clip H).comp (measurable_coord j))

lemma norm_sq_clipVec_sub (H : ℝ) (u v : E d) :
    ‖clipVec H u - clipVec H v‖ ^ 2 = ∑ j, (clip H (u j) - clip H (v j)) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp

/-- Coordinatewise clipping does not increase distances. -/
lemma norm_clipVec_sub_le (H : ℝ) (u v : E d) : ‖clipVec H u - clipVec H v‖ ≤ ‖u - v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_clipVec_sub, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro j _
  have h1 := clip_sub_clip_le_abs H (u j) (v j)
  have h2 := clip_sub_clip_le_abs H (v j) (u j)
  rw [abs_sub_comm] at h2
  have h3 : (clip H (u j) - clip H (v j)) ^ 2 ≤ |u j - v j| ^ 2 := sq_le_sq' (by linarith) h1
  rw [sq_abs] at h3
  simpa using h3

/-- Removing the clipping costs the quadratic tails of the two vectors. -/
lemma norm_sq_sub_le_clipVec {H : ℝ} (hH : 0 ≤ H) (u v : E d) :
    ‖u - v‖ ^ 2 ≤ 3 * ‖clipVec H u - clipVec H v‖ ^ 2 +
      3 * quadraticTailTerm H u + 3 * quadraticTailTerm H v := by
  have hu : ‖u - clipVec H u‖ ^ 2 ≤ quadraticTailTerm H u := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using sum_sq_sub_clip_le hH u
  have hv : ‖v - clipVec H v‖ ^ 2 ≤ quadraticTailTerm H v := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa using sum_sq_sub_clip_le hH v
  have hsplit : u - v =
      (u - clipVec H u) + (clipVec H u - clipVec H v) - (v - clipVec H v) := by abel
  have htri : ‖u - v‖ ≤
      ‖u - clipVec H u‖ + ‖clipVec H u - clipVec H v‖ + ‖v - clipVec H v‖ := by
    calc ‖u - v‖ = ‖(u - clipVec H u) + (clipVec H u - clipVec H v) - (v - clipVec H v)‖ := by
          rw [← hsplit]
      _ ≤ ‖(u - clipVec H u) + (clipVec H u - clipVec H v)‖ + ‖v - clipVec H v‖ :=
          norm_sub_le _ _
      _ ≤ ‖u - clipVec H u‖ + ‖clipVec H u - clipVec H v‖ + ‖v - clipVec H v‖ := by
          linarith [norm_add_le (u - clipVec H u) (clipVec H u - clipVec H v)]
  have hsq := mul_self_le_mul_self (norm_nonneg (u - v)) htri
  nlinarith [hsq, hu, hv,
    sq_nonneg (‖u - clipVec H u‖ - ‖clipVec H u - clipVec H v‖),
    sq_nonneg (‖u - clipVec H u‖ - ‖v - clipVec H v‖),
    sq_nonneg (‖clipVec H u - clipVec H v‖ - ‖v - clipVec H v‖)]

/-- The pointwise secant bound, written with extended nonnegative reals. -/
lemma ofReal_slope_bound {H X A Bu Bv G : ℝ} (hH : 0 ≤ H) (hBu : 0 ≤ Bu) (hBv : 0 ≤ Bv)
    (hG : 0 ≤ G) (h : X ≤ A ^ 2 + 4 * H * (Bu + Bv) + G) :
    ENNReal.ofReal X ≤ ENNReal.ofReal (A ^ 2) +
      ENNReal.ofReal (4 * H) * (ENNReal.ofReal Bu + ENNReal.ofReal Bv) + ENNReal.ofReal G := by
  have h4 : 0 ≤ 4 * H := by positivity
  have hB : 0 ≤ Bu + Bv := add_nonneg hBu hBv
  rw [← ENNReal.ofReal_add hBu hBv, ← ENNReal.ofReal_mul h4,
    ← ENNReal.ofReal_add (sq_nonneg A) (mul_nonneg h4 hB),
    ← ENNReal.ofReal_add (add_nonneg (sq_nonneg A) (mul_nonneg h4 hB)) hG]
  exact ENNReal.ofReal_le_ofReal h

/-! ### Active maps -/

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A map that selects, at every point, a site at which the finite potential is attained. -/
def IsActiveMap (y : ι → E d) (a : ι → ℝ) (T : E d → E d) : Prop :=
  ∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i

/-- An active map supports its potential at every point. -/
lemma IsActiveMap.supports {y : ι → E d} {a : ι → ℝ} {T : E d → E d} (hT : IsActiveMap y a T)
    (x z : E d) :
    FiniteAffine.potential y a x + ⟪z - x, T x⟫ ≤ FiniteAffine.potential y a z := by
  obtain ⟨i, hi, hmax⟩ := hT x
  have h1 := (FiniteAffine.potential_eq_iff_maximizes y a x i).mpr hmax
  have h2 := FiniteAffine.affine_le_potential y a z i
  rw [hi, h1, inner_sub_left]
  linarith

/-- The forward difference quotient of a finite potential along the `j`-th coordinate. -/
def fwdQuot (y : ι → E d) (a : ι → ℝ) (j : Fin d) (h : ℝ) (x : E d) : ℝ :=
  (FiniteAffine.potential y a (x + EuclideanSpace.single j h) - FiniteAffine.potential y a x) / h

lemma fwdQuot_sub (y : ι → E d) (a : ι → ℝ) (j : Fin d) (h : ℝ) (x : E d) :
    fwdQuot y a j h (x - EuclideanSpace.single j h) =
      (FiniteAffine.potential y a x -
        FiniteAffine.potential y a (x - EuclideanSpace.single j h)) / h := by
  unfold fwdQuot
  rw [sub_add_cancel]

lemma measurable_fwdQuot (y : ι → E d) (a : ι → ℝ) (j : Fin d) (h : ℝ) :
    Measurable (fwdQuot y a j h) := by
  have hc : Continuous fun x : E d =>
      (FiniteAffine.potential y a (x + EuclideanSpace.single j h) -
        FiniteAffine.potential y a x) / h :=
    (((FiniteAffine.continuous_potential y a).comp (continuous_id.add continuous_const)).sub
      (FiniteAffine.continuous_potential y a)).div_const h
  exact hc.measurable

lemma IsActiveMap.le_fwdQuot {y : ι → E d} {a : ι → ℝ} {T : E d → E d}
    (hT : IsActiveMap y a T) (j : Fin d) {h : ℝ} (hh : 0 < h) (x : E d) :
    T x j ≤ fwdQuot y a j h x := by
  have h1 := hT.supports x (x + EuclideanSpace.single j h)
  rw [add_sub_cancel_left, EuclideanSpace.inner_single_left] at h1
  simp only [conj_trivial] at h1
  unfold fwdQuot
  rw [le_div_iff₀ hh]
  linarith

lemma IsActiveMap.fwdQuot_sub_le {y : ι → E d} {a : ι → ℝ} {T : E d → E d}
    (hT : IsActiveMap y a T) (j : Fin d) {h : ℝ} (hh : 0 < h) (x : E d) :
    fwdQuot y a j h (x - EuclideanSpace.single j h) ≤ T x j := by
  have h1 := hT.supports x (x - EuclideanSpace.single j h)
  rw [sub_sub_cancel_left, inner_neg_left, EuclideanSpace.inner_single_left] at h1
  simp only [conj_trivial] at h1
  rw [fwdQuot_sub, div_le_iff₀ hh]
  linarith

lemma IsActiveMap.fwdQuot_mono {y : ι → E d} {a : ι → ℝ} {T : E d → E d}
    (hT : IsActiveMap y a T) (j : Fin d) {h : ℝ} (hh : 0 < h) (x : E d) :
    fwdQuot y a j h (x - EuclideanSpace.single j h) ≤ fwdQuot y a j h x :=
  (hT.fwdQuot_sub_le j hh x).trans (hT.le_fwdQuot j hh x)

/-- **Clipped interpolation for two active maps.** -/
theorem clipped_interpolation_of_active {ρ : Measure (E d)} {U : Set (E d)} {B : ℝ}
    (hstrip : StripInterpolation ρ U B) {κ : Type*} [Fintype κ] [Nonempty κ]
    {y : ι → E d} {a : ι → ℝ} {T : E d → E d} {z : κ → E d} {b : κ → ℝ} {S : E d → E d}
    (hT : IsActiveMap y a T) (hS : IsActiveMap z b S) (hTm : Measurable T) (hSm : Measurable S)
    {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h) :
    (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
      ENNReal.ofReal (4 * d / h ^ 2) *
          (∫⁻ x, ENNReal.ofReal
            ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) +
        ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by
  have hΦm : ∀ j : Fin d,
      Measurable fun x => ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) := fun j =>
    ENNReal.measurable_ofReal.comp
      ((((measurable_clip H).comp ((measurable_coord j).comp hTm)).sub
        ((measurable_clip H).comp ((measurable_coord j).comp hSm))).pow_const 2)
  -- one coordinate
  have hcoord : ∀ j : Fin d,
      (∫⁻ x, ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) ∂ρ) ≤
        ENNReal.ofReal (4 / h ^ 2) *
            (∫⁻ x, ENNReal.ofReal
              ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) +
          ENNReal.ofReal (24 * H ^ 2 * h * B) := by
    intro j
    have ha : ∀ x ∈ U, ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) ≤
        ENNReal.ofReal (4 * H ^ 2) :=
      fun x _ => ENNReal.ofReal_le_ofReal (sq_clip_sub_clip_le hH _ _)
    have hb : ∀ x, x ∈ U → x + EuclideanSpace.single j h ∈ U →
        x - EuclideanSpace.single j h ∈ U →
        ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) ≤
          ENNReal.ofReal
            ((((FiniteAffine.potential y a (x + EuclideanSpace.single j h) -
                FiniteAffine.potential z b (x + EuclideanSpace.single j h)) -
              (FiniteAffine.potential y a x - FiniteAffine.potential z b x)) / h) ^ 2) +
          ENNReal.ofReal (4 * H) *
            (ENNReal.ofReal (clip H (fwdQuot y a j h x) -
                clip H (fwdQuot y a j h (x - EuclideanSpace.single j h))) +
              ENNReal.ofReal (clip H (fwdQuot z b j h x) -
                clip H (fwdQuot z b j h (x - EuclideanSpace.single j h)))) + 0 := by
      intro x _ _ _
      have hsl := clipped_slope_sq_le hH (hT.le_fwdQuot j hh x) (hT.fwdQuot_sub_le j hh x)
        (hS.le_fwdQuot j hh x) (hS.fwdQuot_sub_le j hh x)
      have hq : fwdQuot y a j h x - fwdQuot z b j h x =
          ((FiniteAffine.potential y a (x + EuclideanSpace.single j h) -
              FiniteAffine.potential z b (x + EuclideanSpace.single j h)) -
            (FiniteAffine.potential y a x - FiniteAffine.potential z b x)) / h := by
        unfold fwdQuot
        ring
      rw [hq] at hsl
      have hBu := sub_nonneg.mpr (clip_mono H (hT.fwdQuot_mono j hh x))
      have hBv := sub_nonneg.mpr (clip_mono H (hS.fwdQuot_mono j hh x))
      have hres := ofReal_slope_bound hH hBu hBv le_rfl (hsl.trans_eq (add_zero _).symm)
      rw [ENNReal.ofReal_zero] at hres
      exact hres
    have key := hstrip j H h hH hh
      (fun x => ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2)) (fun _ => 0)
      (fun x => FiniteAffine.potential y a x - FiniteAffine.potential z b x)
      (fun x => clip H (fwdQuot y a j h x)) (fun x => clip H (fwdQuot z b j h x))
      (hΦm j) measurable_const
      ((FiniteAffine.continuous_potential y a).sub
        (FiniteAffine.continuous_potential z b)).measurable
      ((measurable_clip H).comp (measurable_fwdQuot y a j h))
      ((measurable_clip H).comp (measurable_fwdQuot z b j h))
      (fun x => abs_clip_le hH _) (fun x => abs_clip_le hH _)
      (fun x => clip_mono H (hT.fwdQuot_mono j hh x))
      (fun x => clip_mono H (hS.fwdQuot_mono j hh x)) ha hb
    rw [lintegral_zero, add_zero] at key
    exact key
  have hsum : ∀ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) =
      ∑ j : Fin d, ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) := by
    intro x
    rw [norm_sq_clipVec_sub, ENNReal.ofReal_sum_of_nonneg fun j _ => sq_nonneg _]
  have hd : (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) := (ENNReal.ofReal_natCast d).symm
  have e1 : (d : ℝ≥0∞) * ENNReal.ofReal (4 / h ^ 2) = ENNReal.ofReal (4 * d / h ^ 2) := by
    rw [hd, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    congr 1
    ring
  have e2 : (d : ℝ≥0∞) * ENNReal.ofReal (24 * H ^ 2 * h * B) =
      ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by
    rw [hd, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    congr 1
    ring
  calc (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ)
      = ∫⁻ x, ∑ j : Fin d, ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) ∂ρ := by
        simp only [hsum]
    _ = ∑ j : Fin d, ∫⁻ x, ENNReal.ofReal ((clip H (T x j) - clip H (S x j)) ^ 2) ∂ρ :=
        lintegral_finsetSum _ fun j _ => hΦm j
    _ ≤ ∑ _j : Fin d, (ENNReal.ofReal (4 / h ^ 2) *
            (∫⁻ x, ENNReal.ofReal
              ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) +
          ENNReal.ofReal (24 * H ^ 2 * h * B)) := Finset.sum_le_sum fun j _ => hcoord j
    _ = ENNReal.ofReal (4 * d / h ^ 2) *
            (∫⁻ x, ENNReal.ofReal
              ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) +
          ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_add,
          ← mul_assoc, e1, e2]

end

end BrenierMoment
