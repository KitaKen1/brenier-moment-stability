module

public import BrenierMoment.PotentialBound

@[expose] public section

/-!
# The atomic potential estimate for power densities

A density proportional to `h ^ r`, with `h` positive and concave on a bounded
open convex set, is reached from the uniform case by `r` one-coordinate lifts:
the density `h ^ (r + 1)` is the marginal of the density `h ^ r` on the region
under the graph of `h`, which is again bounded, open and convex, with radius
increased from `R` to `√(R² + η²)` when `h ≤ η`. Since the constant of the
uniform estimate depends on the source only through its radius, induction on
`r` gives the constant `c₀ * √(R² + r η²)`.

The uniform estimate enters as the hypothesis `UniformPotentialBound c₀`.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

/-- The atomic potential estimate for uniform sources on convex bodies of every
dimension, with a constant proportional to the radius of the body. -/
def UniformPotentialBound (c₀ : ℝ) : Prop :=
  ∀ (k : ℕ) (K : Set (E k)) (R : ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
    (∀ x ∈ K, ‖x‖ ≤ R) → AtomicPotentialBound (uniformMeasure K) (c₀ * R)

variable {k : ℕ}

/-- A positive concave function, bounded by `η`, on a nonempty open convex set. -/
structure ConcaveProfile (U : Set (E k)) (h : E k → ℝ) (η : ℝ) : Prop where
  isOpen : IsOpen U
  nonempty : U.Nonempty
  measurable : Measurable h
  continuousOn : ContinuousOn h U
  concaveOn : ConcaveOn ℝ U h
  pos : ∀ x ∈ U, 0 < h x
  le : ∀ x ∈ U, h x ≤ η

/-- The profile is inherited by the region under the graph. -/
lemma ConcaveProfile.subgraph {U : Set (E k)} {h : E k → ℝ} {η : ℝ}
    (hp : ConcaveProfile U h η) :
    ConcaveProfile (subgraph U h) (fun w => h (dropLast w)) η where
  isOpen := isOpen_subgraph hp.isOpen hp.continuousOn
  nonempty := subgraph_nonempty hp.nonempty hp.pos
  measurable := hp.measurable.comp measurable_dropLast
  continuousOn := hp.continuousOn.comp continuous_dropLast.continuousOn fun _ hw => hw.1
  concaveOn := (hp.concaveOn.comp_linearMap dropLast).subset (fun _ hw => hw.1)
    (convex_subgraph hp.concaveOn)
  pos := fun _ hw => hp.pos _ hw.1
  le := fun _ hw => hp.le _ hw.1

/-- With exponent zero the power source is the uniform measure of the closure. -/
lemma powerSource_zero {U : Set (E k)} (hconv : Convex ℝ U) (h : E k → ℝ) :
    powerSource U h 0 = uniformMeasure (closure U) := by
  have hae : closure U =ᵐ[volume] U :=
    closure_ae_eq_of_null_frontier (hconv.addHaar_frontier volume)
  have hpm : powerMeasure U h 0 = volume.restrict U := by
    unfold powerMeasure
    simp only [pow_zero, ENNReal.ofReal_one]
    exact withDensity_one
  unfold powerSource uniformMeasure
  rw [hpm, Measure.restrict_apply_univ, Measure.restrict_congr_set hae, measure_congr hae]

/-- **Power densities.** If uniform sources satisfy the atomic potential
estimate with constant `c₀ * R`, then a source with density proportional to
`h ^ r` on a set of radius `R`, with `h` a concave profile bounded by `η`,
satisfies it with constant `c₀ * √(R² + r η²)`. -/
theorem atomicPotentialBound_powerSource {c₀ : ℝ} (hc₀ : UniformPotentialBound c₀) (r : ℕ) :
    ∀ (k : ℕ) (U : Set (E k)) (h : E k → ℝ) (R η : ℝ), ConcaveProfile U h η →
      (∀ x ∈ U, ‖x‖ ≤ R) →
      AtomicPotentialBound (powerSource U h r) (c₀ * Real.sqrt (R ^ 2 + r * η ^ 2)) := by
  induction r with
  | zero =>
    intro k U h R η hp hR
    obtain ⟨x₀, hx₀⟩ := hp.nonempty
    have hR0 : 0 ≤ R := (norm_nonneg x₀).trans (hR x₀ hx₀)
    have hsub : closure U ⊆ Metric.closedBall (0 : E k) R :=
      closure_minimal (fun x hx => mem_closedBall_zero_iff.mpr (hR x hx))
        Metric.isClosed_closedBall
    have hcompact : IsCompact (closure U) :=
      (isCompact_closedBall (0 : E k) R).of_isClosed_subset isClosed_closure hsub
    have hint : (interior (closure U)).Nonempty :=
      ⟨x₀, hp.isOpen.subset_interior_closure hx₀⟩
    have hbase := hc₀ k (closure U) R hcompact hp.concaveOn.1.closure hint
      (fun x hx => mem_closedBall_zero_iff.mp (hsub hx))
    rw [powerSource_zero hp.concaveOn.1]
    have hconst : c₀ * Real.sqrt (R ^ 2 + ((0 : ℕ) : ℝ) * η ^ 2) = c₀ * R := by
      rw [Nat.cast_zero, zero_mul, add_zero, Real.sqrt_sq hR0]
    rw [hconst]
    exact hbase
  | succ r ih =>
    intro k U h R η hp hR
    have hlift := ih (k + 1) (subgraph U h) (fun w => h (dropLast w))
      (Real.sqrt (R ^ 2 + η ^ 2)) η hp.subgraph
      (fun w hw => norm_le_of_mem_subgraph hR hp.le hw)
    have hmarg := map_dropLast_powerSource hp.isOpen.measurableSet hp.measurable
      (fun x hx => (hp.pos x hx).le) r
    have hdesc := AtomicPotentialBound.of_marginal hmarg
      (powerSource_absolutelyContinuous U h (r + 1)) hlift
    have hconst : c₀ * Real.sqrt (Real.sqrt (R ^ 2 + η ^ 2) ^ 2 + (r : ℝ) * η ^ 2) =
        c₀ * Real.sqrt (R ^ 2 + ((r + 1 : ℕ) : ℝ) * η ^ 2) := by
      rw [Real.sq_sqrt (by positivity)]
      push_cast
      congr 2
      ring
    rw [← hconst]
    exact hdesc

/-- Scaling the profile by a positive constant does not change the normalized source. -/
lemma powerSource_const_mul (U : Set (E k)) (h : E k → ℝ) {t : ℝ} (ht : 0 < t) (r : ℕ) :
    powerSource U (fun x => t * h x) r = powerSource U h r := by
  have hpm : powerMeasure U (fun x => t * h x) r =
      ENNReal.ofReal (t ^ r) • powerMeasure U h r := by
    unfold powerMeasure
    have hfun : (fun x => ENNReal.ofReal ((t * h x) ^ r)) =
        ENNReal.ofReal (t ^ r) • fun x => ENNReal.ofReal (h x ^ r) := by
      funext x
      rw [Pi.smul_apply, smul_eq_mul, mul_pow, ENNReal.ofReal_mul (pow_nonneg ht.le r)]
    change (volume.restrict U).withDensity (fun x => ENNReal.ofReal ((t * h x) ^ r)) = _
    rw [hfun, withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  have h0 : ENNReal.ofReal (t ^ r) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos ht r)).ne'
  unfold powerSource
  rw [hpm, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.ofReal_ne_top), smul_smul, mul_right_comm,
    ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, one_mul]

/-- **Power densities, normalized.** For a positive exponent the bound of the
profile is scaled away, and the constant is `c₀ * √(R² + 1)` whatever the
exponent. -/
theorem atomicPotentialBound_powerSource_unit {c₀ : ℝ} (hc₀ : UniformPotentialBound c₀)
    {U : Set (E k)} {h : E k → ℝ} {R η : ℝ} (hp : ConcaveProfile U h η)
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) {r : ℕ} (hr : 0 < r) :
    AtomicPotentialBound (powerSource U h r) (c₀ * Real.sqrt (R ^ 2 + 1)) := by
  obtain ⟨x₀, hx₀⟩ := hp.nonempty
  have hη : 0 < η := (hp.pos x₀ hx₀).trans_le (hp.le x₀ hx₀)
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr'
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = 1 / (η * Real.sqrt r) := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [ht_def]
    exact one_div_pos.mpr (mul_pos hη hs)
  have htη : t * η = 1 / Real.sqrt r := by
    rw [ht_def, div_mul_eq_mul_div, one_mul, div_eq_div_iff (mul_pos hη hs).ne' hs.ne']
    ring
  have hp' : ConcaveProfile U (fun x => t * h x) (1 / Real.sqrt r) :=
    { isOpen := hp.isOpen
      nonempty := hp.nonempty
      measurable := measurable_const.mul hp.measurable
      continuousOn := continuousOn_const.mul hp.continuousOn
      concaveOn := by
        refine ⟨hp.concaveOn.1, fun x hx y hy a b ha hb hab => ?_⟩
        have hc := hp.concaveOn.2 hx hy ha hb hab
        simp only [smul_eq_mul] at hc
        change a * (t * h x) + b * (t * h y) ≤ t * h (a • x + b • y)
        calc a * (t * h x) + b * (t * h y) = t * (a * h x + b * h y) := by ring
          _ ≤ t * h (a • x + b • y) := mul_le_mul_of_nonneg_left hc ht.le
      pos := fun x hx => mul_pos ht (hp.pos x hx)
      le := fun x hx => by
        rw [← htη]
        exact mul_le_mul_of_nonneg_left (hp.le x hx) ht.le }
  have hmain := atomicPotentialBound_powerSource hc₀ r k U (fun x => t * h x) R
    (1 / Real.sqrt r) hp' hR
  have hconst : R ^ 2 + (r : ℝ) * (1 / Real.sqrt r) ^ 2 = R ^ 2 + 1 := by
    rw [one_div, inv_pow, Real.sq_sqrt hr'.le, mul_inv_cancel₀ hr'.ne']
  rw [hconst, powerSource_const_mul U h ht r] at hmain
  exact hmain

end

end BrenierMoment
