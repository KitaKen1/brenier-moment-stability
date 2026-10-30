module

public import BrenierMoment.PowerSource
public import OAI.Analysis.Brenier.CanonicalPaths
public import OAI.Analysis.Brenier.NormalizedPaths

@[expose] public section

/-!
# The atomic potential estimate for uniform sources

The upstream development proves the estimate for uniform sources on convex
bodies, with the constant `√(2 (1 + 162)) R` depending only on the radius `R`
of the body. Its final statement hides the potentials behind an existential
quantifier. Here the same chain of upstream results is run once more with the
intercepts and the active-site maps kept as data, which is the form required
by `AtomicPotentialBound`.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358 Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

noncomputable section

/-- The atomic potential estimate for the uniform source on a convex body of
radius `R`, in explicit form. -/
theorem atomicPotentialBound_uniform {d : ℕ} {K : Set (E d)} (hK : IsCompact K)
    (hKconv : Convex ℝ K) (hKint : (interior K).Nonempty) {R : ℝ}
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) :
    AtomicPotentialBound (uniformMeasure K) (Real.sqrt 326 * R) := by
  intro n m y z hm hsum hinj
  have hR0 : 0 ≤ R := by
    obtain ⟨x₀, hx₀⟩ := hKint
    exact (norm_nonneg x₀).trans (hKR x₀ (interior_subset hx₀))
  obtain ⟨Rn, hRn⟩ : ∃ Rn : ℝ≥0, (Rn : ℝ) = R := ⟨⟨R, hR0⟩, rfl⟩
  have hxR : ∀ᵐ x ∂uniformMeasure K, ‖x‖ ≤ Rn := by
    filter_upwards [UniformSource.ae_mem hK.measurableSet] with x hx
    rw [hRn]
    exact hKR x hx
  have hprob : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hKint
  obtain ⟨c, r, hc, hr, hdc, hmass, hnormal, henergy⟩ :=
    FixedMassIntercepts.exists_actual_atomic_intercept_path hK hKconv hKint
      m hm hsum y z Rn hxR (fun t ht => hinj t ht.1 ht.2)
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = ∑ i, m i * ‖y i - z i‖ ^ 2 := ⟨_, rfl⟩
  have he : 0 ≤ e := by
    rw [he_def]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (sq_nonneg _)
  have hsqrt : Real.sqrt e ^ 2 = e := Real.sq_sqrt he
  -- the affine site paths
  let path : Fin (n + 1) → ℝ → E d := fun i t => (1 - t) • y i + t • z i
  let velocity : Fin (n + 1) → ℝ → E d := fun i _ => z i - y i
  have hpath : ∀ i, Continuous (path i) := by intro i; dsimp [path]; fun_prop
  have hdpath : ∀ i t, HasDerivAt (path i) (velocity i t) t := by
    intro i t
    have heq : path i = fun q : ℝ => y i + q • (z i - y i) := by
      funext q
      dsimp [path]
      module
    rw [heq]
    simpa only [velocity, one_smul] using!
      ((hasDerivAt_id t).smul_const (z i - y i)).const_add (y i)
  have hvEnergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, m i * ‖velocity i t‖ ^ 2) ≤ Real.sqrt e ^ 2 := by
    intro t _
    rw [hsqrt, he_def]
    exact le_of_eq (Finset.sum_congr rfl fun i _ => by simp only [velocity, norm_sub_rev])
  have hrEnergy : ∀ t ∈ Ioo (0 : ℝ) 1,
      (∑ i, m i * r i t ^ 2) ≤ 162 * (Rn : ℝ) ^ 2 * Real.sqrt e ^ 2 := by
    intro t ht
    rw [hsqrt, he_def]
    exact henergy t ht
  have hinj' : ∀ q ∈ Ioo (0 : ℝ) 1, Function.Injective (fun i => path i q) :=
    fun t ht => hinj t ht.1 ht.2
  -- a jointly measurable active index with the prescribed cell masses
  obtain ⟨active, hactiveMeas, hactive, hmassA⟩ :=
    CellGeometry.exists_joint_measurable_selector_prescribed_masses hK.measurableSet
      (fun q i => path i q) (fun q i => c i q) (fun _ i => m i) (Ioo 0 1)
      (fun i => (hpath i).measurable) hc hinj' hmass
  -- continuous intercepts up to the endpoints, and the potential estimate
  obtain ⟨cbar, hcbar, hEq, _, _, _, hbound⟩ :=
    exists_normalized_finite_affine_endpoint_potentials K path velocity c r active m
      (Real.sqrt_nonneg e) (by norm_num : (0 : ℝ) ≤ 162) hxR hm hpath
      (fun _ => continuousOn_const) hr hactiveMeas (fun i t _ => hdpath i t) hdc hinj'
      (fun q _ => hactive q) hmassA hnormal hvEnergy hrEnergy
  -- the endpoint maps
  let T : ℝ → E d → E d := fun q x => path (active (q, x)) q
  have hTm (q : ℝ) : Measurable (T q) :=
    (measurable_of_countable (fun i => path i q)).comp
      (hactiveMeas.comp (measurable_const.prodMk measurable_id))
  have hweights : (∑ i, ENNReal.ofReal (m i)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (hm i).le), hsum]
    exact ENNReal.ofReal_one
  have hactivebar : ∀ q ∈ Ioo (0 : ℝ) 1, ∀ x j,
      ⟪x, path j q⟫ + cbar j q ≤
        ⟪x, path (active (q, x)) q⟫ + cbar (active (q, x)) q := by
    intro q hq x j
    rw [← hEq j hq, ← hEq (active (q, x)) hq]
    exact hactive q x j
  have hpush (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) :
      Measure.map (T q) (uniformMeasure K) =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (path i q) := by
    apply map_finite_selector_of_masses (uniformMeasure K)
      (fun x => active (q, x))
      (hactiveMeas.comp (measurable_const.prodMk measurable_id))
      (fun i => path i q) (fun i => ENNReal.ofReal (m i))
    intro i
    rw [← hmassA q hq i]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  obtain ⟨T₀, T₁, hT₀active, hT₁active, hT₀opt, hT₁opt⟩ :=
    exists_unique_optimal_finite_affine_path_endpoints hK hKconv hKint
      (by norm_num : (0 : ℝ) < 1) (fun i => ENNReal.ofReal (m i)) hweights
      (fun i => (hpath i).continuousOn) (fun i => (hcbar i).continuousOn)
      (fun q _ => hTm q)
      (fun q hq => Filter.Eventually.of_forall fun x =>
        ⟨active (q, x), rfl, hactivebar q hq x⟩) hpush
  have hy0 : ∀ i, path i 0 = y i := by
    intro i
    simp [path]
  have hz1 : ∀ i, path i 1 = z i := by
    intro i
    simp [path]
  have hY : (fun i => path i 0) = y := funext hy0
  have hZ : (fun i => path i 1) = z := funext hz1
  -- everything so far is stated for the endpoint sites; replace them by `y` and `z`
  have key : ∀ (Y Z : Fin (n + 1) → E d), Y = y → Z = z →
      (∀ x, ∃ i, T₀ x = Y i ∧
        ∀ j, inner ℝ x (Y j) + cbar j 0 ≤ inner ℝ x (Y i) + cbar i 0) →
      (∀ x, ∃ i, T₁ x = Z i ∧
        ∀ j, inner ℝ x (Z j) + cbar j 1 ≤ inner ℝ x (Z i) + cbar i 1) →
      Measure.map T₀ (uniformMeasure K) = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (Y i) →
      Measure.map T₁ (uniformMeasure K) = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (Z i) →
      (∫ x, (FiniteAffine.potential Z (fun i => cbar i 1) x -
          FiniteAffine.potential Y (fun i => cbar i 0) x) ^ 2 ∂uniformMeasure K) ≤
        2 * (1 + 162) * (Rn : ℝ) ^ 2 * Real.sqrt e ^ 2 →
      ∃ (a b : Fin (n + 1) → ℝ) (T S : E d → E d),
        Measurable T ∧ Measurable S ∧
        (∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i) ∧
        (∀ x, ∃ i, S x = z i ∧ FiniteAffine.Maximizes z b x i) ∧
        Measure.map T (uniformMeasure K) = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
        Measure.map S (uniformMeasure K) = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (z i) ∧
        (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2
            ∂uniformMeasure K) ≤
          (Real.sqrt 326 * R) ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2 := by
    intro Y Z hYy hZz h0 h1 hp0 hp1 hb
    subst Y
    subst Z
    refine ⟨fun i => cbar i 0, fun i => cbar i 1, T₀, T₁, hT₀opt.1.1, hT₁opt.1.1,
      h0, h1, hp0, hp1, ?_⟩
    rw [hsqrt, hRn, he_def] at hb
    have hP : (Real.sqrt 326 * R) ^ 2 = 2 * (1 + 162) * R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    have hswap : (∫ x, (FiniteAffine.potential y (fun i => cbar i 0) x -
        FiniteAffine.potential z (fun i => cbar i 1) x) ^ 2 ∂uniformMeasure K) =
        ∫ x, (FiniteAffine.potential z (fun i => cbar i 1) x -
          FiniteAffine.potential y (fun i => cbar i 0) x) ^ 2 ∂uniformMeasure K := by
      congr 1
      funext x
      ring
    rw [hP, hswap]
    exact hb
  exact key _ _ hY hZ hT₀active hT₁active hT₀opt.1.2.1 hT₁opt.1.2.1 hbound

/-- Uniform sources satisfy the atomic potential estimate with constant `√326` times
the radius, in every dimension. -/
theorem uniformPotentialBound : UniformPotentialBound (Real.sqrt 326) :=
  fun _ _ _ hK hKconv hKint hKR => atomicPotentialBound_uniform hK hKconv hKint hKR

end

end BrenierMoment
