module

public import BrenierMoment.PotentialBoundLimit
public import BrenierMoment.PowerSource

@[expose] public section

/-!
# The atomic potential estimate for log-concave sources

Let `V` be convex on a bounded open convex set `U`. On the part of `U` where
`V < n` the function `1 - V / n` is a positive concave profile, and its `n`-th
power increases to `exp (-V)`. The power sources therefore satisfy the atomic
potential estimate with a constant that does not depend on `n`, they are
dominated by a multiple `c n → 1` of the log-concave source, and the estimate
passes to the limit in total variation.
-/

namespace BrenierMoment

open MeasureTheory Filter OAI.Problem358
open scoped ENNReal Topology

noncomputable section

/-! ### Total variation from domination -/

/-- A probability measure dominated by `c` times another probability measure is
within `c - 1` of it on every measurable function with values in `[0, 1]`. -/
lemma abs_integral_sub_le_of_le_smul {α : Type*} [MeasurableSpace α] {μ ρ : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hle : μ ≤ c • ρ) {g : α → ℝ} (hg : Measurable g) (hg01 : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    |(∫ x, g x ∂μ) - ∫ x, g x ∂ρ| ≤ c.toReal - 1 := by
  have hint : ∀ (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ), Measurable f →
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) → Integrable f ν := by
    intro ν _ f hf hf01
    refine Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [(hf01 x).1], (hf01 x).2⟩
  have hone : ∀ (ν : Measure α) [IsProbabilityMeasure ν], (∫ _, (1 : ℝ) ∂ν) = 1 := by
    intro ν _
    simp
  have key : ∀ f : α → ℝ, Measurable f → (∀ x, 0 ≤ f x ∧ f x ≤ 1) →
      (∫ x, f x ∂μ) ≤ c.toReal * ∫ x, f x ∂ρ := by
    intro f hf hf01
    calc (∫ x, f x ∂μ) ≤ ∫ x, f x ∂(c • ρ) :=
          integral_mono_measure hle (Eventually.of_forall fun x => (hf01 x).1)
            ((hint ρ f hf hf01).smul_measure hc)
      _ = c.toReal * ∫ x, f x ∂ρ := by rw [integral_smul_measure, smul_eq_mul]
  have h1 := key g hg hg01
  have h2 := key (fun x => 1 - g x) (measurable_const.sub hg)
    (fun x => ⟨by linarith [(hg01 x).2], by linarith [(hg01 x).1]⟩)
  have hc1 : 1 ≤ c.toReal := by
    have h := key (fun _ => (1 : ℝ)) measurable_const (fun _ => ⟨zero_le_one, le_rfl⟩)
    rw [hone μ, hone ρ, mul_one] at h
    exact h
  rw [integral_sub (integrable_const (1 : ℝ)) (hint μ g hg hg01),
    integral_sub (integrable_const (1 : ℝ)) (hint ρ g hg hg01), hone μ, hone ρ] at h2
  have hρ0 : 0 ≤ ∫ x, g x ∂ρ := integral_nonneg fun x => (hg01 x).1
  have hρ1 : (∫ x, g x ∂ρ) ≤ 1 := by
    calc (∫ x, g x ∂ρ) ≤ ∫ _, (1 : ℝ) ∂ρ :=
          integral_mono (hint ρ g hg hg01) (integrable_const (1 : ℝ)) fun x => (hg01 x).2
      _ = 1 := hone ρ
  have hp1 := mul_nonneg (sub_nonneg.mpr hc1) hρ0
  have hp2 := mul_nonneg (sub_nonneg.mpr hc1) (sub_nonneg.mpr hρ1)
  rw [abs_le]
  constructor <;> nlinarith [h1, h2, hp1, hp2]

variable {d : ℕ}

/-- Domination by multiples of the limit gives a total-variation bound. -/
lemma tvBound_of_le_smul {ρN : ℕ → Measure (E d)} {ρ : Measure (E d)}
    [∀ N, IsProbabilityMeasure (ρN N)] [IsProbabilityMeasure ρ] {c : ℕ → ℝ≥0∞}
    (hc : ∀ N, c N ≠ ∞) (hle : ∀ N, ρN N ≤ c N • ρ) :
    TVBound ρN ρ fun N => (c N).toReal - 1 :=
  fun N _ hg hg01 => abs_integral_sub_le_of_le_smul (hc N) (hle N) hg hg01

/-! ### The sources -/

/-- The unnormalized source with density `exp (-V)` on `U`. -/
def expMeasure (U : Set (E d)) (V : E d → ℝ) : Measure (E d) :=
  (volume.restrict U).withDensity fun x => ENNReal.ofReal (Real.exp (-V x))

/-- The probability source with density proportional to `exp (-V)` on `U`. -/
def logConcaveSource (U : Set (E d)) (V : E d → ℝ) : Measure (E d) :=
  (expMeasure U V Set.univ)⁻¹ • expMeasure U V

lemma expMeasure_eq_powerMeasure (U : Set (E d)) (V : E d → ℝ) :
    expMeasure U V = powerMeasure U (fun x => Real.exp (-V x)) 1 := by
  unfold expMeasure powerMeasure
  simp only [pow_one]

lemma logConcaveSource_eq_powerSource (U : Set (E d)) (V : E d → ℝ) :
    logConcaveSource U V = powerSource U (fun x => Real.exp (-V x)) 1 := by
  unfold logConcaveSource powerSource
  rw [expMeasure_eq_powerMeasure]

/-- The part of `U` where `V < n`. -/
def sublevel (U : Set (E d)) (V : E d → ℝ) (n : ℕ) : Set (E d) := {x | x ∈ U ∧ V x < n}

/-- The profile `1 - V / n`, whose `n`-th power approximates `exp (-V)`. -/
def linProfile (V : E d → ℝ) (n : ℕ) (x : E d) : ℝ := 1 - V x / n

lemma sublevel_subset (U : Set (E d)) (V : E d → ℝ) (n : ℕ) : sublevel U V n ⊆ U :=
  fun _ hx => hx.1

lemma measurableSet_sublevel {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) (n : ℕ) : MeasurableSet (sublevel U V n) :=
  hU.inter (measurableSet_lt hV measurable_const)

lemma measurable_linProfile {V : E d → ℝ} (hV : Measurable V) (n : ℕ) :
    Measurable (linProfile V n) :=
  measurable_const.sub (hV.div_const _)

lemma volume_ne_top_of_norm_le {U : Set (E d)} {R : ℝ} (hR : ∀ x ∈ U, ‖x‖ ≤ R) :
    volume U ≠ ∞ := by
  have hsub : U ⊆ Metric.closedBall (0 : E d) R :=
    fun x hx => mem_closedBall_zero_iff.mpr (hR x hx)
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne

/-- On the part of `U` where `V < n`, the function `1 - V / n` is a concave profile. -/
lemma concaveProfile_sublevel {U : Set (E d)} {V : E d → ℝ} {m : ℝ} (hU : IsOpen U)
    (hV : ConvexOn ℝ U V) (hVm : Measurable V) (hlow : ∀ x ∈ U, m ≤ V x) {n : ℕ}
    (hn : 0 < n) (hne : (sublevel U V n).Nonempty) :
    ConcaveProfile (sublevel U V n) (linProfile V n) (1 + |m|) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcont : ContinuousOn V U := hV.continuousOn hU
  have hopen : IsOpen (sublevel U V n) :=
    hcont.isOpen_inter_preimage hU (isOpen_Iio (a := (n : ℝ)))
  have hconv : Convex ℝ (sublevel U V n) := hV.convex_lt (n : ℝ)
  refine
    { isOpen := hopen
      nonempty := hne
      measurable := measurable_linProfile hVm n
      continuousOn := ?_
      concaveOn := ⟨hconv, ?_⟩
      pos := ?_
      le := ?_ }
  · exact (continuousOn_const.sub (hcont.div_const _)).mono (sublevel_subset U V n)
  · intro x hx y hy a b ha hb hab
    have hc := hV.2 hx.1 hy.1 ha hb hab
    simp only [smul_eq_mul] at hc
    change a * (1 - V x / n) + b * (1 - V y / n) ≤ 1 - V (a • x + b • y) / n
    have hdiv : V (a • x + b • y) / n ≤ (a * V x + b * V y) / n :=
      div_le_div_of_nonneg_right hc hn'.le
    have hsplit : (a * V x + b * V y) / n = a * (V x / n) + b * (V y / n) := by ring
    linarith
  · intro x hx
    have hlt : V x / n < 1 := (div_lt_one hn').mpr hx.2
    change 0 < 1 - V x / n
    linarith
  · intro x hx
    have h1 : m / n ≤ V x / n := div_le_div_of_nonneg_right (hlow x hx.1) hn'.le
    have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : |m / n| ≤ |m| := by
      rw [abs_div, abs_of_pos hn']
      exact div_le_self (abs_nonneg m) h1n
    have h3 := neg_abs_le (m / n)
    change 1 - V x / n ≤ 1 + |m|
    linarith

/-- The truncated power density is below the exponential density. -/
lemma powerMeasure_sublevel_le {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) (n : ℕ) :
    powerMeasure (sublevel U V n) (linProfile V n) n ≤ expMeasure U V := by
  have hS := measurableSet_sublevel hU hV n
  have h1 : powerMeasure (sublevel U V n) (linProfile V n) n ≤
      (volume.restrict (sublevel U V n)).withDensity
        fun x => ENNReal.ofReal (Real.exp (-V x)) := by
    unfold powerMeasure
    refine withDensity_mono ((ae_restrict_iff' hS).mpr (Eventually.of_forall fun x hx => ?_))
    exact ENNReal.ofReal_le_ofReal (Real.one_sub_div_pow_le_exp_neg hx.2.le)
  refine h1.trans ?_
  unfold expMeasure
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [withDensity_apply _ hA, withDensity_apply _ hA]
  exact lintegral_mono' (Measure.restrict_mono Set.Subset.rfl
    (Measure.restrict_mono (sublevel_subset U V n) le_rfl)) le_rfl

/-- The normalized truncated power source is dominated by a multiple of the
log-concave source; the multiple is the ratio of the total masses. -/
lemma powerSource_sublevel_le {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) (hZ0 : expMeasure U V Set.univ ≠ 0)
    (hZtop : expMeasure U V Set.univ ≠ ∞) (n : ℕ) :
    powerSource (sublevel U V n) (linProfile V n) n ≤
      (expMeasure U V Set.univ / powerMeasure (sublevel U V n) (linProfile V n) n Set.univ) •
        logConcaveSource U V := by
  have hle := powerMeasure_sublevel_le hU hV n
  unfold powerSource logConcaveSource
  rw [smul_smul, ENNReal.div_eq_inv_mul, mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, mul_one]
  refine Measure.le_iff.mpr fun A _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  gcongr

/-- The total masses of the truncated power densities converge to the mass of
the exponential density. -/
lemma tendsto_powerMeasure_sublevel {U : Set (E d)} (hU : MeasurableSet U) {V : E d → ℝ}
    (hV : Measurable V) (hfin : expMeasure U V Set.univ ≠ ∞) (k₀ : ℕ) :
    Tendsto (fun N : ℕ =>
      powerMeasure (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀) Set.univ)
      atTop (𝓝 (expMeasure U V Set.univ)) := by
  have hZ : expMeasure U V Set.univ = ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x)) := by
    rw [expMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hM : ∀ n : ℕ, powerMeasure (sublevel U V n) (linProfile V n) n Set.univ =
      ∫⁻ x in U, (sublevel U V n).indicator
        (fun x => ENNReal.ofReal (linProfile V n x ^ n)) x := by
    intro n
    rw [powerMeasure_univ, lintegral_indicator (measurableSet_sublevel hU hV n),
      Measure.restrict_restrict (measurableSet_sublevel hU hV n),
      Set.inter_eq_left.mpr (sublevel_subset U V n)]
  rw [hZ] at hfin ⊢
  simp only [hM]
  refine tendsto_lintegral_of_dominated_convergence
    (fun x => ENNReal.ofReal (Real.exp (-V x))) (fun N => ?_) (fun N => ?_) hfin ?_
  · exact (ENNReal.measurable_ofReal.comp
      ((measurable_linProfile hV (N + k₀)).pow_const (N + k₀))).indicator
        (measurableSet_sublevel hU hV (N + k₀))
  · refine Eventually.of_forall fun x => ?_
    change (sublevel U V (N + k₀)).indicator
      (fun x => ENNReal.ofReal (linProfile V (N + k₀) x ^ (N + k₀))) x ≤
        ENNReal.ofReal (Real.exp (-V x))
    by_cases hx : x ∈ sublevel U V (N + k₀)
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal (Real.one_sub_div_pow_le_exp_neg hx.2.le)
    · rw [Set.indicator_of_notMem hx]
      simp
  · filter_upwards [ae_restrict_mem hU] with x hxU
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (V x)
    have hlim : Tendsto
        (fun N : ℕ => ENNReal.ofReal ((1 + -V x / ((N + k₀ : ℕ) : ℝ)) ^ (N + k₀)))
        atTop (𝓝 (ENNReal.ofReal (Real.exp (-V x)))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        ((Real.tendsto_one_add_div_pow_exp (-V x)).comp (tendsto_add_atTop_nat k₀))
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop N₁] with N hN
    have hcast : ((N₁ : ℕ) : ℝ) ≤ ((N + k₀ : ℕ) : ℝ) := by
      exact_mod_cast hN.trans (Nat.le_add_right N k₀)
    have hmem : x ∈ sublevel U V (N + k₀) := And.intro hxU (hN₁.trans_le hcast)
    change ENNReal.ofReal ((1 + -V x / ((N + k₀ : ℕ) : ℝ)) ^ (N + k₀)) =
      (sublevel U V (N + k₀)).indicator
        (fun x => ENNReal.ofReal (linProfile V (N + k₀) x ^ (N + k₀))) x
    rw [Set.indicator_of_mem hmem]
    change _ = ENNReal.ofReal ((1 - V x / ((N + k₀ : ℕ) : ℝ)) ^ (N + k₀))
    rw [neg_div, ← sub_eq_add_neg]

/-! ### Convex functions on bounded sets -/

/-- A convex function on a bounded open convex set is bounded below. -/
lemma exists_lower_bound_of_convexOn {U : Set (E d)} {V : E d → ℝ} {R : ℝ} (hU : IsOpen U)
    (hne : U.Nonempty) (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hV : ConvexOn ℝ U V) :
    ∃ m : ℝ, ∀ x ∈ U, m ≤ V x := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg x₀).trans (hR x₀ hx₀)
  have hcont : ContinuousOn V U := hV.continuousOn hU
  have hnhds : ∀ᶠ z in 𝓝 x₀, z ∈ U ∧ V z < V x₀ + 1 :=
    (Filter.eventually_mem_set.mpr (hU.mem_nhds hx₀)).and
      ((hcont.continuousAt (hU.mem_nhds hx₀)).eventually_lt continuousAt_const
        (lt_add_one (V x₀)))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnhds
  have hD : 0 < 2 * (2 * R + 1) := by positivity
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = r / (2 * (2 * R + 1)) := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [ht_def]
    exact div_pos hr hD
  have h1t : 0 < 1 + t := by linarith
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = 1 / (1 + t) := ⟨_, rfl⟩
  have hs0 : 0 < s := by
    rw [hs_def]
    exact one_div_pos.mpr h1t
  have hs : s * (1 + t) = 1 := by
    rw [hs_def, one_div, inv_mul_cancel₀ h1t.ne']
  refine ⟨V x₀ - 1 / t, fun x hx => ?_⟩
  -- the reflection of `x` through `x₀`, pulled into the ball
  obtain ⟨z, hz_def⟩ : ∃ z : E d, z = x₀ + t • (x₀ - x) := ⟨_, rfl⟩
  have hz : z ∈ Metric.ball x₀ r := by
    have hzx : z - x₀ = t • (x₀ - x) := by
      rw [hz_def, add_sub_cancel_left]
    have hxx : ‖x₀ - x‖ ≤ 2 * R := by
      have := norm_sub_le x₀ x
      linarith [hR x₀ hx₀, hR x hx]
    rw [Metric.mem_ball, dist_eq_norm, hzx, norm_smul, Real.norm_of_nonneg ht.le]
    calc t * ‖x₀ - x‖ ≤ t * (2 * R) := mul_le_mul_of_nonneg_left hxx ht.le
      _ < r := by
        rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ hD]
        nlinarith [mul_pos hr (show (0 : ℝ) < 2 * R + 2 by linarith)]
  obtain ⟨hzU, hzV⟩ := hball z hz
  -- `x₀` is a convex combination of `z` and `x`
  have hcomb : s • z + (t * s) • x = x₀ := by
    have h1 : s • z + (t * s) • x = (s * (1 + t)) • x₀ := by
      rw [hz_def]
      module
    rw [h1, hs, one_smul]
  have hsum : s + t * s = 1 := by
    rw [← hs]
    ring
  have hconv := hV.2 hzU hx hs0.le (mul_nonneg ht.le hs0.le) hsum
  rw [hcomb] at hconv
  simp only [smul_eq_mul] at hconv
  have h1 : (1 + t) * V x₀ ≤ V z + t * V x := by
    have h := mul_le_mul_of_nonneg_left hconv h1t.le
    have e : (1 + t) * (s * V z + t * s * V x) = (s * (1 + t)) * (V z + t * V x) := by ring
    rw [e, hs, one_mul] at h
    exact h
  have h2 : t * (V x₀ - 1 / t) ≤ t * V x := by
    have e : t * (V x₀ - 1 / t) = t * V x₀ - 1 := by
      rw [mul_sub, mul_one_div_cancel ht.ne']
    rw [e]
    linarith
  exact le_of_mul_le_mul_left h2 ht

/-! ### The estimate -/

/-- The atomic potential estimate for the log-concave source, given a lower bound of `V`. -/
theorem atomicPotentialBound_logConcave_of_le {c₀ : ℝ} (hc₀ : UniformPotentialBound c₀)
    {U : Set (E d)} {V : E d → ℝ} {R m : ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hV : ConvexOn ℝ U V) (hVm : Measurable V)
    (hlow : ∀ x ∈ U, m ≤ V x) :
    AtomicPotentialBound (logConcaveSource U V) (c₀ * Real.sqrt (R ^ 2 + 1)) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hR0 : 0 ≤ R := (norm_nonneg x₀).trans (hR x₀ hx₀)
  have hUm : MeasurableSet U := hU.measurableSet
  have hvol0 : volume U ≠ 0 := (hU.measure_pos volume ⟨x₀, hx₀⟩).ne'
  have hvol : volume U ≠ ∞ := volume_ne_top_of_norm_le hR
  -- the limit source
  have hexp_meas : Measurable fun x => Real.exp (-V x) := Real.measurable_exp.comp hVm.neg
  have hexp_pos : ∀ x ∈ U, 0 < Real.exp (-V x) := fun x _ => Real.exp_pos _
  have hexp_le : ∀ x ∈ U, Real.exp (-V x) ≤ Real.exp (-m) :=
    fun x hx => Real.exp_le_exp.mpr (neg_le_neg (hlow x hx))
  have hZ0 : expMeasure U V Set.univ ≠ 0 := by
    rw [expMeasure_eq_powerMeasure]
    exact (powerMeasure_univ_pos hUm hexp_meas hvol0 hexp_pos 1).ne'
  have hZtop : expMeasure U V Set.univ ≠ ∞ := by
    rw [expMeasure_eq_powerMeasure]
    exact powerMeasure_univ_ne_top hvol (fun x hx => (hexp_pos x hx).le) hexp_le 1
  have hρprob : IsProbabilityMeasure (logConcaveSource U V) := by
    rw [logConcaveSource_eq_powerSource]
    exact powerSource_isProbabilityMeasure hUm hexp_meas hvol0 hvol hexp_pos hexp_le 1
  have hρac : logConcaveSource U V ≪ volume := by
    rw [logConcaveSource_eq_powerSource]
    exact powerSource_absolutelyContinuous U _ 1
  have hρR : ∀ᵐ x ∂logConcaveSource U V, ‖x‖ ≤ R := by
    rw [logConcaveSource_eq_powerSource]
    filter_upwards [ae_mem_powerSource hUm (fun x => Real.exp (-V x)) 1] with x hx
    exact hR x hx
  -- the approximating sources
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (max (V x₀) 0)
  have hk₀V : V x₀ < k₀ := (le_max_left _ _).trans_lt hk₀
  have hk₀pos : 0 < k₀ := by
    exact_mod_cast (le_max_right (V x₀) 0).trans_lt hk₀
  have hpos : ∀ N : ℕ, 0 < N + k₀ := fun N => Nat.add_pos_right N hk₀pos
  have hSne : ∀ N : ℕ, (sublevel U V (N + k₀)).Nonempty := by
    intro N
    have hcast : ((k₀ : ℕ) : ℝ) ≤ ((N + k₀ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left k₀ N
    exact ⟨x₀, And.intro hx₀ (hk₀V.trans_le hcast)⟩
  have hprof : ∀ N : ℕ,
      ConcaveProfile (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (1 + |m|) :=
    fun N => concaveProfile_sublevel hU hV hVm hlow (hpos N) (hSne N)
  have hSR : ∀ N : ℕ, ∀ x ∈ sublevel U V (N + k₀), ‖x‖ ≤ R := fun N x hx => hR x hx.1
  have hSm : ∀ N : ℕ, MeasurableSet (sublevel U V (N + k₀)) :=
    fun N => measurableSet_sublevel hUm hVm (N + k₀)
  have hSvol0 : ∀ N : ℕ, volume (sublevel U V (N + k₀)) ≠ 0 :=
    fun N => ((hprof N).isOpen.measure_pos volume (hSne N)).ne'
  have hSvol : ∀ N : ℕ, volume (sublevel U V (N + k₀)) ≠ ∞ :=
    fun N => volume_ne_top_of_norm_le (hSR N)
  have hM0 : ∀ N : ℕ,
      powerMeasure (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀) Set.univ ≠ 0 :=
    fun N => (powerMeasure_univ_pos (hSm N) (hprof N).measurable (hSvol0 N) (hprof N).pos
      (N + k₀)).ne'
  obtain ⟨ρN, hρN⟩ : ∃ ρN : ℕ → Measure (E d), ∀ N,
      ρN N = powerSource (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀) :=
    ⟨fun N => powerSource (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀),
      fun _ => rfl⟩
  have hbound : ∀ N, AtomicPotentialBound (ρN N) (c₀ * Real.sqrt (R ^ 2 + 1)) := by
    intro N
    rw [hρN N]
    exact atomicPotentialBound_powerSource_unit hc₀ (hprof N) (hSR N) (hpos N)
  have hρNprob : ∀ N, IsProbabilityMeasure (ρN N) := by
    intro N
    rw [hρN N]
    exact powerSource_isProbabilityMeasure (hSm N) (hprof N).measurable (hSvol0 N) (hSvol N)
      (hprof N).pos (hprof N).le (N + k₀)
  have hρNR : ∀ N, ∀ᵐ x ∂ρN N, ‖x‖ ≤ R := by
    intro N
    rw [hρN N]
    filter_upwards [ae_mem_powerSource (hSm N) (linProfile V (N + k₀)) (N + k₀)] with x hx
    exact hSR N x hx
  -- domination, with constants tending to one
  have hle : ∀ N, ρN N ≤ (expMeasure U V Set.univ /
      powerMeasure (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀) Set.univ) •
        logConcaveSource U V := by
    intro N
    rw [hρN N]
    exact powerSource_sublevel_le hUm hVm hZ0 hZtop (N + k₀)
  have hctop : ∀ N, expMeasure U V Set.univ /
      powerMeasure (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀) Set.univ ≠ ∞ :=
    fun N => ENNReal.div_ne_top hZtop (hM0 N)
  have hTV := tvBound_of_le_smul (ρN := ρN) (ρ := logConcaveSource U V) hctop hle
  have hε : Tendsto (fun N => (expMeasure U V Set.univ /
      powerMeasure (sublevel U V (N + k₀)) (linProfile V (N + k₀)) (N + k₀) Set.univ).toReal
        - 1) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_div (a := expMeasure U V Set.univ)
      (tendsto_powerMeasure_sublevel hUm hVm hZtop k₀) (Or.inl hZtop)
    rw [ENNReal.div_self hZ0 hZtop] at h1
    have h3 := ((ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1).sub_const 1
    rw [ENNReal.toReal_one, sub_self] at h3
    exact h3
  exact AtomicPotentialBound.of_tendsto hR0 hTV hε hρNR hρR hρac hbound

/-- **Log-concave sources.** If uniform sources satisfy the atomic potential
estimate with constant `c₀ * R`, then the source with density proportional to
`exp (-V)` on a bounded open convex set of radius `R`, with `V` convex,
satisfies it with constant `c₀ * √(R² + 1)`. -/
theorem atomicPotentialBound_logConcave {c₀ : ℝ} (hc₀ : UniformPotentialBound c₀)
    {U : Set (E d)} {V : E d → ℝ} {R : ℝ} (hU : IsOpen U) (hne : U.Nonempty)
    (hR : ∀ x ∈ U, ‖x‖ ≤ R) (hV : ConvexOn ℝ U V) (hVm : Measurable V) :
    AtomicPotentialBound (logConcaveSource U V) (c₀ * Real.sqrt (R ^ 2 + 1)) := by
  obtain ⟨m, hm⟩ := exists_lower_bound_of_convexOn hU hne hR hV
  exact atomicPotentialBound_logConcave_of_le hc₀ hU hne hR hV hVm hm

end

end BrenierMoment
