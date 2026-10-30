module

public import BrenierMoment.CoordBox
public import BrenierMoment.FourCellSlices
public import BrenierMoment.FourAtomTargets
public import BrenierMoment.MomentTail
public import OAI.Analysis.Brenier.AffineOptimality
public import OAI.Analysis.Brenier.Argmax

@[expose] public section

/-!
# The four-atom example in dimension `d`

The source is uniform on the box `[0,1] × [-1,1]^(d-1)`. Four parallel planes
with slopes `0, R, 2R, 3R` have cells of masses `1 - 3a, a, a, a`; tilting the
third plane transversally keeps these masses. All quantities are certified
directly: the active plane by the explicit selector, the cell masses by slices,
optimality by the finite-affine certificate, and the target distance by a
coordinate lower bound. Nothing is solved for.
-/

namespace BrenierMoment.Sharp

open MeasureTheory OAI.Problem358
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ}

/-! ### The source box -/

/-- Lower endpoints: `0` in the distinguished coordinate and `-1` elsewhere. -/
def sourceLo (i : Fin d) : Fin d → ℝ := fun k => if k = i then 0 else -1

/-- Upper endpoints. -/
def sourceHi : Fin d → ℝ := fun _ => 1

/-- `[0,1]` in coordinate `i` and `[-1,1]` in every other coordinate. -/
def sourceBox (i : Fin d) : Set (E d) := coordBox (sourceLo i) sourceHi

lemma sourceLo_lt_sourceHi (i k : Fin d) : sourceLo i k < sourceHi k := by
  unfold sourceLo sourceHi
  split_ifs <;> norm_num

lemma sourceLo_self (i : Fin d) : sourceLo i i = 0 := by simp [sourceLo]

lemma sourceLo_of_ne {i k : Fin d} (h : k ≠ i) : sourceLo i k = -1 := by simp [sourceLo, h]

lemma isCompact_sourceBox (i : Fin d) : IsCompact (sourceBox i) := isCompact_coordBox _ _

lemma sourceBox_isProbabilityMeasure (i : Fin d) :
    IsProbabilityMeasure (uniformMeasure (sourceBox i)) :=
  uniformMeasure_coordBox_isProbabilityMeasure (sourceLo_lt_sourceHi i)

lemma ae_mem_sourceBox (i : Fin d) : ∀ᵐ x ∂uniformMeasure (sourceBox i), x ∈ sourceBox i :=
  Measure.ae_smul_measure (ae_restrict_mem (isCompact_sourceBox i).measurableSet) _

lemma mem_Icc_of_mem_sourceBox {i : Fin d} {x : E d} (hx : x ∈ sourceBox i) (k : Fin d) :
    x k ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := hx k
  have hlo : (-1 : ℝ) ≤ sourceLo i k := by
    unfold sourceLo
    split_ifs <;> norm_num
  exact ⟨hlo.trans h.1, h.2⟩

lemma measurable_coord (k : Fin d) : Measurable fun x : E d => x k :=
  (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) k).measurable

/-! ### The planar selector -/

/-- The cell index in slice coordinates, transverse coordinate first. The
parameter `τ` scales the tilt: `τ = 0` for the first target, `τ = 1` for the second. -/
def planarIndex (a τ : ℝ) (q : ℝ × ℝ) : Fin 4 := FourAtom.activeIndex a q.2 (τ * q.1)

lemma measurable_planarIndex (a τ : ℝ) : Measurable (planarIndex a τ) := by
  have h12 : Measurable fun q : ℝ × ℝ => FourAtom.boundary12 a (τ * q.1) := by
    unfold FourAtom.boundary12
    fun_prop
  have h23 : Measurable fun q : ℝ × ℝ => FourAtom.boundary23 a (τ * q.1) := by
    unfold FourAtom.boundary23
    fun_prop
  unfold planarIndex FourAtom.activeIndex
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_snd h12) measurable_const
      (Measurable.ite (measurableSet_le measurable_snd h23) measurable_const
        measurable_const))

lemma tilt_bounds {τ s : ℝ} (hτ : |τ| ≤ 1) (hs : s ∈ Set.Icc (-1 : ℝ) 1) :
    -1 ≤ τ * s ∧ τ * s ≤ 1 := by
  have hs' : |s| ≤ 1 := abs_le.mpr hs
  have h : |τ * s| ≤ 1 := by
    rw [abs_mul]
    nlinarith [mul_nonneg (abs_nonneg τ) (sub_nonneg.mpr hs'), abs_nonneg τ]
  exact abs_le.mp h

theorem planar_mass_zero {a : ℝ} (τ : ℝ) (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (planarIndex a τ ⁻¹' {0}) =
      ENNReal.ofReal (1 - 3 * a) := by
  have hS : MeasurableSet (planarIndex a τ ⁻¹' {0}) :=
    measurable_planarIndex a τ (measurableSet_singleton 0)
  have hβ : |(0 : ℝ)| ≤ 1 - 3 * a := by
    rw [abs_zero]
    linarith
  rw [prod_intervalLaw_of_slices hS (len := fun s => 1 - 3 * a + 0 * s),
    lintegral_affine_intervalLaw_symm hβ]
  intro s _
  have hpre : Prod.mk s ⁻¹' (planarIndex a τ ⁻¹' {0}) = Set.Iic (FourAtom.boundary01 a) := by
    ext t
    exact FourAtom.activeIndex_eq_zero_iff a t (τ * s)
  have h0 : 0 ≤ FourAtom.boundary01 a := by
    unfold FourAtom.boundary01
    linarith
  rw [hpre, intervalLaw_unit_Iic h0 (by unfold FourAtom.boundary01; linarith)]
  congr 1
  unfold FourAtom.boundary01
  ring

theorem planar_mass_one {a τ : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) (hτ : |τ| ≤ 1) :
    ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (planarIndex a τ ⁻¹' {1}) =
      ENNReal.ofReal a := by
  have hS : MeasurableSet (planarIndex a τ ⁻¹' {1}) :=
    measurable_planarIndex a τ (measurableSet_singleton 1)
  have hβ : |(-(a / 4) * τ)| ≤ a := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ a / 4)]
    nlinarith [mul_nonneg (by positivity : 0 ≤ a / 4) (sub_nonneg.mpr hτ)]
  rw [prod_intervalLaw_of_slices hS (len := fun s => a + -(a / 4) * τ * s),
    lintegral_affine_intervalLaw_symm hβ]
  intro s hs
  obtain ⟨hσ0, hσ1⟩ := tilt_bounds hτ hs
  obtain ⟨h0, h01, h12, h1⟩ := FourAtom.boundary_bounds ha ha3 hσ0 hσ1
  have hpre : Prod.mk s ⁻¹' (planarIndex a τ ⁻¹' {1}) =
      Set.Ioc (FourAtom.boundary01 a) (FourAtom.boundary12 a (τ * s)) := by
    ext t
    exact FourAtom.activeIndex_eq_one_iff a t (τ * s)
  rw [hpre, intervalLaw_unit_Ioc h0 h01 (h12.trans h1), FourAtom.boundary12_sub_boundary01]
  congr 1
  ring

theorem planar_mass_two {a τ : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) (hτ : |τ| ≤ 1) :
    ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (planarIndex a τ ⁻¹' {2}) =
      ENNReal.ofReal a := by
  have hS : MeasurableSet (planarIndex a τ ⁻¹' {2}) :=
    measurable_planarIndex a τ (measurableSet_singleton 2)
  have hβ : |a / 2 * τ| ≤ a := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ a / 2)]
    nlinarith [mul_nonneg (by positivity : 0 ≤ a / 2) (sub_nonneg.mpr hτ)]
  rw [prod_intervalLaw_of_slices hS (len := fun s => a + a / 2 * τ * s),
    lintegral_affine_intervalLaw_symm hβ]
  intro s hs
  obtain ⟨hσ0, hσ1⟩ := tilt_bounds hτ hs
  obtain ⟨h0, h01, h12, h1⟩ := FourAtom.boundary_bounds ha ha3 hσ0 hσ1
  have hpre : Prod.mk s ⁻¹' (planarIndex a τ ⁻¹' {2}) =
      Set.Ioc (FourAtom.boundary12 a (τ * s)) (FourAtom.boundary23 a (τ * s)) := by
    ext t
    exact FourAtom.activeIndex_eq_two_iff h01
  rw [hpre, intervalLaw_unit_Ioc (h0.trans h01) h12 h1, FourAtom.boundary23_sub_boundary12]
  congr 1
  ring

theorem planar_mass_three {a τ : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) (hτ : |τ| ≤ 1) :
    ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (planarIndex a τ ⁻¹' {3}) =
      ENNReal.ofReal a := by
  have hS : MeasurableSet (planarIndex a τ ⁻¹' {3}) :=
    measurable_planarIndex a τ (measurableSet_singleton 3)
  have hβ : |(-(a / 4) * τ)| ≤ a := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ a / 4)]
    nlinarith [mul_nonneg (by positivity : 0 ≤ a / 4) (sub_nonneg.mpr hτ)]
  rw [prod_intervalLaw_of_slices hS (len := fun s => a + -(a / 4) * τ * s),
    lintegral_affine_intervalLaw_symm hβ]
  intro s hs
  obtain ⟨hσ0, hσ1⟩ := tilt_bounds hτ hs
  obtain ⟨h0, h01, h12, h1⟩ := FourAtom.boundary_bounds ha ha3 hσ0 hσ1
  have hpre : Prod.mk s ⁻¹' (planarIndex a τ ⁻¹' {3}) =
      Set.Ioi (FourAtom.boundary23 a (τ * s)) := by
    ext t
    exact FourAtom.activeIndex_eq_three_iff h01 h12
  rw [hpre, intervalLaw_unit_Ioi (h0.trans (h01.trans h12)) h1, FourAtom.one_sub_boundary23]
  congr 1
  ring

/-! ### Cells in the box -/

/-- The cell index of a point: coordinate `i` carries the slopes, `j` the tilt. -/
def cellIndex (i j : Fin d) (a τ : ℝ) (x : E d) : Fin 4 := planarIndex a τ (x j, x i)

lemma measurable_cellIndex (i j : Fin d) (a τ : ℝ) : Measurable (cellIndex i j a τ) :=
  (measurable_planarIndex a τ).comp ((measurable_coord j).prodMk (measurable_coord i))

theorem cell_mass {i j : Fin d} (hij : i ≠ j) {a τ : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1)
    (hτ : |τ| ≤ 1) (k : Fin 4) :
    uniformMeasure (sourceBox i) (cellIndex i j a τ ⁻¹' {k}) = FourAtom.weights a k := by
  have hS : MeasurableSet (planarIndex a τ ⁻¹' {k}) :=
    measurable_planarIndex a τ (measurableSet_singleton k)
  have hpre : cellIndex i j a τ ⁻¹' {k} =
      (fun x : E d => (x j, x i)) ⁻¹' (planarIndex a τ ⁻¹' {k}) := rfl
  rw [hpre, sourceBox,
    uniformMeasure_coordBox_coordPair_preimage (sourceLo_lt_sourceHi i) j i hij.symm _ hS,
    sourceLo_of_ne hij.symm, sourceLo_self]
  change ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (planarIndex a τ ⁻¹' {k}) =
    FourAtom.weights a k
  fin_cases k
  · exact planar_mass_zero τ ha ha3
  · exact planar_mass_one ha ha3 hτ
  · exact planar_mass_two ha ha3 hτ
  · exact planar_mass_three ha ha3 hτ

/-! ### Sites, potential and transport map -/

/-- The four sites: slopes `0, R, 2R, 3R` along `i`; the third carries the tilt `b` along `j`. -/
def sites (i j : Fin d) (R b : ℝ) : Fin 4 → E d :=
  ![0, EuclideanSpace.single i R,
    EuclideanSpace.single i (2 * R) + EuclideanSpace.single j b,
    EuclideanSpace.single i (3 * R)]

/-- The intercepts giving the cell masses `1 - 3a, a, a, a`. -/
def intercepts (a R : ℝ) : Fin 4 → ℝ :=
  ![0, R * (-1 + 3 * a), R * (-2 + 5 * a), R * (-3 + 6 * a)]

/-- The transverse tilt of the third site, scaled by `τ`. -/
def tilt (a R τ : ℝ) : ℝ := R * (a * τ / 4)

lemma tilt_zero (a R : ℝ) : tilt a R 0 = 0 := by
  unfold tilt
  ring

lemma tilt_one (a R : ℝ) : tilt a R 1 = R * a / 4 := by
  unfold tilt
  ring

/-- Every affine branch is `R` times the scalar plane of `FourCellGeometry`. -/
lemma affine_eq_plane (i j : Fin d) (a R τ : ℝ) (x : E d) (k : Fin 4) :
    ⟪x, sites i j R (tilt a R τ) k⟫ + intercepts a R k =
      R * FourAtom.tiltedPlane a (x i) (τ * x j) k := by
  fin_cases k <;>
    simp [sites, intercepts, tilt, FourAtom.tiltedPlane, inner_add_right,
      EuclideanSpace.inner_single_right] <;>
    ring

/-- The explicit transport map. -/
def cellMap (i j : Fin d) (a R τ : ℝ) (x : E d) : E d :=
  sites i j R (tilt a R τ) (cellIndex i j a τ x)

lemma measurable_cellMap (i j : Fin d) (a R τ : ℝ) : Measurable (cellMap i j a R τ) :=
  (measurable_of_countable (sites i j R (tilt a R τ))).comp (measurable_cellIndex i j a τ)

/-- On the box the selected plane is active. -/
lemma maximizes_cellIndex {i j : Fin d} {a R τ : ℝ} (ha : 0 ≤ a)
    (hR : 0 ≤ R) (hτ : |τ| ≤ 1) {x : E d} (hx : x ∈ sourceBox i) :
    FiniteAffine.Maximizes (sites i j R (tilt a R τ)) (intercepts a R) x
      (cellIndex i j a τ x) := by
  intro k
  obtain ⟨hσ0, hσ1⟩ := tilt_bounds hτ (mem_Icc_of_mem_sourceBox hx j)
  rw [affine_eq_plane, affine_eq_plane]
  exact mul_le_mul_of_nonneg_left (FourAtom.activeIndex_spec ha hσ0 hσ1 k) hR

/-- The slope of each site along the distinguished coordinate, in units of `R`. -/
def siteSlope : Fin 4 → ℝ := ![0, 1, 2, 3]

lemma sites_apply_main {i j : Fin d} (hij : i ≠ j) (R b : ℝ) (k : Fin 4) :
    sites i j R b k i = siteSlope k * R := by
  fin_cases k <;> simp [sites, siteSlope, hij]

lemma sites_apply_transverse {i j : Fin d} (hij : i ≠ j) (R b : ℝ) (k : Fin 4) :
    sites i j R b k j = if k = 2 then b else 0 := by
  fin_cases k <;> simp [sites, hij.symm]

lemma siteSlope_sub_sq {k l : Fin 4} (hkl : k ≠ l) :
    1 ≤ (siteSlope k - siteSlope l) ^ 2 := by
  fin_cases k <;> fin_cases l <;> first | exact absurd rfl hkl | norm_num [siteSlope]

lemma sites_injective {i j : Fin d} (hij : i ≠ j) {R : ℝ} (hR : 0 < R) (b : ℝ) :
    Function.Injective (sites i j R b) := by
  intro k l h
  by_contra hkl
  have hc := congrArg (fun x : E d => x i) h
  simp only [sites_apply_main hij] at hc
  have h1 := siteSlope_sub_sq hkl
  have h2 : (siteSlope k - siteSlope l) * R = 0 := by linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rw [h3] at h1
    norm_num at h1
  · linarith

/-- The four-atom target with transverse tilt `b`. -/
def target (i j : Fin d) (a R b : ℝ) : Measure (E d) :=
  ∑ k, FourAtom.weights a k • Measure.dirac (sites i j R b k)

/-- A probability measure with exactly four atoms. -/
def HasFourAtoms (μ : Measure (E d)) : Prop :=
  ∃ y : Fin 4 → E d, Function.Injective y ∧
    ∃ w : Fin 4 → ℝ≥0∞, (∀ k, 0 < w k) ∧ (∑ k, w k) = 1 ∧
      μ = ∑ k, w k • Measure.dirac (y k)

theorem target_hasFourAtoms {i j : Fin d} (hij : i ≠ j) {a R : ℝ} (b : ℝ)
    (ha : 0 < a) (ha3 : 3 * a < 1) (hR : 0 < R) : HasFourAtoms (target i j a R b) :=
  ⟨sites i j R b, sites_injective hij hR b, FourAtom.weights a, FourAtom.weights_pos ha ha3,
    FourAtom.weights_sum ha.le ha3.le, rfl⟩

lemma target_isProbabilityMeasure (i j : Fin d) {a : ℝ} (R b : ℝ)
    (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) : IsProbabilityMeasure (target i j a R b) :=
  finite_atomic_probability (sites i j R b) (FourAtom.weights a) (FourAtom.weights_sum ha ha3)

/-- The explicit map pushes the uniform box law to the four-atom target. -/
theorem map_cellMap {i j : Fin d} (hij : i ≠ j) {a τ : ℝ} (R : ℝ) (ha : 0 ≤ a)
    (ha3 : 3 * a ≤ 1) (hτ : |τ| ≤ 1) :
    Measure.map (cellMap i j a R τ) (uniformMeasure (sourceBox i)) =
      target i j a R (tilt a R τ) :=
  map_finite_selector_of_masses (uniformMeasure (sourceBox i)) (cellIndex i j a τ)
    (measurable_cellIndex i j a τ) (sites i j R (tilt a R τ)) (FourAtom.weights a)
    (cell_mass hij ha ha3 hτ)

/-- The explicit map is the unique optimal map onto the four-atom target. -/
theorem isUniqueOptimal_cellMap {i j : Fin d} (hij : i ≠ j) {a R τ : ℝ} (ha : 0 ≤ a)
    (ha3 : 3 * a ≤ 1) (hR : 0 < R) (hτ : |τ| ≤ 1) :
    IsUniqueQuadraticOptimalMap (uniformMeasure (sourceBox i))
      (target i j a R (tilt a R τ)) (cellMap i j a R τ) := by
  have : IsProbabilityMeasure (uniformMeasure (sourceBox i)) :=
    sourceBox_isProbabilityMeasure i
  have hactive : ∀ᵐ x ∂uniformMeasure (sourceBox i), ∃ k,
      cellMap i j a R τ x = sites i j R (tilt a R τ) k ∧
        FiniteAffine.Maximizes (sites i j R (tilt a R τ)) (intercepts a R) x k := by
    filter_upwards [ae_mem_sourceBox i] with x hx
    exact ⟨cellIndex i j a τ x, rfl, maximizes_cellIndex ha hR.le hτ hx⟩
  have h := isUniqueQuadraticOptimalMap_uniform_of_finite_affine (sourceBox i)
    (isCompact_sourceBox i) (sites i j R (tilt a R τ)) (intercepts a R)
    (sites_injective hij hR _) (measurable_cellMap i j a R τ) hactive
  rwa [map_cellMap hij R ha ha3 hτ] at h

/-! ### The target distance -/

lemma target_ae_transverse_zero {i j : Fin d} (hij : i ≠ j) (a R : ℝ) :
    ∀ᵐ x ∂target i j a R 0, x j = 0 := by
  unfold target
  rw [ae_finsetSum_measure_iff]
  intro k _
  apply Measure.ae_smul_measure
  have hx : sites i j R 0 k j = 0 := by
    rw [sites_apply_transverse hij]
    split_ifs <;> rfl
  simpa using hx

lemma target_transverse_moment {i j : Fin d} (hij : i ≠ j) (a R b : ℝ) :
    (∫⁻ x, ENNReal.ofReal ((x j) ^ 2) ∂target i j a R b) =
      ENNReal.ofReal a * ENNReal.ofReal (b ^ 2) := by
  simp [target, FourAtom.weights, Fin.sum_univ_succ, lintegral_smul_measure,
    sites_apply_transverse hij]

lemma norm_sites_sub_sq (i j : Fin d) (R b : ℝ) (k : Fin 4) :
    ‖sites i j R 0 k - sites i j R b k‖ ^ 2 = if k = 2 then b ^ 2 else 0 := by
  fin_cases k
  · simp [sites]
  · simp [sites]
  · have e : sites i j R 0 2 - sites i j R b 2 = EuclideanSpace.single j (0 - b) := by
      change EuclideanSpace.single i (2 * R) + EuclideanSpace.single j 0 -
        (EuclideanSpace.single i (2 * R) + EuclideanSpace.single j b) = _
      rw [add_sub_add_left_eq_sub, ← PiLp.single_sub]
    change ‖sites i j R 0 2 - sites i j R b 2‖ ^ 2 = if (2 : Fin 4) = 2 then b ^ 2 else 0
    rw [e]
    simp [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
  · simp [sites]

lemma matching_cost (i j : Fin d) (a R b : ℝ) :
    quadraticPlanCost (atomicMatchingPlan (FourAtom.weights a) (sites i j R 0)
      (sites i j R b)) = ENNReal.ofReal a * ENNReal.ofReal (b ^ 2) := by
  rw [quadraticPlanCost_atomicMatchingPlan]
  simp_rw [norm_sites_sub_sq]
  simp [FourAtom.weights, Fin.sum_univ_succ]

/-- The exact target distance, certified against all couplings. -/
theorem wasserstein2_target {i j : Fin d} (hij : i ≠ j) {a : ℝ} (R b : ℝ)
    (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    wasserstein2 (target i j a R 0) (target i j a R b) = Real.sqrt (a * b ^ 2) := by
  have hπ : IsCoupling (target i j a R 0) (target i j a R b)
      (atomicMatchingPlan (FourAtom.weights a) (sites i j R 0) (sites i j R b)) :=
    atomicMatchingPlan_isCoupling _ _ _ (FourAtom.weights_sum ha ha3)
  have hc : quadraticPlanCost (atomicMatchingPlan (FourAtom.weights a) (sites i j R 0)
      (sites i j R b)) = ∫⁻ x, ENNReal.ofReal ((x j) ^ 2) ∂target i j a R b := by
    rw [matching_cost, target_transverse_moment hij]
  rw [wasserstein2_eq_sqrt_coordinate_moment j (target_ae_transverse_zero hij a R) hπ hc,
    target_transverse_moment hij, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
    ENNReal.toReal_ofReal (sq_nonneg b)]

/-! ### The map error -/

/-- The planar region swept by the last cell boundary. -/
def sweep23 (a : ℝ) : Set (ℝ × ℝ) :=
  {q | min (FourAtom.boundary23 a q.1) (FourAtom.boundary23 a 0) < q.2 ∧
    q.2 ≤ max (FourAtom.boundary23 a q.1) (FourAtom.boundary23 a 0)}

/-- The planar region swept by the middle cell boundary. -/
def sweep12 (a : ℝ) : Set (ℝ × ℝ) :=
  {q | min (FourAtom.boundary12 a q.1) (FourAtom.boundary12 a 0) < q.2 ∧
    q.2 ≤ max (FourAtom.boundary12 a q.1) (FourAtom.boundary12 a 0)}

lemma measurableSet_sweep23 (a : ℝ) : MeasurableSet (sweep23 a) := by
  have hg : Measurable fun q : ℝ × ℝ =>
      min (FourAtom.boundary23 a q.1) (FourAtom.boundary23 a 0) := by
    unfold FourAtom.boundary23
    fun_prop
  have hh : Measurable fun q : ℝ × ℝ =>
      max (FourAtom.boundary23 a q.1) (FourAtom.boundary23 a 0) := by
    unfold FourAtom.boundary23
    fun_prop
  exact (measurableSet_lt hg measurable_snd).inter (measurableSet_le measurable_snd hh)

lemma measurableSet_sweep12 (a : ℝ) : MeasurableSet (sweep12 a) := by
  have hg : Measurable fun q : ℝ × ℝ =>
      min (FourAtom.boundary12 a q.1) (FourAtom.boundary12 a 0) := by
    unfold FourAtom.boundary12
    fun_prop
  have hh : Measurable fun q : ℝ × ℝ =>
      max (FourAtom.boundary12 a q.1) (FourAtom.boundary12 a 0) := by
    unfold FourAtom.boundary12
    fun_prop
  exact (measurableSet_lt hg measurable_snd).inter (measurableSet_le measurable_snd hh)

theorem planar_sweep23 {a : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (sweep23 a) = ENNReal.ofReal (a / 8) := by
  have hg : Measurable fun s : ℝ =>
      min (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) := by
    unfold FourAtom.boundary23
    fun_prop
  have hh : Measurable fun s : ℝ =>
      max (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) := by
    unfold FourAtom.boundary23
    fun_prop
  obtain ⟨h0', h01', h12', h1'⟩ := FourAtom.boundary_bounds (s := 0) ha ha3
    (by norm_num) (by norm_num)
  have hbd : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ min (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) ∧
      min (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) ≤
        max (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) ∧
      max (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) ≤ 1 := by
    intro s hs
    obtain ⟨h0, h01, h12, h1⟩ := FourAtom.boundary_bounds ha ha3 hs.1 hs.2
    exact ⟨le_min (h0.trans (h01.trans h12)) (h0'.trans (h01'.trans h12')),
      (min_le_left _ _).trans (le_max_left _ _), max_le h1 h1'⟩
  calc ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (sweep23 a)
      = ∫⁻ s, ENNReal.ofReal (max (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0) -
          min (FourAtom.boundary23 a s) (FourAtom.boundary23 a 0)) ∂intervalLaw (-1) 1 :=
        prod_intervalLaw_region hg hh hbd
    _ = ∫⁻ s, ENNReal.ofReal (a / 4 * |s|) ∂intervalLaw (-1) 1 := by
        apply lintegral_congr
        intro s
        rw [FourAtom.max_sub_min_boundary23 ha]
    _ = ENNReal.ofReal (a / 4 / 2) := lintegral_mul_abs_intervalLaw_symm (by positivity)
    _ = ENNReal.ofReal (a / 8) := by
        congr 1
        ring

theorem planar_sweep12 {a : ℝ} (ha : 0 ≤ a) (ha3 : 3 * a ≤ 1) :
    ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (sweep12 a) = ENNReal.ofReal (a / 8) := by
  have hg : Measurable fun s : ℝ =>
      min (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) := by
    unfold FourAtom.boundary12
    fun_prop
  have hh : Measurable fun s : ℝ =>
      max (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) := by
    unfold FourAtom.boundary12
    fun_prop
  obtain ⟨h0', h01', h12', h1'⟩ := FourAtom.boundary_bounds (s := 0) ha ha3
    (by norm_num) (by norm_num)
  have hbd : ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ min (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) ∧
      min (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) ≤
        max (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) ∧
      max (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) ≤ 1 := by
    intro s hs
    obtain ⟨h0, h01, h12, h1⟩ := FourAtom.boundary_bounds ha ha3 hs.1 hs.2
    exact ⟨le_min (h0.trans h01) (h0'.trans h01'),
      (min_le_left _ _).trans (le_max_left _ _), max_le (h12.trans h1) (h12'.trans h1')⟩
  calc ((intervalLaw (-1) 1).prod (intervalLaw 0 1)) (sweep12 a)
      = ∫⁻ s, ENNReal.ofReal (max (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0) -
          min (FourAtom.boundary12 a s) (FourAtom.boundary12 a 0)) ∂intervalLaw (-1) 1 :=
        prod_intervalLaw_region hg hh hbd
    _ = ∫⁻ s, ENNReal.ofReal (a / 4 * |s|) ∂intervalLaw (-1) 1 := by
        apply lintegral_congr
        intro s
        rw [FourAtom.max_sub_min_boundary12 ha]
    _ = ENNReal.ofReal (a / 4 / 2) := lintegral_mul_abs_intervalLaw_symm (by positivity)
    _ = ENNReal.ofReal (a / 8) := by
        congr 1
        ring

lemma coord_sq_le_norm_sq (v : E d) (k : Fin d) : (v k) ^ 2 ≤ ‖v‖ ^ 2 := by
  have h : |v k| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v k
  calc (v k) ^ 2 = |v k| ^ 2 := (sq_abs _).symm
    _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2

/-- Sites of different indices are at distance at least `R`, whatever the tilts. -/
lemma sq_le_norm_sites_sub_sq {i j : Fin d} (hij : i ≠ j) (R b b' : ℝ) {k l : Fin 4}
    (hkl : k ≠ l) : R ^ 2 ≤ ‖sites i j R b k - sites i j R b' l‖ ^ 2 := by
  have h1 := coord_sq_le_norm_sq (sites i j R b k - sites i j R b' l) i
  have h2 : (sites i j R b k - sites i j R b' l) i = (siteSlope k - siteSlope l) * R := by
    change sites i j R b k i - sites i j R b' l i = _
    rw [sites_apply_main hij, sites_apply_main hij]
    ring
  rw [h2] at h1
  have h3 := siteSlope_sub_sq hkl
  nlinarith [mul_le_mul_of_nonneg_right h3 (sq_nonneg R)]

/-- The squared map error is at least `R ^ 2 * a / 4`. -/
theorem mapError_lower {i j : Fin d} (hij : i ≠ j) {a R : ℝ} (ha : 0 ≤ a)
    (ha3 : 3 * a ≤ 1) :
    R * Real.sqrt a / 2 ≤
      mapL2Dist (uniformMeasure (sourceBox i)) (cellMap i j a R 0) (cellMap i j a R 1) := by
  have : IsProbabilityMeasure (uniformMeasure (sourceBox i)) :=
    sourceBox_isProbabilityMeasure i
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Measure (E d), ρ = uniformMeasure (sourceBox i) := ⟨_, rfl⟩
  have : IsProbabilityMeasure ρ := by rw [hρ]; infer_instance
  rw [← hρ]
  -- the two disagreement regions
  have hpair : Measurable fun x : E d => (x j, x i) :=
    (measurable_coord j).prodMk (measurable_coord i)
  obtain ⟨D23, hD23⟩ : ∃ D : Set (E d), D = (fun x : E d => (x j, x i)) ⁻¹' sweep23 a :=
    ⟨_, rfl⟩
  obtain ⟨D12, hD12⟩ : ∃ D : Set (E d), D = (fun x : E d => (x j, x i)) ⁻¹' sweep12 a :=
    ⟨_, rfl⟩
  have hm23 : MeasurableSet D23 := by rw [hD23]; exact hpair (measurableSet_sweep23 a)
  have hm12 : MeasurableSet D12 := by rw [hD12]; exact hpair (measurableSet_sweep12 a)
  have hmass23 : ρ D23 = ENNReal.ofReal (a / 8) := by
    rw [hρ, hD23, sourceBox,
      uniformMeasure_coordBox_coordPair_preimage (sourceLo_lt_sourceHi i) j i hij.symm _
        (measurableSet_sweep23 a),
      sourceLo_of_ne hij.symm, sourceLo_self]
    exact planar_sweep23 ha ha3
  have hmass12 : ρ D12 = ENNReal.ofReal (a / 8) := by
    rw [hρ, hD12, sourceBox,
      uniformMeasure_coordBox_coordPair_preimage (sourceLo_lt_sourceHi i) j i hij.symm _
        (measurableSet_sweep12 a),
      sourceLo_of_ne hij.symm, sourceLo_self]
    exact planar_sweep12 ha ha3
  have ha8 : 0 ≤ a / 8 := by positivity
  have hreal23 : ρ.real D23 = a / 8 := by
    rw [measureReal_def, hmass23, ENNReal.toReal_ofReal ha8]
  have hreal12 : ρ.real D12 = a / 8 := by
    rw [measureReal_def, hmass12, ENNReal.toReal_ofReal ha8]
  -- integrability of the squared error
  obtain ⟨f, hf⟩ : ∃ f : E d → ℝ,
      f = fun x => ‖cellMap i j a R 0 x - cellMap i j a R 1 x‖ ^ 2 := ⟨_, rfl⟩
  have hfm : Measurable f := by
    rw [hf]
    exact ((measurable_cellMap i j a R 0).sub (measurable_cellMap i j a R 1)).norm.pow_const 2
  have hfbound : ∀ x, f x ≤ ∑ k : Fin 4, ∑ l : Fin 4,
      ‖sites i j R (tilt a R 0) k - sites i j R (tilt a R 1) l‖ ^ 2 := by
    intro x
    rw [hf]
    exact (Finset.single_le_sum
      (f := fun l : Fin 4 => ‖sites i j R (tilt a R 0) (cellIndex i j a 0 x) -
        sites i j R (tilt a R 1) l‖ ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ (cellIndex i j a 1 x))).trans
      (Finset.single_le_sum
        (f := fun k : Fin 4 => ∑ l : Fin 4,
          ‖sites i j R (tilt a R 0) k - sites i j R (tilt a R 1) l‖ ^ 2)
        (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg _)
        (Finset.mem_univ (cellIndex i j a 0 x)))
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    rw [hf]
    exact sq_nonneg _
  have hfint : Integrable f ρ := by
    apply (integrable_const (∑ k : Fin 4, ∑ l : Fin 4,
      ‖sites i j R (tilt a R 0) k - sites i j R (tilt a R 1) l‖ ^ 2)).mono'
      hfm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hfbound x
  -- pointwise lower bound on the box
  have hpoint : ∀ x ∈ sourceBox i,
      D23.indicator (fun _ => R ^ 2) x + D12.indicator (fun _ => R ^ 2) x ≤ f x := by
    intro x hx
    have hxj := mem_Icc_of_mem_sourceBox hx j
    obtain ⟨h0, h01, h12, h1⟩ := FourAtom.boundary_bounds ha ha3 hxj.1 hxj.2
    obtain ⟨h0', h01', h12', h1'⟩ := FourAtom.boundary_bounds (s := 0) ha ha3
      (by norm_num) (by norm_num)
    have e1 : cellIndex i j a 1 x = FourAtom.activeIndex a (x i) (x j) := by
      change FourAtom.activeIndex a (x i) (1 * x j) = _
      rw [one_mul]
    have e0 : cellIndex i j a 0 x = FourAtom.activeIndex a (x i) 0 := by
      change FourAtom.activeIndex a (x i) (0 * x j) = _
      rw [zero_mul]
    have hne_bound : cellIndex i j a 0 x ≠ cellIndex i j a 1 x → R ^ 2 ≤ f x := by
      intro hne
      rw [hf]
      exact sq_le_norm_sites_sub_sq hij R _ _ hne
    have hsep : max (FourAtom.boundary12 a (x j)) (FourAtom.boundary12 a 0) ≤
        min (FourAtom.boundary23 a (x j)) (FourAtom.boundary23 a 0) := by
      have hc1 : FourAtom.boundary12 a (x j) ≤ FourAtom.boundary23 a 0 := by
        unfold FourAtom.boundary12 FourAtom.boundary23
        nlinarith [mul_nonneg ha (by linarith [hxj.1] : (0 : ℝ) ≤ 1 + x j)]
      have hc2 : FourAtom.boundary12 a 0 ≤ FourAtom.boundary23 a (x j) := by
        unfold FourAtom.boundary12 FourAtom.boundary23
        nlinarith [mul_nonneg ha (by linarith [hxj.1] : (0 : ℝ) ≤ 1 + x j)]
      exact max_le (le_min h12 hc1) (le_min hc2 h12')
    by_cases h23 : x ∈ D23
    · have h23' : min (FourAtom.boundary23 a (x j)) (FourAtom.boundary23 a 0) < x i ∧
          x i ≤ max (FourAtom.boundary23 a (x j)) (FourAtom.boundary23 a 0) := by
        rw [hD23] at h23
        exact h23
      have hnot12 : x ∉ D12 := by
        intro h12mem
        rw [hD12] at h12mem
        have h12'' : x i ≤ max (FourAtom.boundary12 a (x j)) (FourAtom.boundary12 a 0) :=
          h12mem.2
        linarith [h23'.1]
      have hne : cellIndex i j a 0 x ≠ cellIndex i j a 1 x := by
        rw [e0, e1]
        exact (FourAtom.activeIndex_ne_of_between23 ⟨h01, h12⟩ ⟨h01', h12'⟩
          h23'.1 h23'.2).symm
      rw [Set.indicator_of_mem h23, Set.indicator_of_notMem hnot12, add_zero]
      exact hne_bound hne
    · by_cases h12mem : x ∈ D12
      · have h12'' : min (FourAtom.boundary12 a (x j)) (FourAtom.boundary12 a 0) < x i ∧
            x i ≤ max (FourAtom.boundary12 a (x j)) (FourAtom.boundary12 a 0) := by
          rw [hD12] at h12mem
          exact h12mem
        have hne : cellIndex i j a 0 x ≠ cellIndex i j a 1 x := by
          rw [e0, e1]
          exact (FourAtom.activeIndex_ne_of_between12 h01 h01' h12''.1 h12''.2).symm
        rw [Set.indicator_of_notMem h23, Set.indicator_of_mem h12mem, zero_add]
        exact hne_bound hne
      · rw [Set.indicator_of_notMem h23, Set.indicator_of_notMem h12mem, add_zero]
        exact hf0 x
  -- integrate
  have hg1 : Integrable (D23.indicator fun _ : E d => R ^ 2) ρ :=
    (integrable_const _).indicator hm23
  have hg2 : Integrable (D12.indicator fun _ : E d => R ^ 2) ρ :=
    (integrable_const _).indicator hm12
  have hae : ∀ᵐ x ∂ρ, D23.indicator (fun _ => R ^ 2) x + D12.indicator (fun _ => R ^ 2) x ≤
      f x := by
    rw [hρ]
    filter_upwards [ae_mem_sourceBox i] with x hx
    exact hpoint x hx
  have hint : R ^ 2 * a / 4 ≤ ∫ x, f x ∂ρ := by
    have h1 : (∫ x, D23.indicator (fun _ => R ^ 2) x + D12.indicator (fun _ => R ^ 2) x ∂ρ) ≤
        ∫ x, f x ∂ρ := integral_mono_ae (hg1.add hg2) hfint hae
    rw [integral_add hg1 hg2, integral_indicator_const _ hm23, integral_indicator_const _ hm12,
      hreal23, hreal12, smul_eq_mul] at h1
    linarith
  have hsq : (R * Real.sqrt a / 2) ^ 2 ≤ ∫ x, f x ∂ρ := by
    have e : (R * Real.sqrt a / 2) ^ 2 = R ^ 2 * a / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt ha]
      ring
    rw [e]
    exact hint
  have habs := Real.abs_le_sqrt hsq
  have hmap : mapL2Dist ρ (cellMap i j a R 0) (cellMap i j a R 1) =
      Real.sqrt (∫ x, f x ∂ρ) := by
    rw [hf]
    rfl
  rw [hmap]
  exact (le_abs_self _).trans habs

/-! ### Moments -/

lemma norm_single_eq (k : Fin d) (r : ℝ) : ‖(EuclideanSpace.single k r : E d)‖ = |r| := by
  simp [PiLp.norm_single, Real.norm_eq_abs]

lemma norm_sites_le (i j : Fin d) {R b : ℝ} (hR : 0 ≤ R) (hb : |b| ≤ R) (k : Fin 4) :
    ‖sites i j R b k‖ ≤ 3 * R := by
  fin_cases k
  · change ‖(0 : E d)‖ ≤ 3 * R
    rw [norm_zero]
    linarith
  · change ‖(EuclideanSpace.single i R : E d)‖ ≤ 3 * R
    rw [norm_single_eq, abs_of_nonneg hR]
    linarith
  · change ‖(EuclideanSpace.single i (2 * R) + EuclideanSpace.single j b : E d)‖ ≤ 3 * R
    calc ‖(EuclideanSpace.single i (2 * R) + EuclideanSpace.single j b : E d)‖
        ≤ ‖(EuclideanSpace.single i (2 * R) : E d)‖ + ‖(EuclideanSpace.single j b : E d)‖ :=
          norm_add_le _ _
      _ = 2 * R + |b| := by
          rw [norm_single_eq, norm_single_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * R)]
      _ ≤ 3 * R := by linarith
  · change ‖(EuclideanSpace.single i (3 * R) : E d)‖ ≤ 3 * R
    rw [norm_single_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * R)]

lemma momentWeight_le_of_norm_le {p β r : ℝ} (hp : 0 ≤ p) (hβ : 0 ≤ β) {y : E d}
    (hy : ‖y‖ ≤ r) :
    momentWeight p β y ≤ r ^ p * Real.log (Real.exp 1 + r) ^ β := by
  have hr : 0 ≤ r := (norm_nonneg y).trans hy
  have h1 : ‖y‖ ^ p ≤ r ^ p := Real.rpow_le_rpow (norm_nonneg y) hy hp
  have hlog : Real.log (Real.exp 1 + ‖y‖) ≤ Real.log (Real.exp 1 + r) :=
    Real.log_le_log (by linarith [one_lt_exp_one_add (norm_nonneg y)]) (by linarith)
  have h2 : Real.log (Real.exp 1 + ‖y‖) ^ β ≤ Real.log (Real.exp 1 + r) ^ β :=
    Real.rpow_le_rpow (log_exp_one_add_pos (norm_nonneg y)).le hlog hβ
  unfold momentWeight
  exact mul_le_mul h1 h2 (Real.rpow_nonneg (log_exp_one_add_pos (norm_nonneg y)).le β)
    (Real.rpow_nonneg hr p)

lemma momentWeight_zero {p : ℝ} (hp : 0 < p) (β : ℝ) : momentWeight p β (0 : E d) = 0 := by
  unfold momentWeight
  rw [norm_zero, Real.zero_rpow hp.ne', zero_mul]

/-- The power-logarithmic moment of the four-atom target. -/
theorem lintegral_momentWeight_target_le (i j : Fin d) {a R b p β : ℝ} (ha : 0 ≤ a)
    (hR : 0 ≤ R) (hb : |b| ≤ R) (hp : 0 < p) (hβ : 0 ≤ β) :
    (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂target i j a R b) ≤
      ENNReal.ofReal (3 * a * ((3 * R) ^ p * Real.log (Real.exp 1 + 3 * R) ^ β)) := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = (3 * R) ^ p * Real.log (Real.exp 1 + 3 * R) ^ β := ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by
    rw [hW]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) p)
      (Real.rpow_nonneg (log_exp_one_add_pos (by linarith)).le β)
  have hle : ∀ k : Fin 4, ENNReal.ofReal (momentWeight p β (sites i j R b k)) ≤
      ENNReal.ofReal W := by
    intro k
    rw [hW]
    exact ENNReal.ofReal_le_ofReal
      (momentWeight_le_of_norm_le hp.le hβ (norm_sites_le i j hR hb k))
  have h0 : ENNReal.ofReal (momentWeight p β (sites i j R b 0)) = 0 := by
    change ENNReal.ofReal (momentWeight p β (0 : E d)) = 0
    rw [momentWeight_zero hp, ENNReal.ofReal_zero]
  have hsum : (∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂target i j a R b) =
      ∑ k, FourAtom.weights a k * ENNReal.ofReal (momentWeight p β (sites i j R b k)) := by
    simp [target, lintegral_smul_measure]
  rw [hsum, Fin.sum_univ_four, h0, mul_zero, zero_add, ← hW]
  have hw1 : FourAtom.weights a 1 = ENNReal.ofReal a := rfl
  have hw2 : FourAtom.weights a 2 = ENNReal.ofReal a := rfl
  have hw3 : FourAtom.weights a 3 = ENNReal.ofReal a := rfl
  rw [hw1, hw2, hw3]
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  calc ENNReal.ofReal a * ENNReal.ofReal (momentWeight p β (sites i j R b 1)) +
        ENNReal.ofReal a * ENNReal.ofReal (momentWeight p β (sites i j R b 2)) +
        ENNReal.ofReal a * ENNReal.ofReal (momentWeight p β (sites i j R b 3))
      ≤ ENNReal.ofReal a * ENNReal.ofReal W + ENNReal.ofReal a * ENNReal.ofReal W +
          ENNReal.ofReal a * ENNReal.ofReal W := by
        gcongr
    _ = ENNReal.ofReal (3 * a * W) := by
        rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_add (mul_nonneg ha hW0)
          (mul_nonneg ha hW0), ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg ha hW0) (mul_nonneg ha hW0)) (mul_nonneg ha hW0)]
        congr 1
        ring

end

end BrenierMoment.Sharp
