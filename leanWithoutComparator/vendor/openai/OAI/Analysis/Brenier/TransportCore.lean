module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The finite atomic transport core

The proof bodies below are taken verbatim from Basic, Atomic, Optimality and
Wasserstein in openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
They are compiled together to share the expensive initial Mathlib import.
The original four module paths re-export this module.
-/

/- Upstream file: Basic.lean -/

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def uniformMeasure {d : ℕ} (K : Set (E d)) : Measure (E d) :=
  (volume K)⁻¹ • volume.restrict K

def IsSupported {d : ℕ} (μ : Measure (E d)) (Y : Set (E d)) : Prop :=
  μ (Yᶜ) = 0

def IsCoupling {d : ℕ} (μ ν : Measure (E d))
    (π : Measure (E d × E d)) : Prop :=
  IsProbabilityMeasure π ∧
    Measure.map Prod.fst π = μ ∧
    Measure.map Prod.snd π = ν

def quadraticPlanCost {d : ℕ} (π : Measure (E d × E d)) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (‖p.1 - p.2‖ ^ 2) ∂π

def wasserstein2 {d : ℕ} (μ ν : Measure (E d)) : ℝ :=
  Real.sqrt
    (ENNReal.toReal
      (sInf {r : ℝ≥0∞ |
        ∃ π : Measure (E d × E d),
          IsCoupling μ ν π ∧ quadraticPlanCost π = r}))

def graphPlan {d : ℕ} (ρ : Measure (E d)) (T : E d → E d) :
    Measure (E d × E d) :=
  Measure.map (fun x => (x, T x)) ρ

def IsQuadraticOptimalMap {d : ℕ} (ρ μ : Measure (E d))
    (T : E d → E d) : Prop :=
  Measurable T ∧
    Measure.map T ρ = μ ∧
    ∀ π : Measure (E d × E d),
      IsCoupling ρ μ π →
        quadraticPlanCost (graphPlan ρ T) ≤ quadraticPlanCost π

def IsUniqueQuadraticOptimalMap {d : ℕ} (ρ μ : Measure (E d))
    (T : E d → E d) : Prop :=
  IsQuadraticOptimalMap ρ μ T ∧
    ∀ π : Measure (E d × E d),
      IsCoupling ρ μ π →
        quadraticPlanCost π ≤ quadraticPlanCost (graphPlan ρ T) →
          π = graphPlan ρ T

def mapL2Dist {d : ℕ} (ρ : Measure (E d))
    (T S : E d → E d) : ℝ :=
  Real.sqrt (∫ x, ‖T x - S x‖ ^ 2 ∂ρ)

def cube (d : ℕ) : Set (E d) :=
  {x | ∀ i, |x i| ≤ 1}

def HasExactlyThreeAtoms {d : ℕ} (μ : Measure (E d))
    (Y : Set (E d)) : Prop :=
  ∃ y : Fin 3 → E d, Function.Injective y ∧
    (∀ i, y i ∈ Y) ∧
    ∃ w : Fin 3 → ℝ≥0∞, (∀ i, 0 < w i) ∧
      (∑ i, w i) = 1 ∧
      μ = ∑ i, (w i) • Measure.dirac (y i)

end Problem358

end

end OAI

/- Upstream file: Atomic.lean -/

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Problem358

lemma finite_atomic_probability {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (∑ i, w i • Measure.dirac (y i)) := by
  constructor
  simpa using hw

lemma finite_atomic_supported {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) {Y : Set (E d)}
    (hy : ∀ i, y i ∈ Y) :
    IsSupported (∑ i, w i • Measure.dirac (y i)) Y := by
  classical
  unfold IsSupported
  simp [Measure.finsetSum_apply, Measure.dirac_apply, hy]

lemma HasExactlyThreeAtoms.isProbabilityMeasure {d : ℕ}
    {μ : Measure (E d)} {Y : Set (E d)} (h : HasExactlyThreeAtoms μ Y) :
    IsProbabilityMeasure μ := by
  obtain ⟨y, _, _, w, _, hw, rfl⟩ := h
  exact finite_atomic_probability y w hw

lemma HasExactlyThreeAtoms.isSupported {d : ℕ}
    {μ : Measure (E d)} {Y : Set (E d)} (h : HasExactlyThreeAtoms μ Y) :
    IsSupported μ Y := by
  obtain ⟨y, _, hy, w, _, _, rfl⟩ := h
  exact finite_atomic_supported y w hy

lemma finite_atomic_singleton {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) (hy : Function.Injective y) (i : ι) :
    (∑ j, w j • Measure.dirac (y j)) {y i} = w i := by
  classical
  simp [Measure.finsetSum_apply, Pi.single_apply, hy.eq_iff]

lemma finite_atomic_singleton_of_not_mem {ι : Type*} [Fintype ι] {d : ℕ}
    (y : ι → E d) (w : ι → ℝ≥0∞) {x : E d}
    (hx : x ∉ Set.range y) :
    (∑ j, w j • Measure.dirac (y j)) {x} = 0 := by
  classical
  have hxy : ∀ j, y j ≠ x := by
    intro j hj
    exact hx ⟨j, hj⟩
  simp [Measure.finsetSum_apply, hxy]

lemma finite_atomic_ne_of_missing_atom {ι κ : Type*} [Fintype ι] [Fintype κ]
    {d : ℕ} (y : ι → E d) (z : κ → E d) (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞)
    (hy : Function.Injective y) (i : ι) (hwi : 0 < w i)
    (hi : y i ∉ Set.range z) :
    (∑ j, w j • Measure.dirac (y j)) ≠ ∑ j, v j • Measure.dirac (z j) := by
  intro h
  have he := congrArg (fun μ : Measure (E d) => μ {y i}) h
  rw [finite_atomic_singleton y w hy i,
    finite_atomic_singleton_of_not_mem z v hi] at he
  exact (ne_of_gt hwi) he

end Problem358

namespace Problem358

/-- The coupling which matches equally indexed atoms without splitting mass. -/
def atomicMatchingPlan {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) : Measure (E d × E d) :=
  ∑ i, w i • Measure.dirac (y i, z i)

theorem atomicMatchingPlan_isProbability {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (atomicMatchingPlan w y z) := by
  constructor
  simpa [atomicMatchingPlan, Measure.finsetSum_apply, Measure.smul_apply] using hw

theorem atomicMatchingPlan_fst {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    Measure.map Prod.fst (atomicMatchingPlan w y z) =
      ∑ i, w i • Measure.dirac (y i) := by
  unfold atomicMatchingPlan
  rw [Measure.map_finset_sum measurable_fst.aemeasurable]
  simp only [Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_dirac]

theorem atomicMatchingPlan_snd {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    Measure.map Prod.snd (atomicMatchingPlan w y z) =
      ∑ i, w i • Measure.dirac (z i) := by
  unfold atomicMatchingPlan
  rw [Measure.map_finset_sum measurable_snd.aemeasurable]
  simp only [Measure.map_smul _ measurable_snd.aemeasurable, Measure.map_dirac]

theorem atomicMatchingPlan_isCoupling {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ i, w i • Measure.dirac (z i)) (atomicMatchingPlan w y z) := by
  exact ⟨atomicMatchingPlan_isProbability w y z hw,
    atomicMatchingPlan_fst w y z, atomicMatchingPlan_snd w y z⟩

theorem quadraticPlanCost_atomicMatchingPlan {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) :
    quadraticPlanCost (atomicMatchingPlan w y z) =
      ∑ i, w i * ENNReal.ofReal (‖y i - z i‖ ^ 2) := by
  simp [quadraticPlanCost, atomicMatchingPlan,
    lintegral_smul_measure, lintegral_dirac]

theorem quadraticPlanCost_atomicMatchingPlan_ne_top {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    quadraticPlanCost (atomicMatchingPlan w y z) ≠ ∞ := by
  have hsum : (∑ i, w i) ≠ ∞ := by rw [hw]; exact ENNReal.one_ne_top
  rw [quadraticPlanCost_atomicMatchingPlan]
  exact ENNReal.sum_ne_top.mpr fun i hi =>
    ENNReal.mul_ne_top (ENNReal.sum_ne_top.mp hsum i hi) ENNReal.ofReal_ne_top

/-- Matching equally indexed atoms gives an explicit upper bound for the exact
Wasserstein quantity used in the challenge. -/
theorem wasserstein2_atomic_le {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ≥0∞) (y z : ι → E d) (hw : ∑ i, w i = 1) :
    wasserstein2 (∑ i, w i • Measure.dirac (y i))
      (∑ i, w i • Measure.dirac (z i)) ≤
      Real.sqrt (∑ i, (w i).toReal * ‖y i - z i‖ ^ 2) := by
  have hcost := quadraticPlanCost_atomicMatchingPlan_ne_top w y z hw
  have hsum : (∑ i, w i) ≠ ∞ := by rw [hw]; exact ENNReal.one_ne_top
  have hfinite : ∀ i, w i * ENNReal.ofReal (‖y i - z i‖ ^ 2) ≠ ∞ :=
    fun i => ENNReal.mul_ne_top
      (ENNReal.sum_ne_top.mp hsum i (Finset.mem_univ i)) ENNReal.ofReal_ne_top
  have hreal : (quadraticPlanCost (atomicMatchingPlan w y z)).toReal =
      ∑ i, (w i).toReal * ‖y i - z i‖ ^ 2 := by
    rw [quadraticPlanCost_atomicMatchingPlan, ENNReal.toReal_sum (fun i _ => hfinite i)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rw [← hreal]
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono hcost
  exact sInf_le ⟨atomicMatchingPlan w y z, atomicMatchingPlan_isCoupling w y z hw, rfl⟩

end Problem358

namespace Problem358

/-- A measure concentrated on an injectively indexed finite set is the sum of
its point masses. -/
theorem eq_sum_dirac_of_ae_mem_range {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (μ : Measure X) (y : ι → X)
    (hy : Function.Injective y) (hμ : ∀ᵐ x ∂μ, x ∈ Set.range y) :
    μ = ∑ i, μ {y i} • Measure.dirac (y i) := by
  classical
  have hm : ∀ᵐ x ∂μ, x ∈ Finset.univ.image y := by
    simpa only [Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range] using hμ
  have heq := Measure.ae_mem_finset_iff.mp hm
  rw [Finset.sum_image] at heq
  · exact heq
  · intro a _ b _ hab
    exact hy hab

/-- Every weighted finite atomic measure is concentrated on its listed atoms. -/
theorem ae_mem_range_sum_dirac {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (w : ι → ℝ≥0∞) (y : ι → X) :
    ∀ᵐ x ∂(∑ i, w i • Measure.dirac (y i)), x ∈ Set.range y := by
  rw [ae_finsetSum_measure_iff]
  intro i _
  exact Measure.ae_smul_measure (by simp) _

/-- All mass of a coupling of finite atomic measures is carried by pairs of
listed atoms. -/
theorem IsCoupling.ae_mem_atomic_pairs {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π) :
    ∀ᵐ p ∂π, p ∈ Set.range (fun q : ι × κ => (y q.1, z q.2)) := by
  have hfst : ∀ᵐ p ∂π, p.1 ∈ Set.range y := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    rw [hπ.2.1]
    exact ae_mem_range_sum_dirac w y
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Set.range z := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    rw [hπ.2.2]
    exact ae_mem_range_sum_dirac v z
  filter_upwards [hfst, hsnd] with p hp hq
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hq
  exact ⟨(i,j), Prod.ext hi hj⟩

/-- A coupling of injectively indexed atomic measures has the usual finite
matrix representation. -/
theorem IsCoupling.atomic_decomposition {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    π = ∑ q : ι × κ, π {(y q.1, z q.2)} • Measure.dirac (y q.1, z q.2) := by
  apply eq_sum_dirac_of_ae_mem_range
  · intro a b hab
    exact Prod.ext (hy (congrArg Prod.fst hab)) (hz (congrArg Prod.snd hab))
  · exact hπ.ae_mem_atomic_pairs

theorem finite_atomic_apply_atom {X ι : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [Fintype ι] (w : ι → ℝ≥0∞) (y : ι → X)
    (hy : Function.Injective y) (i : ι) :
    (∑ j, w j • Measure.dirac (y j)) {y i} = w i := by
  classical
  simp [Measure.finsetSum_apply, Measure.smul_apply, Pi.single_apply, hy.eq_iff]

theorem IsCoupling.atomic_row_sum {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (i : ι) :
    ∑ j, π {(y i, z j)} = w i := by
  classical
  have he := congrArg (fun μ : Measure (E d) => μ {y i}) hπ.2.1
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  rw [hd, atomicMatchingPlan_fst] at he
  simpa [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Pi.single_apply, hy.eq_iff, Fintype.sum_prod_type] using he

theorem IsCoupling.atomic_col_sum {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (j : κ) :
    ∑ i, π {(y i, z j)} = v j := by
  classical
  have he := congrArg (fun μ : Measure (E d) => μ {z j}) hπ.2.2
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  rw [hd, atomicMatchingPlan_snd] at he
  simpa [Measure.finsetSum_apply, Measure.smul_apply, Measure.dirac_apply,
    Pi.single_apply, hz.eq_iff, Fintype.sum_prod_type] using he

theorem IsCoupling.atomic_cost {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    quadraticPlanCost π =
      ∑ q : ι × κ, π {(y q.1, z q.2)} * ENNReal.ofReal (‖y q.1 - z q.2‖ ^ 2) := by
  have hd : π = atomicMatchingPlan (fun q : ι × κ => π {(y q.1, z q.2)})
      (fun q => y q.1) (fun q => z q.2) := hπ.atomic_decomposition hy hz
  conv_lhs => rw [hd, quadraticPlanCost_atomicMatchingPlan]

theorem atomicMatchingPlan_isCoupling_of_marginal_sums
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (p : ι × κ → ℝ≥0∞)
    (y : ι → E d) (z : κ → E d) (hw : ∑ i, w i = 1)
    (hrow : ∀ i, ∑ j, p (i,j) = w i) (hcol : ∀ j, ∑ i, p (i,j) = v j) :
    IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j))
      (atomicMatchingPlan p (fun q => y q.1) (fun q => z q.2)) := by
  have hp : ∑ q, p q = 1 := by
    rw [Fintype.sum_prod_type]
    simpa only [hrow] using hw
  refine ⟨atomicMatchingPlan_isProbability _ _ _ hp, ?_, ?_⟩
  · rw [atomicMatchingPlan_fst, Fintype.sum_prod_type]
    simp_rw [← Finset.sum_smul, hrow]
  · rw [atomicMatchingPlan_snd, Fintype.sum_prod_type_right]
    simp_rw [← Finset.sum_smul, hcol]

theorem IsCoupling.atomic_row_sum_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (i : ι) :
    ∑ j, (π {(y i, z j)}).toReal = (w i).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top π _)]
  exact congrArg ENNReal.toReal (hπ.atomic_row_sum hy hz i)

theorem IsCoupling.atomic_col_sum_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) (j : κ) :
    ∑ i, (π {(y i, z j)}).toReal = (v j).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  rw [← ENNReal.toReal_sum (fun i _ => measure_ne_top π _)]
  exact congrArg ENNReal.toReal (hπ.atomic_col_sum hy hz j)

theorem IsCoupling.atomic_cost_ne_top {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    quadraticPlanCost π ≠ ∞ := by
  let : IsProbabilityMeasure π := hπ.1
  rw [hπ.atomic_cost hy hz]
  exact ENNReal.sum_ne_top.mpr fun q _ =>
    ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top

theorem IsCoupling.atomic_cost_toReal {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {w : ι → ℝ≥0∞} {v : κ → ℝ≥0∞} {y : ι → E d} {z : κ → E d}
    {π : Measure (E d × E d)}
    (hπ : IsCoupling (∑ i, w i • Measure.dirac (y i))
      (∑ j, v j • Measure.dirac (z j)) π)
    (hy : Function.Injective y) (hz : Function.Injective z) :
    (quadraticPlanCost π).toReal =
      ∑ q : ι × κ, (π {(y q.1, z q.2)}).toReal * ‖y q.1 - z q.2‖ ^ 2 := by
  let : IsProbabilityMeasure π := hπ.1
  rw [hπ.atomic_cost hy hz, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  · intro q _
    exact ENNReal.mul_ne_top (measure_ne_top π _) ENNReal.ofReal_ne_top

end Problem358

end

end OAI

/- Upstream file: Optimality.lean -/

namespace OAI

section

open MeasureTheory

namespace Problem358

/-- A measure concentrated on the graph of a measurable function is determined
by its first marginal. This is the last step in uniqueness of a transport plan. -/
theorem eq_graph_map_of_ae_on_graph
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (π : Measure (X × Y)) {T : X → Y} (hT : Measurable T)
    (hgraph : ∀ᵐ p ∂π, p.2 = T p.1) :
    π = Measure.map (fun x => (x, T x)) (Measure.map Prod.fst π) := by
  have hm : Measurable (fun x : X => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map hm measurable_fst]
  calc
    π = Measure.map id π := (Measure.map_id).symm
    _ = Measure.map ((fun x => (x, T x)) ∘ Prod.fst) π := by
      apply Measure.map_congr
      filter_upwards [hgraph] with p hp
      exact Prod.ext rfl hp

/-- The same reconstruction statement with an explicitly prescribed marginal. -/
theorem eq_graph_map_of_fst_eq_and_ae_on_graph
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {π : Measure (X × Y)} {ρ : Measure X} {T : X → Y}
    (hT : Measurable T) (hfst : Measure.map Prod.fst π = ρ)
    (hgraph : ∀ᵐ p ∂π, p.2 = T p.1) :
    π = Measure.map (fun x => (x, T x)) ρ := by
  rw [← hfst]
  exact eq_graph_map_of_ae_on_graph π hT hgraph

end Problem358

end

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ : Measure (E d)} {π : Measure (E d × E d)}

/-- A finite quadratic plan cost is an ordinary integrable squared distance. -/
theorem integrable_sqdist_of_cost_ne_top
    (h : quadraticPlanCost π ≠ ∞) :
    Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop) (Filter.Eventually.of_forall fun p => sq_nonneg _)).mp
  exact h

/-- Conversion between the extended and real quadratic costs. -/
theorem quadraticPlanCost_eq_ofReal_integral
    (h : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π) :
    quadraticPlanCost π = ENNReal.ofReal (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) := by
  exact (ofReal_integral_eq_lintegral_ofReal h
    (Filter.Eventually.of_forall fun p => sq_nonneg _)).symm

/-- Integrability of a separable dual potential under any coupling. -/
theorem dual_integrable_sum (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ) :
    Integrable (fun p : E d × E d => f p.1 + g p.2) π := by
  have hf' : Integrable f (Measure.map Prod.fst π) := hπ.2.1.symm ▸ hf
  have hg' : Integrable g (Measure.map Prod.snd π) := hπ.2.2.symm ▸ hg
  exact (hf'.comp_measurable measurable_fst).add
    (hg'.comp_measurable measurable_snd)

/-- The integral of a separable dual potential depends only on the marginals. -/
theorem dual_integral_sum (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ) :
    (∫ p, f p.1 + g p.2 ∂π) = (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
  have hf' : Integrable f (Measure.map Prod.fst π) := hπ.2.1.symm ▸ hf
  have hg' : Integrable g (Measure.map Prod.snd π) := hπ.2.2.symm ▸ hg
  have hfi : Integrable (fun p : E d × E d => f p.1) π := hf'.comp_measurable measurable_fst
  have hgi : Integrable (fun p : E d × E d => g p.2) π := hg'.comp_measurable measurable_snd
  rw [integral_add hfi hgi]
  rw [← integral_map measurable_fst.aemeasurable hf'.aestronglyMeasurable,
    ← integral_map measurable_snd.aemeasurable hg'.aestronglyMeasurable,
    hπ.2.1, hπ.2.2]

/-- Weak Kantorovich duality for the problem's quadratic cost definition. -/
theorem dual_cost_lower_bound (hπ : IsCoupling ρ μ π)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2) :
    ENNReal.ofReal ((∫ x, f x ∂ρ) + ∫ y, g y ∂μ) ≤ quadraticPlanCost π := by
  by_cases htop : quadraticPlanCost π = ∞
  · simp [htop]
  have hc := integrable_sqdist_of_cost_ne_top htop
  rw [quadraticPlanCost_eq_ofReal_integral hc,
    ← dual_integral_sum hπ hf hg]
  exact ENNReal.ofReal_le_ofReal (integral_mono_ae (dual_integrable_sum hπ hf hg) hc hbound)

/-- A graph saturating a separable dual bound has exactly the dual cost. -/
theorem quadraticPlanCost_graph_eq_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    quadraticPlanCost (graphPlan ρ T) =
      ENNReal.ofReal ((∫ x, f x ∂ρ) + ∫ y, g y ∂μ) := by
  have hg' : Integrable g (Measure.map T ρ) := hpush.symm ▸ hg
  have hgT : Integrable (fun x => g (T x)) ρ := hg'.comp_measurable hT
  have hc : Integrable (fun x => ‖x - T x‖ ^ 2) ρ := (hf.add hgT).congr (heq.mono fun x hx => hx.symm)
  unfold quadraticPlanCost graphPlan
  have hm : Measurable (fun x : E d => (x, T x)) := by fun_prop
  rw [lintegral_map (by fun_prop) hm]
  change (∫⁻ x, ENNReal.ofReal (‖x - T x‖ ^ 2) ∂ρ) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hc
    (Filter.Eventually.of_forall fun x => sq_nonneg _), integral_congr_ae heq,
    integral_add hf hgT, ← integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    hpush]

/-- Dual attainment certifies optimality against every probability coupling. -/
theorem isQuadraticOptimalMap_of_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    IsQuadraticOptimalMap ρ μ T := by
  refine ⟨hT, hpush, fun π hπ => ?_⟩
  rw [quadraticPlanCost_graph_eq_dual hT hpush hf hg heq]
  exact dual_cost_lower_bound hπ hf hg (hbound π hπ)

end Problem358

end

noncomputable section

open MeasureTheory

namespace Problem358

/-- There is only one coupling with a fixed first marginal and a Dirac second marginal. -/
theorem coupling_dirac_eq_graphPlan_const {d : ℕ} {ρ : Measure (E d)}
    {π : Measure (E d × E d)} {y : E d}
    (hπ : IsCoupling ρ (Measure.dirac y) π) :
    π = graphPlan ρ (fun _ => y) := by
  apply eq_graph_map_of_fst_eq_and_ae_on_graph measurable_const hπ.2.1
  apply ae_of_ae_map (μ := π) (p := fun z => z = y) measurable_snd.aemeasurable
  rw [hπ.2.2]
  simp

/-- The constant map to a point is the unique quadratic optimal map to its Dirac law.
No moment assumption is necessary: every competing coupling is already the same graph. -/
theorem isUniqueQuadraticOptimalMap_const {d : ℕ} (ρ : Measure (E d))
    [IsProbabilityMeasure ρ] (y : E d) :
    IsUniqueQuadraticOptimalMap ρ (Measure.dirac y) (fun _ => y) := by
  constructor
  · refine ⟨measurable_const, ?_, ?_⟩
    · simp [Measure.map_const]
    · intro π hπ
      rw [coupling_dirac_eq_graphPlan_const hπ]
  · intro π hπ _
    exact coupling_dirac_eq_graphPlan_const hπ

/-- A probability measure supported on a singleton is the corresponding Dirac law. -/
theorem eq_dirac_of_supported_singleton {d : ℕ} (μ : Measure (E d))
    [IsProbabilityMeasure μ] (y : E d) (hμ : IsSupported μ {y}) :
    μ = Measure.dirac y := by
  have hae : ∀ᵐ x ∂μ, x = y := by
    exact ae_iff.mpr hμ
  calc
    μ = Measure.map id μ := Measure.map_id.symm
    _ = Measure.map (fun _ => y) μ := Measure.map_congr hae
    _ = Measure.dirac y := by simp [Measure.map_const]

/-- The same conclusion holds for any nonempty subsingleton support set. -/
theorem eq_dirac_of_supported_subsingleton {d : ℕ} (μ : Measure (E d))
    [IsProbabilityMeasure μ] {Y : Set (E d)} (hY : Y.Subsingleton)
    {y : E d} (hy : y ∈ Y) (hμ : IsSupported μ Y) :
    μ = Measure.dirac y := by
  apply eq_dirac_of_supported_singleton μ y
  have hae : ∀ᵐ x ∂μ, x ∈ Y := ae_iff.mpr hμ
  apply ae_iff.mp
  filter_upwards [hae] with x hx
  exact hY hx hy

/-- The singleton-target case of stability, for an arbitrary probability source. -/
theorem one_third_stability_of_subsingleton_target {d : ℕ}
    (ρ : Measure (E d)) [IsProbabilityMeasure ρ]
    {Y : Set (E d)} (hY : Y.Subsingleton) (hYn : Y.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (μ ν : Measure (E d)),
      IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      IsSupported μ Y → IsSupported ν Y →
      ∃ Tμ Tν : E d → E d,
        IsUniqueQuadraticOptimalMap ρ μ Tμ ∧
        IsUniqueQuadraticOptimalMap ρ ν Tν ∧
        mapL2Dist ρ Tμ Tν ≤ C * Real.rpow (wasserstein2 μ ν) (1 / 3 : ℝ) := by
  obtain ⟨y, hy⟩ := hYn
  refine ⟨0, le_rfl, ?_⟩
  intro μ ν hμ hν hμY hνY
  let := hμ
  let := hν
  rw [eq_dirac_of_supported_subsingleton μ hY hy hμY,
    eq_dirac_of_supported_subsingleton ν hY hy hνY]
  refine ⟨fun _ => y, fun _ => y, isUniqueQuadraticOptimalMap_const ρ y,
    isUniqueQuadraticOptimalMap_const ρ y, ?_⟩
  simp [mapL2Dist]

end Problem358

end

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ} {ρ μ : Measure (E d)} {π : Measure (E d × E d)}

/-- Equality in the integral dual bound forces saturation almost everywhere. -/
theorem dual_saturation_of_integral_eq
    (hπ : IsCoupling ρ μ π) {f g : E d → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g μ)
    (hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ) :
    ∀ᵐ p ∂π, f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 := by
  apply (integral_eq_iff_of_ae_le (dual_integrable_sum hπ hf hg) hc hbound).mp
  rw [dual_integral_sum hπ hf hg]
  exact heq.symm

/-- A saturated dual bound whose equality locus is a graph identifies the full plan. -/
theorem eq_graphPlan_of_dual_saturation
    {T : E d → E d} (hT : Measurable T)
    (hπ : IsCoupling ρ μ π) {f g : E d → ℝ}
    (hf : Integrable f ρ) (hg : Integrable g μ)
    (hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π)
    (hbound : ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ)
    (hstrict : ∀ᵐ p ∂π,
      f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1) :
    π = graphPlan ρ T := by
  apply eq_graph_map_of_fst_eq_and_ae_on_graph hT hπ.2.1
  filter_upwards [dual_saturation_of_integral_eq hπ hf hg hc hbound heq,
    hstrict] with p hp hs
  exact hs hp

/-- A dual value attained by a graph is nonnegative. -/
theorem dual_value_nonneg_of_graph
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x)) :
    0 ≤ (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
  have hg' : Integrable g (Measure.map T ρ) := hpush.symm ▸ hg
  have hgT : Integrable (fun x => g (T x)) ρ := hg'.comp_measurable hT
  rw [← hpush, integral_map hT.aemeasurable hg'.aestronglyMeasurable,
    ← integral_add hf hgT]
  apply integral_nonneg_of_ae
  filter_upwards [heq] with x hx
  rw [← hx]
  exact sq_nonneg _

/-- Strictness of a dual certificate identifies every optimal plan with its graph.
The strictness premise is only required almost everywhere for each coupling, so
null tie sets and support restrictions can be used directly. -/
theorem isUniqueQuadraticOptimalMap_of_dual
    {T : E d → E d} (hT : Measurable T) (hpush : Measure.map T ρ = μ)
    {f g : E d → ℝ} (hf : Integrable f ρ) (hg : Integrable g μ)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 ≤ ‖p.1 - p.2‖ ^ 2)
    (heq : ∀ᵐ x ∂ρ, ‖x - T x‖ ^ 2 = f x + g (T x))
    (hstrict : ∀ π : Measure (E d × E d), IsCoupling ρ μ π →
      ∀ᵐ p ∂π, f p.1 + g p.2 = ‖p.1 - p.2‖ ^ 2 → p.2 = T p.1) :
    IsUniqueQuadraticOptimalMap ρ μ T := by
  have hopt := isQuadraticOptimalMap_of_dual hT hpush hf hg hbound heq
  refine ⟨hopt, fun π hπ hle => ?_⟩
  have hgraph := quadraticPlanCost_graph_eq_dual hT hpush hf hg heq
  have hfinite : quadraticPlanCost π ≠ ∞ := by
    apply ne_top_of_le_ne_top _ hle
    rw [hgraph]
    exact ENNReal.ofReal_ne_top
  have hc := integrable_sqdist_of_cost_ne_top hfinite
  have hcosteq : quadraticPlanCost π = quadraticPlanCost (graphPlan ρ T) :=
    le_antisymm hle (hopt.2.2 π hπ)
  have hvalue := dual_value_nonneg_of_graph hT hpush hf hg heq
  have hint : (∫ p, ‖p.1 - p.2‖ ^ 2 ∂π) =
      (∫ x, f x ∂ρ) + ∫ y, g y ∂μ := by
    have hh := (quadraticPlanCost_eq_ofReal_integral hc).symm.trans
      (hcosteq.trans hgraph)
    have hn : 0 ≤ ∫ p : E d × E d, ‖p.1 - p.2‖ ^ 2 ∂π :=
      integral_nonneg (fun p => sq_nonneg _)
    simpa only [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal hvalue] using
      congrArg ENNReal.toReal hh
  exact eq_graphPlan_of_dual_saturation hT hπ hf hg hc (hbound π hπ)
    hint (hstrict π hπ)

end Problem358

end

end OAI

/- Upstream file: Wasserstein.lean -/

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ}

/-- The real-valued transport distance is nonnegative. -/
theorem wasserstein2_nonneg (μ ν : Measure (E d)) :
    0 ≤ wasserstein2 μ ν :=
  Real.sqrt_nonneg _

/-- Any finite-cost coupling supplies an upper bound for the transport distance. -/
theorem wasserstein2_le_of_coupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hfin : quadraticPlanCost π ≠ ∞) :
    wasserstein2 μ ν ≤ Real.sqrt (quadraticPlanCost π).toReal := by
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono hfin
  exact sInf_le ⟨π, hπ, rfl⟩

/-- A coupling which minimizes the extended cost computes the defined distance. -/
theorem wasserstein2_eq_of_minimizing_coupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hmin : ∀ π', IsCoupling μ ν π' → quadraticPlanCost π ≤ quadraticPlanCost π') :
    wasserstein2 μ ν = Real.sqrt (quadraticPlanCost π).toReal := by
  have hinf : sInf {r : ℝ≥0∞ | ∃ π' : Measure (E d × E d),
      IsCoupling μ ν π' ∧ quadraticPlanCost π' = r} = quadraticPlanCost π := by
    apply le_antisymm
    · exact sInf_le ⟨π, hπ, rfl⟩
    · apply le_sInf
      rintro r ⟨π', hπ', rfl⟩
      exact hmin π' hπ'
  unfold wasserstein2
  rw [hinf]

private theorem swap_isCoupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π) :
    IsCoupling ν μ (π.map Prod.swap) := by
  have : IsProbabilityMeasure π := hπ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact hπ.2.2
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact hπ.2.1

/-- Swapping both variables in a plan preserves quadratic cost. -/
theorem quadraticPlanCost_swap (π : Measure (E d × E d)) :
    quadraticPlanCost (π.map Prod.swap) = quadraticPlanCost π := by
  unfold quadraticPlanCost
  rw [lintegral_map (by fun_prop) measurable_swap]
  congr 1
  funext p
  dsimp only [Prod.swap]
  rw [norm_sub_rev]

/-- The transport distance is symmetric, including for arbitrary input measures. -/
theorem wasserstein2_symm (μ ν : Measure (E d)) :
    wasserstein2 μ ν = wasserstein2 ν μ := by
  have hset : {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π = r} =
      {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
      IsCoupling ν μ π ∧ quadraticPlanCost π = r} := by
    ext r
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨π.map Prod.swap, swap_isCoupling hπ, quadraticPlanCost_swap π⟩
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨π.map Prod.swap, swap_isCoupling hπ, quadraticPlanCost_swap π⟩
  unfold wasserstein2
  rw [hset]

/-- Every probability measure has zero distance from itself. -/
theorem wasserstein2_self (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    wasserstein2 μ μ = 0 := by
  let π : Measure (E d × E d) := μ.map (fun x => (x, x))
  have hmeas : Measurable (fun x : E d => (x, x)) := measurable_id.prodMk measurable_id
  have hπ : IsCoupling μ μ π := by
    refine ⟨inferInstance, ?_, ?_⟩
    · change (μ.map (fun x => (x, x))).map Prod.fst = μ
      rw [Measure.map_map measurable_fst hmeas]
      exact Measure.map_id
    · change (μ.map (fun x => (x, x))).map Prod.snd = μ
      rw [Measure.map_map measurable_snd hmeas]
      exact Measure.map_id
  have hcost : quadraticPlanCost π = 0 := by
    unfold quadraticPlanCost π
    rw [lintegral_map (by fun_prop) hmeas]
    simp
  apply le_antisymm
  · have h := wasserstein2_le_of_coupling hπ (by rw [hcost]; exact ENNReal.zero_ne_top)
    simpa [hcost] using h
  · exact wasserstein2_nonneg μ μ

/-- The infimum defining `wasserstein2` can be approximated by finite-cost plans.
This does not require existence of an optimal coupling. -/
theorem exists_coupling_sqrt_cost_lt {μ ν : Measure (E d)}
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧
      quadraticPlanCost π ≠ ∞ ∧
      Real.sqrt (quadraticPlanCost π).toReal < wasserstein2 μ ν + ε := by
  let c : ℝ≥0∞ := sInf {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
    IsCoupling μ ν π ∧ quadraticPlanCost π = r}
  have hcfinite : c ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (sInf_le ⟨π₀, hπ₀, rfl⟩)
  have hc : c < ENNReal.ofReal ((wasserstein2 μ ν + ε) ^ 2) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hcfinite).2
    change c.toReal < (Real.sqrt c.toReal + ε) ^ 2
    have hsqrt := Real.sq_sqrt (ENNReal.toReal_nonneg (a := c))
    have hnonneg := Real.sqrt_nonneg c.toReal
    nlinarith
  obtain ⟨r, ⟨π, hπ, hcost⟩, hr⟩ := sInf_lt_iff.mp hc
  have hlt : quadraticPlanCost π < ENNReal.ofReal ((wasserstein2 μ ν + ε) ^ 2) := by
    rwa [hcost]
  refine ⟨π, hπ, hlt.ne_top, ?_⟩
  apply (Real.sqrt_lt' (add_pos_of_nonneg_of_pos (wasserstein2_nonneg μ ν) hε)).2
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

end Problem358

namespace Problem358

/-- A single Euclidean coordinate is dominated by the Euclidean norm. -/
lemma coordinate_sq_le_norm_sq {d : ℕ} (x : E d) (j : Fin d) :
    (x j) ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := PiLp.norm_apply_le x j
  have hsq := pow_le_pow_left₀ (norm_nonneg (x j)) h 2
  simpa only [Real.norm_eq_abs, sq_abs] using hsq

/-- If the source coordinate vanishes, displacement controls the target coordinate. -/
lemma coordinate_sq_le_displacement_sq {d : ℕ} (x y : E d) (j : Fin d)
    (hx : x j = 0) :
    (y j) ^ 2 ≤ ‖x - y‖ ^ 2 := by
  simpa [hx] using coordinate_sq_le_norm_sq (x - y) j

/-- Every coupling pays at least the target coordinate second moment when the
source is concentrated on the zero coordinate hyperplane. -/
lemma coordinate_moment_le_quadraticPlanCost {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π) :
    (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) ≤ quadraticPlanCost π := by
  have hsource : ∀ᵐ p ∂π, p.1 j = 0 := by
    have hμ' : ∀ᵐ x ∂Measure.map Prod.fst π, x j = 0 := by
      simpa only [hπ.2.1] using hμ
    exact ae_of_ae_map measurable_fst.aemeasurable hμ'
  rw [← hπ.2.2, lintegral_map (by fun_prop) measurable_snd]
  apply lintegral_mono_ae
  filter_upwards [hsource] with p hp
  exact ENNReal.ofReal_le_ofReal (coordinate_sq_le_displacement_sq p.1 p.2 j hp)

/-- The same lower bound passes to the infimum of all coupling costs. -/
lemma coordinate_moment_le_sInf_cost {d : ℕ}
    {μ ν : Measure (E d)} (j : Fin d) (hμ : ∀ᵐ x ∂μ, x j = 0) :
    (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) ≤
      sInf {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
        IsCoupling μ ν π ∧ quadraticPlanCost π = r} := by
  apply le_sInf
  rintro r ⟨π, hπ, rfl⟩
  exact coordinate_moment_le_quadraticPlanCost j hμ hπ

/-- A finite-cost coupling makes the coordinate-moment bound valid after taking
`toReal` and square roots. The finiteness hypothesis is essential because
`ENNReal.toReal ∞ = 0`. -/
lemma sqrt_coordinate_moment_le_wasserstein2 {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π)
    (hfinite : quadraticPlanCost π < ∞) :
    Real.sqrt (ENNReal.toReal (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν)) ≤
      wasserstein2 μ ν := by
  unfold wasserstein2
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono _ (coordinate_moment_le_sInf_cost j hμ)
  apply ne_of_lt
  refine lt_of_le_of_lt ?_ hfinite
  exact sInf_le ⟨π, hπ, rfl⟩

/-- A coupling attaining the coordinate lower bound computes the Wasserstein
quantity exactly; in particular this applies to the central-atom matching plan. -/
lemma wasserstein2_eq_sqrt_coordinate_moment {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π)
    (hcost : quadraticPlanCost π = ∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) :
    wasserstein2 μ ν =
      Real.sqrt (ENNReal.toReal (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν)) := by
  unfold wasserstein2
  congr 2
  apply le_antisymm
  · exact sInf_le ⟨π, hπ, hcost⟩
  · exact coordinate_moment_le_sInf_cost j hμ

/-- A positive target coordinate moment separates the measures in Wasserstein
quantity whenever a finite-cost coupling exists. -/
lemma wasserstein2_pos_of_coordinate_moment_pos {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π)
    (hfinite : quadraticPlanCost π < ∞)
    (hpos : 0 < ∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) :
    0 < wasserstein2 μ ν := by
  have hmfinite : (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) < ∞ :=
    lt_of_le_of_lt (coordinate_moment_le_quadraticPlanCost j hμ hπ) hfinite
  have hmpos : 0 < ENNReal.toReal (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) :=
    ENNReal.toReal_pos hpos.ne' hmfinite.ne
  exact lt_of_lt_of_le (Real.sqrt_pos.2 hmpos)
    (sqrt_coordinate_moment_le_wasserstein2 j hμ hπ hfinite)

end Problem358

end

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem358

/-- The second-moment inequality for a real random variable on a probability space. -/
theorem testing_integral_sq_le {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} [IsProbabilityMeasure ρ] {f : X → ℝ} (hf : MemLp f 2 ρ) :
    (∫ x, f x ∂ρ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂ρ := by
  have h := ProbabilityTheory.variance_nonneg f ρ
  rw [ProbabilityTheory.variance_eq_sub hf] at h
  exact sub_nonneg.mp h

/-- A finite-cost coupling controls the difference of Lipschitz test integrals. -/
theorem integral_test_le_sqrt_cost {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hc : quadraticPlanCost π ≠ ∞) {L : ℝ≥0} {f : E d → ℝ}
    (hf : LipschitzWith L f) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    |(∫ x, f x ∂μ) - ∫ y, f y ∂ν| ≤
      L * Real.sqrt (quadraticPlanCost π).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  have hd2 := integrable_sqdist_of_cost_ne_top hc
  have hdLp : MemLp (fun p : E d × E d => ‖p.1 - p.2‖) 2 π :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hd2
  have hd : Integrable (fun p : E d × E d => ‖p.1 - p.2‖) π :=
    hdLp.integrable (by norm_num)
  have hmean : (∫ p : E d × E d, ‖p.1 - p.2‖ ∂π) ≤
      Real.sqrt (quadraticPlanCost π).toReal := by
    have hsq := testing_integral_sq_le hdLp
    rw [quadraticPlanCost_eq_ofReal_integral hd2, ENNReal.toReal_ofReal
      (integral_nonneg fun p => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hsq
  have hdiff : Integrable (fun p : E d × E d => f p.1 - f p.2) π := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using dual_integrable_sum hπ hfμ hfν.neg
  have heq : (∫ p : E d × E d, f p.1 - f p.2 ∂π) =
      (∫ x, f x ∂μ) - ∫ y, f y ∂ν := by
    simpa only [sub_eq_add_neg, Pi.neg_apply, integral_neg] using dual_integral_sum hπ hfμ hfν.neg
  rw [← heq, ← Real.norm_eq_abs]
  calc
    ‖∫ p : E d × E d, f p.1 - f p.2 ∂π‖ ≤
        ∫ p : E d × E d, ‖f p.1 - f p.2‖ ∂π := norm_integral_le_integral_norm _
    _ ≤ ∫ p : E d × E d, (L : ℝ) * ‖p.1 - p.2‖ ∂π :=
      integral_mono hdiff.norm (hd.const_mul _) (fun p => by
        simpa only [dist_eq_norm] using hf.dist_le_mul p.1 p.2)
    _ = (L : ℝ) * ∫ p : E d × E d, ‖p.1 - p.2‖ ∂π := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean L.coe_nonneg

/-- A nonnegative square-root lower bound passes to the infimum of extended costs. -/
theorem testing_sqrt_sInf_bound (S : Set ℝ≥0∞)
    (hfinite : ∃ r ∈ S, r ≠ ∞) {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hbound : ∀ r ∈ S, r ≠ ∞ → D ≤ L * Real.sqrt r.toReal) :
    D ≤ L * Real.sqrt (sInf S).toReal := by
  obtain ⟨r₀, hr₀, hfin₀⟩ := hfinite
  by_cases hzero : L = 0
  · simpa only [hzero, zero_mul] using hbound r₀ hr₀ hfin₀
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
  have hSfinite : sInf S ≠ ∞ :=
    (lt_of_le_of_lt (sInf_le hr₀) (lt_top_iff_ne_top.mpr hfin₀)).ne
  have hlower : ENNReal.ofReal ((D / L) ^ 2) ≤ sInf S := by
    apply le_sInf
    intro r hr
    by_cases hrTop : r = ∞
    · simp only [hrTop, le_top]
    have hdiv : D / L ≤ Real.sqrt r.toReal :=
      (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm] using hbound r hr hrTop)
    apply ENNReal.ofReal_le_of_le_toReal
    exact (Real.le_sqrt (div_nonneg hD hL) ENNReal.toReal_nonneg).mp hdiv
  have hsq : (D / L) ^ 2 ≤ (sInf S).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hSfinite).mp hlower
  have h := (div_le_iff₀ hLpos).mp (Real.le_sqrt_of_sq_le hsq)
  simpa only [mul_comm] using h

/-- Lipschitz testing is controlled by the problem's Wasserstein distance whenever a
finite-cost coupling exists. Compact support is not required in this interface. -/
theorem integral_test_le_wasserstein2 {d : ℕ} {μ ν : Measure (E d)}
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    {L : ℝ≥0} {f : E d → ℝ} (hf : LipschitzWith L f)
    (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    |(∫ x, f x ∂μ) - ∫ y, f y ∂ν| ≤ L * wasserstein2 μ ν := by
  unfold wasserstein2
  refine testing_sqrt_sInf_bound _ ?_ (abs_nonneg _) L.coe_nonneg ?_
  · obtain ⟨π, hπ, hc⟩ := hfinite
    exact ⟨quadraticPlanCost π, ⟨π, hπ, rfl⟩, hc⟩
  · intro r hr hfin
    obtain ⟨π, hπ, rfl⟩ := hr
    exact integral_test_le_sqrt_cost hπ hfin hf hfμ hfν

/-- A zero-Wasserstein pair agrees on every integrable Lipschitz test. -/
theorem integral_test_eq_of_wasserstein2_eq_zero {d : ℕ} {μ ν : Measure (E d)}
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    (hzero : wasserstein2 μ ν = 0) {L : ℝ≥0} {f : E d → ℝ}
    (hf : LipschitzWith L f) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    (∫ x, f x ∂μ) = ∫ y, f y ∂ν := by
  have h := integral_test_le_wasserstein2 hfinite hf hfμ hfν
  rw [hzero, mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Wasserstein convergence with finite-cost couplings implies weak convergence. -/
theorem tendsto_probabilityMeasure_of_wasserstein2_tendsto_zero
    {d : ℕ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure (E d)} {ν : ProbabilityMeasure (E d)}
    (hfinite : ∀ i, ∃ π : Measure (E d × E d),
      IsCoupling (μs i : Measure (E d)) (ν : Measure (E d)) π ∧ quadraticPlanCost π ≠ ∞)
    (hW : Tendsto (fun i => wasserstein2 (μs i : Measure (E d)) (ν : Measure (E d))) l (𝓝 0)) :
    Tendsto μs l (𝓝 ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hb hLip
  obtain ⟨L, hf⟩ := hLip
  let g : BoundedContinuousFunction (E d) ℝ :=
    { toFun := f
      continuous_toFun := hf.continuous
      map_bounded' := hb }
  have hfμ (i : ι) : Integrable f (μs i : Measure (E d)) := g.integrable (μ := (μs i : Measure (E d)))
  have hfν : Integrable f (ν : Measure (E d)) := g.integrable (μ := (ν : Measure (E d)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i => (L : ℝ) *
    wasserstein2 (μs i : Measure (E d)) (ν : Measure (E d)))
    (fun _ => norm_nonneg _) (fun i => ?_) ?_
  · simpa only [Real.norm_eq_abs] using
      integral_test_le_wasserstein2 (hfinite i) hf (hfμ i) hfν
  · simpa only [mul_zero] using hW.const_mul (L : ℝ)

/-- Finite-cost probability measures at zero Wasserstein distance are equal. -/
theorem measure_eq_of_wasserstein2_eq_zero {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    (hzero : wasserstein2 μ ν = 0) : μ = ν := by
  let μp : ProbabilityMeasure (E d) := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure (E d) := ⟨ν, inferInstance⟩
  have hconv : Tendsto (fun _ : ℕ => μp) atTop (𝓝 νp) := by
    apply tendsto_probabilityMeasure_of_wasserstein2_tendsto_zero (fun _ => hfinite)
    change Tendsto (fun _ : ℕ => wasserstein2 μ ν) atTop (𝓝 0)
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have heq : μp = νp := tendsto_nhds_unique tendsto_const_nhds hconv
  exact congrArg (fun p : ProbabilityMeasure (E d) => (p : Measure (E d))) heq

/-- Distinct probabilities with a finite-cost coupling have positive Wasserstein distance. -/
theorem wasserstein2_pos_of_ne_of_finite_coupling {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞) (hne : μ ≠ ν) :
    0 < wasserstein2 μ ν := by
  apply lt_of_le_of_ne (Real.sqrt_nonneg _)
  intro hzero
  exact hne (measure_eq_of_wasserstein2_eq_zero hfinite hzero.symm)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem358

variable {d : ℕ}

/-- A continuous nondecreasing function of root cost commutes with the transport
infimum for purposes of universal lower estimates. No minimizing plan is required. -/
theorem le_of_le_all_coupling_sqrt_cost {μ ν : Measure (E d)}
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {F : ℝ → ℝ}
    (hmono : MonotoneOn F (Set.Ici 0))
    (hcont : ContinuousAt F (wasserstein2 μ ν)) {a : ℝ}
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ → a ≤ F (Real.sqrt (quadraticPlanCost π).toReal)) :
    a ≤ F (wasserstein2 μ ν) := by
  have hlim : Tendsto (fun ε : ℝ => F (wasserstein2 μ ν + ε))
      (𝓝[>] 0) (𝓝 (F (wasserstein2 μ ν))) := by
    apply hcont.tendsto.comp
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun ε : ℝ => wasserstein2 μ ν + ε) (𝓝[>] 0)
        (𝓝 (wasserstein2 μ ν + 0)))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨π, hπ, hfin, hlt⟩ := exists_coupling_sqrt_cost_lt hπ₀ hfinite hε
  exact (hbound π hπ hfin).trans (hmono (Real.sqrt_nonneg _)
    (add_nonneg (wasserstein2_nonneg μ ν) hε.le) hlt.le)

/-- Power-type estimates valid for every finite-cost coupling descend to the
exact transport distance, including at zero distance. -/
theorem le_mul_rpow_wasserstein2_of_coupling_bound {μ ν : Measure (E d)}
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {a C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ →
      a ≤ C * Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) α) :
    a ≤ C * Real.rpow (wasserstein2 μ ν) α := by
  apply le_of_le_all_coupling_sqrt_cost hπ₀ hfinite (F := fun x => C * x ^ α)
  · intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy hα) hC
  · exact (continuous_const.mul (Real.continuous_rpow_const hα)).continuousAt
  · exact hbound

end Problem358

end

end OAI
