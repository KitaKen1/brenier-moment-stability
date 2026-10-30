module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# One-sided transfer of quadratic tails

The pointwise estimate and its integral form do not require an optimal coupling.
Only its quadratic displacement cost enters the estimate.
-/

namespace BrenierMoment

open MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]

def quadraticTailTerm (H : ℝ) (y : E) : ℝ :=
  if H < ‖y‖ then ‖y‖ ^ 2 else 0

lemma quadraticTailTerm_nonneg (H : ℝ) (y : E) :
    0 ≤ quadraticTailTerm H y := by
  unfold quadraticTailTerm
  split_ifs <;> positivity

lemma quadraticTailTerm_le_sq (H : ℝ) (y : E) :
    quadraticTailTerm H y ≤ ‖y‖ ^ 2 := by
  unfold quadraticTailTerm
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

/-- The elementary estimate underlying the one-sided moment condition. -/
theorem quadraticTailTerm_transfer (H : ℝ) (_hH : 0 ≤ H) (y z : E) :
    quadraticTailTerm (2 * H) z ≤
      4 * ‖z - y‖ ^ 2 + 2 * quadraticTailTerm H y := by
  have hd : 0 ≤ ‖z - y‖ := norm_nonneg _
  have hy : 0 ≤ ‖y‖ := norm_nonneg _
  have hz : 0 ≤ ‖z‖ := norm_nonneg _
  have htri : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
    simpa using norm_add_le (z - y) y
  unfold quadraticTailTerm
  split_ifs with hbig hsmall hsmall
  · nlinarith [sq_nonneg (‖z - y‖ - ‖y‖),
      mul_nonneg (sub_nonneg.mpr htri) (by positivity : 0 ≤ ‖z - y‖ + ‖y‖ + ‖z‖)]
  · have hyH : ‖y‖ ≤ H := le_of_not_gt hsmall
    have hzD : ‖z‖ ≤ 2 * ‖z - y‖ := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hzD) (by positivity : 0 ≤ 2 * ‖z - y‖ + ‖z‖)]
  · positivity
  · positivity

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_quadraticTailTerm (H : ℝ) : Measurable (quadraticTailTerm H : E → ℝ) := by
  unfold quadraticTailTerm
  exact Measurable.ite (measurableSet_lt measurable_const measurable_norm)
    (measurable_norm.pow_const 2) measurable_const

lemma integrable_quadraticTailTerm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → E} (hY : AEMeasurable Y μ)
    (hY2 : Integrable (fun x => ‖Y x‖ ^ 2) μ) (H : ℝ) :
    Integrable (fun x => quadraticTailTerm H (Y x)) μ := by
  apply hY2.mono' ((measurable_quadraticTailTerm H).comp_aemeasurable hY).aestronglyMeasurable
  filter_upwards [] with x
  change ‖quadraticTailTerm H (Y x)‖ ≤ ‖Y x‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (quadraticTailTerm_nonneg H (Y x))]
  exact quadraticTailTerm_le_sq H (Y x)

def quadraticTail (μ : Measure E) (H : ℝ) : ℝ :=
  ∫ y, quadraticTailTerm H y ∂μ

/-- Transfer tails between random variables on any common measure space. -/
theorem integral_quadraticTailTerm_transfer {Ω : Type*} [MeasurableSpace Ω]
    {π : Measure Ω} {Y Z : Ω → E}
    (hY : AEMeasurable Y π) (hZ : AEMeasurable Z π)
    (hY2 : Integrable (fun x => ‖Y x‖ ^ 2) π)
    (hZ2 : Integrable (fun x => ‖Z x‖ ^ 2) π)
    (hD2 : Integrable (fun x => ‖Z x - Y x‖ ^ 2) π)
    {H : ℝ} (hH : 0 ≤ H) :
    (∫ x, quadraticTailTerm (2 * H) (Z x) ∂π) ≤
      4 * (∫ x, ‖Z x - Y x‖ ^ 2 ∂π) +
        2 * (∫ x, quadraticTailTerm H (Y x) ∂π) := by
  have hleft := integrable_quadraticTailTerm hZ hZ2 (2 * H)
  have hright := (hD2.const_mul 4).add ((integrable_quadraticTailTerm hY hY2 H).const_mul 2)
  calc
    _ ≤ ∫ x, 4 * ‖Z x - Y x‖ ^ 2 + 2 * quadraticTailTerm H (Y x) ∂π :=
      integral_mono hleft hright (fun x => quadraticTailTerm_transfer H hH (Y x) (Z x))
    _ = _ := by
      rw [integral_add (hD2.const_mul 4)
        ((integrable_quadraticTailTerm hY hY2 H).const_mul 2),
        integral_const_mul, integral_const_mul]

variable [SecondCountableTopology E]

/-- The finite second moments of the two marginals suffice; no higher moment
of the second marginal is required. -/
theorem quadraticTail_transfer_of_coupling
    {μ ν : Measure E} {π : Measure (E × E)}
    (hfst : Measure.map Prod.fst π = μ) (hsnd : Measure.map Prod.snd π = ν)
    (hμ2 : Integrable (fun y : E => ‖y‖ ^ 2) μ)
    (hν2 : Integrable (fun z : E => ‖z‖ ^ 2) ν)
    {H : ℝ} (hH : 0 ≤ H) :
    quadraticTail ν (2 * H) ≤
      4 * (∫ p : E × E, ‖p.2 - p.1‖ ^ 2 ∂π) + 2 * quadraticTail μ H := by
  have hm : StronglyMeasurable (fun y : E => ‖y‖ ^ 2) :=
    (measurable_norm.pow_const 2).stronglyMeasurable
  have hY2 : Integrable (fun p : E × E => ‖p.1‖ ^ 2) π := by
    apply (integrable_map_measure hm.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [hfst]
  have hZ2 : Integrable (fun p : E × E => ‖p.2‖ ^ 2) π := by
    apply (integrable_map_measure hm.aestronglyMeasurable measurable_snd.aemeasurable).mp
    rwa [hsnd]
  have hD2 : Integrable (fun p : E × E => ‖p.2 - p.1‖ ^ 2) π := by
    apply ((hZ2.const_mul 2).add (hY2.const_mul 2)).mono'
      ((measurable_snd.sub measurable_fst).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖p.2 - p.1‖ ^ 2 ≤ 2 * ‖p.2‖ ^ 2 + 2 * ‖p.1‖ ^ 2
    have ht := norm_sub_le p.2 p.1
    have hn := norm_nonneg (p.2 - p.1)
    nlinarith [sq_nonneg (‖p.2‖ - ‖p.1‖),
      mul_nonneg (sub_nonneg.mpr ht)
        (by positivity : 0 ≤ ‖p.2‖ + ‖p.1‖ + ‖p.2 - p.1‖)]
  have h := integral_quadraticTailTerm_transfer
    measurable_fst.aemeasurable measurable_snd.aemeasurable hY2 hZ2 hD2 hH
  have hleft : (∫ p : E × E, quadraticTailTerm (2 * H) p.2 ∂π) =
      quadraticTail ν (2 * H) := by
    unfold quadraticTail
    rw [← hsnd]
    exact (integral_map_of_stronglyMeasurable measurable_snd
      (measurable_quadraticTailTerm (2 * H)).stronglyMeasurable).symm
  have hright : (∫ p : E × E, quadraticTailTerm H p.1 ∂π) =
      quadraticTail μ H := by
    unfold quadraticTail
    rw [← hfst]
    exact (integral_map_of_stronglyMeasurable measurable_fst
      (measurable_quadraticTailTerm H).stronglyMeasurable).symm
  rwa [hleft, hright] at h

end

end BrenierMoment
