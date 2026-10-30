module

public import BrenierMoment.LastCoordinate
public import OAI.Analysis.Brenier.AffineCertificate
public import OAI.Analysis.Brenier.AffineTies

@[expose] public section

/-!
# The atomic potential estimate and its descent to a marginal

The estimate is stated with explicit data: intercepts for the two finite
potentials and maps that select an active site at every point. In this form
it passes from a source on `E (k + 1)` to its marginal on `E k`, because a
finite potential whose sites have vanishing last coordinate does not depend
on that coordinate. This is the step used to reduce a weighted source to a
uniform source one dimension higher.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped BigOperators ENNReal RealInnerProductSpace

noncomputable section

/-- The atomic potential estimate for the source `ρ` with constant `P`, in
explicit form: two targets with common masses `m` at sites `y` and `z` have
finite potentials with intercepts `a`, `b` and active-site maps `T`, `S`
pushing `ρ` to the targets, and the potentials differ in `L²(ρ)` by at most
`P` times the transport cost of the matching. -/
def AtomicPotentialBound {d : ℕ} (ρ : Measure (E d)) (P : ℝ) : Prop :=
  ∀ (n : ℕ) (m : Fin (n + 1) → ℝ) (y z : Fin (n + 1) → E d),
    (∀ i, 0 < m i) → (∑ i, m i) = 1 →
    (∀ t : ℝ, 0 < t → t < 1 →
      Function.Injective (fun i => (1 - t) • y i + t • z i)) →
    ∃ (a b : Fin (n + 1) → ℝ) (T S : E d → E d),
      Measurable T ∧ Measurable S ∧
      (∀ x, ∃ i, T x = y i ∧ FiniteAffine.Maximizes y a x i) ∧
      (∀ x, ∃ i, S x = z i ∧ FiniteAffine.Maximizes z b x i) ∧
      Measure.map T ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) ∧
      Measure.map S ρ = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (z i) ∧
      (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 ∂ρ) ≤
        P ^ 2 * ∑ i, m i * ‖y i - z i‖ ^ 2

variable {k : ℕ}

lemma maximizes_appendZero_iff {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → E k) (c : ι → ℝ)
    (w : E (k + 1)) (i : ι) :
    FiniteAffine.Maximizes (fun j => appendZero (y j)) c w i ↔
      FiniteAffine.Maximizes y c (dropLast w) i := by
  unfold FiniteAffine.Maximizes
  simp only [inner_appendZero]

lemma potential_appendZero {ι : Type*} [Fintype ι] [Nonempty ι] (y : ι → E k) (c : ι → ℝ)
    (w : E (k + 1)) :
    FiniteAffine.potential (fun j => appendZero (y j)) c w =
      FiniteAffine.potential y c (dropLast w) := by
  unfold FiniteAffine.potential
  simp only [inner_appendZero]

/-- An active-site map upstairs and its descent agree almost everywhere after projection. -/
lemma dropLast_comp_ae_eq {ι : Type*} [Fintype ι] [Nonempty ι] {ρ' : Measure (E (k + 1))}
    (hac : Measure.map dropLast ρ' ≪ (volume : Measure (E k)))
    (y : ι → E k) (c : ι → ℝ) {T' : E (k + 1) → E (k + 1)}
    (hact : ∀ w, ∃ i, T' w = appendZero (y i) ∧
      FiniteAffine.Maximizes (fun j => appendZero (y j)) c w i) :
    (fun w => dropLast (T' (appendZero (dropLast w)))) =ᵐ[ρ'] fun w => dropLast (T' w) := by
  have hties : ∀ᵐ x ∂Measure.map dropLast ρ', ∀ i j,
      ⟪x, y i⟫ + c i = ⟪x, y j⟫ + c j → y i = y j :=
    hac.ae_le (ae_affine_tie_implies_slopes_eq volume y c)
  filter_upwards [ae_of_ae_map measurable_dropLast.aemeasurable hties] with w hw
  obtain ⟨i, hi, hmi⟩ := hact (appendZero (dropLast w))
  obtain ⟨j, hj, hmj⟩ := hact w
  have hmi' := (maximizes_appendZero_iff y c _ i).mp hmi
  rw [dropLast_appendZero] at hmi'
  have hmj' := (maximizes_appendZero_iff y c w j).mp hmj
  have hij : y i = y j := hw i j (le_antisymm (hmj' i) (hmi' j))
  change dropLast (T' (appendZero (dropLast w))) = dropLast (T' w)
  rw [hi, hj, dropLast_appendZero, dropLast_appendZero, hij]

/-- **Descent to a marginal.** If the source `ρ` on `E k` is the marginal of
`ρ'` on `E (k + 1)` and is absolutely continuous, the atomic potential estimate
for `ρ'` gives the estimate for `ρ` with the same constant. -/
theorem AtomicPotentialBound.of_marginal {ρ' : Measure (E (k + 1))} {ρ : Measure (E k)}
    {P : ℝ} (hmarg : Measure.map dropLast ρ' = ρ) (hac : ρ ≪ volume)
    (h : AtomicPotentialBound ρ' P) : AtomicPotentialBound ρ P := by
  intro n m y z hm hsum hinj
  have hdm := measurable_dropLast (k := k)
  have ham := measurable_appendZero (k := k)
  have hinj' : ∀ t : ℝ, 0 < t → t < 1 →
      Function.Injective (fun i => (1 - t) • appendZero (y i) + t • appendZero (z i)) := by
    intro t ht0 ht1 i j hij
    apply hinj t ht0 ht1
    have h1 := congrArg dropLast hij
    simpa only [map_add, map_smul, dropLast_appendZero] using h1
  obtain ⟨a, b, T', S', hT'm, hS'm, hT'act, hS'act, hT'push, hS'push, hL2⟩ :=
    h n m (fun i => appendZero (y i)) (fun i => appendZero (z i)) hm hsum hinj'
  have hac' : Measure.map dropLast ρ' ≪ (volume : Measure (E k)) := by rw [hmarg]; exact hac
  have hpush : ∀ (y : Fin (n + 1) → E k) (c : Fin (n + 1) → ℝ) (T' : E (k + 1) → E (k + 1)),
      Measurable T' →
      (∀ w, ∃ i, T' w = appendZero (y i) ∧
        FiniteAffine.Maximizes (fun j => appendZero (y j)) c w i) →
      Measure.map T' ρ' = ∑ i, ENNReal.ofReal (m i) • Measure.dirac (appendZero (y i)) →
      Measure.map (fun x => dropLast (T' (appendZero x))) ρ =
        ∑ i, ENNReal.ofReal (m i) • Measure.dirac (y i) := by
    intro y c T' hT'm hact hmap
    have hTm : Measurable fun x : E k => dropLast (T' (appendZero x)) :=
      hdm.comp (hT'm.comp ham)
    rw [← hmarg, Measure.map_map hTm hdm]
    have hcongr : Measure.map ((fun x => dropLast (T' (appendZero x))) ∘ dropLast) ρ' =
        Measure.map (fun w => dropLast (T' w)) ρ' :=
      Measure.map_congr (dropLast_comp_ae_eq hac' y c hact)
    have hcomp : Measure.map (fun w => dropLast (T' w)) ρ' =
        Measure.map dropLast (Measure.map T' ρ') := (Measure.map_map hdm hT'm).symm
    rw [hcongr, hcomp, hmap, Measure.map_finset_sum hdm.aemeasurable]
    simp only [Measure.map_smul _ hdm.aemeasurable, Measure.map_dirac, dropLast_appendZero]
  have hactive : ∀ (y : Fin (n + 1) → E k) (c : Fin (n + 1) → ℝ) (T' : E (k + 1) → E (k + 1)),
      (∀ w, ∃ i, T' w = appendZero (y i) ∧
        FiniteAffine.Maximizes (fun j => appendZero (y j)) c w i) →
      ∀ x, ∃ i, dropLast (T' (appendZero x)) = y i ∧ FiniteAffine.Maximizes y c x i := by
    intro y c T' hact x
    obtain ⟨i, hi, hmax⟩ := hact (appendZero x)
    have hmax' := (maximizes_appendZero_iff y c _ i).mp hmax
    rw [dropLast_appendZero] at hmax'
    exact ⟨i, by rw [hi, dropLast_appendZero], hmax'⟩
  refine ⟨a, b, fun x => dropLast (T' (appendZero x)), fun x => dropLast (S' (appendZero x)),
    hdm.comp (hT'm.comp ham), hdm.comp (hS'm.comp ham), hactive y a T' hT'act,
    hactive z b S' hS'act, hpush y a T' hT'm hT'act hT'push, hpush z b S' hS'm hS'act hS'push,
    ?_⟩
  -- the L² bound
  have hcont : Continuous fun x : E k =>
      (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 :=
    ((FiniteAffine.continuous_potential y a).sub (FiniteAffine.continuous_potential z b)).pow 2
  have hint : (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 ∂ρ) =
      ∫ w, (FiniteAffine.potential (fun j => appendZero (y j)) a w -
        FiniteAffine.potential (fun j => appendZero (z j)) b w) ^ 2 ∂ρ' := by
    rw [← hmarg, integral_map hdm.aemeasurable hcont.aestronglyMeasurable]
    simp only [potential_appendZero]
  have hnorm : ∀ i, ‖appendZero (y i) - appendZero (z i)‖ = ‖y i - z i‖ := by
    intro i
    rw [← map_sub, norm_appendZero]
  rw [hint]
  simpa only [hnorm] using hL2

end

end BrenierMoment
