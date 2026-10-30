module

public import BrenierMoment.LineInterpolation
public import OAI.Analysis.Brenier.TransportCore
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Slices along a coordinate

`E (m + 1)` is identified with `ℝ × E m` by splitting off the `i`-th
coordinate; the identification preserves volume. A set whose slices along the
`i`-th coordinate are order-connected then inherits the interpolation estimate
of `LineInterpolation.lean`, with the constant term multiplied by the volume
of any measurable set containing the transverse points of nonempty slices.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

variable {m : ℕ}

/-- Split off the `i`-th coordinate: `w ↦ (w i, the other coordinates)`. -/
def coordSplit (i : Fin (m + 1)) : E (m + 1) → ℝ × E m :=
  Prod.map id (WithLp.toLp 2) ∘
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i) ∘ WithLp.ofLp

/-- Insert a value as the `i`-th coordinate. -/
def coordJoin (i : Fin (m + 1)) (p : ℝ × E m) : E (m + 1) :=
  WithLp.toLp 2 (i.insertNth (α := fun _ : Fin (m + 1) => ℝ) p.1 fun j => p.2 j)

@[simp] lemma coordJoin_same (i : Fin (m + 1)) (p : ℝ × E m) : coordJoin i p i = p.1 := by
  simp [coordJoin]

@[simp] lemma coordJoin_succAbove (i : Fin (m + 1)) (p : ℝ × E m) (j : Fin m) :
    coordJoin i p (i.succAbove j) = p.2 j := by
  simp [coordJoin]

lemma coordSplit_fst (i : Fin (m + 1)) (w : E (m + 1)) : (coordSplit i w).1 = w i := rfl

lemma coordSplit_snd (i : Fin (m + 1)) (w : E (m + 1)) (j : Fin m) :
    (coordSplit i w).2 j = w (i.succAbove j) := rfl

lemma coordSplit_coordJoin (i : Fin (m + 1)) (p : ℝ × E m) :
    coordSplit i (coordJoin i p) = p := by
  refine Prod.ext ?_ ?_
  · rw [coordSplit_fst, coordJoin_same]
  · ext j
    rw [coordSplit_snd, coordJoin_succAbove]

lemma coordJoin_coordSplit (i : Fin (m + 1)) (w : E (m + 1)) :
    coordJoin i (coordSplit i w) = w := by
  ext k
  refine (Fin.forall_iff_succAbove (P := fun k => coordJoin i (coordSplit i w) k = w k)
    i).mpr ⟨?_, fun j => ?_⟩ k
  · rw [coordJoin_same, coordSplit_fst]
  · rw [coordJoin_succAbove, coordSplit_snd]

/-- A coordinate other than the `i`-th does not depend on the inserted value. -/
lemma coordJoin_apply_of_ne (i : Fin (m + 1)) {k : Fin (m + 1)} (hk : k ≠ i) (t t' : ℝ)
    (x : E m) : coordJoin i (t, x) k = coordJoin i (t', x) k := by
  obtain ⟨z, rfl⟩ := Fin.exists_succAbove_eq hk
  rw [coordJoin_succAbove, coordJoin_succAbove]

/-- Translation along the `i`-th coordinate. -/
lemma coordJoin_add (i : Fin (m + 1)) (t s : ℝ) (x : E m) :
    coordJoin i (t + s, x) = coordJoin i (t, x) + EuclideanSpace.single i s := by
  ext k
  refine (Fin.forall_iff_succAbove
    (P := fun k => coordJoin i (t + s, x) k =
      (coordJoin i (t, x) + EuclideanSpace.single i s) k) i).mpr ⟨?_, fun j => ?_⟩ k
  · simp
  · simp [Fin.succAbove_ne]

lemma coordJoin_sub (i : Fin (m + 1)) (t s : ℝ) (x : E m) :
    coordJoin i (t - s, x) = coordJoin i (t, x) - EuclideanSpace.single i s := by
  have h := coordJoin_add i (t - s) s x
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- Convex combinations along the `i`-th coordinate. -/
lemma coordJoin_combo (i : Fin (m + 1)) {a b : ℝ} (hab : a + b = 1) (t₁ t₂ : ℝ) (x : E m) :
    coordJoin i (a * t₁ + b * t₂, x) = a • coordJoin i (t₁, x) + b • coordJoin i (t₂, x) := by
  ext k
  refine (Fin.forall_iff_succAbove
    (P := fun k => coordJoin i (a * t₁ + b * t₂, x) k =
      (a • coordJoin i (t₁, x) + b • coordJoin i (t₂, x)) k) i).mpr ⟨?_, fun j => ?_⟩ k
  · simp
  · have h : x j = a * x j + b * x j := by
      rw [← add_mul, hab, one_mul]
    simpa using h

/-- The squared norm splits into the `i`-th coordinate and the others. -/
lemma norm_sq_coordJoin (i : Fin (m + 1)) (p : ℝ × E m) :
    ‖coordJoin i p‖ ^ 2 = p.1 ^ 2 + ‖p.2‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ i]
  simp

lemma norm_snd_le_norm_coordJoin (i : Fin (m + 1)) (p : ℝ × E m) : ‖p.2‖ ≤ ‖coordJoin i p‖ := by
  have h := norm_sq_coordJoin i p
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg p.1])

theorem measurePreserving_coordSplit (i : Fin (m + 1)) :
    MeasurePreserving (coordSplit i) volume
      ((volume : Measure ℝ).prod (volume : Measure (E m))) := by
  have h1 : MeasurePreserving (WithLp.ofLp : E (m + 1) → Fin (m + 1) → ℝ) volume volume :=
    PiLp.volume_preserving_ofLp (Fin (m + 1))
  have h2 : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i)
      volume ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have h3 : MeasurePreserving (Prod.map id (WithLp.toLp 2) : ℝ × (Fin m → ℝ) → ℝ × E m)
      ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ)))
      ((volume : Measure ℝ).prod (volume : Measure (E m))) :=
    (MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin m))
  exact h3.comp (h2.comp h1)

/-- Integration over `E (m + 1)` in split coordinates: the `i`-th coordinate is integrated first. -/
theorem lintegral_comp_coordSplit (i : Fin (m + 1)) {K : ℝ × E m → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ w, K (coordSplit i w) = ∫⁻ x, ∫⁻ t, K (t, x) := by
  rw [(measurePreserving_coordSplit i).lintegral_comp hK,
    lintegral_prod_symm _ hK.aemeasurable]

lemma measurable_coordJoin (i : Fin (m + 1)) : Measurable (coordJoin i) := by
  have h : Measurable fun p : ℝ × E m =>
      WithLp.toLp 2 ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
        (p.1, WithLp.ofLp p.2)) :=
    (WithLp.measurable_toLp 2 _).comp ((MeasurableEquiv.measurable _).comp
      (measurable_fst.prodMk ((WithLp.measurable_ofLp 2 _).comp measurable_snd)))
  exact h

/-! ### Slices -/

/-- The slice of `G` along the `i`-th coordinate through the transverse point `x`. -/
def slice (i : Fin (m + 1)) (G : Set (E (m + 1))) (x : E m) : Set ℝ :=
  {t | coordJoin i (t, x) ∈ G}

lemma measurableSet_slice (i : Fin (m + 1)) {G : Set (E (m + 1))} (hG : MeasurableSet G)
    (x : E m) : MeasurableSet (slice i G x) :=
  ((measurable_coordJoin i).comp (measurable_id.prodMk measurable_const)) hG

lemma lintegral_slice_eq (i : Fin (m + 1)) {G : Set (E (m + 1))} (hG : MeasurableSet G)
    (F : E (m + 1) → ℝ≥0∞) (x : E m) :
    ∫⁻ t in slice i G x, F (coordJoin i (t, x)) = ∫⁻ t, G.indicator F (coordJoin i (t, x)) := by
  rw [← lintegral_indicator (measurableSet_slice i hG x)]
  apply lintegral_congr
  intro t
  by_cases ht : coordJoin i (t, x) ∈ G
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ slice i G x from ht)]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ slice i G x from ht)]

/-- Integration over `G` by slices along the `i`-th coordinate. -/
theorem setLIntegral_eq_lintegral_slice (i : Fin (m + 1)) {G : Set (E (m + 1))}
    (hG : MeasurableSet G) {F : E (m + 1) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w in G, F w = ∫⁻ x, ∫⁻ t in slice i G x, F (coordJoin i (t, x)) := by
  have hK : Measurable fun p : ℝ × E m => G.indicator F (coordJoin i p) :=
    (hF.indicator hG).comp (measurable_coordJoin i)
  calc (∫⁻ w in G, F w) = ∫⁻ w, G.indicator F w := (lintegral_indicator hG F).symm
    _ = ∫⁻ w, G.indicator F (coordJoin i (coordSplit i w)) := by
        simp only [coordJoin_coordSplit]
    _ = ∫⁻ x, ∫⁻ t, G.indicator F (coordJoin i (t, x)) := lintegral_comp_coordSplit i hK
    _ = ∫⁻ x, ∫⁻ t in slice i G x, F (coordJoin i (t, x)) :=
        lintegral_congr fun x => (lintegral_slice_eq i hG F x).symm

lemma measurable_lintegral_slice (i : Fin (m + 1)) {G : Set (E (m + 1))} (hG : MeasurableSet G)
    {F : E (m + 1) → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun x : E m => ∫⁻ t in slice i G x, F (coordJoin i (t, x)) := by
  have hK : Measurable fun p : ℝ × E m => G.indicator F (coordJoin i p) :=
    (hF.indicator hG).comp (measurable_coordJoin i)
  have h : Measurable fun x : E m => ∫⁻ t, G.indicator F (coordJoin i (t, x)) :=
    hK.lintegral_prod_left'
  have heq : (fun x : E m => ∫⁻ t in slice i G x, F (coordJoin i (t, x))) =
      fun x => ∫⁻ t, G.indicator F (coordJoin i (t, x)) :=
    funext fun x => lintegral_slice_eq i hG F x
  rw [heq]
  exact h

/-- **Interpolation by slices.** If every slice of `G` along the `i`-th
coordinate is order-connected with finite length, the pointwise hypotheses of
`line_interpolation` along that coordinate give the integrated estimate over
`G`. The constant term carries the volume of a measurable set `N` containing
the transverse points of the nonempty slices. -/
theorem sliced_interpolation (i : Fin (m + 1)) {G : Set (E (m + 1))} (hGm : MeasurableSet G)
    (hGord : ∀ x : E m, (slice i G x).OrdConnected)
    (hGfin : ∀ x : E m, volume (slice i G x) ≠ ∞)
    {N : Set (E m)} (hNm : MeasurableSet N) (hN : ∀ x : E m, (slice i G x).Nonempty → x ∈ N)
    {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h)
    {Φ Γ : E (m + 1) → ℝ≥0∞} (hΦ : Measurable Φ) (hΓ : Measurable Γ)
    {D cu cv : E (m + 1) → ℝ} (hD : Measurable D) (hcu : Measurable cu) (hcv : Measurable cv)
    (hcuH : ∀ w, |cu w| ≤ H) (hcvH : ∀ w, |cv w| ≤ H)
    (hcu_mono : ∀ w, cu (w - EuclideanSpace.single i h) ≤ cu w)
    (hcv_mono : ∀ w, cv (w - EuclideanSpace.single i h) ≤ cv w)
    (ha : ∀ w ∈ G, Φ w ≤ ENNReal.ofReal (4 * H ^ 2))
    (hb : ∀ w, w ∈ G → w + EuclideanSpace.single i h ∈ G → w - EuclideanSpace.single i h ∈ G →
      Φ w ≤ ENNReal.ofReal (((D (w + EuclideanSpace.single i h) - D w) / h) ^ 2) +
        ENNReal.ofReal (4 * H) * (ENNReal.ofReal (cu w - cu (w - EuclideanSpace.single i h)) +
          ENNReal.ofReal (cv w - cv (w - EuclideanSpace.single i h))) + Γ w) :
    (∫⁻ w in G, Φ w) ≤
      ENNReal.ofReal (4 / h ^ 2) * (∫⁻ w in G, ENNReal.ofReal (D w ^ 2)) +
        ENNReal.ofReal (24 * H ^ 2 * h) * volume N + ∫⁻ w in G, Γ w := by
  have hDsq : Measurable fun w => ENNReal.ofReal (D w ^ 2) :=
    ENNReal.measurable_ofReal.comp (hD.pow_const 2)
  -- the estimate on each slice
  have hslice : ∀ x : E m, (∫⁻ t in slice i G x, Φ (coordJoin i (t, x))) ≤
      ENNReal.ofReal (4 / h ^ 2) *
          (∫⁻ t in slice i G x, ENNReal.ofReal (D (coordJoin i (t, x)) ^ 2)) +
        N.indicator (fun _ => ENNReal.ofReal (24 * H ^ 2 * h)) x +
      ∫⁻ t in slice i G x, Γ (coordJoin i (t, x)) := by
    intro x
    have hjm : Measurable fun t : ℝ => coordJoin i (t, x) :=
      (measurable_coordJoin i).comp (measurable_id.prodMk measurable_const)
    by_cases hne : (slice i G x).Nonempty
    · have hline := line_interpolation (measurableSet_slice i hGm x) (hGord x) (hGfin x) hH hh
        (φ := fun t => Φ (coordJoin i (t, x))) (γ := fun t => Γ (coordJoin i (t, x)))
        (hΓ.comp hjm) (D := fun t => D (coordJoin i (t, x)))
        (cu := fun t => cu (coordJoin i (t, x))) (cv := fun t => cv (coordJoin i (t, x)))
        (hD.comp hjm) (hcu.comp hjm) (hcv.comp hjm) (fun t => hcuH _) (fun t => hcvH _)
        (fun t => by
          have h1 := hcu_mono (coordJoin i (t, x))
          rw [← coordJoin_sub] at h1
          exact h1)
        (fun t => by
          have h1 := hcv_mono (coordJoin i (t, x))
          rw [← coordJoin_sub] at h1
          exact h1)
        (fun t ht => ha _ ht)
        (fun t ht htp htm => by
          have hp : coordJoin i (t, x) + EuclideanSpace.single i h ∈ G := by
            rw [← coordJoin_add]
            exact htp
          have hm : coordJoin i (t, x) - EuclideanSpace.single i h ∈ G := by
            rw [← coordJoin_sub]
            exact htm
          have h1 := hb (coordJoin i (t, x)) ht hp hm
          rw [← coordJoin_add, ← coordJoin_sub] at h1
          exact h1)
      rw [Set.indicator_of_mem (hN x hne)]
      exact hline
    · have hempty : slice i G x = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hzero : (∫⁻ t in slice i G x, Φ (coordJoin i (t, x))) = 0 := by
        rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
      rw [hzero]
      exact zero_le
  have hmD := measurable_lintegral_slice i hGm hDsq
  have hmΓ := measurable_lintegral_slice i hGm hΓ
  calc (∫⁻ w in G, Φ w) = ∫⁻ x, ∫⁻ t in slice i G x, Φ (coordJoin i (t, x)) :=
        setLIntegral_eq_lintegral_slice i hGm hΦ
    _ ≤ ∫⁻ x, (ENNReal.ofReal (4 / h ^ 2) *
            (∫⁻ t in slice i G x, ENNReal.ofReal (D (coordJoin i (t, x)) ^ 2)) +
          N.indicator (fun _ => ENNReal.ofReal (24 * H ^ 2 * h)) x +
          ∫⁻ t in slice i G x, Γ (coordJoin i (t, x))) := lintegral_mono hslice
    _ = ENNReal.ofReal (4 / h ^ 2) *
            (∫⁻ x, ∫⁻ t in slice i G x, ENNReal.ofReal (D (coordJoin i (t, x)) ^ 2)) +
          ENNReal.ofReal (24 * H ^ 2 * h) * volume N +
          ∫⁻ x, ∫⁻ t in slice i G x, Γ (coordJoin i (t, x)) := by
        rw [lintegral_add_right _ hmΓ, lintegral_add_right _ (measurable_const.indicator hNm),
          lintegral_const_mul _ hmD, lintegral_indicator_const hNm]
    _ = ENNReal.ofReal (4 / h ^ 2) * (∫⁻ w in G, ENNReal.ofReal (D w ^ 2)) +
          ENNReal.ofReal (24 * H ^ 2 * h) * volume N + ∫⁻ w in G, Γ w := by
        rw [← setLIntegral_eq_lintegral_slice i hGm hDsq,
          ← setLIntegral_eq_lintegral_slice i hGm hΓ]

end

end BrenierMoment
