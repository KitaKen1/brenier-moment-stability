module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

@[expose] public section

/-!
# The interpolation estimate on a line

Let `J ⊆ ℝ` be order-connected with finite length. On the part of `J` whose
two translates by `±h` stay in `J`, a pointwise bound by a squared difference
quotient of `D`, by telescoping differences of two functions with values in
`[-H, H]`, and by an error `γ` is assumed; elsewhere only the bound `4 H²` is
used. The integral over `J` is then bounded by `4/h²` times the integral of
`D²`, by `24 H² h`, and by the integral of `γ`.

The set where a translate leaves `J` has length at most `h` on each side, and
the telescoping sums lose at most `2 H h`. No endpoint of `J` is ever named.
-/

namespace BrenierMoment

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- An order-connected set loses length at most `h` under the shift by `h`. -/
lemma volume_shift_exit_le {A : Set ℝ} (hA : A.OrdConnected) {h : ℝ} (hh : 0 ≤ h) :
    volume {t | t ∈ A ∧ t + h ∉ A} ≤ ENNReal.ofReal h := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun t₁ ht₁ t₂ ht₂ => ?_)
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq, abs_le]
  constructor
  · by_contra hc
    have hlt : t₁ + h < t₂ := by linarith
    exact ht₁.2 (hA.out ht₁.1 ht₂.1 ⟨by linarith, hlt.le⟩)
  · by_contra hc
    have hlt : t₂ + h < t₁ := by linarith
    exact ht₂.2 (hA.out ht₂.1 ht₁.1 ⟨by linarith, hlt.le⟩)

/-- An order-connected set loses length at most `h` under the shift by `-h`. -/
lemma volume_shift_exit_le' {A : Set ℝ} (hA : A.OrdConnected) {h : ℝ} (hh : 0 ≤ h) :
    volume {t | t ∈ A ∧ t - h ∉ A} ≤ ENNReal.ofReal h := by
  refine (Real.volume_le_diam _).trans (Metric.ediam_le fun t₁ ht₁ t₂ ht₂ => ?_)
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq, abs_le]
  constructor
  · by_contra hc
    have hlt : t₁ < t₂ - h := by linarith
    exact ht₂.2 (hA.out ht₁.1 ht₂.1 ⟨hlt.le, by linarith⟩)
  · by_contra hc
    have hlt : t₂ < t₁ - h := by linarith
    exact ht₁.2 (hA.out ht₂.1 ht₁.1 ⟨hlt.le, by linarith⟩)

/-- Integration over a set whose translate stays inside another set. -/
lemma setLIntegral_shift_le {G J : Set ℝ} (hGm : MeasurableSet G) (hJm : MeasurableSet J)
    {h : ℝ} (hGJ : ∀ t ∈ G, t + h ∈ J) (Ψ : ℝ → ℝ≥0∞) :
    (∫⁻ t in G, Ψ (t + h)) ≤ ∫⁻ t in J, Ψ t := by
  have hpt : ∀ t, G.indicator (fun t => Ψ (t + h)) t ≤ J.indicator Ψ (t + h) := by
    intro t
    by_cases ht : t ∈ G
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (hGJ t ht)]
    · rw [Set.indicator_of_notMem ht]
      exact zero_le
  calc (∫⁻ t in G, Ψ (t + h)) = ∫⁻ t, G.indicator (fun t => Ψ (t + h)) t :=
        (lintegral_indicator hGm _).symm
    _ ≤ ∫⁻ t, J.indicator Ψ (t + h) := lintegral_mono hpt
    _ = ∫⁻ t, J.indicator Ψ t := lintegral_add_right_eq_self (fun t => J.indicator Ψ t) h
    _ = ∫⁻ t in J, Ψ t := lintegral_indicator hJm Ψ

/-- Telescoping of a bounded function under a shift, over an order-connected set. -/
lemma lintegral_shift_difference_le {G : Set ℝ} (hGm : MeasurableSet G) (hG : G.OrdConnected)
    (hGfin : volume G ≠ ∞) {H h : ℝ} (hH : 0 ≤ H) (hh : 0 ≤ h) {c : ℝ → ℝ}
    (hc : Measurable c) (hcH : ∀ t, |c t| ≤ H) (hmono : ∀ t, c (t - h) ≤ c t) :
    (∫⁻ t in G, ENNReal.ofReal (c t - c (t - h))) ≤ ENNReal.ofReal (2 * H * h) := by
  -- the function shifted into `[0, 2H]`
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ≥0∞, F = fun t => ENNReal.ofReal (c t + H) := ⟨_, rfl⟩
  have hFm : Measurable F := by
    rw [hF]
    exact ENNReal.measurable_ofReal.comp (hc.add_const H)
  have hFs : Measurable fun t => F (t - h) := hFm.comp (measurable_id.sub_const h)
  have hFle : ∀ t, F t ≤ ENNReal.ofReal (2 * H) := by
    intro t
    rw [hF]
    exact ENNReal.ofReal_le_ofReal (by linarith [(abs_le.mp (hcH t)).2])
  have hsplit : ∀ t, ENNReal.ofReal (c t - c (t - h)) + F (t - h) = F t := by
    intro t
    rw [hF]
    change ENNReal.ofReal (c t - c (t - h)) + ENNReal.ofReal (c (t - h) + H) =
      ENNReal.ofReal (c t + H)
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr (hmono t))
      (by linarith [(abs_le.mp (hcH (t - h))).1])]
    congr 1
    ring
  have hsum : (∫⁻ t in G, ENNReal.ofReal (c t - c (t - h))) + ∫⁻ t in G, F (t - h) =
      ∫⁻ t in G, F t :=
    (lintegral_add_right (μ := volume.restrict G)
      (fun t => ENNReal.ofReal (c t - c (t - h))) hFs).symm.trans
      (lintegral_congr fun t => hsplit t)
  -- the shifted integral, written over the translated set
  have hB : (∫⁻ t in G, F (t - h)) =
      ∫⁻ t, G.indicator (fun _ => (1 : ℝ≥0∞)) (t + h) * F t := by
    calc (∫⁻ t in G, F (t - h)) = ∫⁻ t, G.indicator (fun t => F (t - h)) t :=
          (lintegral_indicator hGm _).symm
      _ = ∫⁻ t, G.indicator (fun t => F (t - h)) (t + h) :=
          (lintegral_add_right_eq_self (fun t => G.indicator (fun t => F (t - h)) t) h).symm
      _ = ∫⁻ t, G.indicator (fun _ => (1 : ℝ≥0∞)) (t + h) * F t := by
          apply lintegral_congr
          intro t
          by_cases ht : t + h ∈ G
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, one_mul, add_sub_cancel_right]
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  -- the two integrals differ by the part of `G` that the shift moves out
  obtain ⟨X, hX⟩ : ∃ X : Set ℝ, X = {t | t ∈ G ∧ t + h ∉ G} := ⟨_, rfl⟩
  have hXm : MeasurableSet X := by
    rw [hX]
    exact hGm.inter ((measurable_id.add_const h) hGm.compl)
  have hXvol : volume X ≤ ENNReal.ofReal h := by
    rw [hX]
    exact volume_shift_exit_le hG hh
  have hpt : ∀ t, G.indicator F t ≤ G.indicator (fun _ => (1 : ℝ≥0∞)) (t + h) * F t +
      X.indicator (fun _ => ENNReal.ofReal (2 * H)) t := by
    intro t
    by_cases ht : t ∈ G
    · by_cases hth : t + h ∈ G
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem hth, one_mul]
        exact le_self_add
      · have htX : t ∈ X := by
          rw [hX]
          exact ⟨ht, hth⟩
        rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hth, zero_mul, zero_add,
          Set.indicator_of_mem htX]
        exact hFle t
    · rw [Set.indicator_of_notMem ht]
      exact zero_le
  have hm1 : Measurable fun t => G.indicator (fun _ => (1 : ℝ≥0∞)) (t + h) * F t :=
    ((measurable_const.indicator hGm).comp (measurable_id.add_const h)).mul hFm
  have hA : (∫⁻ t in G, F t) ≤ (∫⁻ t in G, F (t - h)) + ENNReal.ofReal (2 * H * h) := by
    calc (∫⁻ t in G, F t) = ∫⁻ t, G.indicator F t := (lintegral_indicator hGm F).symm
      _ ≤ ∫⁻ t, (G.indicator (fun _ => (1 : ℝ≥0∞)) (t + h) * F t +
            X.indicator (fun _ => ENNReal.ofReal (2 * H)) t) := lintegral_mono hpt
      _ = (∫⁻ t, G.indicator (fun _ => (1 : ℝ≥0∞)) (t + h) * F t) +
            ∫⁻ t, X.indicator (fun _ => ENNReal.ofReal (2 * H)) t := lintegral_add_left hm1 _
      _ = (∫⁻ t in G, F (t - h)) + ENNReal.ofReal (2 * H) * volume X := by
          rw [← hB, lintegral_indicator_const hXm]
      _ ≤ (∫⁻ t in G, F (t - h)) + ENNReal.ofReal (2 * H) * ENNReal.ofReal h := by gcongr
      _ = (∫⁻ t in G, F (t - h)) + ENNReal.ofReal (2 * H * h) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
  have hBfin : (∫⁻ t in G, F (t - h)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' hGm fun t _ => hFle (t - h))
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin
  have hfinal : (∫⁻ t in G, ENNReal.ofReal (c t - c (t - h))) + ∫⁻ t in G, F (t - h) ≤
      ENNReal.ofReal (2 * H * h) + ∫⁻ t in G, F (t - h) := by
    rw [hsum, add_comm (ENNReal.ofReal (2 * H * h))]
    exact hA
  exact ENNReal.le_of_add_le_add_right hBfin hfinal

/-- **Interpolation on a line.** -/
theorem line_interpolation {J : Set ℝ} (hJm : MeasurableSet J) (hJ : J.OrdConnected)
    (hJfin : volume J ≠ ∞) {H h : ℝ} (hH : 0 ≤ H) (hh : 0 < h)
    {φ γ : ℝ → ℝ≥0∞} (hγ : Measurable γ)
    {D cu cv : ℝ → ℝ} (hD : Measurable D) (hcu : Measurable cu) (hcv : Measurable cv)
    (hcuH : ∀ t, |cu t| ≤ H) (hcvH : ∀ t, |cv t| ≤ H)
    (hcu_mono : ∀ t, cu (t - h) ≤ cu t) (hcv_mono : ∀ t, cv (t - h) ≤ cv t)
    (ha : ∀ t ∈ J, φ t ≤ ENNReal.ofReal (4 * H ^ 2))
    (hb : ∀ t, t ∈ J → t + h ∈ J → t - h ∈ J →
      φ t ≤ ENNReal.ofReal (((D (t + h) - D t) / h) ^ 2) +
        ENNReal.ofReal (4 * H) * (ENNReal.ofReal (cu t - cu (t - h)) +
          ENNReal.ofReal (cv t - cv (t - h))) + γ t) :
    (∫⁻ t in J, φ t) ≤
      ENNReal.ofReal (4 / h ^ 2) * (∫⁻ t in J, ENNReal.ofReal (D t ^ 2)) +
        ENNReal.ofReal (24 * H ^ 2 * h) + ∫⁻ t in J, γ t := by
  -- the part of `J` whose two translates stay in `J`
  obtain ⟨G, hG⟩ : ∃ G : Set ℝ, G = {t | t ∈ J ∧ t + h ∈ J ∧ t - h ∈ J} := ⟨_, rfl⟩
  have hGm : MeasurableSet G := by
    rw [hG]
    exact hJm.inter (((measurable_id.add_const h) hJm).inter ((measurable_id.sub_const h) hJm))
  have hGJ : G ⊆ J := by
    rw [hG]
    exact fun t ht => ht.1
  have hGord : G.OrdConnected := by
    rw [hG]
    refine ⟨fun x hx y hy z hz => ⟨hJ.out hx.1 hy.1 hz, ?_, ?_⟩⟩
    · exact hJ.out hx.2.1 hy.2.1 ⟨by linarith [hz.1], by linarith [hz.2]⟩
    · exact hJ.out hx.2.2 hy.2.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hGfin : volume G ≠ ∞ := ne_top_of_le_ne_top hJfin (measure_mono hGJ)
  -- the rest of `J` has length at most `2h`
  have hbad : volume (J \ G) ≤ ENNReal.ofReal (2 * h) := by
    have hsub : J \ G ⊆ {t | t ∈ J ∧ t + h ∉ J} ∪ {t | t ∈ J ∧ t - h ∉ J} := by
      intro t ht
      rw [hG] at ht
      by_cases h1 : t + h ∈ J
      · exact Or.inr ⟨ht.1, fun h2 => ht.2 ⟨ht.1, h1, h2⟩⟩
      · exact Or.inl ⟨ht.1, h1⟩
    calc volume (J \ G)
        ≤ volume ({t | t ∈ J ∧ t + h ∉ J} ∪ {t | t ∈ J ∧ t - h ∉ J}) := measure_mono hsub
      _ ≤ volume {t | t ∈ J ∧ t + h ∉ J} + volume {t | t ∈ J ∧ t - h ∉ J} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal h + ENNReal.ofReal h :=
          add_le_add (volume_shift_exit_le hJ hh.le) (volume_shift_exit_le' hJ hh.le)
      _ = ENNReal.ofReal (2 * h) := by
          rw [← ENNReal.ofReal_add hh.le hh.le]
          congr 1
          ring
  -- the three terms of the pointwise bound
  obtain ⟨E1, hE1⟩ : ∃ E1 : ℝ → ℝ≥0∞,
      E1 = fun t => ENNReal.ofReal (((D (t + h) - D t) / h) ^ 2) := ⟨_, rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : ℝ → ℝ≥0∞, E2 = fun t => ENNReal.ofReal (4 * H) *
      (ENNReal.ofReal (cu t - cu (t - h)) + ENNReal.ofReal (cv t - cv (t - h))) := ⟨_, rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℝ → ℝ≥0∞, Ψ = fun t => ENNReal.ofReal (D t ^ 2) := ⟨_, rfl⟩
  have hΨm : Measurable Ψ := by
    rw [hΨ]
    exact ENNReal.measurable_ofReal.comp (hD.pow_const 2)
  have hmu : Measurable fun t => ENNReal.ofReal (cu t - cu (t - h)) :=
    ENNReal.measurable_ofReal.comp (hcu.sub (hcu.comp (measurable_id.sub_const h)))
  have hmv : Measurable fun t => ENNReal.ofReal (cv t - cv (t - h)) :=
    ENNReal.measurable_ofReal.comp (hcv.sub (hcv.comp (measurable_id.sub_const h)))
  have hmuv : Measurable fun t =>
      ENNReal.ofReal (cu t - cu (t - h)) + ENNReal.ofReal (cv t - cv (t - h)) := hmu.add hmv
  have hE2m : Measurable E2 := by
    rw [hE2]
    exact hmuv.const_mul _
  have hpt : ∀ t, J.indicator φ t ≤ G.indicator (fun t => E1 t + E2 t + γ t) t +
      (J \ G).indicator (fun _ => ENNReal.ofReal (4 * H ^ 2)) t := by
    intro t
    by_cases htJ : t ∈ J
    · by_cases htG : t ∈ G
      · have hnot : t ∉ J \ G := fun hc => hc.2 htG
        have htG' := htG
        rw [hG] at htG'
        rw [Set.indicator_of_mem htJ, Set.indicator_of_mem htG, Set.indicator_of_notMem hnot,
          add_zero, hE1, hE2]
        exact hb t htG'.1 htG'.2.1 htG'.2.2
      · have hmem : t ∈ J \ G := ⟨htJ, htG⟩
        rw [Set.indicator_of_mem htJ, Set.indicator_of_notMem htG, Set.indicator_of_mem hmem,
          zero_add]
        exact ha t htJ
    · rw [Set.indicator_of_notMem htJ]
      exact zero_le
  have hint : (∫⁻ t in J, φ t) ≤ (∫⁻ t in G, (E1 t + E2 t + γ t)) +
      ENNReal.ofReal (4 * H ^ 2) * volume (J \ G) := by
    calc (∫⁻ t in J, φ t) = ∫⁻ t, J.indicator φ t := (lintegral_indicator hJm φ).symm
      _ ≤ ∫⁻ t, (G.indicator (fun t => E1 t + E2 t + γ t) t +
            (J \ G).indicator (fun _ => ENNReal.ofReal (4 * H ^ 2)) t) := lintegral_mono hpt
      _ = (∫⁻ t, G.indicator (fun t => E1 t + E2 t + γ t) t) +
            ∫⁻ t, (J \ G).indicator (fun _ => ENNReal.ofReal (4 * H ^ 2)) t :=
          lintegral_add_right _ (measurable_const.indicator (hJm.diff hGm))
      _ = (∫⁻ t in G, (E1 t + E2 t + γ t)) + ENNReal.ofReal (4 * H ^ 2) * volume (J \ G) := by
          rw [lintegral_indicator hGm, lintegral_indicator_const (hJm.diff hGm)]
  have hsplit : (∫⁻ t in G, (E1 t + E2 t + γ t)) =
      (∫⁻ t in G, E1 t) + (∫⁻ t in G, E2 t) + ∫⁻ t in G, γ t := by
    rw [lintegral_add_right _ hγ, lintegral_add_right _ hE2m]
  -- the difference quotient
  have hE1le : ∀ t, E1 t ≤ ENNReal.ofReal (2 / h ^ 2) * (Ψ (t + h) + Ψ t) := by
    intro t
    have hreal : ((D (t + h) - D t) / h) ^ 2 ≤ 2 / h ^ 2 * (D (t + h) ^ 2 + D t ^ 2) := by
      have h1 : ((D (t + h) - D t) / h) ^ 2 = (D (t + h) - D t) ^ 2 / h ^ 2 := div_pow _ _ _
      have h2 : 2 / h ^ 2 * (D (t + h) ^ 2 + D t ^ 2) =
          (2 * (D (t + h) ^ 2 + D t ^ 2)) / h ^ 2 := by ring
      rw [h1, h2]
      exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (D (t + h) + D t)])
        (by positivity)
    rw [hE1, hΨ]
    change ENNReal.ofReal (((D (t + h) - D t) / h) ^ 2) ≤
      ENNReal.ofReal (2 / h ^ 2) * (ENNReal.ofReal (D (t + h) ^ 2) + ENNReal.ofReal (D t ^ 2))
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hΨs : Measurable fun t => Ψ (t + h) + Ψ t :=
    (hΨm.comp (measurable_id.add_const h)).add hΨm
  have hshift : (∫⁻ t in G, Ψ (t + h)) ≤ ∫⁻ t in J, Ψ t :=
    setLIntegral_shift_le hGm hJm
      (fun t ht => by
        rw [hG] at ht
        exact ht.2.1) Ψ
  have hstay : (∫⁻ t in G, Ψ t) ≤ ∫⁻ t in J, Ψ t := lintegral_mono_set hGJ
  have hfour : ENNReal.ofReal (4 / h ^ 2) = ENNReal.ofReal (2 / h ^ 2) * 2 := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hI1 : (∫⁻ t in G, E1 t) ≤ ENNReal.ofReal (4 / h ^ 2) * ∫⁻ t in J, Ψ t := by
    calc (∫⁻ t in G, E1 t)
        ≤ ∫⁻ t in G, ENNReal.ofReal (2 / h ^ 2) * (Ψ (t + h) + Ψ t) :=
          lintegral_mono fun t => hE1le t
      _ = ENNReal.ofReal (2 / h ^ 2) * ((∫⁻ t in G, Ψ (t + h)) + ∫⁻ t in G, Ψ t) := by
          rw [lintegral_const_mul _ hΨs, lintegral_add_right _ hΨm]
      _ ≤ ENNReal.ofReal (2 / h ^ 2) * ((∫⁻ t in J, Ψ t) + ∫⁻ t in J, Ψ t) := by gcongr
      _ = ENNReal.ofReal (4 / h ^ 2) * ∫⁻ t in J, Ψ t := by
          rw [hfour, mul_assoc, two_mul]
  -- the telescoping terms
  have hE2eq : (∫⁻ t in G, E2 t) = ∫⁻ t in G, ENNReal.ofReal (4 * H) *
      (ENNReal.ofReal (cu t - cu (t - h)) + ENNReal.ofReal (cv t - cv (t - h))) := by
    rw [hE2]
  have hu := lintegral_shift_difference_le hGm hGord hGfin hH hh.le hcu hcuH hcu_mono
  have hv := lintegral_shift_difference_le hGm hGord hGfin hH hh.le hcv hcvH hcv_mono
  have hI2 : (∫⁻ t in G, E2 t) ≤ ENNReal.ofReal (16 * H ^ 2 * h) := by
    calc (∫⁻ t in G, E2 t)
        = ENNReal.ofReal (4 * H) * ((∫⁻ t in G, ENNReal.ofReal (cu t - cu (t - h))) +
            ∫⁻ t in G, ENNReal.ofReal (cv t - cv (t - h))) := by
          rw [hE2eq, lintegral_const_mul _ hmuv, lintegral_add_right _ hmv]
      _ ≤ ENNReal.ofReal (4 * H) *
            (ENNReal.ofReal (2 * H * h) + ENNReal.ofReal (2 * H * h)) := by gcongr
      _ = ENNReal.ofReal (16 * H ^ 2 * h) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hI3 : (∫⁻ t in G, γ t) ≤ ∫⁻ t in J, γ t := lintegral_mono_set hGJ
  have e1 : ENNReal.ofReal (4 * H ^ 2) * ENNReal.ofReal (2 * h) =
      ENNReal.ofReal (8 * H ^ 2 * h) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have e2 : ENNReal.ofReal (16 * H ^ 2 * h) + ENNReal.ofReal (8 * H ^ 2 * h) =
      ENNReal.ofReal (24 * H ^ 2 * h) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hfinal : (∫⁻ t in J, φ t) ≤ ENNReal.ofReal (4 / h ^ 2) * (∫⁻ t in J, Ψ t) +
      ENNReal.ofReal (24 * H ^ 2 * h) + ∫⁻ t in J, γ t := by
    calc (∫⁻ t in J, φ t)
        ≤ (∫⁻ t in G, (E1 t + E2 t + γ t)) +
            ENNReal.ofReal (4 * H ^ 2) * volume (J \ G) := hint
      _ = (∫⁻ t in G, E1 t) + (∫⁻ t in G, E2 t) + (∫⁻ t in G, γ t) +
            ENNReal.ofReal (4 * H ^ 2) * volume (J \ G) := by rw [hsplit]
      _ ≤ ENNReal.ofReal (4 / h ^ 2) * (∫⁻ t in J, Ψ t) + ENNReal.ofReal (16 * H ^ 2 * h) +
            (∫⁻ t in J, γ t) + ENNReal.ofReal (4 * H ^ 2) * ENNReal.ofReal (2 * h) := by
          gcongr
      _ = ENNReal.ofReal (4 / h ^ 2) * (∫⁻ t in J, Ψ t) + ENNReal.ofReal (24 * H ^ 2 * h) +
            ∫⁻ t in J, γ t := by
          rw [e1, ← e2]
          ring
  rw [hΨ] at hfinal
  exact hfinal

end

end BrenierMoment
