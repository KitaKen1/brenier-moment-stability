module

public import BrenierMoment.Presentation.Model
public import BrenierMoment.UpperBound
public import BrenierMoment.Sharpness

@[expose] public section

/-!
# The Mathlib-only statements

`Presentation/Model.lean` defines couplings, the Wasserstein distance, Brenier maps, the
sources, the moment and the modulus using Mathlib alone. Here those definitions are identified
with the ones used in the proof, and the three statements are derived from
`BrenierMoment.moment_stability`, `BrenierMoment.moment_rate_sharp` and
`BrenierMoment.no_modulus_at_second_moment`.

The final theorems are in the namespace `BrenierStability`. Their statements are the ones of
`ComparatorChallenges/BrenierMomentStability.lean`.
-/

namespace BrenierMoment.Presentation

open MeasureTheory OAI.Problem358
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ### The vocabulary of the model and of the proof -/

lemma isCoupling_iff (μ ν : Measure (E d)) (π : Measure (E d × E d)) :
    BrenierStability.IsCoupling μ ν π ↔ IsCoupling μ ν π := Iff.rfl

lemma cost_eq (π : Measure (E d × E d)) : BrenierStability.cost π = quadraticPlanCost π := rfl

lemma wasserstein_eq (μ ν : Measure (E d)) :
    BrenierStability.wasserstein μ ν = wasserstein2 μ ν := rfl

lemma graph_eq (ρ : Measure (E d)) (T : E d → E d) :
    BrenierStability.graph ρ T = graphPlan ρ T := rfl

lemma isBrenierMap_iff (ρ μ : Measure (E d)) (T : E d → E d) :
    BrenierStability.IsBrenierMap ρ μ T ↔ IsUniqueQuadraticOptimalMap ρ μ T := Iff.rfl

lemma mapDist_eq (ρ : Measure (E d)) (T S : E d → E d) :
    BrenierStability.mapDist ρ T S = mapL2Dist ρ T S := rfl

lemma logConcaveSource_eq (U : Set (E d)) (V : E d → ℝ) :
    BrenierStability.logConcaveSource U V = logConcaveSource U V := rfl

lemma moment_eq (p β : ℝ) (μ : Measure (E d)) :
    BrenierStability.moment p β μ = ∫⁻ y, ENNReal.ofReal (momentWeight p β y) ∂μ := rfl

lemma modulus_eq (p β δ : ℝ) : BrenierStability.modulus p β δ = momentModulus p β δ := rfl

lemma hasFourAtoms_iff (μ : Measure (E d)) :
    BrenierStability.HasFourAtoms μ ↔ Sharp.HasFourAtoms μ := Iff.rfl

/-- The moment with `p = 2`, `β = 0` is the second moment. -/
lemma moment_two_zero (μ : Measure (E d)) :
    BrenierStability.moment 2 0 μ = ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂μ := by
  unfold BrenierStability.moment
  refine lintegral_congr fun y => ?_
  rw [Real.rpow_two, Real.rpow_zero, mul_one]

/-! ### The box source -/

lemma axis0_eq_zero (d : ℕ) (h : 2 ≤ d + 2) : Sharp.axis0 (d + 2) h = 0 := by
  apply Fin.ext
  simp [Sharp.axis0]

lemma mem_sourceBox_zero_iff (d : ℕ) (x : E (d + 2)) :
    x ∈ Sharp.sourceBox (0 : Fin (d + 2)) ↔
      x 0 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ i, x i ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · intro hx
    have hx' : ∀ k, x k ∈ Set.Icc (Sharp.sourceLo (0 : Fin (d + 2)) k) (Sharp.sourceHi k) := hx
    refine ⟨?_, fun i => ?_⟩
    · have h0 := hx' 0
      rw [Sharp.sourceLo_self] at h0
      exact h0
    · have hi := hx' i
      have hlo : (-1 : ℝ) ≤ Sharp.sourceLo (0 : Fin (d + 2)) i := by
        unfold Sharp.sourceLo
        split_ifs <;> norm_num
      exact ⟨hlo.trans hi.1, hi.2⟩
  · rintro ⟨h0, h⟩
    have hx' : ∀ k, x k ∈ Set.Icc (Sharp.sourceLo (0 : Fin (d + 2)) k) (Sharp.sourceHi k) := by
      intro k
      by_cases hk : k = 0
      · rw [hk, Sharp.sourceLo_self]
        exact h0
      · rw [Sharp.sourceLo_of_ne hk]
        exact h k
    exact hx'

/-- The box of the model is the source box of the sharpness statements. -/
lemma box_eq (d : ℕ) (h : 2 ≤ d + 2) :
    BrenierStability.box d = Sharp.sourceBox (Sharp.axis0 (d + 2) h) := by
  rw [axis0_eq_zero d h]
  ext x
  exact (mem_sourceBox_zero_iff d x).symm

lemma boxSource_eq (d : ℕ) (h : 2 ≤ d + 2) :
    BrenierStability.boxSource d = sharpSource (d + 2) h := by
  unfold BrenierStability.boxSource sharpSource uniformMeasure
  rw [box_eq d h]

/-! ### The statements -/

/-- The upper bound, in the vocabulary of the model. -/
theorem moment_stability_model {U : Set (E d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUn : U.Nonempty) {V : E d → ℝ} (hV : ConvexOn ℝ U V) {p β : ℝ} (hp : 2 ≤ p)
    (hβ : 0 ≤ β) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ μ ν : Measure (E d), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        BrenierStability.moment p β μ ≤ 1 → BrenierStability.moment 2 0 ν < ∞ →
        ∃ Tμ Tν : E d → E d,
          BrenierStability.IsBrenierMap (BrenierStability.logConcaveSource U V) μ Tμ ∧
          BrenierStability.IsBrenierMap (BrenierStability.logConcaveSource U V) ν Tν ∧
          (0 < BrenierStability.wasserstein μ ν → BrenierStability.wasserstein μ ν ≤ δ₀ →
            BrenierStability.mapDist (BrenierStability.logConcaveSource U V) Tμ Tν ≤
              C * BrenierStability.modulus p β (BrenierStability.wasserstein μ ν)) := by
  rw [logConcaveSource_eq]
  obtain ⟨R, hR⟩ := hUb.exists_norm_le
  obtain ⟨C, hC⟩ := moment_stability hU hUn hR hV hp hβ
  refine ⟨max C 1, smallDistance β, lt_of_lt_of_le one_pos (le_max_right C 1),
    smallDistance_pos β, smallDistance_lt_one hβ, ?_⟩
  intro μ ν hμ hν hM h2
  rw [moment_two_zero] at h2
  rw [moment_eq] at hM
  obtain ⟨Tμ, Tν, hTμ, hTν, hbound⟩ := hC μ ν hμ hν hM h2
  refine ⟨Tμ, Tν, (isBrenierMap_iff _ _ _).mpr hTμ, (isBrenierMap_iff _ _ _).mpr hTν,
    fun _ hle => ?_⟩
  rw [wasserstein_eq] at hle
  rw [mapDist_eq, modulus_eq, wasserstein_eq]
  have hω : 0 ≤ momentModulus p β (wasserstein2 μ ν) :=
    momentModulus_nonneg p β (Real.sqrt_nonneg _) (hle.trans (smallDistance_lt_one hβ).le)
  exact (hbound hle).trans (mul_le_mul_of_nonneg_right (le_max_left C 1) hω)

/-- Sharpness, in the vocabulary of the model. -/
theorem moment_rate_sharp_model (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (E (d + 2))) (Tμ Tν : E (d + 2) → E (d + 2)),
        BrenierStability.HasFourAtoms μ ∧ BrenierStability.HasFourAtoms ν ∧
        BrenierStability.moment p β μ ≤ 1 ∧ BrenierStability.moment p β ν ≤ 1 ∧
        BrenierStability.IsBrenierMap (BrenierStability.boxSource d) μ Tμ ∧
        BrenierStability.IsBrenierMap (BrenierStability.boxSource d) ν Tν ∧
        BrenierStability.wasserstein μ ν = δ ∧
        c * BrenierStability.modulus p β δ ≤
          BrenierStability.mapDist (BrenierStability.boxSource d) Tμ Tν := by
  have hd : 2 ≤ d + 2 := Nat.le_add_left 2 d
  obtain ⟨c, hc, δ₁, hδ₁, hsharp⟩ := moment_rate_sharp (d + 2) hd hp hβ
  refine ⟨c, δ₁, hc, hδ₁, fun δ hδ0 hδ => ?_⟩
  obtain ⟨μ, ν, Tμ, Tν, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hsharp δ hδ0 hδ
  rw [boxSource_eq d hd]
  exact ⟨μ, ν, Tμ, Tν, h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The endpoint, in the vocabulary of the model. -/
theorem no_modulus_at_second_moment_model (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ ν : Measure (E (d + 2))) (Tμ Tν : E (d + 2) → E (d + 2)),
      BrenierStability.HasFourAtoms μ ∧ BrenierStability.HasFourAtoms ν ∧
      BrenierStability.moment 2 0 μ ≤ 1 ∧ BrenierStability.moment 2 0 ν ≤ 1 ∧
      BrenierStability.IsBrenierMap (BrenierStability.boxSource d) μ Tμ ∧
      BrenierStability.IsBrenierMap (BrenierStability.boxSource d) ν Tν ∧
      0 < BrenierStability.wasserstein μ ν ∧ BrenierStability.wasserstein μ ν < ε ∧
      1 / 20 ≤ BrenierStability.mapDist (BrenierStability.boxSource d) Tμ Tν := by
  have hd : 2 ≤ d + 2 := Nat.le_add_left 2 d
  obtain ⟨μ, ν, Tμ, Tν, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    no_modulus_at_second_moment (d + 2) hd hε
  rw [boxSource_eq d hd]
  refine ⟨μ, ν, Tμ, Tν, h1, h2, ?_, ?_, h5, h6, h7, h8, h9⟩
  · rw [moment_two_zero]
    exact h3
  · rw [moment_two_zero]
    exact h4

end

end BrenierMoment.Presentation

namespace BrenierStability

noncomputable section
open MeasureTheory
open scoped ENNReal

/-- Moment stability of Brenier maps. Let $U \subset \mathbb{R}^d$ be bounded, open, convex and
nonempty, let $V$ be convex on $U$, and let $\rho$ be the probability measure on $U$ with density
proportional to $e^{-V}$. Let $p \ge 2$ and $\beta \ge 0$. There are $C > 0$ and
$0 < \delta_0 < 1$ such that, for every probability measure $\mu$ with $M_{p,\beta}(\mu) \le 1$
and every probability measure $\nu$ with finite second moment, there are Brenier maps $T_\mu$
and $T_\nu$ from $\rho$ to $\mu$ and to $\nu$, and
$\|T_\mu - T_\nu\|_{L^2(\rho)} \le C\,\omega_{p,\beta}(\delta)$ whenever
$0 < \delta = W_2(\mu, \nu) \le \delta_0$. -/
theorem moment_stability {d : ℕ} {U : Set (Space d)} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUn : U.Nonempty) {V : Space d → ℝ} (hV : ConvexOn ℝ U V)
    {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
      ∀ μ ν : Measure (Space d), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        moment p β μ ≤ 1 → moment 2 0 ν < ∞ →
        ∃ Tμ Tν : Space d → Space d,
          IsBrenierMap (logConcaveSource U V) μ Tμ ∧
          IsBrenierMap (logConcaveSource U V) ν Tν ∧
          (0 < wasserstein μ ν → wasserstein μ ν ≤ δ₀ →
            mapDist (logConcaveSource U V) Tμ Tν ≤ C * modulus p β (wasserstein μ ν)) :=
  BrenierMoment.Presentation.moment_stability_model hU hUb hUn hV hp hβ

/-- Sharpness of the modulus. Let $\rho_0$ be the uniform probability measure on
$[0,1] \times [-1,1]^{d+1} \subset \mathbb{R}^{d+2}$, and let $p \ge 2$, $\beta \ge 0$. There are
$c > 0$ and $\delta_1 > 0$ such that for every $0 < \delta \le \delta_1$ there are two measures
$\mu$ and $\nu$ with four atoms, with $M_{p,\beta}(\mu) \le 1$, $M_{p,\beta}(\nu) \le 1$ and
$W_2(\mu, \nu) = \delta$, whose Brenier maps from $\rho_0$ satisfy
$\|T_\mu - T_\nu\|_{L^2(\rho_0)} \ge c\,\omega_{p,\beta}(\delta)$. -/
theorem moment_rate_sharp (d : ℕ) {p β : ℝ} (hp : 2 ≤ p) (hβ : 0 ≤ β) :
    ∃ c δ₁ : ℝ, 0 < c ∧ 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ →
      ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
        HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment p β μ ≤ 1 ∧ moment p β ν ≤ 1 ∧
        IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
        wasserstein μ ν = δ ∧ c * modulus p β δ ≤ mapDist (boxSource d) Tμ Tν :=
  BrenierMoment.Presentation.moment_rate_sharp_model d hp hβ

/-- No modulus at the second moment. Let $\rho_0$ be the uniform probability measure on
$[0,1] \times [-1,1]^{d+1} \subset \mathbb{R}^{d+2}$. For every $\varepsilon > 0$ there are two
measures $\mu$ and $\nu$ with four atoms and second moments at most $1$ such that
$0 < W_2(\mu, \nu) < \varepsilon$ and the Brenier maps from $\rho_0$ satisfy
$\|T_\mu - T_\nu\|_{L^2(\rho_0)} \ge 1/20$. -/
theorem no_modulus_at_second_moment (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (μ ν : Measure (Space (d + 2))) (Tμ Tν : Space (d + 2) → Space (d + 2)),
      HasFourAtoms μ ∧ HasFourAtoms ν ∧ moment 2 0 μ ≤ 1 ∧ moment 2 0 ν ≤ 1 ∧
      IsBrenierMap (boxSource d) μ Tμ ∧ IsBrenierMap (boxSource d) ν Tν ∧
      0 < wasserstein μ ν ∧ wasserstein μ ν < ε ∧ 1 / 20 ≤ mapDist (boxSource d) Tμ Tν :=
  BrenierMoment.Presentation.no_modulus_at_second_moment_model d hε

end

end BrenierStability
