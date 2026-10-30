module

public import BrenierMoment.LimitCertificate
public import OAI.Analysis.Brenier.AtomicTransport
public import OAI.Analysis.Brenier.CompactMeasure

@[expose] public section

/-!
# Finite targets

`GoodSource ρ U R P B` collects what is used of the source from here on: it is
a probability measure concentrated on a bounded set `U`, it satisfies the
atomic potential estimate with constant `P`, and it has the interpolation
property with strip constant `B`.

For such a source every finitely supported probability is the law of an
active map of a finite potential, that map is the unique optimal map, and two
such maps satisfy the clipped estimate with the Wasserstein distance of their
laws: the common masses and the non-colliding sites needed by the potential
estimate are those of an optimal coupling of the two finite laws.
-/

namespace BrenierMoment

open MeasureTheory OAI.Problem358 Filter
open scoped BigOperators ENNReal RealInnerProductSpace Topology

noncomputable section

variable {d : ℕ}

/-- A source to which the stability theory applies. -/
structure GoodSource (ρ : Measure (E d)) (U : Set (E d)) (R P B : ℝ) : Prop where
  prob : IsProbabilityMeasure ρ
  nonempty : U.Nonempty
  norm_le : ∀ x ∈ U, ‖x‖ ≤ R
  ae_mem : ∀ᵐ x ∂ρ, x ∈ U
  potential : AtomicPotentialBound ρ P
  strip : StripInterpolation ρ U B
  strip_nonneg : 0 ≤ B

/-- The law of an active map is carried by the sites. -/
lemma isSupported_map_of_active {ρ : Measure (E d)} {ι : Type*} [Fintype ι] [Nonempty ι]
    {y : ι → E d} {a : ι → ℝ} {T : E d → E d} (hT : IsActiveMap y a T) (hTm : Measurable T) :
    IsSupported (Measure.map T ρ) (Set.range y) := by
  have hpre : T ⁻¹' (Set.range y)ᶜ = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, _⟩ := hT x
      exact (hx ⟨i, hi.symm⟩).elim
    · intro hx
      exact hx.elim
  unfold IsSupported
  rw [Measure.map_apply hTm (Set.finite_range y).measurableSet.compl, hpre, measure_empty]

/-- An active map of a finite potential is bounded. -/
lemma IsFinitePotentialMap.bounded {T : E d → E d} (hT : IsFinitePotentialMap T) :
    ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C := by
  obtain ⟨n, y, a, hact⟩ := hT
  refine ⟨∑ i, ‖y i‖, fun x => ?_⟩
  obtain ⟨i, hi, _⟩ := hact x
  rw [hi]
  exact Finset.single_le_sum (f := fun j => ‖y j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)

/-- An active map of a finite potential is the unique optimal map to its law. -/
theorem IsFinitePotentialMap.isUniqueQuadraticOptimalMap {ρ : Measure (E d)} {U : Set (E d)}
    {R P B : ℝ} (hρ : GoodSource ρ U R P B) {T : E d → E d} (hT : IsFinitePotentialMap T)
    (hTm : Measurable T) : IsUniqueQuadraticOptimalMap ρ (Measure.map T ρ) T := by
  have hprob := hρ.prob
  obtain ⟨C, hC⟩ := hT.bounded
  have hT2 : (∫⁻ x, ENNReal.ofReal (‖T x‖ ^ 2) ∂ρ) ≠ ∞ := by
    have hle : (∫⁻ x, ENNReal.ofReal (‖T x‖ ^ 2) ∂ρ) ≤ ENNReal.ofReal (C ^ 2) := by
      calc (∫⁻ x, ENNReal.ofReal (‖T x‖ ^ 2) ∂ρ) ≤ ∫⁻ _, ENNReal.ofReal (C ^ 2) ∂ρ :=
            lintegral_mono fun x =>
              ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hC x) 2)
        _ = ENNReal.ofReal (C ^ 2) := by rw [lintegral_const, measure_univ, mul_one]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have h0 : (fun _ : ℕ => ∫⁻ x, ENNReal.ofReal (‖T x - T x‖ ^ 2) ∂ρ) = fun _ => 0 := by
    funext n
    simp
  have hlim : Tendsto (fun _ : ℕ => ∫⁻ x, ENNReal.ofReal (‖T x - T x‖ ^ 2) ∂ρ) atTop (𝓝 0) := by
    rw [h0]
    exact tendsto_const_nhds
  exact isUniqueQuadraticOptimalMap_of_tendsto_active hρ.nonempty hρ.norm_le hρ.ae_mem
    hρ.strip_nonneg hρ.strip (Tn := fun _ => T) (fun _ => hT) (fun _ => hTm) hTm hT2 hlim

/-- The potentials of a good source are integrable in square. -/
lemma GoodSource.lintegral_potential_sq {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (y : ι → E d) (a : ι → ℝ) (z : κ → E d) (b : κ → ℝ) :
    (∫⁻ x, ENNReal.ofReal
      ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) =
      ENNReal.ofReal
        (∫ x, (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 ∂ρ) := by
  have hprob := hρ.prob
  have hball : closure U ⊆ Metric.closedBall (0 : E d) R :=
    closure_minimal (fun x hx => mem_closedBall_zero_iff.mpr (hρ.norm_le x hx))
      Metric.isClosed_closedBall
  have hK : IsCompact (closure U) :=
    (isCompact_closedBall (0 : E d) R).of_isClosed_subset isClosed_closure hball
  have hmem : ∀ᵐ x ∂ρ, x ∈ closure U := hρ.ae_mem.mono fun x hx => subset_closure hx
  have hcont : Continuous fun x : E d =>
      (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2 :=
    ((FiniteAffine.continuous_potential y a).sub (FiniteAffine.continuous_potential z b)).pow 2
  have hint : Integrable (fun x : E d =>
      (FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ρ :=
    integrable_of_continuousOn_of_ae_mem_compact hK hmem hcont.continuousOn
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => sq_nonneg _)).symm

/-- **Two finite targets.** Both are laws of active maps of finite potentials,
and the two maps satisfy the clipped estimate with the Wasserstein distance of
the targets. -/
theorem exists_active_pair_of_finite {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {μ ν : Measure (E d)} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {F G : Set (E d)} (hF : F.Finite) (hG : G.Finite)
    (hμ : IsSupported μ F) (hν : IsSupported ν G) :
    ∃ T S : E d → E d, Measurable T ∧ Measurable S ∧ IsFinitePotentialMap T ∧
      IsFinitePotentialMap S ∧ Measure.map T ρ = μ ∧ Measure.map S ρ = ν ∧
      ∀ H h : ℝ, 0 ≤ H → 0 < h →
        (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
          ENNReal.ofReal
            (4 * d * P ^ 2 * wasserstein2 μ ν ^ 2 / h ^ 2 + 24 * d * H ^ 2 * h * B) := by
  obtain ⟨N, hN, w, y, z, hw, hsum, _, _, hμeq, hνeq, _, henergy, hinj⟩ :=
    exists_finite_atomic_motion hF hG hμ hν
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨a, b, T, S, hTm, hSm, hTact, hSact, hTpush, hSpush, hL2⟩ :=
    hρ.potential k w y z hw hsum hinj
  refine ⟨T, S, hTm, hSm, ⟨k, y, a, hTact⟩, ⟨k, z, b, hSact⟩, hTpush.trans hμeq.symm,
    hSpush.trans hνeq.symm, ?_⟩
  intro H h hH hh
  have hB := hρ.strip_nonneg
  have hcl := clipped_interpolation_of_active hρ.strip hTact hSact hTm hSm hH hh
  rw [henergy] at hL2
  have hpot : (∫⁻ x, ENNReal.ofReal
      ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) ≤
      ENNReal.ofReal (P ^ 2 * wasserstein2 μ ν ^ 2) := by
    rw [hρ.lintegral_potential_sq y a z b]
    exact ENNReal.ofReal_le_ofReal hL2
  have h4 : (0 : ℝ) ≤ 4 * d / h ^ 2 := by positivity
  calc (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ)
      ≤ ENNReal.ofReal (4 * d / h ^ 2) *
          (∫⁻ x, ENNReal.ofReal
            ((FiniteAffine.potential y a x - FiniteAffine.potential z b x) ^ 2) ∂ρ) +
        ENNReal.ofReal (24 * d * H ^ 2 * h * B) := hcl
    _ ≤ ENNReal.ofReal (4 * d / h ^ 2) * ENNReal.ofReal (P ^ 2 * wasserstein2 μ ν ^ 2) +
        ENNReal.ofReal (24 * d * H ^ 2 * h * B) := by gcongr
    _ = ENNReal.ofReal
          (4 * d * P ^ 2 * wasserstein2 μ ν ^ 2 / h ^ 2 + 24 * d * H ^ 2 * h * B) := by
        rw [← ENNReal.ofReal_mul h4, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- Every finitely supported probability is the law of an active map of a finite potential. -/
theorem exists_finitePotentialMap_of_finite {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {μ : Measure (E d)} [IsProbabilityMeasure μ] {F : Set (E d)}
    (hF : F.Finite) (hμ : IsSupported μ F) :
    ∃ T : E d → E d, Measurable T ∧ IsFinitePotentialMap T ∧ Measure.map T ρ = μ := by
  obtain ⟨T, _, hTm, _, hT, _, hpush, _, _⟩ := exists_active_pair_of_finite hρ hF hF hμ hμ
  exact ⟨T, hTm, hT, hpush⟩

/-- **The clipped estimate for two active maps**, with the Wasserstein distance of their laws. -/
theorem clipped_estimate_of_finitePotential {ρ : Measure (E d)} {U : Set (E d)} {R P B : ℝ}
    (hρ : GoodSource ρ U R P B) {T S : E d → E d} (hT : IsFinitePotentialMap T)
    (hS : IsFinitePotentialMap S) (hTm : Measurable T) (hSm : Measurable S) {H h : ℝ}
    (hH : 0 ≤ H) (hh : 0 < h) :
    (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) ≤
      ENNReal.ofReal
        (4 * d * P ^ 2 * wasserstein2 (Measure.map T ρ) (Measure.map S ρ) ^ 2 / h ^ 2 +
          24 * d * H ^ 2 * h * B) := by
  have hprob := hρ.prob
  have hT0 := hT
  have hS0 := hS
  obtain ⟨k, y, a, hTa⟩ := hT
  obtain ⟨l, z, b, hSb⟩ := hS
  have hμ : IsSupported (Measure.map T ρ) (Set.range y) := isSupported_map_of_active hTa hTm
  have hν : IsSupported (Measure.map S ρ) (Set.range z) := isSupported_map_of_active hSb hSm
  have hμp : IsProbabilityMeasure (Measure.map T ρ) :=
    (Measure.isProbabilityMeasure_map_iff hTm.aemeasurable).mpr hprob
  have hνp : IsProbabilityMeasure (Measure.map S ρ) :=
    (Measure.isProbabilityMeasure_map_iff hSm.aemeasurable).mpr hprob
  obtain ⟨T', S', hT'm, hS'm, hT', hS', hT'push, hS'push, hest⟩ :=
    exists_active_pair_of_finite hρ (Set.finite_range y) (Set.finite_range z) hμ hν
  -- the maps found for the pair agree with the given ones
  have huT' := hT'.isUniqueQuadraticOptimalMap hρ hT'm
  rw [hT'push] at huT'
  have huS' := hS'.isUniqueQuadraticOptimalMap hρ hS'm
  rw [hS'push] at huS'
  have hTae : T' =ᵐ[ρ] T :=
    huT'.ae_eq_of_optimal (hT0.isUniqueQuadraticOptimalMap hρ hTm).1
  have hSae : S' =ᵐ[ρ] S :=
    huS'.ae_eq_of_optimal (hS0.isUniqueQuadraticOptimalMap hρ hSm).1
  have hcongr : (∫⁻ x, ENNReal.ofReal (‖clipVec H (T x) - clipVec H (S x)‖ ^ 2) ∂ρ) =
      ∫⁻ x, ENNReal.ofReal (‖clipVec H (T' x) - clipVec H (S' x)‖ ^ 2) ∂ρ := by
    apply lintegral_congr_ae
    filter_upwards [hTae, hSae] with x h1 h2
    rw [h1, h2]
  rw [hcongr]
  exact hest H h hH hh

end

end BrenierMoment
