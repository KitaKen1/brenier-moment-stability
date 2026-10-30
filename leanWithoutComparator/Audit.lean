module

import BrenierMoment

/-! Axiom reports for the principal declarations. -/

-- the upper bound
#print axioms BrenierMoment.moment_stability

-- sharpness
#print axioms BrenierMoment.moment_rate_sharp
#print axioms BrenierMoment.no_modulus_at_second_moment

-- the upper bound on uniform sources, and both bounds on the box source
#print axioms BrenierMoment.uniformMeasure_eq_logConcaveSource
#print axioms BrenierMoment.moment_stability_uniform
#print axioms BrenierMoment.moment_rate_two_sided

-- the Mathlib-only statements
#print axioms BrenierMoment.Presentation.boxSource_eq
#print axioms BrenierStability.moment_stability
#print axioms BrenierStability.moment_rate_sharp
#print axioms BrenierStability.no_modulus_at_second_moment

-- the four-atom example in dimension `d`
#print axioms BrenierMoment.Sharp.cell_mass
#print axioms BrenierMoment.Sharp.map_cellMap
#print axioms BrenierMoment.Sharp.isUniqueOptimal_cellMap
#print axioms BrenierMoment.Sharp.wasserstein2_target
#print axioms BrenierMoment.Sharp.mapError_lower
#print axioms BrenierMoment.Sharp.lintegral_momentWeight_target_le
#print axioms BrenierMoment.sharp_parameters

-- scalar end of the upper bound
#print axioms BrenierMoment.quadraticTailTerm_transfer
#print axioms BrenierMoment.integral_quadraticTailTerm_transfer
#print axioms BrenierMoment.quadraticTail_transfer_of_coupling
#print axioms BrenierMoment.quadraticTail_le_envelope
#print axioms BrenierMoment.rate_of_threshold_family
#print axioms BrenierMoment.rate_of_interpolation
#print axioms BrenierMoment.clipped_slope_sq_le
#print axioms BrenierMoment.sum_sq_sub_clip_le

-- the atomic potential estimate for weighted sources
#print axioms BrenierMoment.AtomicPotentialBound.of_marginal
#print axioms BrenierMoment.map_dropLast_powerMeasure
#print axioms BrenierMoment.AtomicPotentialBound.of_tendsto
#print axioms BrenierMoment.atomicPotentialBound_powerSource
#print axioms BrenierMoment.atomicPotentialBound_logConcave

-- interpolation with tails
#print axioms BrenierMoment.clipped_slope_sq_le_of_slack
#print axioms BrenierMoment.line_interpolation
#print axioms BrenierMoment.sliced_interpolation
#print axioms BrenierMoment.stripInterpolation_logConcave
#print axioms BrenierMoment.clipped_interpolation_of_active
#print axioms BrenierMoment.clipped_plan_comparison

-- unique optimal maps for targets with finite second moment
#print axioms BrenierMoment.isUniqueQuadraticOptimalMap_of_tendsto_active
#print axioms BrenierMoment.exists_active_pair_of_finite
#print axioms BrenierMoment.exists_limit_map
#print axioms BrenierMoment.clipped_estimate_of_limits
#print axioms BrenierMoment.exists_optimal_map_with_approximation

-- the estimate for uniform sources, exported from the upstream development
#print axioms BrenierMoment.atomicPotentialBound_uniform
#print axioms BrenierMoment.uniformPotentialBound

-- the upper bound, with the estimate for uniform sources as a hypothesis
#print axioms BrenierMoment.sq_mapL2Dist_le_of_limits
#print axioms BrenierMoment.moment_stability_of_goodSource
#print axioms BrenierMoment.goodSource_logConcave
#print axioms BrenierMoment.moment_stability_logConcave

-- earlier special cases
#print axioms BrenierMoment.quadraticTail_le_inv_square_of_fourth_moment
#print axioms BrenierMoment.p4_bound_from_interpolation
#print axioms BrenierMoment.FourAtom.activeIndex_spec
#print axioms BrenierMoment.FourAtom.wasserstein2_sq_tilt
#print axioms BrenierMoment.FourAtom.fourth_moment_le
