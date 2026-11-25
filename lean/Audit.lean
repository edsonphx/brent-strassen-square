import Brent
import Brent.KernelCheck.SquareJacobianRank
import Brent.KernelCheck.QuadraticCertificates
import Brent.KernelCheck.TangentFrame
import Brent.KernelCheck.FamilyQuadratics
import Brent.KernelCheck.EmbeddingBound
import Brent.KernelCheck.LowerBound
import Brent.KernelCheck.MainTheorem
import Brent.KernelCheck.HilbertValues
import Brent.Formal.ReducedTangent
import Brent.Formal.Completion
import Brent.Formal.Singular
import Brent.Formal.TwoBranch
import Brent.Formal.OrbitDimension
import Brent.Formal.SliceIndependence
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let theorems := [
    ``Brent.strassen_solves,
    ``Brent.strassenSquare_solves,
    ``Brent.square_variable_count,
    ``Brent.square_equation_count,
    ``Brent.pointEvaluation_surjective,
    ``Brent.Decomposition.entry_line,
    ``Brent.Decomposition.tangent_satisfies_differential,
    ``Brent.Decomposition.mixed_entry_of_solution,
    ``Brent.QuadraticData.archived_covectors_annihilate,
    ``Brent.QuadraticData.archived_mixed_coefficients,
    ``Brent.QuadraticData.archived_mixed_zero_before,
    ``Brent.QuadraticData.archived_mixed_pivots,
    ``Brent.QuadraticData.same_family_polar_zero,
    ``Brent.TangentData.archived_origin,
    ``Brent.TangentData.chart_independent_derivatives,
    ``Brent.QuadraticData.archived_nonmixed_zero,
    ``Brent.QuadraticData.archived_square_zero,
    ``Brent.QuadraticData.archived_polar_mixed,
    ``Brent.QuadraticData.archived_polar_leading,
    ``Brent.TangentData.archived_frame_rank,
    ``Brent.TangentData.archived_frame_tangent,
    ``Brent.TangentData.archived_frame_split,
    ``Brent.TangentData.archived_left_coordinates,
    ``Brent.TangentData.archived_right_coordinates,
    ``Brent.Decomposition.solves_changeBasis,
    ``Brent.Decomposition.solves_rescale,
    ``Brent.leftFamily_solves,
    ``Brent.rightFamily_solves,
    ``Brent.leftFamily_at_identity,
    ``Brent.rightFamily_at_identity,
    ``Brent.quadraticMatching_disjoint,
    ``Brent.SparseRow.coefficient_subScaled,
    ``Brent.rowSpan_eq_of_elimination,
    ``Brent.linearIndependent_of_pivots,
    ``Brent.rowRank_eq_of_elimination,
    ``Brent.SparseRow.rank_of_checked_trace,
    ``Brent.SparseRow.rank_of_checked_radix_trace,
    ``Brent.square_jacobian_rank,
    ``Brent.square_jacobian_nullity,
    ``Brent.Decomposition.jacobianColumn_eq,
    ``Brent.squareJacobianColumn_correct,
    ``Brent.square_nullity_of_rank,
    ``Brent.quotient_dimension_of_le_nilradical,
    ``Brent.localDimension_le_of_power_le_span_sup_pow,
    ``Brent.ker_eval_eq_span,
    ``Brent.Decomposition.jacobianEntry_eq_sum,
    ``Brent.Decomposition.equation_eq_expansion,
    ``Brent.maximalIdeal_pointLocalRing,
    ``Brent.pointLocalDimension_le,
    ``Brent.squareLocalDimension_le_tangent,
    ``Brent.ringKrullDim_le_of_maximalIdeal_le,
    ``Brent.le_ringKrullDim_affineGerm,
    ``Brent.mem_sq_of_germJet,
    ``Brent.LowerBound.le_squareLocalDimension,
    ``Brent.pow_succ_le_of_triangular,
    ``Brent.exists_dual_frame,
    ``Brent.Decomposition.quadraticEntry_lc,
    ``Brent.Decomposition.quadraticEntry_sub_mem,
    ``Brent.triangular_dim_le,
    ``Brent.CharThree.annihilate,
    ``Brent.CharThree.polar_value,
    ``Brent.CharThree.square_value,
    ``Brent.CharThree.rowSpace_finrank,
    ``Brent.CharThree.frame_independent,
    ``Brent.UpperBound.quad_rel_local,
    ``Brent.UpperBound.mixed_rel,
    ``Brent.UpperBound.squareLocalDimension_le_197,
    ``Brent.Transfer.charZero_dim_le,
    ``Brent.QuadraticData.integerEntry_cast,
    ``Brent.QuadraticData.integer_annihilates,
    ``Brent.CharZeroBound.mu_annihilate,
    ``Brent.CharZeroBound.rel_B,
    ``Brent.CharZeroBound.squareLocalDimension_le_197,
    ``Brent.squareLocalDimension_eq_197_of_charThree,
    ``Brent.squareLocalDimension_eq_197_of_charZero,
    ``Brent.HilbertInitial.hilbertValue_zero,
    ``Brent.HilbertInitial.hilbertValue_one,
    ``Brent.HilbertTwo.ker_Ψ₂,
    ``Brent.HilbertTwo.hilbertValue_two_add,
    ``Brent.KernelVanishing.nonmixed_zero,
    ``Brent.KernelVanishing.square_zero,
    ``Brent.AugmentedTrace.augmented_rank,
    ``Brent.MixedRank.finrank_map_Mt,
    ``Brent.MixedRank.finrank_Rel,
    ``Brent.HilbertValues.hilbertValue_two,
    ``Brent.HilbertValues.hilbert_initial,
    ``Brent.HilbertValues.hilbert_initial_charP_three,
    ``Brent.HilbertValues.hilbert_initial_charZero,
    ``Brent.Formal.isNoetherianRing_mvPowerSeries,
    ``Brent.Formal.value_left_eq_right,
    ``Brent.Formal.subst_bijective_equiv,
    ``Brent.Formal.ker_killCompl,
    ``Brent.Formal.quotientKillEquiv,
    ``Brent.Formal.psFamily_solves,
    ``Brent.Formal.coeff_sel_in,
    ``Brent.Formal.value_orbit_left_eq_right,
    ``Brent.Formal.coeff_H,
    ``Brent.Formal.H_bijective,
    ``Brent.Formal.map_brentPS_le,
    ``Brent.Formal.map_maximalIdeal,
    ``Brent.Formal.ringKrullDim_Ahat_le_charThree,
    ``Brent.Formal.ringKrullDim_Ahat_le_charZero,
    ``Brent.Formal.ringKrullDim_mvPowerSeries,
    ``Brent.Formal.branchQuotEquiv,
    ``Brent.Formal.ringKrullDim_branch,
    ``Brent.Formal.branchPrime_minimal_charThree,
    ``Brent.Formal.branchPrime_minimal_charZero,
    ``Brent.Formal.branchPrime_ne,
    ``Brent.Formal.intersectionEquiv,
    ``Brent.Formal.ringKrullDim_intersection,
    ``Brent.Formal.hilbertValue_reduced_one,
    ``Brent.Formal.mem_pow_iff_lowZero,
    ``Brent.Formal.truncEquiv,
    ``Brent.Formal.completionEquiv,
    ``Brent.Formal.sqEquiv,
    ``Brent.Formal.ringKrullDim_squareCompletion_le_charThree,
    ``Brent.Formal.ringKrullDim_squareCompletion_le_charZero,
    ``Brent.Formal.sqBranchQuotEquiv,
    ``Brent.Formal.ringKrullDim_sqBranch,
    ``Brent.Formal.sqBranchPrime_minimal_charThree,
    ``Brent.Formal.sqBranchPrime_minimal_charZero,
    ``Brent.Formal.sqBranchPrime_ne,
    ``Brent.Formal.sqIntersectionEquiv,
    ``Brent.Formal.ringKrullDim_sqIntersection,
    ``Brent.Formal.le_spanFinrank_maximalIdeal_Ared,
    ``Brent.Formal.not_isRegularLocalRing_Ared_charThree,
    ``Brent.Formal.not_isRegularLocalRing_Ared_charZero,
    ``Brent.Formal.hilbertValue_eq_of_algHom,
    ``Brent.Formal.hilbertValue_two_Ahat,
    ``Brent.Formal.sqAlgEquiv,
    ``Brent.Formal.hilbertValue_two_squareCompletion,
    ``Brent.Formal.card_QIdx,
    ``Brent.Formal.hilbertValue_two_twoBranch,
    ``Brent.Formal.unionIdeal_ne_bot,
    ``Brent.Formal.sqBranchPrime_inf_ne_bot,
    ``Brent.Formal.not_isReduced_or_extra_minimalPrime,
    ``Brent.Formal.not_isReduced_or_extra_minimalPrime_charThree,
    ``Brent.Formal.not_isReduced_or_extra_minimalPrime_charZero,
    ``Brent.Formal.minor_upper,
    ``Brent.Formal.minor_diag,
    ``Brent.Formal.det_minor_ne_zero,
    ``Brent.Formal.orbPull_eqPS,
    ``Brent.Formal.coeff_orbitPull_X,
    ``Brent.Formal.dOrbit_kerVec,
    ``Brent.Formal.kerVec_independent,
    ``Brent.Formal.finrank_range_dOrbit_le,
    ``Brent.Formal.le_finrank_range_dOrbit,
    ``Brent.Formal.finrank_range_dOrbit,
    ``Brent.Formal.finrank_ker_dOrbit,
    ``Brent.Formal.slicePull_eq,
    ``Brent.Formal.sliceHat_eq,
    ``Brent.Formal.slicePull_surjective,
    ``Brent.Formal.sliceHat_surjective,
    ``Brent.Formal.ringKrullDim_slice,
    ``Brent.Formal.killCompl_subst,
    ``Brent.Formal.ker_fullHat_isPrime,
    ``Brent.Formal.branchMap_eq,
    ``Brent.Formal.ker_fullHat,
    ``Brent.Formal.ker_fullHat_charThree,
    ``Brent.Formal.ker_fullHat_charZero,
    ``Brent.Formal.slice_independent,
    ``Brent.Formal.gauge_origin,
    ``Brent.Formal.slot_none,
    ``Brent.Formal.orbitMap_eq,
    ``Brent.Formal.orbitMap_eq_slice,
    ``Brent.Formal.eq_ker_of_le,
    ``Brent.Formal.ker_sliceHat,
    ``Brent.Formal.orbitSubgermEquiv
  ]
  for name in theorems do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun dependency =>
      !([``propext, ``Classical.choice, ``Quot.sound].contains dependency))
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.toList}"

#print axioms Brent.strassenSquare_solves
#print axioms Brent.leftFamily_solves
#print axioms Brent.rightFamily_solves
#print axioms Brent.localDimension_le_of_power_le_span_sup_pow
#print axioms Brent.square_jacobian_rank
#print axioms Brent.square_jacobian_nullity
#print axioms Brent.squareLocalDimension_le_tangent
#print axioms Brent.LowerBound.le_squareLocalDimension
#print axioms Brent.UpperBound.squareLocalDimension_le_197
#print axioms Brent.squareLocalDimension_eq_197_of_charThree
#print axioms Brent.squareLocalDimension_eq_197_of_charZero
#print axioms Brent.HilbertValues.hilbert_initial_charP_three
#print axioms Brent.HilbertValues.hilbert_initial_charZero
#print axioms Brent.QuadraticData.archived_covectors_annihilate
#print axioms Brent.QuadraticData.archived_mixed_coefficients
#print axioms Brent.TangentData.archived_frame_tangent
#print axioms Brent.TangentData.archived_frame_split
#print axioms Brent.Formal.branchPrime_minimal_charThree
#print axioms Brent.Formal.ringKrullDim_intersection
#print axioms Brent.Formal.hilbertValue_reduced_one
#print axioms Brent.Formal.sqEquiv
#print axioms Brent.Formal.sqBranchPrime_minimal_charZero
#print axioms Brent.Formal.ringKrullDim_sqIntersection
#print axioms Brent.Formal.not_isRegularLocalRing_Ared_charThree
#print axioms Brent.Formal.not_isRegularLocalRing_Ared_charZero
#print axioms Brent.Formal.hilbertValue_two_squareCompletion
#print axioms Brent.Formal.hilbertValue_two_twoBranch
#print axioms Brent.Formal.not_isReduced_or_extra_minimalPrime_charThree
#print axioms Brent.Formal.not_isReduced_or_extra_minimalPrime_charZero
#print axioms Brent.Formal.finrank_range_dOrbit
#print axioms Brent.Formal.finrank_ker_dOrbit
#print axioms Brent.Formal.sliceHat_eq
#print axioms Brent.Formal.sliceHat_surjective
#print axioms Brent.Formal.ker_fullHat_charThree
#print axioms Brent.Formal.ker_fullHat_charZero
#print axioms Brent.Formal.slice_independent
#print axioms Brent.Formal.ker_sliceHat
