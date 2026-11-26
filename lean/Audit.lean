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
import Brent.Formal.SwapSymmetry
import Brent.Formal.SmoothPoints
import Brent.Equidim.Equidim
import Brent.LWH
import Brent.Theorem11
import Brent.Section7
import Brent.Groebner.Paper
import Brent.Groebner.MonomialHeight
import Brent.InitialForms
import Brent.CM.HilbertSamuelPoly
import Brent.CM.Lemma41
import Brent.CM.RegularCoprime
import Brent.CM.LiftInstance
import Brent.CM.Lemma41Gen
import Brent.CM.PowerSeriesInstance
import Brent.CM.LiftedQuadrics
import Brent.BaseLemma
import Brent.BranchTangents
import Brent.SecondOrderLift
import Brent.Z3Basis
import Brent.LeftKernelLift
import Brent.Catalogue.ExactAnchors
import Brent.CM.GradedPresentation
import Brent.PaperDetails
import Brent.CM.QuadraticHeight
import Brent.Formal.BaseChange
import Brent.Formal.NormalEliminationZ3
import Brent.HadamardSmall
import Brent.CM.GradedRingAssembly
import Brent.CM.GradedPolynomial
import Brent.Formal.OrbitClosure
import Brent.Formal.NormalFrameZ3
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
    ``Brent.Formal.orbitSubgermEquiv,
    ``Brent.Formal.swapDec_solves,
    ``Brent.Formal.swapDec_leftFamily,
    ``Brent.Formal.swapDec_strassenSquare,
    ``Brent.Formal.swapDec_changeBasis,
    ``Brent.Formal.swapDec_value,
    ``Brent.Formal.swapPS_eqPS,
    ``Brent.Formal.swapHatEquiv,
    ``Brent.Formal.fullHat_swapHat,
    ``Brent.Formal.comap_swapHat_right,
    ``Brent.Formal.comap_swapHat_left,
    ``Brent.Formal.comap_swapHat_sup,
    ``Brent.Formal.comap_swapHat_right_charThree,
    ``Brent.Formal.comap_swapHat_right_charZero,
    ``Brent.SmoothL.rank_of_checks,
    ``Brent.SmoothL.checked,
    ``Brent.SmoothL.det_minor_ne_zero,
    ``Brent.Formal.SmoothLeftMinor.isUnit_minor_map,
    ``Brent.Formal.SmoothLeftMinor.freeVar_not_col,
    ``Brent.Formal.SmoothLeftMinor.col_injective,
    ``Brent.Formal.injective_of_surjective_endo,
    ``Brent.Formal.coeff_eqAt,
    ``Brent.Formal.freeMap_surjective,
    ``Brent.Formal.freeMap_bijective,
    ``Brent.Formal.swapAtEquiv,
    ``Brent.Formal.swapDec_value_trivial,
    ``Brent.Formal.coeff_qArg,
    ``Brent.Formal.qGroup_jet,
    ``Brent.GermLower.le_pointLocalDimension,
    ``Brent.Formal.le_localDimension_of_tangents,
    ``Brent.spanFinrank_maximalIdeal_le,
    ``Brent.isRegularLocalRing_of_dim,
    ``Brent.Formal.pqInt_value_left,
    ``Brent.Formal.curve_value_zero,
    ``Brent.Formal.curve_one,
    ``Brent.Formal.det_e12,
    ``Brent.Formal.det_e21,
    ``Brent.Formal.SmoothLeftPoint.jacobian_rank,
    ``Brent.Formal.SmoothLeftPoint.tangent_dimension,
    ``Brent.Formal.SmoothLeftPoint.local_dimension,
    ``Brent.Formal.SmoothLeftPoint.ahatEquiv,
    ``Brent.Formal.SmoothRightPoint.jacobian_rank,
    ``Brent.Formal.SmoothRightPoint.tangent_dimension,
    ``Brent.Formal.SmoothRightPoint.local_dimension,
    ``Brent.Formal.SmoothRightPoint.ahat_equiv,
    ``Brent.Formal.SmoothPoints.minor_det_ne_zero,
    ``Brent.Formal.SmoothPoints.qL_regular,
    ``Brent.Formal.SmoothPoints.qR_regular,
    ``Brent.Formal.SmoothPoints.smooth_points,
    ``Brent.Equidim.height_eq_ringKrullDim_of_isMaximal,
    ``Brent.Equidim.ringKrullDim_localization_eq,
    ``Brent.Equidim.ringKrullDim_ne_top,
    ``Brent.Equidim.eq_zero_of_eval_eq_zero_of_eval_ne_zero,
    ``Brent.LWH.pointDec_solves,
    ``Brent.LWH.checked,
    ``Brent.LWH.kerChecked,
    ``Brent.LWH.det_minor_ne_zero,
    ``Brent.LWH.kvec_free,
    ``Brent.LWH.orbitGens_tangent,
    ``Brent.LWH.kept_independent,
    ``Brent.LWH.orbit_finrank,
    ``Brent.LWH.solves,
    ``Brent.LWH.jacobian_rank,
    ``Brent.LWH.tangent_dimension,
    ``Brent.LWH.orbit_in_tangent,
    ``Brent.LWH.orbit_tangent_dimension,
    ``Brent.LWH.lwh_point
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
#print axioms Brent.Formal.swapDec_value
#print axioms Brent.Formal.comap_swapHat_right_charThree
#print axioms Brent.Formal.comap_swapHat_right_charZero
#print axioms Brent.Formal.comap_swapHat_sup
#print axioms Brent.Formal.SmoothPoints.smooth_points
#print axioms Brent.Formal.SmoothPoints.qL_regular
#print axioms Brent.Formal.SmoothPoints.qR_regular
#print axioms Brent.Equidim.height_eq_ringKrullDim_of_isMaximal
#print axioms Brent.Equidim.ringKrullDim_localization_eq
#print axioms Brent.Equidim.ringKrullDim_ne_top
#print axioms Brent.LWH.lwh_point

run_cmd do
  let theorems := [
    ``Brent.Formal.Component.ringKrullDim_locQ_le,
    ``Brent.Formal.Component.ringKrullDim_locQ_succ_le,
    ``Brent.Formal.Component.generic_map_evS,
    ``Brent.Formal.Component.family_kills,
    ``Brent.Formal.Component.derivD_independent,
    ``Brent.Formal.Component.localDim_closure,
    ``Brent.Formal.Component.prime_eq_ker,
    ``Brent.Formal.Component.vanishingIdeal_isPrime,
    ``Brent.Formal.Component.familyClosure_maximal,
    ``Brent.Formal.Component.familyClosure_isComponent,
    ``Brent.Formal.Component.ker_mem_minimalPrimes,
    ``Brent.Formal.Component.ringKrullDim_closure,
    ``Brent.Census.isClosed_rankBound,
    ``Brent.Census.det_submatrix_eq_zero_of_rank_lt,
    ``Brent.Census.mem_rankBound_of_profileBound,
    ``Brent.Census.dominated_of_formula,
    ``Brent.Census.profileBound_of_dominated,
    ``Brent.Census.strassen_factor,
    ``Brent.Census.rank_value_le,
    ``Brent.Census.profileBound_family,
    ``Brent.Census.closure_saturation_subset_rankBound,
    ``Brent.Census.BoundW.not_mem_rankBound,
    ``Brent.Census.BoundW.not_mem_closure,
    ``Brent.Census.boundWitnesses_check,
    ``Brent.Census.boundWitnesses_indices,
    ``Brent.Census.alphaTensor_bound_excluded,
    ``Brent.squareLocalDimension_eq_197,
    ``Brent.reduced_localDimension_eq_197,
    ``Brent.sqBranchPrime_minimal,
    ``Brent.hilbert_initial_values,
    ``Brent.main_theorem,
    ``Brent.Census.FieldTransfer.rank_map_algebraMap,
    ``Brent.Census.FieldTransfer.rank_intCast_eq,
    ``Brent.Census.Minors.rank_le_iff_minors,
    ``Brent.Census.isClosed_stackOK,
    ``Brent.Census.isClosed_budgetOK,
    ``Brent.Census.family_stackOK,
    ``Brent.Census.closure_stackOK,
    ``Brent.Census.closure_budgetOK,
    ``Brent.Census.rank_modeMat_catPoint,
    ``Brent.Census.rankBounds_of_mem,
    ``Brent.Census.rank_eq_budget,
    ``Brent.Census.canAnchor_of_stack,
    ``Brent.Census.anchorTest_of_mem,
    ``Brent.Census.catalogue_excluded,
    ``Brent.Census.card_excluded,
    ``Brent.Census.catPoint_not_mem_rankBound,
    ``Brent.Census.catPoint_not_mem_saturated,
    ``Brent.Census.rank_bound_exclusions,
    ``Brent.Census.equivalent_changeBasis,
    ``Brent.Census.equivalent_rescale,
    ``Brent.Census.shape_of_equivalent,
    ``Brent.Census.closure_eqClosed_subset,
    ``Brent.Census.anchorTest_of_shape,
    ``Brent.Census.anchor_excluded_eqClosed,
    ``Brent.Census.not_mem_familyClosure,
    ``Brent.Census.excluded_card,
    ``Brent.Catalogue.anchorTest_transfer,
    ``Brent.Catalogue.facts_allFields,
    ``Brent.Catalogue.AllFields.card_fullProfile,
    ``Brent.Catalogue.AllFields.fullProfile_iff_rankBounds,
    ``Brent.Catalogue.AllFields.card_not_rankBounds,
    ``Brent.Catalogue.AllFields.anchor_excluded,
    ``Brent.Catalogue.AllFields.card_pass_both,
    ``Brent.Catalogue.Q.card_fullProfile,
    ``Brent.Catalogue.Q.anchor_excluded,
    ``Brent.Catalogue.F3.card_fullProfile,
    ``Brent.Catalogue.F3.anchor_excluded,
    ``Brent.Census.rank_kron_eq,
    ``Brent.Census.rank_value_eq,
    ``Brent.Census.family_profile,
    ``Brent.Section7.family_rank_profile,
    ``Brent.Section7.closure_dimension,
    ``Brent.Section7.closure_component,
    ``Brent.Section7.closure_minimalPrime,
    ``Brent.Section7.closure_dimension_algClosed,
    ``Brent.Section7.closure_component_algClosed,
    ``Brent.Section7.curve_matrices,
    ``Brent.Section7.smooth_points,
    ``Brent.Section7.swap_symmetry,
    ``Brent.Section7.lwh_point,
    ``Brent.Section7.rank_bounds_closed,
    ``Brent.Section7.anchor_structure_closed,
    ``Brent.Section7.census,
    ``Brent.Section7.rank_bound_exclusion,
    ``Brent.Section7.anchor_exclusion,
    ``Brent.Section7.excluded_count,
    ``Brent.Section3.lemma_base,
    ``Brent.Section3.kron_line,
    ``Brent.Section3.derivative_injective,
    ``Brent.Section3.KMat_line,
    ``Brent.Section3.mixed_independent,
    ``Brent.Section3.two_ne_zero_of,
    ``Brent.TangentData.branchTangent_inf,
    ``Brent.TangentData.finrank_branchTangent,
    ``Brent.TangentData.finrank_orbitTangent,
    ``Brent.TangentData.branchTangent_ne,
    ``Brent.TangentData.branchTangent_generators,
    ``Brent.Decomposition.second_order_expansion,
    ``Brent.Decomposition.liftsToOrderTwo_iff,
    ``Brent.Census.family_factor_ne_zero,
    ``Brent.Z3.kernel_basis_Z3,
    ``Brent.Z3.kernel_retract_Z3,
    ``Brent.Z3.kernel_lift_mod3,
    ``Brent.Z3.kernel_span_field,
    ``Brent.Groebner.isGroebnerBasis_iff,
    ``Brent.Groebner.isGroebnerBasis_of_coprime,
    ``Brent.Groebner.initialIdeal_span_of_coprime,
    ``Brent.Groebner.Paper.degree_q,
    ``Brent.Groebner.Paper.monic_q,
    ``Brent.Groebner.Paper.leadingTerm_q,
    ``Brent.Groebner.Paper.coprime_degree,
    ``Brent.Groebner.Paper.q_isGroebnerBasis,
    ``Brent.Groebner.Paper.q_initialIdeal,
    ``Brent.Groebner.Paper.row11,
    ``Brent.Groebner.MonomialHeight.height_pairIdeal,
    ``Brent.Groebner.MonomialHeight.prime_contains_pair,
    ``Brent.Groebner.MonomialHeight.primeHeight_choice,
    ``Brent.InitialForms.initialRegular_iff,
    ``Brent.InitialForms.principal_exact,
    ``Brent.InitialForms.ker_mapPowerPiece_eq_range,
    ``Brent.InitialForms.firstIdeal_inf_pow_le,
    ``Brent.CM.orderLE_length_fam,
    ``Brent.CM.length_quot_add_le_rel,
    ``Brent.CM.chain_bound,
    ``Brent.CM.length_quot_pow_ne_top,
    ``Brent.CM.gnoeth_grFam,
    ``Brent.CM.orderLE_chi,
    ``Brent.CM.ringKrullDim_le_of_orderLE_chi,
    ``Brent.CM.orderLE_R,
    ``Brent.CM.length_gr_le,
    ``Brent.CM.lemma41_chain,
    ``Brent.CM.lemma41,
    ``Brent.CM.mem_of_mul_mem_of_coprime,
    ``Brent.CM.q_regular,
    ``Brent.CM.LiftInstance.isWeaklyRegular_q,
    ``Brent.CM.LiftInstance.cons_regular_lift,
    ``Brent.CM.LiftInstance.lifted_regular_local,
    ``Brent.CM.LiftInstance.lifted_regular_flat,
    ``Brent.CM.LiftInstance.ker_rho3,
    ``Brent.CM.LiftInstance.lifted_quadrics_regular,
    ``Brent.CM.length_le_card,
    ``Brent.CM.pow_le_span_mono,
    ``Brent.CM.orderLE_hilbR_zero,
    ``Brent.CM.lemma41_of_span,
    ``Brent.CM.PSInstance.Hs_mul,
    ``Brent.CM.PSInstance.Hs_relI,
    ``Brent.CM.PSInstance.hreg_q,
    ``Brent.CM.PSInstance.lemma41_q,
    ``Brent.CM.LiftedQuadrics.map_qtOf,
    ``Brent.CM.LiftedQuadrics.qtOf_regular,
    ``Brent.Census.unique_rankTwo_left,
    ``Brent.Census.unique_rankTwo_right,
    ``Brent.CM.LiftedQuadrics.map_lamExact,
    ``Brent.CM.LiftedQuadrics.lamExact_annihilates,
    ``Brent.CM.LiftedQuadrics.map_qtExact,
    ``Brent.CM.LiftedQuadrics.qtExact_regular,
    ``Brent.CM.LiftedQuadrics.qtCanon_regular,
    ``Brent.LeftKernelLift.span_trace,
    ``Brent.LeftKernelLift.span_selected,
    ``Brent.LeftKernelLift.inLeft_iff_selected,
    ``Brent.LeftKernelLift.D_unit,
    ``Brent.LeftKernelLift.project_inLeft,
    ``Brent.LeftKernelLift.project_eq_self,
    ``Brent.LeftKernelLift.project_idempotent,
    ``Brent.LeftKernelLift.leftKernel_lift_mod3,
    ``Brent.LeftKernelLift.inLeft_iff_jacobian,
    ``Brent.LeftKernelLift.actual_leftKernel_lift_mod3,
    ``Brent.Catalogue.useful_card_le_possible,
    ``Brent.Catalogue.positiveRank_sound,
    ``Brent.Catalogue.positiveUseful_sound,
    ``Brent.Catalogue.exact_usefulAnchors,
    ``Brent.Catalogue.usefulAnchors_2445_Q,
    ``Brent.Catalogue.usefulAnchors_2445_F,
    ``Brent.Catalogue.usefulAnchors_5969_Q,
    ``Brent.Catalogue.usefulAnchors_5969_F,
    ``Brent.Catalogue.usefulAnchors_count_2445,
    ``Brent.Catalogue.usefulAnchors_count_5969,
    ``Brent.CM.firstIdeal_inf_pow_le_relI,
    ``Brent.CM.toGr_firstIdeal_injective,
    ``Brent.CM.lemma41_gradedPieceEquiv,
    ``Brent.PaperDetails.appendix_mixed_entry,
    ``Brent.PaperDetails.appendix_covector_entry,
    ``Brent.PaperDetails.appendix_unique_support,
    ``Brent.PaperDetails.appendix_earlier_zero,
    ``Brent.PaperDetails.appendix_projected_coefficient,
    ``Brent.PaperDetails.int_vanishing_iff_mod,
    ``Brent.PaperDetails.minor_vanishing_iff_mod_prime,
    ``Brent.LeftKernelLift.mem_leftKer,
    ``Brent.LeftKernelLift.leftKernel_linear_retraction,
    ``Brent.LeftKernelLift.leftKernelFreeEquiv,
    ``Brent.LeftKernelLift.leftKernelBasis,
    ``Brent.CM.qPrefix_primeHeight_ge,
    ``Brent.CM.quadraticIdeal_height_eq_54,
    ``Brent.CM.relI_mul_pow,
    ``Brent.CM.graded_product_congr,
    ``Brent.CM.lemma41_product_representatives,
    ``Brent.Formal.map_subst_centered,
    ``Brent.Formal.inverse_tuple_baseChange,
    ``Brent.Formal.normal_substitution_mod3,
    ``Brent.PaperDetails.det_abs_le_factorial,
    ``Brent.PaperDetails.censusPrime_isPrime,
    ``Brent.PaperDetails.censusPrime_hadamard_expression,
    ``Brent.PaperDetails.censusPrime_leibniz_expression,
    ``Brent.PaperDetails.censusMinor_vanishing_iff,
    ``Brent.Formal.NormalEliminationZ3.exists_unit_minor,
    ``Brent.Formal.NormalEliminationZ3.map_eqAt_square,
    ``Brent.Formal.NormalEliminationZ3.map_newCoord,
    ``Brent.Formal.NormalEliminationZ3.exists_centered_inverse,
    ``Brent.Formal.NormalEliminationZ3.normal_elimination_for_minor,
    ``Brent.Formal.NormalEliminationZ3.card_free,
    ``Brent.Formal.NormalEliminationZ3.normal_elimination_exists,
    ``Brent.PaperDetails.HadamardSmall.entry_endpoint,
    ``Brent.PaperDetails.HadamardSmall.corner_dominates_aux,
    ``Brent.PaperDetails.HadamardSmall.sign_bound,
    ``Brent.PaperDetails.HadamardSmall.squared_hadamard,
    ``Brent.PaperDetails.HadamardSmall.censusMinor_vanishing_iff_hadamard,
    ``Brent.CM.GradedRingAssembly.product_mk,
    ``Brent.CM.GradedRingAssembly.pieceEquiv_mul,
    ``Brent.CM.GradedRingAssembly.lemma41_ringEquiv,
    ``Brent.CM.GradedRingAssembly.lemma41_ringEquiv_of,
    ``Brent.CM.firstIdeal_inf_pow_le_relI_prefix,
    ``Brent.CM.GradedRingAssembly.projection_ker,
    ``Brent.CM.GradedRingAssembly.initialQuotientEquiv,
    ``Brent.CM.GradedRingAssembly.lemma41_initialQuotientEquiv,
    ``Brent.CM.GradedPolynomial.H_mul,
    ``Brent.CM.GradedPolynomial.basePolynomialEquiv,
    ``Brent.CM.GradedPolynomial.map_initialIdeal,
    ``Brent.CM.GradedPolynomial.H_mem_iff_relI,
    ``Brent.CM.GradedPolynomial.initialRegular_of_polynomial,
    ``Brent.CM.GradedPolynomial.lemma41_polynomialQuotientEquiv,
    ``Brent.CM.GradedPolynomial.lemma41_polynomialQuotientEquiv_of_regular,
    ``Brent.CM.GradedPolynomial.lemma41_finite_polynomialQuotientEquiv,
    ``Brent.Formal.OrbitClosure.orbitClosure_vanishingIdeal,
    ``Brent.Formal.OrbitClosure.centralNormalize_value,
    ``Brent.Formal.OrbitClosure.rowsA_cover,
    ``Brent.Formal.OrbitClosure.orbit_trdeg_lower,
    ``Brent.Formal.OrbitClosure.ker_gaugePsi,
    ``Brent.Formal.OrbitClosure.orbit_trdeg_upper,
    ``Brent.Formal.OrbitClosure.orbitClosure_dimension_eq_143,
    ``Brent.Formal.OrbitClosure.orbitClosure_localDimension_eq_143,
    ``Brent.Formal.OrbitClosure.point_mem_orbitClosure,
    ``Brent.Formal.NormalEliminationZ3.coeff_frame_eqAt,
    ``Brent.Formal.NormalEliminationZ3.inverse_in_frame,
    ``Brent.Formal.NormalEliminationZ3.normal_elimination_frozen_frame,
    ``Brent.Formal.NormalEliminationZ3.weighted_residual_mod_cube,
    ``Brent.Formal.NormalEliminationZ3.actual_residual_initial_quadric,
    ``Brent.Formal.NormalEliminationZ3.liftBilinear_diag,
    ``Brent.Formal.NormalEliminationZ3.liftPolar_nonmixed,
    ``Brent.Formal.NormalEliminationZ3.liftPolar_mixed,
    ``Brent.Formal.NormalEliminationZ3.fullFrameQuadric_mixed
  ]
  for name in theorems do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter (fun dependency =>
      !([``propext, ``Classical.choice, ``Quot.sound].contains dependency))
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.toList}"

#print axioms Brent.main_theorem
#print axioms Brent.Section7.anchor_exclusion
