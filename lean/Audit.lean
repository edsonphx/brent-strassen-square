import Brent
import Brent.KernelCheck.SquareJacobianRank
import Brent.KernelCheck.QuadraticCertificates
import Brent.KernelCheck.TangentFrame
import Brent.KernelCheck.JetProjection
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
    ``Brent.localDimension_le_of_power_le_span_sup_pow
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
#print axioms Brent.QuadraticData.archived_covectors_annihilate
#print axioms Brent.QuadraticData.archived_mixed_coefficients
#print axioms Brent.TangentData.archived_frame_tangent
#print axioms Brent.TangentData.archived_frame_split
